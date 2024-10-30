/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
prelude
import Lean.Meta.Eval
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars
import Lean.Linter.MissingDocs

namespace Lean.Elab.Tactic
open Meta Parser.Tactic Command

/--
Extracts the items from a tactic configuration,
either a `Lean.Parser.Tactic.optConfig`, `Lean.Parser.Tactic.config`, or these wrapped in null nodes.
-/
private partial def getConfigItems (c : Syntax) : TSyntaxArray ``configItem :=
  if c.isOfKind nullKind then
    c.getArgs.flatMap getConfigItems
  else
    match c with
    | `(optConfig| $items:configItem*) => items
    | `(config| (config := $val)) => #[Unhygienic.run <| withRef c `(configItem| (config := $val))]
    | _ => #[]

/--
Appends two tactic configurations.
The configurations can be `Lean.Parser.Tactic.optConfig`, `Lean.Parser.Tactic.config`,
or these wrapped in null nodes (for example because the syntax is `(config)?`).
-/
def appendConfig (cfg cfg' : Syntax) : TSyntax ``optConfig :=
  Unhygienic.run `(optConfig| $(getConfigItems cfg)* $(getConfigItems cfg')*)

private structure ConfigItemView where
  ref : Syntax
  option : Ident
  value : Term
  /-- Whether this was using `+`/`-`, to be able to give a better error message on type mismatch. -/
  (bool : Bool := false)

/-- Interprets the `config` as an array of option/value pairs. -/
private def mkConfigItemViews (c : TSyntaxArray ``configItem) : Array ConfigItemView :=
  c.map fun item =>
    match item with
    | `(configItem| ($option:ident := $value)) => { ref := item, option, value }
    | `(configItem| +$option) => { ref := item, option, bool := true, value := mkCIdentFrom item ``true }
    | `(configItem| -$option) => { ref := item, option, bool := true, value := mkCIdentFrom item ``false }
    | _ => { ref := item, option := ⟨Syntax.missing⟩, value := ⟨Syntax.missing⟩ }

/--
Expands a field access into full field access like `toB.toA.x`.
Returns that and the last projection function for `x` itself.
-/
private def expandFieldName (structName : Name) (fieldName : Name) : MetaM (Name × Name) := do
  let env ← getEnv
  unless isStructure env structName do throwError "'{.ofConstName structName}' is not a structure"
  let some baseStructName := findField? env structName fieldName
    | throwError "structure '{.ofConstName structName}' does not have a field named '{fieldName}'"
  let some path := getPathToBaseStructure? env baseStructName structName
    | throwError "(internal error) failed to access field '{fieldName}' in parent structure"
  let field := path.foldl (init := .anonymous) (fun acc s => Name.appendCore acc <| Name.mkSimple s.getString!) ++ fieldName
  let fieldInfo := (getFieldInfo? env baseStructName fieldName).get!
  return (field, fieldInfo.projFn)


/--
Given a hierarchical name `field`, returns the fully resolved field access, the base struct name, and the last projection function.
-/
private partial def expandField (structName : Name) (field : Name) : MetaM (Name × Name) := do
  match field with
  | .num .. | .anonymous => throwError m!"invalid configuration field"
  | .str .anonymous fieldName => expandFieldName structName (Name.mkSimple fieldName)
  | .str field' fieldName =>
    let (field', projFn) ← expandField structName field'
    let notStructure {α} : MetaM α := throwError "field '{field'}' of structure '{.ofConstName structName}' is not a structure"
    let .const structName' _ := (← getConstInfo projFn).type.getForallBody | notStructure
    unless isStructure (← getEnv) structName' do notStructure
    let (field'', projFn) ← expandFieldName structName' (Name.mkSimple fieldName)
    return (field' ++ field'', projFn)

/-- Elaborates a tactic configuration. -/
private def elabConfig (recover : Bool) (structName : Name) (items : Array ConfigItemView) : TermElabM Expr :=
  withoutModifyingStateWithInfoAndMessages <| withLCtx {} {} <| withSaveInfoContext do
    let mut base? : Option Term := none
    let mut fields : TSyntaxArray ``Parser.Term.structInstField := #[]
    for item in items do
      try
        let option := item.option.getId.eraseMacroScopes
        if option == `config then
          base? ← withRef item.value `(($item.value : $(mkCIdent structName)))
          fields := #[]
        else
          addCompletionInfo <| CompletionInfo.fieldId item.option option {} structName
          let (path, projFn) ← withRef item.option <| expandField structName option
          if item.bool then
            -- Verify that the type is `Bool`
            unless (← getConstInfo projFn).type.bindingBody! == .const ``Bool [] do
              throwErrorAt item.ref m!"option is not boolean-valued, so '({option} := ...)' syntax must be used"
          let value ←
            match item.value with
            | `(by $seq:tacticSeq) =>
              -- Special case: `(opt := by tacs)` uses the `tacs` syntax itself
              withRef item.value <| `(Unhygienic.run `(tacticSeq| $seq))
            | value => pure value
          fields := fields.push <| ← `(Parser.Term.structInstField|
            $(mkCIdentFrom item.option path (canonical := true)):ident := $value)
      catch ex =>
        if recover then
          logException ex
        else
          throw ex
    let stx : Term ← `({$[$base? with]? $fields*})
    let e ← Term.withSynthesize <| Term.elabTermEnsuringType stx (mkConst structName)
    instantiateMVars e

private def mkConfigElaborator
    (doc? : Option (TSyntax ``Parser.Command.docComment)) (elabName type monadName : Ident)
    (adapt recover : Term) : MacroM (TSyntax `command) := do
  let empty ← withRef type `({ : $type})
  `(unsafe def evalUnsafe (e : Expr) : TermElabM $type :=
      Meta.evalExpr' (safety := .unsafe) $type ``$type e
    @[implemented_by evalUnsafe] opaque eval (e : Expr) : TermElabM $type
    $[$doc?:docComment]?
    def $elabName (optConfig : Syntax) : $monadName $type := $adapt do
      let recover := $recover
      let go : TermElabM $type := withRef optConfig do
        let items := mkConfigItemViews (getConfigItems optConfig)
        if items.isEmpty then
          return $empty
        unless (← getEnv).contains ``$type do
          throwError m!"error evaluating configuration, environment does not yet contain type {``$type}"
        let c ← elabConfig recover ``$type items
        if c.hasSyntheticSorry then
          -- An error is already logged, return the default.
          return $empty
        if c.hasSorry then
          throwError m!"configuration contains 'sorry'"
        try
          let res ← eval c
          return res
        catch ex =>
          let msg := m!"error evaluating configuration\n{indentD c}\n\nException: {ex.toMessageData}"
          if false then
            logError msg
            return $empty
          else
            throwError msg
      go)

/-!
`declare_config_elab elabName TypeName` declares a function `elabName : Syntax → TacticM TypeName`
that elaborates a tactic configuration.
The tactic configuration can be from `Lean.Parser.Tactic.optConfig` or `Lean.Parser.Tactic.config`,
and these can also be wrapped in null nodes (for example, from `(config)?`).

The elaborator responds to the current recovery state.

For defining elaborators for commands, use `declare_command_config_elab`.
-/
macro (name := configElab) doc?:(docComment)? "declare_config_elab" elabName:ident type:ident : command => do
  mkConfigElaborator doc? elabName type (mkCIdent ``TacticM) (mkCIdent ``id) (← `((← read).recover))

open Linter.MissingDocs in
@[builtin_missing_docs_handler Elab.Tactic.configElab]
def checkConfigElab : SimpleHandler := mkSimpleHandler "config elab"

/-!
`declare_command_config_elab elabName TypeName` declares a function `elabName : Syntax → CommandElabM TypeName`
that elaborates a command configuration.
The configuration can be from `Lean.Parser.Tactic.optConfig` or `Lean.Parser.Tactic.config`,
and these can also be wrapped in null nodes (for example, from `(config)?`).

The elaborator has error recovery enabled.
-/
macro (name := commandConfigElab) doc?:(docComment)? "declare_command_config_elab" elabName:ident type:ident : command => do
  mkConfigElaborator doc? elabName type (mkCIdent ``CommandElabM) (mkCIdent ``liftTermElabM) (mkCIdent ``true)

open Linter.MissingDocs in
@[builtin_missing_docs_handler Elab.Tactic.commandConfigElab]
def checkCommandConfigElab : SimpleHandler := mkSimpleHandler "config elab"

end Lean.Elab.Tactic
