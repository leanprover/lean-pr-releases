/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter
import Lean.Parser.Module
import Lean.ParserCompiler

namespace Lean

def PPContext.runCoreM {α : Type} (ppCtx : PPContext) (x : CoreM α) : IO α :=
  Prod.fst <$> x.toIO { options := ppCtx.opts, currNamespace := ppCtx.currNamespace
                        openDecls := ppCtx.openDecls
                        fileName := "<PrettyPrinter>", fileMap := default
                        diag     := getDiag ppCtx.opts }
                      { env := ppCtx.env, ngen := { namePrefix := `_pp_uniq } }

def PPContext.runMetaM {α : Type} (ppCtx : PPContext) (x : MetaM α) : IO α :=
  ppCtx.runCoreM <| x.run' { lctx := ppCtx.lctx } { mctx := ppCtx.mctx }

namespace PrettyPrinter

def ppCategory (cat : Name) (stx : Syntax) : CoreM Format := do
  let opts ← getOptions
  let stx := (sanitizeSyntax stx).run' { options := opts }
  parenthesizeCategory cat stx >>= formatCategory cat

def ppTerm (stx : Term) : CoreM Format := ppCategory `term stx

def ppUsing (e : Expr) (delab : Expr → MetaM Term) : MetaM Format := do
  let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx lctx #[] do
    ppTerm (← delab e)

def ppExpr (e : Expr) : MetaM Format := do
  ppUsing e delab

/-- Return a `fmt` representing pretty-printed `e` together with a map from tags in `fmt`
to `Elab.Info` nodes produced by the delaborator at various subexpressions of `e`. -/
def ppExprWithInfos (e : Expr) (optsPerPos : Delaborator.OptionsPerPos := {}) (delab := Delaborator.delab)
    : MetaM FormatWithInfos := do
  let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx lctx #[] do
    let (stx, infos) ← delabCore e optsPerPos delab
    let fmt ← ppTerm stx
    return ⟨fmt, infos⟩

@[export lean_pp_expr]
def ppExprLegacy (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : IO Format :=
  Prod.fst <$> ((withOptions (fun _ => opts) <| ppExpr e).run' { lctx := lctx } { mctx := mctx }).toIO
    { fileName := "<PrettyPrinter>", fileMap := default }
    { env := env }

def ppTactic (stx : TSyntax `tactic) : CoreM Format := ppCategory `tactic stx

def ppCommand (stx : Syntax.Command) : CoreM Format := ppCategory `command stx

def ppModule (stx : TSyntax ``Parser.Module.module) : CoreM Format := do
  parenthesize Lean.Parser.Module.module.parenthesizer stx >>= format Lean.Parser.Module.module.formatter

open Delaborator in
/-- Pretty-prints a declaration `c` as `c.{<levels>} <params> : <type>`. -/
def ppSignature (c : Name) : MetaM FormatWithInfos := do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← delabCore e (delab := delabConstWithSignature)
  return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term

private partial def noContext : MessageData → MessageData
  | MessageData.withContext _   msg => noContext msg
  | MessageData.withNamingContext ctx msg => MessageData.withNamingContext ctx (noContext msg)
  | MessageData.nest n msg => MessageData.nest n (noContext msg)
  | MessageData.group msg  => MessageData.group (noContext msg)
  | MessageData.compose msg₁ msg₂ => MessageData.compose (noContext msg₁) (noContext msg₂)
  | MessageData.tagged tag msg => MessageData.tagged tag (noContext msg)
  | MessageData.trace data header children =>
    MessageData.trace data (noContext header) (children.map noContext)
  | msg => msg

-- strip context (including environments with registered pretty printers) to prevent infinite recursion when pretty printing pretty printer error
private def withoutContext {m} [MonadExcept Exception m] (x : m α) : m α :=
  tryCatch x fun
    | Exception.error ref msg => throw <| Exception.error ref (noContext msg)
    | ex                      => throw ex

builtin_initialize
  ppFnsRef.set {
    ppExprWithInfos := fun ctx e => ctx.runMetaM <| withoutContext <| ppExprWithInfos e,
    ppTerm := fun ctx stx => ctx.runCoreM <| withoutContext <| ppTerm stx,
    ppLevel := fun ctx l => return l.format (mvars := getPPMVars ctx.opts),
    ppGoal := fun ctx mvarId => ctx.runMetaM <| withoutContext <| Meta.ppGoal mvarId
  }

builtin_initialize
  registerTraceClass `PrettyPrinter

@[builtin_init]
unsafe def registerParserCompilers : IO Unit := do
  ParserCompiler.registerParserCompiler ⟨`parenthesizer, parenthesizerAttribute, combinatorParenthesizerAttribute⟩
  ParserCompiler.registerParserCompiler ⟨`formatter, formatterAttribute, combinatorFormatterAttribute⟩

end PrettyPrinter

namespace MessageData

open Lean PrettyPrinter Delaborator

/--
Turns a `MetaM FormatWithInfos` into a `MessageData` using `.ofPPFormat` and running the monadic value in the given context.
Uses the `pp.tagAppFns` option to annotate constants with terminfo, which is necessary for seeing the type on mouse hover.
-/
def ofFormatWithInfosM
    (fmt : MetaM FormatWithInfos)
    (noContext : Unit → Format := fun _ => "<no context, could not generate MessageData>") : MessageData :=
  .ofPPFormat
  { pp := fun
      | some ctx => ctx.runMetaM <| withOptions (pp.tagAppFns.set · true) fmt
      | none => return noContext () }

/-- Pretty print a const expression using `delabConst` and generate terminfo.
This function avoids inserting `@` if the constant is for a function whose first
argument is implicit, which is what the default `toMessageData` for `Expr` does.
Panics if `e` is not a constant. -/
def ofConst (e : Expr) : MessageData :=
  if e.isConst then
    .ofFormatWithInfosM (PrettyPrinter.ppExprWithInfos (delab := delabConst) e) fun _ => f!"{e}"
  else
    panic! "not a constant"

/-- Generates `MessageData` for a declaration `c` as `c.{<levels>} <params> : <type>`, with terminfo. -/
def signature (c : Name) : MessageData :=
  .ofFormatWithInfosM (PrettyPrinter.ppSignature c) fun _ => f!"{c}"

end MessageData

end Lean
