/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Grind.PropagatorAttr

namespace Lean.Meta.Grind

/--
Returns `Grind.MatchCond e`.
Recall that `Grind.MatchCond` is an identity function,
but the following simproc is used to prevent the term `e` from being simplified,
and we have special support for propagating is truth value.
-/
def markAsMatchCond (e : Expr) : Expr :=
  mkApp (mkConst ``Grind.MatchCond) e

builtin_dsimproc_decl reduceMatchCond (Grind.MatchCond _) := fun e => do
  let_expr Grind.MatchCond _ ← e | return .continue
  return .done e

/-- Adds `reduceMatchCond` to `s` -/
def addMatchCond (s : Simprocs) : CoreM Simprocs := do
  s.add ``reduceMatchCond (post := false)

/--
Helper function for `isSatisfied`.
See `isSatisfied`.
-/
private partial def isMatchCondFalseHyp (e : Expr) : GoalM Bool := do
  match_expr e with
  | Eq _ lhs rhs => isFalse lhs rhs
  | HEq _ lhs _ rhs => isFalse lhs rhs
  | _ => return false
where
  isFalse (lhs rhs : Expr) : GoalM Bool := do
    if lhs.hasLooseBVars then return false
    let root ← getRootENode lhs
    if root.ctor then
      let some ctorLhs ← isConstructorApp? root.self | return false
      let some ctorRhs ← isConstructorApp? rhs | return false
      if ctorLhs.name ≠ ctorRhs.name then return true
      let lhsArgs := root.self.getAppArgs
      let rhsArgs := rhs.getAppArgs
      for i in [ctorLhs.numParams : ctorLhs.numParams + ctorLhs.numFields] do
        if (← isFalse lhsArgs[i]! rhsArgs[i]!) then
          return true
      return false
    else if root.interpreted then
      if rhs.hasLooseBVars then return false
      unless (← isLitValue rhs) do return false
      return (← normLitValue root.self) != (← normLitValue rhs)
    else
      return false

/--
Returns `true` if `e` is a `Grind.MatchCond`, and it has been satifisfied.
Recall that we use `Grind.MatchCond` to annotate conditional `match`-equations.
Consider the following example:
```
inductive S where
  | mk1 (n : Nat)
  | mk2 (n : Nat) (s : S)
  | mk3 (n : Bool)
  | mk4 (s1 s2 : S)

def f (x y : S) :=
  match x, y with
  | .mk1 _, _ => 2
  | _, .mk2 1 (.mk4 _ _) => 3
  | .mk3 _, _ => 4
  | _, _ => 5
```
The `match`-expression in the example above has overlapping patterns and
consequently produces conditional `match` equations. Thus, `grind` generates
the following auxiliary `Grind.MatchCond` terms for an application `f a b`:
- `Grind.MatchCond (∀ (n : Nat), a = S.mk1 n → False)`
- `Grind.MatchCond (∀ (s1 s2 : S), b = S.mk2 1 (s1.mk4 s2) → False)`
- `Grind.MatchCond (∀ (n : Bool), a = S.mk3 n → False)`

`isSatisfied` uses the fact that constructor applications and literal values
are always the root of their equivalence classes.
-/
private partial def isStatisfied (e : Expr) : GoalM Bool := do
  let_expr Grind.MatchCond e ← e | return false
  let mut e := e
  repeat
    let .forallE _ d b _ := e | break
    if (← isMatchCondFalseHyp d) then
      trace[grind.debug.matchCond] "satifised{indentExpr e}\nthe following equality is false{indentExpr d}"
      return true
    e := b
  return false

private partial def mkMatchCondProof? (e : Expr) : GoalM (Option Expr) := do
  let_expr Grind.MatchCond f ← e | return none
  forallTelescopeReducing f fun xs _ => do
    for x in xs do
      let type ← inferType x
      if (← isMatchCondFalseHyp type) then
        trace[grind.debug.matchCond] ">>> {type}"
        let some h ← go? x | pure ()
        return some (← mkLambdaFVars xs h)
    return none
where
  go? (h : Expr) : GoalM (Option Expr) := do
    trace[grind.debug.matchCond] "go?: {← inferType h}"
    let (lhs, rhs, isHeq) ← match_expr (← inferType h) with
      | Eq _ lhs rhs => pure (lhs, rhs, false)
      | HEq _ lhs _ rhs => pure (lhs, rhs, true)
      | _ => return none
    let target ← (← get).mvarId.getType
    let root ← getRootENode lhs
    let h ← if isHeq then
      mkEqOfHEq (← mkHEqTrans (← mkHEqProof root.self lhs) h)
    else
      mkEqTrans (← mkEqProof root.self lhs) h
    if root.ctor then
      let some ctorLhs ← isConstructorApp? root.self | return none
      let some ctorRhs ← isConstructorApp? rhs | return none
      let h ← mkNoConfusion target h
      if ctorLhs.name ≠ ctorRhs.name then
        return some h
      else
        let .forallE _ k _ _ ← whnfD (← inferType h)
          | return none
        forallTelescopeReducing k fun xs _ => do
          for x in xs do
            let some hx ← go? x | pure ()
            return some (mkApp h (← mkLambdaFVars xs hx))
          return none
    else if root.interpreted then
      if (← normLitValue root.self) != (← normLitValue rhs) then
        let hne ← mkDecideProof (mkNot (← mkEq root.self rhs))
        return some (mkApp hne h)
      else
        return none
    else
      return none

/-- Propagates `MatchCond` upwards -/
builtin_grind_propagator propagateMatchCond ↑Grind.MatchCond := fun e => do
  trace[grind.debug.matchCond] "visiting{indentExpr e}"
  if !(← isStatisfied e) then return ()
  let some h ← mkMatchCondProof? e
     | reportIssue m!"failed to construct proof for{indentExpr e}"; return ()
  trace[grind.debug.matchCond] "{← inferType h}"
  pushEqTrue e <| mkEqTrueCore e h

end Lean.Meta.Grind
