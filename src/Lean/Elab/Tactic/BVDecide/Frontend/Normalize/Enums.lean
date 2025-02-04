/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic


namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

partial def enumsPass : Pass where
  name := `enums
  run' goal := return goal

/-
Plan:
- Identify inductive enums that are present in the goal
  - this information is already computed in structuresPass
  - maybe have a type information pass that runs if enums or structures are activated and stored the
    information in the PreProcessM monad?
- Generate functions that turn them into BitVec
  - In the first iteration only support types with perfect power of two sizes
```
inductive Simple where
  | a
  | b
  | c

noncomputable def f (x : Simple) : BitVec 2 := Simple.rec 0#2 1#2 2#2 x
noncomputable def g (x : BitVec 2) : Simple :=
  if x = 0 then .a else if x = 1 then .b else if x = 2 then .c else .c

example : ∀ x y, x = y ↔ f x = f y := by
  apply respects_of_inv (g := g)
  intro x
  cases x <;> rfl

example : ∀ x, f x < 3 := by
  intro x
  cases x
  · show_term decide
  · decide
  · decide

- open questions:
  - how to handle `f` applied to constants?
  - how to handle match statements?
```
-/

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
