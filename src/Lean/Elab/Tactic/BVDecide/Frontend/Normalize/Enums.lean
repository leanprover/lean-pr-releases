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
inductive Enum where
  | a
  | b
  | c
  | d

noncomputable def f : Enum → BitVec 2 := Enum.rec (motive := fun _ => BitVec 2) 0#2 1#2 2#2 3#2
- Prove theorem of the form:
  ∀ (x y : Enum), x = y ↔ f x = f y
- substitute with this theorem
- open questions:
  - how to handle `f` applied to constants?
  - how to handle match statements?
```
-/

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
