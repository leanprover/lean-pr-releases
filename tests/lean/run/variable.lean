/-! # Basic section variable tests -/

/-! Directly referenced variables should be included. -/

variable {n : Nat} in
theorem t1 : n = n := by induction n <;> rfl

/-! Variables mentioned only in the body should not be included. -/
variable {n : Nat} in
/-- error: unknown identifier 'n' -/
#guard_msgs in
theorem t2 : ∃ (n : Nat), n = n := by exists n

/-! Variables transitively mentioned should be included. -/
variable {n : Nat} (h : n = n) in
theorem t3 : h = h := rfl

/-! Instance variables mentioning only included variables should be included. -/
variable {α : Type} [ToString α] in
theorem t4 (a : α) : a = a := let _ := toString a; rfl

/-! Instance variables not mentioning only included variables should not be included. -/
variable {α β : Type} [Coe α β] in
/--
error: don't know how to synthesize placeholder
context:
α : Type
a : α
⊢ a = a
-/
#guard_msgs in
theorem t5 (a : α) : a = a := _

/-! Accidentally included variables should be warned for. -/
variable {α : Type} [ToString α] in
/-- warning: included section variable '[ToString α]' is not used in 't6', consider excluding it -/
#guard_msgs in
theorem t6 (a : α) : a = a := rfl

/-! `include` should always include. -/
variable {n : Nat} in
include n in
theorem t7 : ∃ (n : Nat), n = n := by exists n
