import Std.Tactic.BVDecide

inductive State where
  | s1
  | s2
  deriving DecidableEq


structure Machine where
  x : BitVec 64
  s : State

def Machine.transform (m : Machine) : Machine :=
  if m.s = .s1 then
    m
  else if m.s = .s2 then
    if m.x < 10 then
      { m with x := m.x + 1 }
    else
      { m with s := .s1, x := 10 }
  else
    m

example (m : Machine) : (m.transform).x ≤ 10 := by
  simp [Machine.transform]
  sorry

example (m1 m2 : Machine) : m1 = m2 := by
  bv_normalize
  sorry

inductive Enum where
  | a
  | b
  | c
  | d
  deriving DecidableEq

noncomputable def f : Enum → BitVec 2 := Enum.rec (motive := fun _ => BitVec 2) 0#2 1#2 2#2 3#2

theorem Enum.f_respects : ∀ (x y : Enum), x = y ↔ f x = f y := by sorry

example (x y : Enum) : (if x = y then 1#2 else 0#2) = 0#2 := by
  simp [Enum.f_respects]
  bv_decide
