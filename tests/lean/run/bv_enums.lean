import Std.Tactic.BVDecide


namespace Ex1

inductive State where
  | s1
  | s2

structure Pair where
  x : BitVec 16
  s : State

example (a b c : Pair) (h1 : a = b) (h2 : b.x < c.x) (h3 : b.s = c.s) : a.s = c.s ∧ a.x < c.x := by
  bv_normalize
  sorry

end Ex1
