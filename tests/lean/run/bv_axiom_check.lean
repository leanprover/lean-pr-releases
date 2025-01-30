import Std.Tactic.BVDecide

open BitVec

theorem bv_axiomCheck (x : BitVec 2) : x &&& 1 = (x <<< 1) >>> 1 := by
  bv_decide

/--
info: 'bv_axiomCheck' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms bv_axiomCheck
