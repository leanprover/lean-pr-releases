example : (0 : Nat) = Nat.zero := by
  simp only [OfNat.ofNat]

example : (0 : Fin 9) = (Fin.ofNat' _ 0) := by
  simp only [OfNat.ofNat]
