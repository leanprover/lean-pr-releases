/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt.Basic
import Init.Data.Fin.Lemmas
import Init.Data.BitVec.Lemmas
import Init.Data.BitVec.Bitblast

set_option hygiene false in
macro "declare_uint_theorems" typeName:ident : command =>
`(
namespace $typeName

instance : Inhabited $typeName where
  default := 0

theorem zero_def : (0 : $typeName) = ⟨0⟩ := rfl
theorem one_def : (1 : $typeName) = ⟨1⟩ := rfl
theorem sub_def (a b : $typeName) : a - b = ⟨a.toBitVec - b.toBitVec⟩ := rfl
theorem mul_def (a b : $typeName) : a * b = ⟨a.toBitVec * b.toBitVec⟩ := rfl
theorem mod_def (a b : $typeName) : a % b = ⟨a.toBitVec % b.toBitVec⟩ := rfl
theorem add_def (a b : $typeName) : a + b = ⟨a.toBitVec + b.toBitVec⟩ := rfl

@[simp] theorem mk_toBitVec_eq : ∀ (a : $typeName), mk a.toBitVec = a
  | ⟨_, _⟩ => rfl

theorem toBitVec_eq_of_lt {a : Nat} : a < size → (ofNat a).toBitVec.toNat = a :=
  Nat.mod_eq_of_lt

theorem toNat_ofNat_of_lt {n : Nat} (h : n < size) : (ofNat n).toNat = n := by
  rw [toNat, toBitVec_eq_of_lt h]

theorem le_def {a b : $typeName} : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := .rfl

theorem lt_def {a b : $typeName} : a < b ↔ a.toBitVec < b.toBitVec := .rfl

@[simp] protected theorem not_le {a b : $typeName} : ¬ a ≤ b ↔ b < a := by simp [le_def, lt_def]

@[simp] protected theorem not_lt {a b : $typeName} : ¬ a < b ↔ b ≤ a := by simp [le_def, lt_def]

@[simp] protected theorem le_refl (a : $typeName) : a ≤ a := by simp [le_def]

@[simp] protected theorem lt_irrefl (a : $typeName) : ¬ a < a := by simp

protected theorem le_trans {a b c : $typeName} : a ≤ b → b ≤ c → a ≤ c := by
  simp only [le_def, lt_def]
  apply BitVec.le_trans

protected theorem lt_trans {a b c : $typeName} : a < b → b < c → a < c := by
  simp only [le_def, lt_def]
  apply BitVec.lt_trans

protected theorem le_total (a b : $typeName) : a ≤ b ∨ b ≤ a := by
  simp only [le_def, lt_def]
  apply BitVec.le_total

protected theorem lt_asymm {a b : $typeName} : a < b → ¬ b < a := by
  simp only [le_def, lt_def]
  apply BitVec.lt_asymm

protected theorem toBitVec_eq_of_eq {a b : $typeName} (h : a = b) : a.toBitVec = b.toBitVec := h ▸ rfl

protected theorem eq_of_toBitVec_eq {a b : $typeName} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; simp_all

open $typeName (toBitVec_eq_of_eq) in
protected theorem ne_of_toBitVec_ne {a b : $typeName} (h : a.toBitVec ≠ b.toBitVec) : a ≠ b :=
  fun h' => absurd (toBitVec_eq_of_eq h') h

open $typeName (ne_of_toBitVec_ne) in
protected theorem ne_of_lt {a b : $typeName} (h : a < b) : a ≠ b := by
  apply ne_of_toBitVec_ne
  apply BitVec.ne_of_lt
  simpa [lt_def] using h

@[simp] protected theorem toNat_zero : (0 : $typeName).toNat = 0 := Nat.zero_mod _

@[simp] protected theorem toNat_mod (a b : $typeName) : (a % b).toNat = a.toNat % b.toNat := BitVec.toNat_umod ..

@[simp] protected theorem toNat_div (a b : $typeName) : (a / b).toNat = a.toNat / b.toNat := BitVec.toNat_udiv  ..

@[simp] protected theorem toNat_sub_of_le (a b : $typeName) : b ≤ a → (a - b).toNat = a.toNat - b.toNat := sorry--Fin.sub_val_of_le

protected theorem mod_lt (a : $typeName) {b : $typeName} : 0 < b → a % b < b := by
  simp only [lt_def, mod_def]
  apply BitVec.umod_lt

protected theorem toNat.inj : ∀ {a b : $typeName}, a.toNat = b.toNat → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

protected theorem toNat_lt_size (a : $typeName) : a.toNat < size := a.toBitVec.isLt

@[simp] protected theorem ofNat_one : ofNat 1 = 1 := rfl

end $typeName
)

declare_uint_theorems UInt8
declare_uint_theorems UInt16
declare_uint_theorems UInt32
declare_uint_theorems UInt64
declare_uint_theorems USize

theorem UInt32.toNat_lt_of_lt {n : UInt32} {m : Nat} (h : n < OfNat.ofNat m) :
    n.toNat < m := sorry

theorem UInt32.lt_toNat_of_lt {n : UInt32} {m : Nat} (h : OfNat.ofNat m < n) :
    m < n.toNat := sorry

theorem UInt32.toNat_le_of_le {n : UInt32} {m : Nat} (h : n ≤ OfNat.ofNat m) :
    n.toNat ≤ m := sorry

theorem UInt32.le_toNat_of_le {n : UInt32} {m : Nat} (h : OfNat.ofNat m ≤ n) :
    m ≤ n.toNat := sorry

@[deprecated (since := "2024-06-23")] protected abbrev UInt8.zero_toNat := @UInt8.toNat_zero
@[deprecated (since := "2024-06-23")] protected abbrev UInt8.div_toNat := @UInt8.toNat_div
@[deprecated (since := "2024-06-23")] protected abbrev UInt8.mod_toNat := @UInt8.toNat_mod

@[deprecated (since := "2024-06-23")] protected abbrev UInt16.zero_toNat := @UInt16.toNat_zero
@[deprecated (since := "2024-06-23")] protected abbrev UInt16.div_toNat := @UInt16.toNat_div
@[deprecated (since := "2024-06-23")] protected abbrev UInt16.mod_toNat := @UInt16.toNat_mod

@[deprecated (since := "2024-06-23")] protected abbrev UInt32.zero_toNat := @UInt32.toNat_zero
@[deprecated (since := "2024-06-23")] protected abbrev UInt32.div_toNat := @UInt32.toNat_div
@[deprecated (since := "2024-06-23")] protected abbrev UInt32.mod_toNat := @UInt32.toNat_mod

@[deprecated (since := "2024-06-23")] protected abbrev UInt64.zero_toNat := @UInt64.toNat_zero
@[deprecated (since := "2024-06-23")] protected abbrev UInt64.div_toNat := @UInt64.toNat_div
@[deprecated (since := "2024-06-23")] protected abbrev UInt64.mod_toNat := @UInt64.toNat_mod

@[deprecated (since := "2024-06-23")] protected abbrev USize.zero_toNat := @USize.toNat_zero
@[deprecated (since := "2024-06-23")] protected abbrev USize.div_toNat := @USize.toNat_div
@[deprecated (since := "2024-06-23")] protected abbrev USize.mod_toNat := @USize.toNat_mod
