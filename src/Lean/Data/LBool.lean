/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.ToString.Basic

namespace Lean

inductive LBool where
  | false
  | true
  | undef
  deriving Inhabited, BEq

namespace LBool

def neg : LBool → LBool
  | true  => false
  | false => true
  | undef => undef

def and : LBool → LBool → LBool
  | true,  b  => b
  | a,     _  => a

def toString : LBool → String
  | true  => "true"
  | false => "false"
  | undef => "undef"

instance : ToString LBool := ⟨toString⟩

end LBool

end Lean

def Bool.toLBool : Bool → Lean.LBool
  | true  => Lean.LBool.true
  | false => Lean.LBool.false

@[inline] def toLBoolM {m : Type → Type} [Monad m] (x : m Bool) : m Lean.LBool := do
  let b ← x
  pure b.toLBool

def Lean.LBool.toExcept (e : ε) : Lean.LBool → Except ε Bool
  | true  => .ok Bool.true
  | false => .ok Bool.false
  | undef => .error e

@[inline] def Lean.LBool.toExceptM {m : Type → Type} [Monad m] (e : ε) (x : m Lean.LBool) : m (Except ε Bool) := do
  let b ← x
  return b.toExcept e
