import PartitionsLeanblueprint.ModularFormDefs
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Multinomial

open ModularFormDefs Regular Integer


noncomputable section

namespace Modulo2


def reduce (ℓ : ℕ) (a : ℕ → ℤ) [NeZero ℓ] : (ℕ → ZMod ℓ) :=
  fun n ↦ a n


-- A modular form mod ℓ has a weight defined by the congruence of its weight mod ℓ - 1
structure ModularFormMod (ℓ : ℕ) [NeZero ℓ] (k : ZMod (ℓ - 1)) where

  sequence : (ℕ → ZMod ℓ)

  modular : ∃ k' : ℕ, ∃ a : IntegerModularForm k', k' = k ∧ sequence = reduce ℓ a
-- or (k : Fin ℓ), ℓ ∣ k' - k.1


variable {k : ℕ}

def Reduce (a : IntegerModularForm k) ℓ [NeZero ℓ] : ModularFormMod ℓ (k : ZMod (ℓ - 1)) where
  sequence := reduce ℓ a
  modular := ⟨k, a, rfl, rfl⟩



variable {ℓ : ℕ} [NeZero ℓ]
variable {k j : ZMod (ℓ-1)}


instance (priority := 100) : FunLike (ModularFormMod ℓ k) ℕ (ZMod ℓ) where
  coe a := a.1
  coe_injective' a b c := by cases a; cases b; congr


instance [NeZero (ℓ - 1)] : Zero (ModularFormMod ℓ k) where
  zero :=
  { sequence := fun n ↦ (0 : ZMod ℓ)
    modular := by use k.val, 0; constructor; rw[ZMod.natCast_zmod_val]; ext x; simp[reduce] }


instance add : Add (ModularFormMod ℓ k) where
  add a b :=
  { sequence := a + b
    modular := sorry }
    -- Multiply by E₆ ect.


open Finset

def mul (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j) : (ModularFormMod ℓ (k + j)) where

  sequence := fun n ↦ ∑ ⟨x,y⟩ ∈ (antidiagonal n), f x * g y
  -- not 100% sure if this is correct
  -- sum over all x + y = n
  modular := sorry

instance : HMul (ModularFormMod ℓ k) (ModularFormMod ℓ j) (ModularFormMod ℓ (k + j)) where
  hMul := mul


def natify (a : ModularFormMod ℓ k) : ℕ → ℕ :=
  fun n ↦ (a n).val

def pow (a : ModularFormMod ℓ k) (j : ℕ) : ModularFormMod ℓ (k * j) where
  sequence := fun n ↦ (Nat.multinomial (Finset.range j) (natify a)) * a n  -- ???
  modular := sorry
-- probably wrong


instance instSMulZ : SMul ℤ (ModularFormMod ℓ k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}

instance instSMulN : SMul ℕ (ModularFormMod ℓ k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}

instance instNeg : Neg (ModularFormMod ℓ k) where
  neg := fun a ↦
  { sequence := -a
    modular := sorry }

instance instSub : Sub (ModularFormMod ℓ k) :=
  ⟨fun f g => f + -g⟩


variable {ℓ : ℕ} [NeZero ℓ]
variable {k j : ZMod (ℓ-1)}

@[simp]
theorem natify_apply (a : ModularFormMod ℓ k) (n : ℕ) : natify a n = (a n).val := rfl

@[simp]
theorem ModularForm.toFun_eq_coe (f : ModularFormMod ℓ k) : ⇑f = (f : ℕ → ZMod ℓ) := rfl

@[simp]
theorem coe_add (f g : ModularFormMod ℓ k) : ⇑(f + g) = f + g := rfl

@[simp]
theorem add_apply (f g : ModularFormMod ℓ k) (z : ℕ) : (f + g) z = f z + g z := rfl

@[simp]
theorem coe_mul (f g : ModularFormMod ℓ k) : ⇑ (f * g) =
  fun n ↦ ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl

@[simp]
theorem mul_coe (f g : ModularFormMod ℓ k) :
  (f * g : ℕ → ZMod ℓ) = f * g := rfl

@[simp]
theorem mul_apply (f g : ModularFormMod ℓ k) (n : ℕ) : (f * g) n =
  ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl

@[simp]
theorem coe_smulz (f : ModularFormMod ℓ k) (n : ℤ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem coe_smuln (f : ModularFormMod ℓ k) (n : ℕ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem smul_apply (f : ModularFormMod ℓ k) (n z : ℕ) : (n • f) z = n • f z := rfl

@[simp]
theorem coe_zero [NeZero (ℓ - 1)] : ⇑(0 : ModularFormMod ℓ k) = (0 : ℕ → ZMod ℓ) := rfl

@[simp]
theorem zero_apply (z : ℕ) [NeZero (ℓ - 1)] : (0 : ModularFormMod ℓ k) z = 0 := rfl

@[simp]
theorem coe_neg (f : ModularFormMod ℓ k) : ⇑(-f) = -f := rfl

@[simp]
theorem coe_sub (f g : ModularFormMod ℓ k) : ⇑(f - g) = f - g :=
  Eq.symm (Mathlib.Tactic.Abel.unfold_sub (⇑f) (⇑g) (⇑(f - g)) rfl)

@[simp]
theorem sub_apply (f g : ModularFormMod ℓ k) (z : ℕ) : (f - g) z = f z - g z :=
  Eq.symm (Mathlib.Tactic.Abel.unfold_sub (f z) (g z) ((f - g) z) rfl)


theorem coe_pow (f : ModularFormMod ℓ k) (n : ℕ) : ⇑(pow f n) = fun z ↦ (Nat.multinomial (Finset.range n) (natify f)) * f z := rfl


theorem pow_apply (f : ModularFormMod ℓ k) (n z : ℕ) : (pow f n) z = (Nat.multinomial (Finset.range n) (natify f)) * f z := rfl


@[ext]
theorem ModularFormMod.ext {a b : ModularFormMod ℓ k} (h : ∀ n, a n = b n) : a = b :=
  DFunLike.ext a b h
