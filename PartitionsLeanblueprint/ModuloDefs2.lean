import PartitionsLeanblueprint.ModularFormDefs
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Multinomial

/- This file defines Modular Forms Mod ℓ as sequences from ℕ to ZMod ℓ.
Each modular Form Mod ℓ has a weight defined by the congruence of its weight mod ℓ - 1.
a sequence b is modular if there exists an Integer Modular Form a of any weight such that
b is the reduction of a mod ℓ -/


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


open Nat Finset Finset.Nat

def mul (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j) : (ModularFormMod ℓ (k + j)) where

  sequence n := ∑ ⟨x,y⟩ ∈ (antidiagonal n), f x * g y -- ∑ ⟨x,y⟩ ∈ (antidiagonal n), f x * g y
  -- maybe use Nat.antidiagonal instead
  -- sum over all x + y = n
  modular := sorry

instance : HMul (ModularFormMod ℓ k) (ModularFormMod ℓ j) (ModularFormMod ℓ (k + j)) where
  hMul := mul


def natify (a : ModularFormMod ℓ k) : ℕ → ℕ :=
  fun n ↦ (a n).val



-- def antidiagonalFinset (k n : ℕ) : Finset (Multiset ℕ) where
--   val :=

def pow' (a : ModularFormMod ℓ k) (j : ℕ) : ModularFormMod ℓ (k * j) where
  sequence n := sorry -- (range n).sum (a ^ j)
  modular := sorry
-- probably wrong

def pow (a : ModularFormMod ℓ k) (j : ℕ) : ModularFormMod ℓ (k * j) where
  sequence n := ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y)
  -- this is correct, but inconvenient. Maybe define in terms of the Quotient of perm_setoid
  modular := sorry

#check sum_pow



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
theorem coe_apply (f : ModularFormMod ℓ k) (n : ℕ) : f.sequence n = f n := rfl

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


--theorem coe_pow' (a : ModularFormMod ℓ k) (j : ℕ) : ⇑(pow' a j) = fun n ↦ ↑(multinomial (range (n + 1)) (natify a)) := rfl

--theorem pow_apply' (a : ModularFormMod ℓ k) (j n : ℕ) : (pow' a j) n = ↑(multinomial (range (n + 1)) (natify a)) := rfl

theorem coe_pow (a : ModularFormMod ℓ k) (j : ℕ) : ⇑(pow a j) = fun n ↦ ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl

theorem pow_apply (a : ModularFormMod ℓ k) (j n : ℕ) : (pow a j) n = ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl

@[ext]
theorem ModularFormMod.ext {a b : ModularFormMod ℓ k} (h : ∀ n, a n = b n) : a = b :=
  DFunLike.ext a b h

lemma pow_2_eq_mul_self (a : ModularFormMod ℓ k) (n : ℕ) : (pow a 2) n = (a * a) n := by
  rw[pow_apply]; simp[antidiagonalTuple_two]



--lemma pow_j_eq_mul_self ()
