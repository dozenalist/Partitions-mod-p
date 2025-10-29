
import PartitionsLeanblueprint.ModularFormDefs
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Multinomial

/- This file defines Modular Forms Mod ℓ as sequences from ℕ to ZMod ℓ.
Each modular Form Mod ℓ has a weight defined by the congruence of its weight mod ℓ - 1.
a sequence b is modular if there exists an Integer Modular Form a of any weight such that
b is the reduction of a mod ℓ -/


open Integer

noncomputable section



def Modulo.reduce (ℓ : ℕ) (a : ℕ → ℤ) [NeZero ℓ] : (ℕ → ZMod ℓ) :=
  fun n ↦ a n


-- A modular form mod ℓ has a weight defined by the congruence of its weight mod ℓ - 1
structure ModularFormMod (ℓ : ℕ) [NeZero ℓ] (k : ZMod (ℓ - 1)) where

  sequence : (ℕ → ZMod ℓ)

  modular : ∃ k' : ℕ, ∃ a : IntegerModularForm k', k' = k ∧ sequence = Modulo.reduce ℓ a
-- or (k : Fin ℓ), ℓ ∣ k' - k.1


namespace Modulo

variable {k : ℕ}

def Reduce (a : IntegerModularForm k) ℓ [NeZero ℓ] : ModularFormMod ℓ k where
  sequence n := (a n : ZMod ℓ)
  modular := ⟨k, a, rfl, rfl⟩


variable {ℓ n : ℕ} [NeZero ℓ]
variable {k j : ZMod (ℓ-1)}


instance (priority := 100) : FunLike (ModularFormMod ℓ k) ℕ (ZMod ℓ) where
  coe a := a.1
  coe_injective' a b c := by cases a; cases b; congr

instance (priority := 100) : FunLike (ℕ → ZMod ℓ) ℕ (ZMod ℓ) where
  coe a := a
  coe_injective' _ _ h := h


instance [NeZero (ℓ - 1)] : Zero (ModularFormMod ℓ k) where
  zero :=
  { sequence := fun n ↦ (0 : ZMod ℓ)
    modular := by
      use k.val, 0; constructor
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      ext n; simp only [reduce, coe_zero, Pi.zero_apply, Int.cast_zero]
  }


instance add : Add (ModularFormMod ℓ k) where
  add a b :=
  { sequence := a + b
    modular := sorry }
    -- Multiply by E_{ℓ - 1} ect.


open Nat Finset Finset.Nat

def mul (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j) : (ModularFormMod ℓ (k + j)) where

  sequence n := ∑ ⟨x,y⟩ ∈ (antidiagonal n), f x * g y
  -- sum over all x + y = n
  modular := sorry

instance : HMul (ModularFormMod ℓ k) (ModularFormMod ℓ j) (ModularFormMod ℓ (k + j)) where
  hMul := mul


def natify (a : ModularFormMod ℓ k) : ℕ → ℕ :=
  fun n ↦ (a n).val



def Mpow (a : ModularFormMod ℓ k) (j : ℕ) : ModularFormMod ℓ (k * j) where
  sequence n := ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y)
  -- sum over all x1 + ... + xj = n

  modular := sorry

scoped infixl:80 " ** " => Mpow




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
theorem Reduce_apply {k ℓ} [NeZero ℓ] (a : IntegerModularForm k ) (n : ℕ) :
  Reduce a ℓ n = a n := rfl

@[simp]
theorem toFun_eq_coe (f : ModularFormMod ℓ k) : ⇑f = (f : ℕ → ZMod ℓ) := rfl

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
theorem mul_coe (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j ) :
  (f * g : ℕ → ZMod ℓ) = f * g := rfl


theorem mul_apply (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j ) (n : ℕ) : (f * g) n =
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


theorem coe_Mpow (a : ModularFormMod ℓ k) (j : ℕ) : ⇑(Mpow a j) = fun n ↦ ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl

theorem Mpow_apply (a : ModularFormMod ℓ k) (j n : ℕ) : (Mpow a j) n = ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl

@[ext]
theorem ModularFormMod.ext {a b : ModularFormMod ℓ k} (h : ∀ n, a n = b n) : a = b :=
  DFunLike.ext a b h

-- the constant modular forms of weight 0
def const (x : ZMod ℓ) : ModularFormMod ℓ 0 where

  sequence
    | 0 => x
    | _ + 1 => 0

  modular := sorry

instance : Coe (ZMod ℓ) (ModularFormMod ℓ 0) where
  coe x := const x

instance : NatCast (ModularFormMod ℓ 0) where
  natCast n := const n

-- @[simp, norm_cast]
-- lemma coe_natCast (n : ZMod ℓ) :
--     ⇑(n : ModularFormMod ℓ 0) = n := rfl

instance : IntCast (ModularFormMod ℓ 0) where
  intCast z := const z

-- @[simp, norm_cast]
-- lemma coe_intCast (z : ℤ) :
--     ⇑(z : ModularFormMod ℓ 0) = z := rfl


theorem const_apply (x : ZMod ℓ) (n : ℕ) : (const x) n =
    match n with
    | 0 => x
    | succ _ => 0 := by
  cases n <;> rfl


@[simp]
theorem const_zero (x : ZMod ℓ) : (const x) 0 = x := rfl

@[simp]
theorem const_succ (x : ZMod ℓ) (n : ℕ) : (const x) n.succ = 0 := rfl


instance {ℓ : ℕ} [Fact (Nat.Prime ℓ)] : NeZero (ℓ - 1) where
  out :=
    let lg2 := Prime.two_le Fact.out
    Nat.sub_ne_zero_iff_lt.mpr lg2

end Modulo


variable {α : Type*} {k j : ℕ} [CommSemiring α]
open Finset.Nat Finset

def Sequencemul (a b : ℕ → α) : ℕ → α :=
  fun n ↦ ∑ ⟨x,y⟩ ∈ antidiagonal n, a x * b y


def Sequencepow (a : ℕ → α) (j : ℕ) : ℕ → α :=
  fun n ↦ ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y)


theorem coe_Sequencemul (f g : ℕ → α) : Sequencemul f g =
  fun n ↦ ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl


theorem Sequencemul_apply (f g : ℕ → α) (n : ℕ) : (Sequencemul f g) n =
  ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl

theorem coe_Sequencepow (a : ℕ → α) (j : ℕ) :
  Sequencepow a j = fun n ↦ ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl

theorem Sequencepow_apply (a : ℕ → α) (j n : ℕ) :
  (Sequencepow a j) n = ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl


theorem Integer.mul_eq_Sequencemul (a : IntegerModularForm k) (b : IntegerModularForm j) :
  ⇑(a * b) = Sequencemul a b := rfl

theorem Integer.Ipow_eq_Sequencepow (a : IntegerModularForm k) (j : ℕ) :
  Ipow a j = Sequencepow a j := rfl

theorem Integer.mul_eq_Sequencemul_apply (a : IntegerModularForm k) (b : IntegerModularForm j) (n : ℕ) :
  (a * b) n = Sequencemul a b n := rfl

theorem Integer.Ipow_eq_Sequencepow_apply (a : IntegerModularForm k) (j : ℕ) (n : ℕ) :
  Ipow a j n = Sequencepow a j n := rfl


variable {ℓ : ℕ} [NeZero ℓ] {k j : ZMod (ℓ - 1)}

theorem Modulo.mul_eq_Sequencemul (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) :
  ⇑(a * b) = Sequencemul a b := rfl

theorem Modulo.Mpow_eq_Sequencepow (a : ModularFormMod ℓ k) (j : ℕ) :
  Mpow a j = Sequencepow a j := rfl

theorem Modulo.mul_eq_Sequencemul_apply (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (n : ℕ) :
  ⇑(a * b) n = Sequencemul a b n := rfl

theorem Modulo.Mpow_eq_Sequencepow_apply (a : ModularFormMod ℓ k) (j : ℕ) (n : ℕ) :
  Mpow a j n = Sequencepow a j n := rfl


end section
