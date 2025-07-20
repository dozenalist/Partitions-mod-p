import PartitionsLeanblueprint.ModularFormDefs
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs

open ModularFormDefs Modulo Function

infixl:30 "mod" => Reduce

syntax:30 term " (mod " term ")" : term

macro_rules
  | `($a (mod $l)) => `(Reduce $a $l)

local notation "𝔀" => Filtration


variable {k j n ℓ : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {a b : IntegerModularForm k}

#check a (mod ℓ+1)
#check 𝔀 (a * b (mod ℓ))


def Theta (a : ModularFormMod ℓ) : ModularFormMod ℓ where
  sequence := fun n ↦ n * a n
  modular := sorry

def U_Operator (a : ModularFormMod ℓ) : ModularFormMod ℓ where
  sequence := fun n ↦ a (ℓ * n)
  modular := sorry

variable {a b : ModularFormMod ℓ}

local notation "Θ" => Theta

postfix:50 "|𝓤" => U_Operator


#check Θ (a ^ 3 * b)|𝓤
-- Theta operator binds tighter

@[simp]
lemma Pow_Prime {n : ℕ} {a : ModularFormMod ℓ} :
  (a ^ ℓ) n = if (n : ZMod ℓ) = 0 then (a (n / ℓ)) ^ ℓ else 0 := by
  sorry
-- This is by Freshman's Dream, but the definition of Pow makes it hard to work with
-- bad way of writing it

lemma flt {p : ℕ} {n : ZMod p} [Fact (Nat.Prime p)] : n ^ p = n := ZMod.pow_card n


@[simp]
lemma U_apply : (a|𝓤) n = a (ℓ * n) := rfl

@[simp]
lemma Theta_apply : Θ a n = n * a n := rfl

instance : Pow (ModularFormMod ℓ → ModularFormMod ℓ) ℕ where
  pow _ n := Theta^[n]


#check (Θ^3) (a ^ 4 - b)
#check Θ^[3] (a ^ 4 * b)


def δ (ℓ : ℕ) : ℤ := (ℓ^2 - 1) / 24
-- or δℓ : ℤ := (ℓ^2 - 1) / 24


@[simp]
lemma Theta_Pow {n j : ℕ} {a : ModularFormMod ℓ} : Θ^[j] a n = n ^ j * a n := by
  induction' j with j ih; simp
  rw[iterate_succ', pow_add]; simp; rw[ih]; ring




theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one {a : ModularFormMod ℓ} :
(a|𝓤) ^ ℓ = a - Θ^[ℓ - 1] a := by
  ext n; simp[-pow_apply]
  rw[ZMod.pow_card_sub_one]; simp; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
      congr
      have : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      rw [Nat.mul_div_cancel_left' this]
-- terrible
