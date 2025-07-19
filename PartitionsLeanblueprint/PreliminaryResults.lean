import PartitionsLeanblueprint.ModularFormDefs
import Mathlib.Logic.Function.Iterate

open ModularFormDefs Modulo Function

infixl:30 "mod" => Reduce

syntax:30 term " (mod " term ")" : term

macro_rules
  | `($a (mod $l)) => `(Reduce $a $l)

local notation "𝔀" => Filtration

variable {k j n ℓ : ℕ} [NeZero ℓ]
variable {a b : IntegerModularForm k}

#check a (mod ℓ)
#check 𝔀 (a + b (mod ℓ))


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
lemma U_apply : (a|𝓤) n = a (ℓ * n) := rfl

@[simp]
lemma Theta_apply : Θ a n = n * a n := rfl

instance : Pow (ModularFormMod ℓ → ModularFormMod ℓ) ℕ where
  pow _ n := Theta^[n]


#check (Θ^3) (a ^ 4 - b)
#check Θ^[3] (a ^ 4 * b)


def δ (ℓ : ℕ) : ℤ := (ℓ^2 - 1) / 24

@[simp]
lemma Theta_Pow {n j : ℕ} {a : ModularFormMod ℓ} : Θ^[j] a n = n ^ j * a n := by
  induction' j with j ih; simp
  rw[iterate_succ', pow_add]; simp; rw[ih]; ring


theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one {a : ModularFormMod ℓ} :
(a|𝓤) ^ ℓ = a - Θ^[ℓ - 1] a := by
  ext n; simp
  sorry
