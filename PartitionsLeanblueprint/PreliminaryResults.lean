import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.BasicOperators
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs


open ModularFormDefs Integer Modulo2

infixl:30 "mod" => Reduce

syntax:30 term " (mod " term ")" : term

macro_rules
  | `($a (mod $l)) => `(Reduce $a $l)

local notation "𝔀" => Filtration


infixl:80 "**" => pow


variable {ℓ n : ℕ} [NeZero ℓ] [NeZero (ℓ - 1)] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

open Nat Finset

@[simp]
theorem Pow_Prime {n : ℕ} {a : ModularFormMod ℓ k} :
  (a ** ℓ) n = if ℓ ∣ n then (a (n / ℓ)) ^ ℓ else 0 := by
  by_cases h : ℓ ∣ n
  simp [pow_apply,h]
  obtain ⟨k,hk,rfl⟩ := h
  have : ℓ * k / ℓ = k := by refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ rfl); exact Ne.symm (NeZero.ne' ℓ)
  rw[this, multinomial]; simp
  sorry
  simp[pow_apply,h]
  sorry

-- This is by Freshman's Dream, but the definition of Pow makes it hard to work with


@[simp]
lemma flt {p : ℕ} {n : ZMod p} [Fact (Nat.Prime p)] : n ^ p = n := ZMod.pow_card n



theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one' {a : ModularFormMod ℓ k} :
  (a|𝓤) ** ℓ == (a -l (Θ^[ℓ - 1] a)) (by simp) := by
  intro n; simp[ZMod.pow_card_sub_one]; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have h' : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp[h,h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp[h,h']


-- lemma blish {a : ModularFormMod ℓ k} {n : ℕ} :
--   ((a|𝓤) ** ℓ) n = 0 := by rw[U_pow_l_eq_self_sub_Theta_pow_l_minus_one']; simp


def thing (a : ModularFormMod ℓ k) := a - (Mcongr (by simp) (Θ^[ℓ - 1] a))

lemma k_l : k * ℓ = k := by
  calc
    k * ℓ = k * (ℓ - 1 + 1) := by simp
    _ = k * (ℓ - 1) + k := by ring
    _ = k * 0 + k := by
      congr; sorry
    _ = k := by simp only [mul_zero, zero_add]


theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one {a : ModularFormMod ℓ k} :
(Mcongr (k_l) ((a|𝓤) ** ℓ)) = thing a := by
  ext n; simp[thing]
  rw[ZMod.pow_card_sub_one]; simp; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have h' : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp[h,h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp[h,h']


theorem Filtration_Log {i : ℕ} : 𝔀 (a ** i) = i * 𝔀 a := sorry



def δ (ℓ : ℕ) : ℤ := (ℓ^2 - 1) / 24
-- or δℓ : ℤ := (ℓ^2 - 1) / 24
