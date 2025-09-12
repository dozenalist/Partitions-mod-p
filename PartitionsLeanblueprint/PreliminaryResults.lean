import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.BasicOperators
import PartitionsLeanblueprint.PowFacts
import Mathlib.FieldTheory.Finite.Basic

/- This file states and proves some basic theorems which are found in the
introduction of the paper, before the beginning of the proof of Theorem 3.1 -/

open Modulo2

noncomputable section

variable {ℓ n : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

open ZMod Nat

-- This is the cleaner way of proving it, using == and -l
theorem U_pow_l_eq_self_sub_Theta_pow_l_sub_one {a : ModularFormMod ℓ k} :
  a|𝓤 ** ℓ == (a -l Θ^[ℓ - 1] a) (by simp) := by
  intro n; simp[Pow_Prime]; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp only [h, reduceIte, sub_zero, sub_self]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have  h' : ℓ ∣ n := (natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp only [h, reduceIte, h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp only [h, reduceIte, h']



def thing (a : ModularFormMod ℓ k) := a - (Mcongr (by simp) (Θ^[ℓ - 1] a))

lemma k_l : k * ℓ = k := by
  calc
    k * ℓ = k * (ℓ - 1 + 1) := by rw [sub_add_cancel]
    _ = k * (ℓ - 1) + k := by ring
    _ = k * 0 + k := by
      congr; trans ↑(ℓ - 1)
      exact Eq.symm (cast_pred (pos_of_neZero ℓ))
      exact natCast_self (ℓ - 1)
    _ = k := by rw [mul_zero, zero_add]

-- This is a proof using only Mcongr to cast
theorem U_pow_l_eq_self_sub_Theta_pow_l_sub_one' {a : ModularFormMod ℓ k} :
(Mcongr (k_l) ((a|𝓤) ** ℓ)) = thing a := by
  ext n; simp only [cast_eval, thing, sub_apply]
  have := @U_pow_l_eq_self_sub_Theta_pow_l_sub_one _ _ _ _ a
  rw [this n, sub_congr_left_apply]



theorem const_of_Filt_zero {a : ModularFormMod ℓ k} (h : 𝔀 a = 0) : ∃ c : ZMod ℓ, a == const c := sorry


theorem Filtration_Log {i : ℕ} {a : ModularFormMod ℓ k} : 𝔀 (a ** i) = i * 𝔀 a := sorry
