import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.BasicOperators
import PartitionsLeanblueprint.PowFacts
import Mathlib.FieldTheory.Finite.Basic

/- This file states and proves some basic theorems, some of which are found
in the introduction of the paper -/

open Modulo2

noncomputable section

variable {ℓ n : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

open ZMod Nat


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
    k * ℓ = k * (ℓ - 1 + 1) := by simp
    _ = k * (ℓ - 1) + k := by ring
    _ = k * 0 + k := by
      congr; trans ↑(ℓ - 1)
      refine Eq.symm (cast_pred ?_); exact pos_of_neZero ℓ
      exact natCast_self (ℓ - 1)
    _ = k := by simp only [mul_zero, zero_add]


theorem U_pow_l_eq_self_sub_Theta_pow_l_sub_one' {a : ModularFormMod ℓ k} :
(Mcongr (k_l) ((a|𝓤) ** ℓ)) = thing a := by
  ext n; simp[thing, Pow_Prime]
  symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have h' : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp only [h, reduceIte, h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp[h, reduceIte, h']




lemma Theta_pow_ℓ_eq_Theta {a : ModularFormMod ℓ k} : Θ^[ℓ] a == Θ a := by
  intro n; rw[Theta_Pow_apply, pow_card, Theta_apply]


theorem const_of_Filt_zero {a : ModularFormMod ℓ k} (h : 𝔀 a = 0) : ∃ c : ℕ, a == const c := sorry


theorem Filtration_Log {i : ℕ} {a : ModularFormMod ℓ k} : 𝔀 (a ** i) = i * 𝔀 a := sorry
