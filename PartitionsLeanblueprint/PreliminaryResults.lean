import PartitionsLeanblueprint.BasicOperators
import PartitionsLeanblueprint.PowFacts
import Mathlib.FieldTheory.Finite.Basic

/- This file states and proves some basic theorems which are found in the
introduction of the paper, before the beginning of the proof of Theorem 3.1 -/


noncomputable section

variable {ℓ n : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

open ZMod Nat ModularFormMod


-- This is the cleaner way of stating it, using == and -l
theorem U_pow_l_eq_self_sub_Theta_pow_l_sub_one (a : ModularFormMod ℓ k) :
    a|𝓤 ** ℓ == (a -l Θ^[ℓ - 1] a) (by simp) := by
  intro n; simp[Pow_Prime]; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp only [h, reduceIte, sub_zero, sub_self]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have h' : ℓ ∣ n := (natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp only [h, h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp only [h, reduceIte, h']



theorem const_of_Filt_zero {a : ModularFormMod ℓ k} (h : 𝔀 a = 0) : ∃ c : ZMod ℓ, a == const c := by
  have wa0 : hasWeight a 0 := Weight_of_Filt h
  obtain ⟨b,hb⟩ := wa0
  sorry


theorem Filtration_Log {i : ℕ} {a : ModularFormMod ℓ k} : 𝔀 (a ** i) = i * 𝔀 a := sorry



theorem Filtration_congruence (a : ModularFormMod ℓ k) [NeZero a] : (𝔀 a : ZMod (ℓ - 1)) = k := sorry



theorem Reduce_of_reduce {a : ModularFormMod ℓ k} {b : IntegerModularForm n} (hab : ∀ n, a n = b n) :
    ∃ h, a = Mcast h (Reduce ℓ b) := sorry



theorem exists_of_filt_eq (a : ModularFormMod ℓ k) (ha : 𝔀 a = n) :
    ∃ b : IntegerModularForm n, ∃ h, a = Mcast h (Reduce ℓ b) := by
  obtain ⟨b, aeq⟩ := Weight_of_Filt ha
  obtain ⟨h, aeq⟩ := Reduce_of_reduce aeq
  exact ⟨b, h, aeq⟩
