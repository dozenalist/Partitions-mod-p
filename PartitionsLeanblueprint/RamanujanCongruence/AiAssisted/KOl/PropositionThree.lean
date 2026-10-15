import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.ThetaSeparation
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.DropClassification

namespace KOl

open scoped IntegerModularForm

noncomputable section

variable {ell : ℕ} [isLargePrime ell]

/-- Proposition 3 for a modular form whose starting filtration is minimal
in its theta cycle. -/
theorem proposition_three_modular {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (a : ℕ) (ha : 0 < a) (halt : a < ell)
    (hTheta : f.Theta ≠ 0) (hnotdiv : ¬ (ell : ℤ) ∣ f.Filtration)
    (hminimal : ∀ i : ℕ, f.Filtration ≤ (f.Theta_pow i).Filtration)
    (hcong : ∀ n : ℕ, f.coeff (ell * n + a) = 0) :
    f.Filtration ≡ (((ell + 1) / 2 : ℕ) : ℤ) [ZMOD ell] ∨
      f.Filtration ≡ (((ell + 3) / 2 : ℕ) : ℤ) [ZMOD ell] := by
  classical
  have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
  have haZ : (a : ZMod ell) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff a ell).mp hz
    have hle := Nat.le_of_dvd ha hd
    omega
  have hidentity (n : ℕ) :
      (((n : ZMod ell) - a) ^ (ell - 1)) * f.coeff n = f.coeff n := by
    by_cases hn : (n : ZMod ell) - a = 0
    · have hmod : n % ell = a := by
        have hm := (ZMod.natCast_eq_natCast_iff n a ell).mp (sub_eq_zero.mp hn)
        simpa [Nat.ModEq, Nat.mod_eq_of_lt halt] using hm
      have hindex : n = ell * (n / ell) + a := by
        have hm := Nat.mod_add_div n ell
        omega
      have hzero : f.coeff n = 0 := by rw [hindex]; exact hcong (n / ell)
      simp [hzero]
    · rw [ZMod.pow_card_sub_one_eq_one hn, one_mul]
  let h := (ell - 1) / 2
  have hodd : Odd ell :=
    (Nat.Prime.odd_iff (inferInstance : isLargePrime ell).Prime).mpr (by omega)
  have hhalf : ell - 1 = 2 * h := by
    obtain ⟨t, ht⟩ := hodd
    have heven : 2 ∣ ell - 1 := ⟨t, by omega⟩
    exact (Nat.mul_div_cancel' heven).symm
  have hhalf1 : (ell + 1) / 2 = h + 1 := by omega
  have hhalf3 : (ell + 3) / 2 = h + 2 := by omega
  have hpair {j : ℕ} (hj : 1 ≤ j) (hjle : j ≤ h)
      (hdrop : j + h ∈ thetaFiltrationDrops f) :
      j ∈ thetaFiltrationDrops f := by
    have hdiv := (Finset.mem_filter.mp hdrop).2
    have heq := theta_half_cycle_filtration f a haZ hidentity hj hjle
    have heq' : (f.Theta_pow j).Filtration = (f.Theta_pow (j + h)).Filtration := heq
    exact Finset.mem_filter.mpr
      ⟨by simp only [Finset.mem_Icc]; omega, by rwa [heq']⟩
  obtain ⟨k₀, hkpos, hklt, hkmod, s, hs, hcases⟩ :=
    theta_filtration_drop_classification f hTheta hnotdiv hminimal
  rcases hcases with hcase | hcase | hcase | hcase
  · have hdrop : h + h ∈ thetaFiltrationDrops f := by
      rw [hcase.2.1]
      simp only [Finset.mem_singleton]
      omega
    have hp := hpair (j := h) (by omega) le_rfl hdrop
    rw [hcase.2.1] at hp
    simp only [Finset.mem_singleton] at hp
    omega
  · have hdrop : (h - 1) + h ∈ thetaFiltrationDrops f := by
      rw [hcase.2.1]
      simp only [Finset.mem_singleton]
      omega
    have hp := hpair (j := h - 1) (by omega) (by omega) hdrop
    rw [hcase.2.1] at hp
    simp only [Finset.mem_singleton] at hp
    omega
  · have hdrop : h + h ∈ thetaFiltrationDrops f := by
      rw [hcase.2.1]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      omega
    have hp := hpair (j := h) (by omega) le_rfl hdrop
    rw [hcase.2.1] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    have hk : k₀ = h := by omega
    left
    apply hkmod.trans
    rw [hk, hhalf1, Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    omega
  · have hdrop : (h - 1) + h ∈ thetaFiltrationDrops f := by
      rw [hcase.2.2.1]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      omega
    have hp := hpair (j := h - 1) (by omega) (by omega) hdrop
    rw [hcase.2.2.1] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    have hk : k₀ = h - 1 := by omega
    right
    apply hkmod.trans
    rw [hk, hhalf3, Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    omega

end
end KOl
