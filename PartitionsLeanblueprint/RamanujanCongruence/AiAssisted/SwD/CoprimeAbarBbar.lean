import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.SquarefreeAbar

namespace PIntegralModularForm.SwD

noncomputable section

variable {p : ℕ} [isLargePrime p]



/-- Lemma 1.40 (coprimality): the reductions of `A` and `B` are relatively prime.

The proof follows the factor argument from the text. If an irreducible `F`
divided both polynomials, squarefreeness of `Abar` would make its cofactor
coprime to `F`. Differentiating `Abar = F * G` would then show that `F`
divides both polynomial derivatives of `F`. The Euler identity forces `F`
to be weighted homogeneous, and the two derivative identities force it to
divide the discriminant `X^3 - Y^2`. The constant-term evaluation rules out
such a factor of `Abar`.
-/
theorem lemma_1_40_coprime : IsRelPrime (Abar (p := p)) (Bbar (p := p)) := by
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · intro hzero
    exact (Abar_ne_zero (p := p)) hzero.1
  · intro F hF hFA hFB
    have hFdiv : F ∣ Abar (p := p) := hFA
    have hF2not : ¬ F * F ∣ Abar (p := p) := by
      exact (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
        (Abar_ne_zero (p := p))).mp (lemma_1_40_squarefree (p := p)) F hF
    rcases hFA with ⟨G, hA⟩
    have hFG : ¬ F ∣ G := by
      intro hFG
      rcases hFG with ⟨H, hH⟩
      apply hF2not
      refine ⟨H, ?_⟩
      rw [hA, hH]
      ring

    have hEAdiv : F ∣ polynomialEulerDerivationMod (p := p) (Abar (p := p)) := by
      rw [polynomialEuler_Abar (p := p), hA]
      refine ⟨MvPolynomial.C (((p - 1 : ℕ) : ZMod p)) * G, ?_⟩
      simp [Algebra.smul_def]
      ring
    have hEAprod : polynomialEulerDerivationMod (p := p) (Abar (p := p)) =
        polynomialEulerDerivationMod (p := p) F * G +
          F * polynomialEulerDerivationMod (p := p) G := by
      calc
        polynomialEulerDerivationMod (p := p) (Abar (p := p)) =
            polynomialEulerDerivationMod (p := p) (F * G) := by rw [hA]
        _ = polynomialEulerDerivationMod (p := p) F * G +
              F * polynomialEulerDerivationMod (p := p) G := by
          rw [(polynomialEulerDerivationMod (p := p)).leibniz F G]
          simp only [smul_eq_mul]
          ring
    obtain ⟨u, hu⟩ := hEAdiv
    have hEFG : F ∣ polynomialEulerDerivationMod (p := p) F * G := by
      refine ⟨u - polynomialEulerDerivationMod (p := p) G, ?_⟩
      calc
        polynomialEulerDerivationMod (p := p) F * G =
            (polynomialEulerDerivationMod (p := p) F * G +
              F * polynomialEulerDerivationMod (p := p) G) -
                F * polynomialEulerDerivationMod (p := p) G := by ring
        _ = F * u - F * polynomialEulerDerivationMod (p := p) G := by rw [← hEAprod, hu]
        _ = F * (u - polynomialEulerDerivationMod (p := p) G) := by ring
    have hEF : F ∣ polynomialEulerDerivationMod (p := p) F := by
      rcases hF.prime.dvd_mul.mp hEFG with h | h
      · exact h
      · exact (hFG h).elim

    have hDAdiv : F ∣ polynomialDerivationMod (p := p) (Abar (p := p)) := by
      rw [del_Abar_eq_Bbar (p := p)]
      exact hFB
    have hDAprod : polynomialDerivationMod (p := p) (Abar (p := p)) =
        polynomialDerivationMod (p := p) F * G +
          F * polynomialDerivationMod (p := p) G := by
      calc
        polynomialDerivationMod (p := p) (Abar (p := p)) =
            polynomialDerivationMod (p := p) (F * G) := by rw [hA]
        _ = polynomialDerivationMod (p := p) F * G +
              F * polynomialDerivationMod (p := p) G := by
          rw [(polynomialDerivationMod (p := p)).leibniz F G]
          simp only [smul_eq_mul]
          ring
    obtain ⟨v, hv⟩ := hDAdiv
    have hDFG : F ∣ polynomialDerivationMod (p := p) F * G := by
      refine ⟨v - polynomialDerivationMod (p := p) G, ?_⟩
      calc
        polynomialDerivationMod (p := p) F * G =
            (polynomialDerivationMod (p := p) F * G +
              F * polynomialDerivationMod (p := p) G) -
                F * polynomialDerivationMod (p := p) G := by ring
        _ = F * v - F * polynomialDerivationMod (p := p) G := by rw [← hDAprod, hv]
        _ = F * (v - polynomialDerivationMod (p := p) G) := by ring
    have hDF : F ∣ polynomialDerivationMod (p := p) F := by
      rcases hF.prime.dvd_mul.mp hDFG with h | h
      · exact h
      · exact (hFG h).elim

    have hFdegA := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hFdiv
      (Abar_ne_zero (p := p))
    have hAdeg := Abar_totalDegree_bound (p := p)
    have hFdegreeBound : 4 * F.totalDegree ≤ p - 1 := by nlinarith
    have hEigen := euler_divisor_eigen (p := p) F hF hEF
    obtain ⟨c, hEigen⟩ := hEigen
    obtain ⟨d, hhom⟩ := euler_eigen_weightedHomogeneous
      (p := p) F hF.ne_zero hFdegreeBound c hEigen
    have hFdelta := irreducible_factor_divides_discriminant
      (p := p) F hF hEF hDF d hhom hFdegreeBound
    have hFdegD := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hFdelta
      (discriminant_ne_zero (p := p))
    have hFdegD3 : F.totalDegree ≤ 3 := by
      rw [← discriminant_totalDegree (p := p)]
      exact hFdegD
    exact homogeneous_factor_of_discriminant_not_divides_Abar
      (p := p) F hF d hhom hFdegD3 hFdelta hFdiv


end
end PIntegralModularForm.SwD
