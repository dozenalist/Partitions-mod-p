import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.Theorem141

namespace PIntegralModularForm.SwD

open IntegerModularForm

variable {ℓ : ℕ} [isLargePrime ℓ]
variable {k j : ZMod (ℓ - 1)}


/-- A nonzero mod-`ℓ` form and an integral modular form with the same Fourier
series must have the same weight modulo `ℓ - 1`. -/
theorem Reduce_of_reduce {m : ℤ} {f : ModularFormMod ℓ k} [hf : NeZero f]
    {b : IntegerModularForm m} (hab : b.reduce ℓ = f.fourier) :
    ∃ h : (m : ZMod (ℓ - 1)) = k,
      f = ModularFormMod.Mcast h (IntegerModularForm.Reduce ℓ b) := by
  let oneWeighted : ResidueWeightedPolynomial (p := ℓ) 0 :=
    { polynomial := MvPolynomial.C (1 : ZMod ℓ)
      homogeneous := by
        intro n hn
        simp only [MvPolynomial.mem_support_iff] at hn
        have hn0 : n = 0 := by
          by_contra hn0
          exact hn (by
            rw [MvPolynomial.coeff_C]
            simp [Ne.symm hn0])
        subst n
        simp [PIntegralModularForm.weightedDegree] }
  let hasseWeighted : ResidueWeightedPolynomial (p := ℓ) 0 :=
    { polynomial := Abar (p := ℓ)
      homogeneous := by
        intro n hn
        have hn' : n ∈
            (PIntegralModularForm.polynomial (p := ℓ)
              (normalizedEisMinusOne (p := ℓ))).support := by
          exact MvPolynomial.support_map_subset
            (f := PIntegralModularForm.coeffToZMod (p := ℓ))
            (PIntegralModularForm.polynomial (p := ℓ)
              (normalizedEisMinusOne (p := ℓ))) (by simpa [Abar, A, reducePolynomial] using hn)
        have hdegree := PIntegralModularForm.polynomial_isHomogeneous
          (p := ℓ) (normalizedEisMinusOne (p := ℓ)) hn'
        have hmod : (((ℓ : ℤ) - 1 : ℤ) : ZMod (ℓ - 1)) = 0 := by
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
          have hle : 1 ≤ ℓ := by
            have := (inferInstance : isLargePrime ℓ).AtLeastFive
            omega
          rw [Nat.cast_sub hle]
          exact dvd_refl _
        exact (congrArg (fun z : ℤ => (z : ZMod (ℓ - 1))) hdegree).trans hmod }
  obtain ⟨oneForm, hone, honeFourier⟩ :=
    polynomialToGradedForms_weighted_fourier (p := ℓ) oneWeighted
  obtain ⟨hasseForm, hhasse, hhasseFourier⟩ :=
    polynomialToGradedForms_weighted_fourier (p := ℓ) hasseWeighted
  have hhasseOneFourier : hasseForm.fourier = oneForm.fourier := by
    rw [hhasseFourier, honeFourier, evaluate_Abar]
    simp [oneWeighted, evaluateResiduePolynomial]
  have hhasseOne : hasseForm = oneForm :=
    ModularFormMod.fourier_inj hhasseOneFourier
  have hAbar : polynomialToGradedForms (p := ℓ) (Abar (p := ℓ)) =
      polynomialToGradedForms (p := ℓ) (MvPolynomial.C (1 : ZMod ℓ)) := by
    rw [hhasse, hone, hhasseOne]
  have hgradedKernel : hasseIdeal (p := ℓ) ≤
      RingHom.ker (polynomialToGradedForms (p := ℓ)) := by
    rw [hasseIdeal]
    refine Ideal.span_le.2 ?_
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change polynomialToGradedForms (p := ℓ)
      (Abar (p := ℓ) - MvPolynomial.C (1 : ZMod ℓ)) = 0
    rw [map_sub, hAbar]
    exact sub_self _

  obtain ⟨P, hP⟩ := exists_weighted_representation (p := ℓ) f
  let fLift : PIntegralModularForm ℓ m :=
    PIntegralModularForm.ofInteger (p := ℓ) b
  let Q : ResidueWeightedPolynomial (p := ℓ) (m : ZMod (ℓ - 1)) :=
    { polynomial := reducePolynomial (p := ℓ)
          (PIntegralModularForm.polynomial (p := ℓ) fLift)
      homogeneous := by
        intro n hn
        have hn' : n ∈
            (PIntegralModularForm.polynomial (p := ℓ) fLift).support := by
          exact MvPolynomial.support_map_subset
            (f := PIntegralModularForm.coeffToZMod (p := ℓ))
            (PIntegralModularForm.polynomial (p := ℓ) fLift) hn
        exact congrArg (fun z : ℤ => (z : ZMod (ℓ - 1)))
          (PIntegralModularForm.polynomial_isHomogeneous (p := ℓ) fLift hn') }
  have hQ : evaluateResiduePolynomial (p := ℓ) Q.polynomial = b.reduce ℓ := by
    calc
      evaluateResiduePolynomial (p := ℓ) Q.polynomial =
          PowerSeries.map (PIntegralModularForm.coeffToZMod (p := ℓ))
            (PIntegralModularForm.evaluateE4E6 (p := ℓ)
              (PIntegralModularForm.polynomial (p := ℓ) fLift)) := by
        exact evaluateResiduePolynomial_reducePolynomial (p := ℓ)
          (PIntegralModularForm.polynomial (p := ℓ) fLift)
      _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := ℓ)) fLift.fourier := by
        rw [PIntegralModularForm.evaluate_polynomial]
      _ = (fLift.Reduce).fourier := rfl
      _ = (b.Reduce ℓ).fourier := by
        exact congrArg ModularFormMod.fourier
          (PIntegralModularForm.Reduce_ofInteger (p := ℓ) b)
      _ = b.reduce ℓ := rfl
  have hEval : evaluateResiduePolynomial (p := ℓ) P.polynomial =
      evaluateResiduePolynomial (p := ℓ) Q.polynomial :=
    hP.trans (hab.symm.trans hQ.symm)
  let FP : Malgebra ℓ := Malgebra.evaluate P.polynomial
  let FQ : Malgebra ℓ := Malgebra.evaluate Q.polynomial
  have hMalgebra : FP = FQ := by
    apply Subtype.ext
    exact hEval
  have hQuotient :
      Ideal.Quotient.mk (hasseIdeal (p := ℓ)) P.polynomial =
        Ideal.Quotient.mk (hasseIdeal (p := ℓ)) Q.polynomial := by
    have h := congrArg (Malgebra.ringEquiv (p := ℓ)) hMalgebra
    simpa [FP, FQ, Malgebra.ringEquiv] using h
  have hPQ : P.polynomial - Q.polynomial ∈ hasseIdeal (p := ℓ) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (hasseIdeal (p := ℓ))
        (P.polynomial - Q.polynomial) = 0
    rw [map_sub, sub_eq_zero]
    exact hQuotient
  have hGraded : polynomialToGradedForms (p := ℓ) P.polynomial =
      polynomialToGradedForms (p := ℓ) Q.polynomial := by
    have hzero : polynomialToGradedForms (p := ℓ)
        (P.polynomial - Q.polynomial) = 0 := hgradedKernel hPQ
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  obtain ⟨fP, hfP, hfPFourier⟩ :=
    polynomialToGradedForms_weighted_fourier (p := ℓ) P
  obtain ⟨fQ, hfQ, hfQFourier⟩ :=
    polynomialToGradedForms_weighted_fourier (p := ℓ) Q
  have hDirect : DirectSum.of _ k fP =
      DirectSum.of _ (m : ZMod (ℓ - 1)) fQ :=
    hfP.symm.trans (hGraded.trans hfQ)
  have hfP_ne : fP ≠ 0 := by
    intro hfPzero
    apply hf.out
    apply ModularFormMod.fourier_inj
    have hzero : fP.fourier = 0 := by rw [hfPzero]; rfl
    exact (hfPFourier.trans hP).symm.trans hzero
  have hweight : (m : ZMod (ℓ - 1)) = k := by
    by_contra hne
    have hcomponent := congrArg
      (fun x : DirectSum (ZMod (ℓ - 1)) (fun i => ModularFormMod ℓ i) => x k)
      hDirect
    have : fP = 0 := by
      simpa [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hne)] using hcomponent
    exact hfP_ne this
  refine ⟨hweight, ?_⟩
  apply ModularFormMod.fourier_inj
  simpa [ModularFormMod.fourier_Mcast] using hab.symm


end PIntegralModularForm.SwD
