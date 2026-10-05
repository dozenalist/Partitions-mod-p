import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.Filtration



variable {p : ℕ} [isLargePrime p] {k : ZMod (p - 1)}

open ModularFormMod
open PIntegralModularForm.SwD

theorem Filtration_const (c : ZMod p) : (const c).Filtration = 0 := by
  by_cases c0 : c = 0
  · simp [c0, const_zero]

  have : NeZero (const c) :=
    ⟨by contrapose! c0; trans (const c).coeff 0; rw [coeff_const_zero]; rw [c0, coeff_zero]⟩

  apply le_antisymm
  · apply Filtration_le
    use IntegerModularForm.const c.cast
    ext n; simp [PowerSeries.coeff_C n c]

  · trans 12 * (0 : ℕ); rfl
    exact le_Filtration _ fun n nlt => n.not_lt_zero nlt |>.elim


private theorem hasWeight_pow {f : ModularFormMod p k} {n} (h : f.hasWeight n) :
    ∀ m, (f.pow m).hasWeight (m * n)
  | 0 => by simp; use IntegerModularForm.const 1; ext; simp
  | m + 1 => by simpa [add_mul, pow_succ_eq_Mcast] using
      hasWeight_mul (hasWeight_pow h m) h


private theorem Filtration_pow_le (f : ModularFormMod p k) (m : ℕ) :
    (f.pow m).Filtration ≤ m * f.Filtration := by
  by_cases f0 : f = 0
  · simp [f0]
    by_cases m0 : m = 0
    · rw [m0, ModularFormMod.pow_zero, Filtration_Mcast, Filtration_const]
    · rw [ModularFormMod.zero_pow (hj := ⟨m0⟩), Filtration_zero]

  by_cases fp0 : f.pow m = 0
  · rw [fp0, Filtration_zero]; have := f.Filtration_nonneg
    trans 0 * 0; rfl
    gcongr; exact Int.natCast_nonneg m

  · exact Filtration_le (fn0 := ⟨fp0⟩) <| hasWeight_pow f.Filtration_spec m




theorem Filtration_pow (f : ModularFormMod p k) (m : ℕ) :
    (f.pow m).Filtration = m * f.Filtration := by
  apply le_antisymm <| Filtration_pow_le f m

  by_cases f0 : f = 0
  · subst f
    by_cases m0 : m = 0
    · rw [m0, ModularFormMod.pow_zero, Filtration_Mcast, Filtration_const]
      norm_num
    · have hm : m ≠ 0 := m0
      rw [ModularFormMod.zero_pow (hj := ⟨hm⟩), Filtration_zero]
      simp
  by_cases m0 : m = 0
  · rw [m0, ModularFormMod.pow_zero, Filtration_Mcast, Filtration_const]
    norm_num

  let g : PIntegralModularForm p f.Filtration :=
    PIntegralModularForm.ofInteger f.Filtration_choose
  have hg : g.Reduce.fourier = f.fourier := by
    change (PIntegralModularForm.ofInteger (p := p) f.Filtration_choose).Reduce.fourier = _
    rw [PIntegralModularForm.Reduce_ofInteger,
      IntegerModularForm.fourier_Reduce]
    exact f.Filtration_choose_spec.symm
  have hgf : g.Reduce.Filtration = f.Filtration := by
    apply ModularFormMod.Filtration_ext
    intro n
    simpa only [ModularFormMod.coeff_def] using
      congrArg (fun S : PowerSeries (ZMod p) => S.coeff n) hg
  have hg0 : g.Reduce ≠ 0 := by
    intro hz
    apply f0
    apply ModularFormMod.fourier_inj
    rw [← hg]
    exact congrArg ModularFormMod.fourier hz
  have hpowFourier : (g.pow m).Reduce.fourier = (f.pow m).fourier := by
    change PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
        (g.fourier ^ m) = f.fourier ^ m
    rw [map_pow, ← PIntegralModularForm.fourier_Reduce, hg]
  have hpow0 : (g.pow m).Reduce ≠ 0 := by
    intro hz
    have hzero : (f.pow m).fourier = 0 := by
      rw [← hpowFourier]
      exact congrArg ModularFormMod.fourier hz
    apply f0
    apply ModularFormMod.fourier_inj
    exact (pow_ne_zero m (by
      intro hzero'
      apply f0
      apply ModularFormMod.fourier_inj
      exact hzero')).elim hzero
  have hpoly_hom :
      MvPolynomial.IsWeightedHomogeneous
        (fun i : Fin 2 =>
          (PIntegralModularForm.SwD.polynomialWeights i : ℤ)) g.polynomial f.Filtration := by
    intro n hn
    have hn' := g.polynomial_isHomogeneous (MvPolynomial.mem_support_iff.mpr hn)
    calc
      Finsupp.weight (fun i : Fin 2 =>
          (PIntegralModularForm.SwD.polynomialWeights i : ℤ)) n =
          PIntegralModularForm.weightedDegree n := by
            simp [PIntegralModularForm.weightedDegree,
              PIntegralModularForm.SwD.polynomialWeights,
              Finsupp.weight_eq_sum]
            ring
      _ = f.Filtration := hn'
  have hpoly_pow : ∀ n ∈ (g.polynomial ^ m).support,
      PIntegralModularForm.weightedDegree n = m * f.Filtration := by
    intro n hn
    have hn' := hpoly_hom.pow m (MvPolynomial.mem_support_iff.mp hn)
    calc
      PIntegralModularForm.weightedDegree n =
          Finsupp.weight (fun i : Fin 2 =>
            (PIntegralModularForm.SwD.polynomialWeights i : ℤ)) n := by
            simp [PIntegralModularForm.weightedDegree,
              PIntegralModularForm.SwD.polynomialWeights,
              Finsupp.weight_eq_sum]
            ring
      _ = m • f.Filtration := hn'
      _ = m * f.Filtration := by simp
  have hpoly : g.polynomial ^ m = (g.pow m).polynomial := by
    apply PIntegralModularForm.polynomial_unique_of_eval (g.pow m)
    · exact PIntegralModularForm.homogeneous_isPBasisPolynomial
        (p := p) (k := m * f.Filtration) (g.polynomial ^ m) hpoly_pow
    · change PIntegralModularForm.evaluateE4E6Hom (p := p)
        (g.polynomial ^ m) = _
      rw [map_pow]
      change (PIntegralModularForm.evaluateE4E6 (p := p) g.polynomial) ^ m = _
      rw [PIntegralModularForm.evaluate_polynomial,
        PIntegralModularForm.fourier_pow]
  have hredpoly :
      PIntegralModularForm.SwD.reducePolynomial (p := p) (g.pow m).polynomial =
        (PIntegralModularForm.SwD.reducePolynomial (p := p) g.polynomial) ^ m := by
    rw [← hpoly]
    simp [PIntegralModularForm.SwD.reducePolynomial]
  have hiff := PIntegralModularForm.SwD.Filtration_Reduce_lt_iff
    (g.pow m) hpow0
  have hnot : ¬ Abar (p := p) ∣
      PIntegralModularForm.SwD.reducePolynomial (p := p) g.polynomial := by
    intro hdiv
    have hlt := (PIntegralModularForm.SwD.Filtration_Reduce_lt_iff g hg0).2 hdiv
    rw [hgf] at hlt
    exact (lt_irrefl _ hlt)
  have hnotpow : ¬ (g.pow m).Reduce.Filtration < m * g.Reduce.Filtration := by
    intro hlt
    rw [hgf] at hlt
    have hdiv := hiff.1 hlt
    have hdivpow : Abar (p := p) ∣
        (PIntegralModularForm.SwD.reducePolynomial (p := p) g.polynomial) ^ m := by
      rw [← hredpoly]
      exact hdiv
    exact hnot (((lemma_1_40_squarefree (p := p)).dvd_pow_iff_dvd
      (Nat.ne_of_gt (Nat.pos_of_ne_zero m0))).mp hdivpow)
  have hpowFiltration : (g.pow m).Reduce.Filtration = (f.pow m).Filtration := by
    apply ModularFormMod.Filtration_ext
    intro n
    simpa only [ModularFormMod.coeff_def] using
      congrArg (fun S : PowerSeries (ZMod p) => S.coeff n) hpowFourier
  calc
    m * f.Filtration = m * g.Reduce.Filtration := by rw [hgf]
    _ ≤ (g.pow m).Reduce.Filtration := le_of_not_gt hnotpow
    _ = (f.pow m).Filtration := hpowFiltration
