import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.Identities
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

namespace PIntegralModularForm.SwD

noncomputable section

variable {p : ℕ} [isLargePrime p]

/-- Reduction preserves the weighted homogeneity of the defining polynomials. -/
theorem Abar_weightedDegree {m : Fin 2 →₀ ℕ}
    (hm : m ∈ (Abar (p := p)).support) :
    PIntegralModularForm.weightedDegree m = (p : ℤ) - 1 := by
  change m ∈ (MvPolynomial.map (PIntegralModularForm.coeffToZMod (p := p))
    (A (p := p))).support at hm
  have hmA : m ∈ (A (p := p)).support :=
    MvPolynomial.support_map_subset (f := PIntegralModularForm.coeffToZMod (p := p))
      (A (p := p)) hm
  exact PIntegralModularForm.polynomial_isHomogeneous
    (normalizedEisMinusOne (p := p)) hmA

theorem Bbar_weightedDegree {m : Fin 2 →₀ ℕ}
    (hm : m ∈ (Bbar (p := p)).support) :
    PIntegralModularForm.weightedDegree m = (p : ℤ) + 1 := by
  change m ∈ (MvPolynomial.map (PIntegralModularForm.coeffToZMod (p := p))
    (B (p := p))).support at hm
  have hmB : m ∈ (B (p := p)).support :=
    MvPolynomial.support_map_subset (f := PIntegralModularForm.coeffToZMod (p := p))
      (B (p := p)) hm
  exact PIntegralModularForm.polynomial_isHomogeneous
    (normalizedEisPlusOne (p := p)) hmB

/-- The weights of the two polynomial variables. -/
def polynomialWeights : Fin 2 → ℕ := ![4, 6]

/-- The reduction of `A` is weighted homogeneous of weight `p - 1`. -/
theorem Abar_isWeightedHomogeneous :
    MvPolynomial.IsWeightedHomogeneous (polynomialWeights)
      (Abar (p := p)) (p - 1) := by
  intro m hm
  have hsupport : m ∈ (Abar (p := p)).support :=
    MvPolynomial.mem_support_iff.mpr hm
  have hw := Abar_weightedDegree (p := p) hsupport
  have hw' : ((Finsupp.weight polynomialWeights m : ℕ) : ℤ) =
      (p : ℤ) - 1 := by
    have hwt : ((Finsupp.weight polynomialWeights m : ℕ) : ℤ) =
        4 * (m 0 : ℤ) + 6 * (m 1 : ℤ) := by
      simp [Finsupp.weight_eq_sum, polynomialWeights]
      ring
    rw [hwt]
    have hw'' := hw
    simp [PIntegralModularForm.weightedDegree] at hw''
    nlinarith [hw'']
  have hcast : Finsupp.weight polynomialWeights m = p - 1 := by
    have hp : 1 ≤ p := by have := (inferInstance : isLargePrime p).AtLeastFive; omega
    have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    exact_mod_cast (hw'.trans hcast.symm)
  exact hcast

/-- The weighted Euler derivation, which preserves weighted degree. -/
def polynomialEulerDerivationMod :
    Derivation (ZMod p) (ResiduePolynomial p) (ResiduePolynomial p) :=
  (((MvPolynomial.C (4 : ZMod p) : ResiduePolynomial p) *
        (MvPolynomial.X 0 : ResiduePolynomial p)) •
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0) +
    (((MvPolynomial.C (6 : ZMod p) : ResiduePolynomial p) *
        (MvPolynomial.X 1 : ResiduePolynomial p)) •
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1)

/-- Euler's identity for `Abar`. -/
theorem polynomialEuler_Abar :
    polynomialEulerDerivationMod (p := p) (Abar (p := p)) =
      ((p - 1 : ℕ) : ZMod p) • Abar (p := p) := by
  have hC4 : (MvPolynomial.C (4 : ZMod p) : ResiduePolynomial p) = 4 := by
    simpa using (MvPolynomial.C_eq_coe_nat (R := ZMod p) (σ := Fin 2) 4)
  have hC6 : (MvPolynomial.C (6 : ZMod p) : ResiduePolynomial p) = 6 := by
    simpa using (MvPolynomial.C_eq_coe_nat (R := ZMod p) (σ := Fin 2) 6)
  have h := (Abar_isWeightedHomogeneous (p := p)).sum_weight_X_mul_pderiv
  simpa [polynomialEulerDerivationMod, polynomialWeights,
    Derivation.smul_apply, Algebra.smul_def, hC4, hC6, mul_assoc] using h

/-- The Euler operator acts diagonally on monomial coefficients. -/
theorem polynomialEuler_coeff (P : ResiduePolynomial p) (m : Fin 2 →₀ ℕ) :
    (polynomialEulerDerivationMod (p := p) P).coeff m =
      (Finsupp.weight polynomialWeights m : ZMod p) * P.coeff m := by
  have h0 : (MvPolynomial.C (4 : ZMod p) * MvPolynomial.X 0 *
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 P).coeff m =
        (m 0 : ZMod p) * 4 * P.coeff m := by
    by_cases hm : m 0 = 0
    · rw [show MvPolynomial.C (4 : ZMod p) * MvPolynomial.X 0 *
          MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 P =
            MvPolynomial.C 4 * (MvPolynomial.X 0 *
              MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 P) by ring]
      simp [hm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul',
        MvPolynomial.coeff_pderiv]
    · have hm0 : (0 : Fin 2) ∈ m.support := by
        rw [Finsupp.mem_support_iff]
        exact hm
      rw [show MvPolynomial.C (4 : ZMod p) * MvPolynomial.X 0 *
          MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 P =
            MvPolynomial.C 4 * (MvPolynomial.X 0 *
              MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 P) by ring]
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul',
        if_pos hm0, MvPolynomial.coeff_pderiv]
      rw [Finsupp.sub_add_single_one_cancel hm]
      have hmval : (m - Finsupp.single (0 : Fin 2) (1 : ℕ)) (0 : Fin 2) =
          m 0 - 1 := by simp [Finsupp.tsub_apply]
      rw [hmval]
      have hcast : ((m 0 - 1 : ℕ) : ZMod p) + 1 = (m 0 : ZMod p) := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm)]
        ring
      rw [hcast]
      ring
  have h1 : (MvPolynomial.C (6 : ZMod p) * MvPolynomial.X 1 *
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 P).coeff m =
        (m 1 : ZMod p) * 6 * P.coeff m := by
    by_cases hm : m 1 = 0
    · rw [show MvPolynomial.C (6 : ZMod p) * MvPolynomial.X 1 *
          MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 P =
            MvPolynomial.C 6 * (MvPolynomial.X 1 *
              MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 P) by ring]
      simp [hm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul',
        MvPolynomial.coeff_pderiv]
    · have hm1 : (1 : Fin 2) ∈ m.support := by
        rw [Finsupp.mem_support_iff]
        exact hm
      rw [show MvPolynomial.C (6 : ZMod p) * MvPolynomial.X 1 *
          MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 P =
            MvPolynomial.C 6 * (MvPolynomial.X 1 *
              MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 P) by ring]
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul',
        if_pos hm1, MvPolynomial.coeff_pderiv]
      rw [Finsupp.sub_add_single_one_cancel hm]
      have hmval : (m - Finsupp.single (1 : Fin 2) (1 : ℕ)) (1 : Fin 2) =
          m 1 - 1 := by simp [Finsupp.tsub_apply]
      rw [hmval]
      have hcast : ((m 1 - 1 : ℕ) : ZMod p) + 1 = (m 1 : ZMod p) := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm)]
        ring
      rw [hcast]
      ring
  have h0' : (MvPolynomial.C (4 : ZMod p) * (MvPolynomial.X 0 *
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 P)).coeff m =
        (m 0 : ZMod p) * 4 * P.coeff m := by simpa [mul_assoc] using h0
  have h1' : (MvPolynomial.C (6 : ZMod p) * (MvPolynomial.X 1 *
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 P)).coeff m =
        (m 1 : ZMod p) * 6 * P.coeff m := by simpa [mul_assoc] using h1
  simp only [polynomialEulerDerivationMod, Derivation.add_apply,
    Derivation.smul_apply, smul_eq_mul]
  rw [show (MvPolynomial.C (4 : ZMod p) * MvPolynomial.X 0) *
      (MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0) P =
        MvPolynomial.C 4 * (MvPolynomial.X 0 *
          MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 P) by ring,
    show (MvPolynomial.C (6 : ZMod p) * MvPolynomial.X 1) *
      (MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1) P =
        MvPolynomial.C 6 * (MvPolynomial.X 1 *
          MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 P) by ring]
  rw [MvPolynomial.coeff_add, h0', h1']
  simp [Finsupp.weight_eq_sum, polynomialWeights]
  ring

theorem polynomialEuler_support_subset (P : ResiduePolynomial p) :
    (polynomialEulerDerivationMod (p := p) P).support ⊆ P.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, polynomialEuler_coeff] at hm
  rw [MvPolynomial.mem_support_iff]
  contrapose! hm
  simp [hm]

theorem Abar_totalDegree_bound :
    4 * (Abar (p := p)).totalDegree ≤ p - 1 := by
  unfold MvPolynomial.totalDegree
  have hsup : (Abar (p := p)).support.sup
      (fun m => m.sum fun _ e => e) ≤ (p - 1) / 4 := by
    apply Finset.sup_le
    intro m hm
    have hw := Abar_weightedDegree (p := p) hm
    have hsum : m.sum (fun (_ : Fin 2) (e : ℕ) => e) = m 0 + m 1 := by
      classical
      rw [m.sum_fintype (fun (_ : Fin 2) (e : ℕ) => e) (by simp)]
      simp
    simp only [PIntegralModularForm.weightedDegree] at hw
    omega
  calc
    4 * ((Abar (p := p)).support.sup fun m => m.sum fun _ e => e) ≤
        4 * ((p - 1) / 4) := Nat.mul_le_mul_left 4 hsup
    _ ≤ p - 1 := by simpa [Nat.mul_comm] using Nat.div_mul_le_self (p - 1) 4

private theorem polynomialWeight_formula (m : Fin 2 →₀ ℕ) :
    Finsupp.weight polynomialWeights m = 4 * m 0 + 6 * m 1 := by
  rw [Finsupp.weight_eq_sum]
  simp [polynomialWeights]
  ring

private theorem exponent_sum_formula (m : Fin 2 →₀ ℕ) :
    m.sum (fun (_ : Fin 2) (e : ℕ) => e) = m 0 + m 1 := by
  rw [m.sum_fintype (fun (_ : Fin 2) (e : ℕ) => e) (by simp)]
  simp

private theorem polynomialEuler_eq_smul_of_weightedHomogeneous
    (F : ResiduePolynomial p) (d : ℕ)
    (hF : MvPolynomial.IsWeightedHomogeneous polynomialWeights F d) :
    polynomialEulerDerivationMod (p := p) F = (d : ZMod p) • F := by
  have hC4 : (MvPolynomial.C (4 : ZMod p) : ResiduePolynomial p) = 4 := by
    simpa using (MvPolynomial.C_eq_coe_nat (R := ZMod p) (σ := Fin 2) 4)
  have hC6 : (MvPolynomial.C (6 : ZMod p) : ResiduePolynomial p) = 6 := by
    simpa using (MvPolynomial.C_eq_coe_nat (R := ZMod p) (σ := Fin 2) 6)
  have h := hF.sum_weight_X_mul_pderiv
  simpa [polynomialEulerDerivationMod, polynomialWeights,
    Derivation.smul_apply, Algebra.smul_def, hC4, hC6, mul_assoc] using h

/-- An eigenvector for weighted Euler in the degree range below `p` is
weighted homogeneous. The factor of two in the weights and the oddness of `p`
rule out distinct degrees congruent modulo `p`. -/
theorem euler_eigen_weightedHomogeneous (F : ResiduePolynomial p)
    (hF0 : F ≠ 0) (hdeg : 4 * F.totalDegree ≤ p - 1)
    (c : ZMod p)
    (heigen : polynomialEulerDerivationMod (p := p) F = c • F) :
    ∃ d, MvPolynomial.IsWeightedHomogeneous polynomialWeights F d := by
  have hsupport : F.support ≠ ∅ := by
    intro h
    exact hF0 (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨m₀, hm₀⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
  let d := Finsupp.weight polynomialWeights m₀
  have hcast (m : Fin 2 →₀ ℕ) (hm : m ∈ F.support) :
      (Finsupp.weight polynomialWeights m : ZMod p) = c := by
    have hcoeff := congrArg (fun Q : ResiduePolynomial p => Q.coeff m) heigen
    rw [polynomialEuler_coeff] at hcoeff
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq,
      MvPolynomial.coeff_C_mul] at hcoeff
    exact mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hm) hcoeff
  have hweightMod (m : Fin 2 →₀ ℕ) (hm : m ∈ F.support) :
      (Finsupp.weight polynomialWeights m : ZMod p) =
        (Finsupp.weight polynomialWeights m₀ : ZMod p) :=
    (hcast m hm).trans (hcast m₀ hm₀).symm
  have hpOdd : Odd p :=
    (Nat.Prime.odd_iff (inferInstance : isLargePrime p).Prime).mpr (by
      have hp5 := (inferInstance : isLargePrime p).AtLeastFive
      omega)
  have hweightEq (m : Fin 2 →₀ ℕ) (hm : m ∈ F.support) :
      Finsupp.weight polynomialWeights m = d := by
    have hp5 := (inferInstance : isLargePrime p).AtLeastFive
    have hdegreeBound : 4 * F.totalDegree + 1 ≤ p := by omega
    have hmod : Finsupp.weight polynomialWeights m ≡ d [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (hweightMod m hm)
    have hdiv := hmod.dvd
    have hsum : m 0 + m 1 ≤ F.totalDegree := by
      simpa [exponent_sum_formula] using MvPolynomial.le_totalDegree hm
    have hsum₀ : m₀ 0 + m₀ 1 ≤ F.totalDegree := by
      simpa [exponent_sum_formula] using MvPolynomial.le_totalDegree hm₀
    have hlt : Finsupp.weight polynomialWeights m < 2 * p := by
      calc
        Finsupp.weight polynomialWeights m ≤ 6 * (m 0 + m 1) := by
          rw [polynomialWeight_formula]
          omega
        _ ≤ 6 * F.totalDegree := Nat.mul_le_mul_left 6 hsum
        _ < 2 * p := by nlinarith [hdegreeBound]
    have hlt₀ : d < 2 * p := by
      dsimp [d]
      calc
        Finsupp.weight polynomialWeights m₀ ≤ 6 * (m₀ 0 + m₀ 1) := by
          rw [polynomialWeight_formula]
          omega
        _ ≤ 6 * F.totalDegree := Nat.mul_le_mul_left 6 hsum₀
        _ < 2 * p := by nlinarith [hdegreeBound]
    have heven : Even (Finsupp.weight polynomialWeights m) := by
      rw [polynomialWeight_formula]
      exact ⟨2 * m 0 + 3 * m 1, by ring⟩
    have heven₀ : Even d := by
      dsimp [d]
      rw [polynomialWeight_formula]
      exact ⟨2 * m₀ 0 + 3 * m₀ 1, by ring⟩
    rcases heven with ⟨a, ha⟩
    rcases heven₀ with ⟨b, hb⟩
    have hmod' : Finsupp.weight polynomialWeights m % p = d % p := hmod
    have hdecomp : Finsupp.weight polynomialWeights m =
        Finsupp.weight polynomialWeights m % p +
          p * (Finsupp.weight polynomialWeights m / p) := by
      have ht := Nat.mod_add_div (Finsupp.weight polynomialWeights m) p
      omega
    have hdecomp₀ : d = d % p + p * (d / p) := by
      have ht := Nat.mod_add_div d p
      omega
    rw [← hmod'] at hdecomp₀
    have hq : Finsupp.weight polynomialWeights m / p = 0 ∨
        Finsupp.weight polynomialWeights m / p = 1 := by
      have hq' : Finsupp.weight polynomialWeights m / p < 2 :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).2 (by omega)
      have hqle : Finsupp.weight polynomialWeights m / p ≤ 1 :=
        Nat.le_of_lt_succ hq'
      by_cases hz : Finsupp.weight polynomialWeights m / p = 0
      · exact Or.inl hz
      · right
        have hp : 0 < Finsupp.weight polynomialWeights m / p := Nat.pos_of_ne_zero hz
        omega
    have hq₀ : d / p = 0 ∨ d / p = 1 := by
      have hq' : d / p < 2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).2 (by omega)
      have hqle : d / p ≤ 1 := Nat.le_of_lt_succ hq'
      by_cases hz : d / p = 0
      · exact Or.inl hz
      · right
        have hp : 0 < d / p := Nat.pos_of_ne_zero hz
        omega
    rcases hpOdd with ⟨q, hqodd⟩
    rcases hq with hm0 | hm1 <;> rcases hq₀ with h00 | h01
    · rw [hm0] at hdecomp
      rw [h00] at hdecomp₀
      omega
    · rw [hm0] at hdecomp
      rw [h01] at hdecomp₀
      omega
    · rw [hm1] at hdecomp
      rw [h00] at hdecomp₀
      omega
    · rw [hm1] at hdecomp
      rw [h01] at hdecomp₀
      omega
  refine ⟨d, ?_⟩
  intro m hm
  exact hweightEq m (MvPolynomial.mem_support_iff.mpr hm)

theorem Abar_ne_zero : Abar (p := p) ≠ 0 := by
  intro h
  have heval := congrArg (evaluateResiduePolynomial (p := p)) h
  rw [evaluate_Abar] at heval
  simp at heval

/-- Strip off the full multiplicity of an irreducible factor of `Abar`. -/
private theorem exists_exact_factorization (F : ResiduePolynomial p)
    (hF : Irreducible F) (hF2 : F ^ 2 ∣ Abar (p := p)) :
    ∃ n G, 2 ≤ n ∧ n < p ∧ Abar (p := p) = F ^ n * G ∧ ¬ F ∣ G := by
  obtain ⟨n, G, hG, hAG⟩ :=
    WfDvdMonoid.max_power_factor (a₀ := Abar (p := p)) (x := F)
      (Abar_ne_zero (p := p)) hF
  have hn2 : 2 ≤ n := by
    by_contra hn
    have hnlt : n < 2 := by omega
    interval_cases n
    · have hdiv : F ∣ G := by
        have hsq : F ^ 2 ∣ G := by simpa [hAG] using hF2
        exact dvd_trans ⟨F, by ring⟩ hsq
      exact hG hdiv
    · have hsq : F ^ 2 ∣ F * G := by simpa [hAG] using hF2
      rcases hsq with ⟨q, hq⟩
      have heq : F * G = F * (F * q) := by
        calc
          F * G = F ^ 2 * q := hq
          _ = F * (F * q) := by rw [pow_two]; ring
      have hG' : G = F * q := mul_left_cancel₀ hF.ne_zero heq
      exact hG ⟨q, hG'⟩
  have hFdegree_pos : 0 < F.totalDegree := by
    by_contra hnot
    have hdegree : F.totalDegree = 0 := by omega
    have hc : F = MvPolynomial.C (F.coeff 0) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := F)).mp hdegree
    let c : ZMod p := F.coeff 0
    have hcne : c ≠ 0 := by
      intro hz
      have hz' : F.coeff 0 = 0 := by simpa [c] using hz
      have hzero : F = 0 := by rw [hc, hz']; simp
      exact hF.ne_zero hzero
    have hunit : IsUnit (MvPolynomial.C c : ResiduePolynomial p) :=
      (isUnit_iff_ne_zero.mpr hcne).map MvPolynomial.C
    have hFunit : IsUnit F := by
      rw [hc]
      simpa [c] using hunit
    exact hF.not_isUnit hFunit
  have hpowDegree (j : ℕ) : (F ^ j).totalDegree = j * F.totalDegree := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, MvPolynomial.totalDegree_mul_of_isDomain
          (pow_ne_zero _ hF.ne_zero) hF.ne_zero, ih]
        simp [Nat.succ_mul]
  have hpowdvd : F ^ n ∣ Abar (p := p) := ⟨G, hAG⟩
  have hdegreele := MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    hpowdvd (Abar_ne_zero (p := p))
  have hnle : n ≤ (Abar (p := p)).totalDegree := by
    rw [hpowDegree] at hdegreele
    nlinarith
  have hnlt : n < p := by
    have hbound := Abar_totalDegree_bound (p := p)
    omega
  exact ⟨n, G, hn2, hnlt, hAG, hG⟩

/-- Product rule for the weighted Euler derivation after factoring one power. -/
private theorem polynomialEuler_pow_mul_factor (n : ℕ) (hn : 0 < n)
    (F G : ResiduePolynomial p) :
    polynomialEulerDerivationMod (p := p) (F ^ n * G) =
      F ^ (n - 1) * ((n : ZMod p) •
        (polynomialEulerDerivationMod (p := p) F * G) +
        F * polynomialEulerDerivationMod (p := p) G) := by
  let D := polynomialEulerDerivationMod (p := p)
  rw [D.leibniz, D.leibniz_pow]
  simp only [smul_eq_mul, Algebra.smul_def]
  have hcast : (algebraMap ℕ (ResiduePolynomial p)) n =
      algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p) := by simp
  rw [hcast]
  have hpow : F ^ n = F ^ (n - 1) * F := by
    calc
      F ^ n = F ^ ((n - 1) + 1) := by congr 1; omega
      _ = F ^ (n - 1) * F := pow_succ _ _
  rw [hpow]
  ring

/-- If `Abar` contains an exact power of `F`, its Euler identity forces `F`
to divide its own weighted Euler derivative. -/
private theorem exact_factor_dvd_euler (n : ℕ) (F G : ResiduePolynomial p)
    (hF : Irreducible F)
    (hn : 0 < n) (hnp : (n : ZMod p) ≠ 0)
    (hA : Abar (p := p) = F ^ n * G) (hG : ¬ F ∣ G) :
    F ∣ polynomialEulerDerivationMod (p := p) F := by
  let D := polynomialEulerDerivationMod (p := p)
  let K := (n : ZMod p) • (D F * G) + F * D G
  have hdiv : F ^ n ∣ D (Abar (p := p)) := by
    rw [polynomialEuler_Abar (p := p), hA]
    refine ⟨MvPolynomial.C ((p - 1 : ℕ) : ZMod p) * G, ?_⟩
    simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
  have hformula : D (Abar (p := p)) = F ^ (n - 1) * K := by
    rw [hA]
    exact polynomialEuler_pow_mul_factor (p := p) n hn F G
  rw [hformula] at hdiv
  rcases hdiv with ⟨q, hq⟩
  have hnexp : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hpow : F ^ n = F ^ (n - 1) * F := by
    calc
      F ^ n = F ^ ((n - 1) + 1) := by rw [hnexp]
      _ = F ^ (n - 1) * F := pow_succ _ _
  have hmul : F ^ (n - 1) * K = F ^ (n - 1) * (F * q) := by
    calc
      F ^ (n - 1) * K = F ^ n * q := hq
      _ = F ^ (n - 1) * (F * q) := by rw [hpow, mul_assoc]
  have hK : K = F * q := mul_left_cancel₀
    (pow_ne_zero _ hF.ne_zero) hmul
  have hFK : F ∣ K := ⟨q, hK⟩
  have hterm : F ∣ F * D G := ⟨D G, rfl⟩
  have hsub : F ∣ K - F * D G := dvd_sub hFK hterm
  have hsub' : F ∣
      algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p) * (D F * G) := by
    have heq : K - F * D G =
        algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p) * (D F * G) := by
      dsimp [K]
      simp [Algebra.smul_def]
    rw [heq] at hsub
    exact hsub
  let c : ResiduePolynomial p := algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p)
  have hc : IsUnit c := (isUnit_iff_ne_zero.mpr hnp).map
    (algebraMap (ZMod p) (ResiduePolynomial p))
  have hprod : F ∣ c * (D F * G) := by simpa [c] using hsub'
  rcases hF.prime.dvd_mul.mp hprod with hcF | hrest
  · exact False.elim (hF.not_isUnit (isUnit_of_dvd_unit hcF hc))
  · rcases hF.prime.dvd_mul.mp hrest with hDF | hFG
    · exact hDF
    · exact False.elim (hG hFG)

/-- The reduction of the polynomial derivation agrees with the derivation
defined directly over `F_p`. -/
theorem delPolynomialMod_reduce (P : PIntegralModularForm.E4E6Polynomial p) :
    polynomialDerivationMod (p := p) (reducePolynomial (p := p) P) =
      reducePolynomial (p := p)
        (PIntegralModularForm.delPolynomial (p := p) P) := by
  have h4 : PIntegralModularForm.coeffToZMod (p := p)
      (4 : PIntegralModularForm.CoeffRing p) = (4 : ZMod p) := by
    simpa using map_natCast (PIntegralModularForm.coeffToZMod (p := p)) 4
  have h6 : PIntegralModularForm.coeffToZMod (p := p)
      (6 : PIntegralModularForm.CoeffRing p) = (6 : ZMod p) := by
    simpa using map_natCast (PIntegralModularForm.coeffToZMod (p := p)) 6
  simp [polynomialDerivationMod, reducePolynomial,
    PIntegralModularForm.delPolynomial_apply,
    MvPolynomial.pderiv_map,
    h4, h6]

/-- The first identity of Lemma 1.39, viewed as an identity for the
mod-`p` derivation. -/
theorem del_Abar_eq_Bbar :
    polynomialDerivationMod (p := p) (Abar (p := p)) = Bbar (p := p) := by
  rw [Abar, delPolynomialMod_reduce, ← lemma_1_39_first (p := p)]

/-- The second identity of Lemma 1.39, viewed as an identity for the
mod-`p` derivation. -/
theorem del_Bbar_eq_neg_X_mul_Abar :
    polynomialDerivationMod (p := p) (Bbar (p := p)) =
      -(MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) * Abar (p := p) := by
  rw [Bbar, delPolynomialMod_reduce, ← lemma_1_39_second (p := p)]

/-- Leibniz expansion for the mod-`p` derivation on a power times a factor.
The first summand is the term that controls the exact drop in multiplicity
when the derivative of the irreducible factor is not divisible by that
factor. -/
theorem delPolynomialMod_pow_mul (n : ℕ) (F G : ResiduePolynomial p) :
    polynomialDerivationMod (p := p) (F ^ n * G) =
      (n : ZMod p) • (F ^ (n - 1) *
          polynomialDerivationMod (p := p) F * G) +
        F ^ n * polynomialDerivationMod (p := p) G := by
  rw [(polynomialDerivationMod (p := p)).leibniz,
    (polynomialDerivationMod (p := p)).leibniz_pow]
  simp only [smul_eq_mul, Algebra.smul_def]
  have hcast : (algebraMap ℕ (ResiduePolynomial p)) n =
      algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p) := by
    simp
  rw [hcast]
  ring

/-- The preceding formula with the common power factored out. -/
theorem delPolynomialMod_pow_mul_factor (n : ℕ) (_hn : 0 < n)
    (F G : ResiduePolynomial p) :
    polynomialDerivationMod (p := p) (F ^ n * G) =
      F ^ (n - 1) *
        ((n : ZMod p) •
            (polynomialDerivationMod (p := p) F * G) +
          F * polynomialDerivationMod (p := p) G) := by
  rw [delPolynomialMod_pow_mul]
  have hpow : F ^ n = F ^ (n - 1) * F := by
    calc
      F ^ n = F ^ ((n - 1) + 1) := by congr 1; omega
      _ = F ^ (n - 1) * F := pow_succ _ _
  rw [hpow]
  simp only [Algebra.smul_def]
  ring

/-- The cofactor after removing the forced `F^(n-1)` factor is not divisible
by `F`, under the hypotheses of the exact multiplicity argument. -/
theorem delPolynomialMod_pow_mul_remainder_not_dvd
    (n : ℕ) (F G : ResiduePolynomial p)
    (hF : Irreducible F)
    (hD : ¬ F ∣ polynomialDerivationMod (p := p) F)
    (hG : ¬ F ∣ G) (hnp : (n : ZMod p) ≠ 0) :
    ¬ F ∣ ((n : ZMod p) •
      (polynomialDerivationMod (p := p) F * G) +
      F * polynomialDerivationMod (p := p) G) := by
  intro hdiv
  have hterm : F ∣ F * polynomialDerivationMod (p := p) G :=
    ⟨polynomialDerivationMod (p := p) G, rfl⟩
  have hsub := dvd_sub hdiv hterm
  have hscalar : IsUnit
      (algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p)) :=
    (isUnit_iff_ne_zero.mpr hnp).map
      (algebraMap (ZMod p) (ResiduePolynomial p))
  have hprod : F ∣
      algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p) *
        (polynomialDerivationMod (p := p) F * G) := by
    have heq :
        ((n : ZMod p) •
          (polynomialDerivationMod (p := p) F * G) +
          F * polynomialDerivationMod (p := p) G) -
            F * polynomialDerivationMod (p := p) G =
          algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p) *
            (polynomialDerivationMod (p := p) F * G) := by
      simp [Algebra.smul_def]
    rw [heq] at hsub
    exact hsub
  rcases hF.prime.dvd_mul.mp hprod with hFc | hFrest
  · exact hF.not_isUnit (isUnit_of_dvd_unit hFc hscalar)
  · rcases hF.prime.dvd_mul.mp hFrest with hFD | hFG
    · exact hD hFD
    · exact hG hFG

/-- If an irreducible factor does not divide its own derivative, differentiation
lowers its exact multiplicity by one. This is the divisibility half of the
valuation argument used in Lemma 1.40. -/
theorem delPolynomialMod_pow_mul_not_dvd
    (n : ℕ) (hn : 0 < n) (F G : ResiduePolynomial p)
    (hF : Irreducible F)
    (hD : ¬ F ∣ polynomialDerivationMod (p := p) F)
    (hG : ¬ F ∣ G) (hnp : (n : ZMod p) ≠ 0) :
    ¬ F ^ n ∣ polynomialDerivationMod (p := p) (F ^ n * G) := by
  let D := polynomialDerivationMod (p := p)
  let K := (n : ZMod p) • (D F * G) + F * D G
  have hformula : D (F ^ n * G) = F ^ (n - 1) * K := by
    dsimp [K, D]
    exact delPolynomialMod_pow_mul_factor (p := p) n hn F G
  rw [hformula]
  intro hdiv
  rcases hdiv with ⟨q, hq⟩
  have hnexp : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hpow : F ^ n = F ^ (n - 1) * F := by
    calc
      F ^ n = F ^ ((n - 1) + 1) := by rw [hnexp]
      _ = F ^ (n - 1) * F := pow_succ _ _
  have hF0 : F ≠ 0 := hF.ne_zero
  have hpow0 : F ^ (n - 1) ≠ 0 := pow_ne_zero _ hF0
  have hmul : F ^ (n - 1) * K = F ^ (n - 1) * (F * q) := by
    calc
      F ^ (n - 1) * K = F ^ n * q := hq
      _ = F ^ (n - 1) * (F * q) := by rw [hpow, mul_assoc]
  have hK : K = F * q := mul_left_cancel₀ hpow0 hmul
  have hFK : F ∣ K := ⟨q, hK⟩
  have hterm : F ∣ F * D G := ⟨D G, rfl⟩
  have hsub : F ∣ K - F * D G := dvd_sub hFK hterm
  have hsub' : F ∣ (n : ZMod p) • (D F * G) := by
    have heq : K - F * D G = (n : ZMod p) • (D F * G) := by
      dsimp [K]
      module
    rw [heq] at hsub
    exact hsub
  rw [Algebra.smul_def] at hsub'
  let c : ResiduePolynomial p := algebraMap (ZMod p) (ResiduePolynomial p) (n : ZMod p)
  have hc : IsUnit c := (isUnit_iff_ne_zero.mpr hnp).map
    (algebraMap (ZMod p) (ResiduePolynomial p))
  have hprod : F ∣ c * (D F * G) := by simpa [c] using hsub'
  rcases hF.prime.dvd_mul.mp hprod with hcF | hrest
  · exact hF.not_isUnit (isUnit_of_dvd_unit hcF hc)
  · rcases hF.prime.dvd_mul.mp hrest with hDF | hFG
    · exact hD hDF
    · exact hG hFG

/-- Once the first derivative has exact multiplicity `n - 1`, the identity
`∂B̄ = -XĀ` contradicts it. This is the second-derivative step in the proof. -/
theorem lemma_1_40_second_derivative_contradiction
    (n : ℕ) (hn : 2 ≤ n) (F G K : ResiduePolynomial p)
    (hF : Irreducible F)
    (hA : Abar (p := p) = F ^ n * G)
    (hB : Bbar (p := p) = F ^ (n - 1) * K)
    (hG : ¬ F ∣ K)
    (hD : ¬ F ∣ polynomialDerivationMod (p := p) F)
    (hnm1p : ((n - 1 : ℕ) : ZMod p) ≠ 0)
    (hDB : polynomialDerivationMod (p := p) (Bbar (p := p)) =
      -(MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) * Abar (p := p)) : False := by
  have hn1pos : 0 < n - 1 := by omega
  have hnot' : ¬ F ^ (n - 1) ∣
      polynomialDerivationMod (p := p) (F ^ (n - 1) * K) :=
    delPolynomialMod_pow_mul_not_dvd (p := p) (n - 1) hn1pos F K
      hF hD hG hnm1p
  have hnot : ¬ F ^ (n - 1) ∣
      polynomialDerivationMod (p := p) (Bbar (p := p)) := by
    rw [hB]
    exact hnot'
  have hnexp : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hpow : F ^ n = F ^ (n - 1) * F := by
    calc
      F ^ n = F ^ ((n - 1) + 1) := by rw [hnexp]
      _ = F ^ (n - 1) * F := pow_succ _ _
  have hdiv : F ^ (n - 1) ∣
      polynomialDerivationMod (p := p) (Bbar (p := p)) := by
    rw [hDB, hA, hpow]
    refine ⟨-((MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) * F * G), ?_⟩
    ring
  exact hnot hdiv

private def discriminantPolynomial : ResiduePolynomial p :=
  (MvPolynomial.X (0 : Fin 2)) ^ 3 - (MvPolynomial.X (1 : Fin 2)) ^ 2

private theorem euler_del_relation (F : ResiduePolynomial p) :
    MvPolynomial.X (1 : Fin 2) * polynomialEulerDerivationMod (p := p) F +
        MvPolynomial.X (0 : Fin 2) * polynomialDerivationMod (p := p) F =
      MvPolynomial.C (-6 : ZMod p) *
        (discriminantPolynomial (p := p) *
          MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 F) := by
  simp only [polynomialEulerDerivationMod, polynomialDerivationMod,
    Derivation.add_apply, Derivation.smul_apply, smul_eq_mul,
    Algebra.smul_def]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.C_neg,
    discriminantPolynomial]
  have hC4 : (MvPolynomial.C (4 : ZMod p) : ResiduePolynomial p) = 4 := by
    simpa using (MvPolynomial.C_eq_coe_nat (R := ZMod p) (σ := Fin 2) 4)
  have hC6 : (MvPolynomial.C (6 : ZMod p) : ResiduePolynomial p) = 6 := by
    simpa using (MvPolynomial.C_eq_coe_nat (R := ZMod p) (σ := Fin 2) 6)
  rw [hC4, hC6]
  ring

private theorem pderiv_support_source {i : Fin 2} {F : ResiduePolynomial p}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ (MvPolynomial.pderiv (R := ZMod p)
      (σ := Fin 2) i F).support) : m + Finsupp.single i 1 ∈ F.support := by
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [MvPolynomial.coeff_pderiv] at hm
  intro hz
  apply hm
  simp [hz]

private theorem pderiv_totalDegree_lt (F : ResiduePolynomial p) (i : Fin 2)
    (hder : MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) i F ≠ 0) :
    (MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) i F).totalDegree <
      F.totalDegree := by
  let Q := MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) i F
  have hle : ∀ m ∈ Q.support, m.sum (fun _ e => e) ≤ F.totalDegree - 1 := by
    intro m hm
    have hsource := pderiv_support_source (p := p) hm
    have hsource_le := MvPolynomial.le_totalDegree hsource
    have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) =
        m.sum (fun _ e => e) + 1 := by
      rw [exponent_sum_formula, exponent_sum_formula]
      fin_cases i <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> omega
    rw [hsum] at hsource_le
    omega
  have hsup := Finset.sup_le hle
  have hQdeg : Q.totalDegree ≤ F.totalDegree - 1 := by
    exact hsup
  have hFdegpos : 0 < F.totalDegree := by
    by_contra hzero
    have hz : F.totalDegree = 0 := by omega
    have hconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := F)).mp hz
    rw [hconst] at hder
    simp at hder
  have hlt : Q.totalDegree < F.totalDegree := by
    omega
  simpa [Q] using hlt

private theorem natCast_ne_zero_of_lt_prime {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hz
  rcases hdvd with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    simp [this] at hk
    omega
  have hple : p ≤ p * k := by
    calc
      p = p * 1 := by simp
      _ ≤ p * k := Nat.mul_le_mul_left p (by omega)
  omega

private theorem x_not_dvd_discriminant :
    ¬ (MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) ∣
      discriminantPolynomial (p := p) := by
  rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero]
  intro h
  have hcoeff := congrArg (fun Q : ResiduePolynomial p => Q.coeff (Finsupp.single 1 2)) h
  have hnotle : ¬ Finsupp.single (0 : Fin 2) 1 ≤ Finsupp.single 1 2 := by
    intro hle
    have h := hle 0
    norm_num [Finsupp.single_apply] at h
  rw [MvPolynomial.coeff_modMonomial_of_not_le _ hnotle] at hcoeff
  have hne : Finsupp.single (0 : Fin 2) 3 ≠ Finsupp.single 1 2 := by
    intro he
    have h0 := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
    norm_num [Finsupp.single_apply] at h0
  simp [discriminantPolynomial, MvPolynomial.coeff_X_pow, hne] at hcoeff

private theorem y_not_dvd_discriminant :
    ¬ (MvPolynomial.X (1 : Fin 2) : ResiduePolynomial p) ∣
      discriminantPolynomial (p := p) := by
  rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero]
  intro h
  have hcoeff := congrArg (fun Q : ResiduePolynomial p => Q.coeff (Finsupp.single 0 3)) h
  have hnotle : ¬ Finsupp.single (1 : Fin 2) 1 ≤ Finsupp.single 0 3 := by
    intro hle
    have h := hle 1
    norm_num [Finsupp.single_apply] at h
  rw [MvPolynomial.coeff_modMonomial_of_not_le _ hnotle] at hcoeff
  have hne : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 3 := by
    intro he
    have h1 := congrArg (fun m : Fin 2 →₀ ℕ => m 1) he
    norm_num [Finsupp.single_apply] at h1
  simp [discriminantPolynomial, MvPolynomial.coeff_X_pow, hne] at hcoeff

theorem euler_divisor_eigen (F : ResiduePolynomial p)
    (hF : Irreducible F)
    (hdiv : F ∣ polynomialEulerDerivationMod (p := p) F) :
    ∃ c : ZMod p, polynomialEulerDerivationMod (p := p) F = c • F := by
  rcases hdiv with ⟨Q, hQ⟩
  by_cases hQ0 : Q = 0
  · refine ⟨0, ?_⟩
    rw [hQ, hQ0]
    simp
  · have hdegBound :
        (polynomialEulerDerivationMod (p := p) F).totalDegree ≤ F.totalDegree :=
      MvPolynomial.totalDegree_le_of_support_subset
        (polynomialEuler_support_subset (p := p) F)
    have hdegMul := MvPolynomial.totalDegree_mul_of_isDomain hF.ne_zero hQ0
    have hQdeg : Q.totalDegree = 0 := by
      rw [hQ] at hdegBound
      rw [MvPolynomial.totalDegree_mul_of_isDomain hF.ne_zero hQ0] at hdegBound
      omega
    have hQC : Q = MvPolynomial.C (Q.coeff 0) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := Q)).mp hQdeg
    refine ⟨Q.coeff 0, ?_⟩
    calc
      polynomialEulerDerivationMod (p := p) F = F * Q := hQ
      _ = (Q.coeff 0) • F := by
        rw [hQC]
        simp [Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_comm]

private theorem irreducible_totalDegree_pos (F : ResiduePolynomial p)
    (hF : Irreducible F) : 0 < F.totalDegree := by
  by_contra hnot
  have hz : F.totalDegree = 0 := by omega
  have hC := (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := F)).mp hz
  let c : ZMod p := F.coeff 0
  have hc : c ≠ 0 := by
    intro hc
    have hzero : F = 0 := by
      rw [hC]
      simp [c, hc]
    exact hF.ne_zero hzero
  have hunit : IsUnit (MvPolynomial.C c : ResiduePolynomial p) :=
    (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  have hFunit : IsUnit F := by
    rw [hC]
    simpa [c] using hunit
  exact hF.not_isUnit hFunit

private theorem y_exponent_zero_of_pderiv_zero (F : ResiduePolynomial p)
    (hFdeg : F.totalDegree < p)
    (hzero : MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 F = 0)
    {m : Fin 2 →₀ ℕ} (hm : m ∈ F.support) : m 1 = 0 := by
  by_contra hm1
  have hm1pos : 0 < m 1 := Nat.pos_of_ne_zero hm1
  have hsumle := MvPolynomial.le_totalDegree hm
  have hm1lt : m 1 < p := by
    rw [exponent_sum_formula] at hsumle
    omega
  have hm1cast : (m 1 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_lt_prime hm1pos hm1lt
  let m' := m - Finsupp.single (1 : Fin 2) 1
  have hcoeffzero :
      (MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 F).coeff m' = 0 := by
    rw [hzero]
    simp
  rw [MvPolynomial.coeff_pderiv] at hcoeffzero
  have hmdecomp : m' + Finsupp.single (1 : Fin 2) 1 = m :=
    Finsupp.sub_add_single_one_cancel hm1
  rw [hmdecomp] at hcoeffzero
  have hmval : m' 1 + 1 = m 1 := by
    change m 1 - (Finsupp.single (1 : Fin 2) 1) 1 + 1 = m 1
    simp only [Finsupp.single_apply]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm1)
  have hcastval : ((m' 1 + 1 : ℕ) : ZMod p) = (m 1 : ZMod p) := by
    exact congrArg (fun n : ℕ => (n : ZMod p)) hmval
  have hprod : F.coeff m * (m 1 : ZMod p) = 0 := by
    have hcastval' : ((m' 1 : ℕ) : ZMod p) + 1 = (m 1 : ZMod p) := by
      simpa using hcastval
    rw [hcastval'] at hcoeffzero
    exact hcoeffzero
  exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hm) hm1cast) hprod

private theorem no_irreducible_y_independent_self_divisor
    (F : ResiduePolynomial p) (hF : Irreducible F)
    (d : ℕ)
    (hhom : MvPolynomial.IsWeightedHomogeneous polynomialWeights F d)
    (hdegreeBound : 4 * F.totalDegree ≤ p - 1)
    (hDF : F ∣ polynomialDerivationMod (p := p) F)
    (hFy : MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 F = 0) : False := by
  have hFdegP : F.totalDegree < p := by
    have hp5 := (inferInstance : isLargePrime p).AtLeastFive
    omega
  have hF0 : F ≠ 0 := hF.ne_zero
  have hsupport : F.support ≠ ∅ := by
    intro he
    exact hF0 (MvPolynomial.support_eq_empty.mp he)
  obtain ⟨m0, hm0⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
  have hm0y := y_exponent_zero_of_pderiv_zero (p := p) F hFdegP hFy hm0
  have hsame (m : Fin 2 →₀ ℕ) (hm : m ∈ F.support) : m = m0 := by
    have hmy := y_exponent_zero_of_pderiv_zero (p := p) F hFdegP hFy hm
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hm)
    have hweight0 := hhom (MvPolynomial.mem_support_iff.mp hm0)
    have hweightEq : Finsupp.weight polynomialWeights m =
        Finsupp.weight polynomialWeights m0 := hweight.trans hweight0.symm
    simp only [polynomialWeight_formula] at hweightEq
    simp only [hmy, hm0y, Nat.mul_zero, add_zero] at hweightEq
    ext i
    fin_cases i
    · have hx : m 0 = m0 0 := by nlinarith [hweightEq]
      exact hx
    · exact hmy.trans hm0y.symm
  have hmono : F = MvPolynomial.monomial m0 (F.coeff m0) :=
    MvPolynomial.eq_monomial_of_support_subset_singleton hsame
  have hm0eq : m0 = Finsupp.single (0 : Fin 2) (m0 0) := by
    ext i
    fin_cases i
    · simp
    · simp [hm0y]
  let a := m0 0
  let c := F.coeff m0
  have hmono' : F = MvPolynomial.monomial (Finsupp.single (0 : Fin 2) a) c := by
    have hcoeff : F.coeff m0 = F.coeff (Finsupp.single (0 : Fin 2) a) :=
      congrArg F.coeff hm0eq
    have hmonoTmp := hmono
    rw [hm0eq] at hmonoTmp
    rw [← hcoeff] at hmonoTmp
    simpa [a, c] using hmonoTmp
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hm0
  have ha : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := by omega
    have hmzero : m0 = 0 := by
      ext i
      fin_cases i
      · simp [a, ha0]
      · exact hm0y
    have hmonoZero := hmono
    rw [hmzero] at hmonoZero
    have hcoeffzero : F.coeff m0 = F.coeff 0 := congrArg F.coeff hmzero
    rw [← hcoeffzero] at hmonoZero
    have hC : F = MvPolynomial.C c := by simpa [c] using hmonoZero
    have hunit : IsUnit (MvPolynomial.C c : ResiduePolynomial p) :=
      (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
    exact hF.not_isUnit (by rw [hC]; exact hunit)
  have hsumle := MvPolynomial.le_totalDegree hm0
  have halt : a ≤ F.totalDegree := by
    rw [exponent_sum_formula] at hsumle
    simpa [a, hm0y] using hsumle
  have haltp : a < p := lt_of_le_of_lt halt hFdegP
  have hacast : (a : ZMod p) ≠ 0 := natCast_ne_zero_of_lt_prime ha haltp
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have h4cast : (4 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_lt_prime (p := p) (n := 4) (by omega) (by omega)
  have hneg4 : (-4 : ZMod p) ≠ 0 := by
    intro h
    exact h4cast (by simpa using h)
  have hpx : MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 F =
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (a - 1)) (c * a) := by
    rw [hmono', MvPolynomial.pderiv_monomial]
    simp [Finsupp.single_apply, Nat.sub_add_cancel (by omega : 1 ≤ a)]
  have hDexpr : polynomialDerivationMod (p := p) F =
      MvPolynomial.C (-4 : ZMod p) * MvPolynomial.X (1 : Fin 2) *
        MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0 F := by
    simp only [polynomialDerivationMod, Derivation.add_apply,
      Derivation.smul_apply, smul_eq_mul, hFy, mul_zero, add_zero]
  let v := Finsupp.single (0 : Fin 2) (a - 1) +
    Finsupp.single (1 : Fin 2) 1
  let b : ZMod p := (-4) * (a : ZMod p) * c
  have hcoeffb : b ≠ 0 := mul_ne_zero (mul_ne_zero hneg4 hacast) hc
  have hDFmono : polynomialDerivationMod (p := p) F = MvPolynomial.monomial v b := by
    rw [hDexpr, hpx]
    rw [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.monomial_mul_monomial]
    rw [show Finsupp.single (1 : Fin 2) 1 + Finsupp.single 0 (a - 1) = v by
      dsimp [v]
      ext i
      fin_cases i <;> simp [Finsupp.single_apply] <;> omega]
    change MvPolynomial.monomial v ((-4 : ZMod p) * (c * a)) =
      MvPolynomial.monomial v b
    congr 1
    ring
  rcases hDF with ⟨q, hq⟩
  have hmonodvd :
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) a) c ∣
        MvPolynomial.monomial v b := by
    refine ⟨q, ?_⟩
    calc
      MvPolynomial.monomial v b = polynomialDerivationMod (p := p) F := hDFmono.symm
      _ = F * q := hq
      _ = MvPolynomial.monomial (Finsupp.single (0 : Fin 2) a) c * q := by rw [← hmono']
  rw [MvPolynomial.monomial_dvd_monomial] at hmonodvd
  have hle : Finsupp.single (0 : Fin 2) a ≤ v := by
    rcases hmonodvd.1 with hbzero | hle
    · exact False.elim (hcoeffb hbzero)
    · exact hle
  have hxle := hle 0
  simp [v, Finsupp.single_apply] at hxle
  omega

theorem irreducible_factor_divides_discriminant
    (F : ResiduePolynomial p) (hF : Irreducible F)
    (hEF : F ∣ polynomialEulerDerivationMod (p := p) F)
    (hDF : F ∣ polynomialDerivationMod (p := p) F)
    (d : ℕ)
    (hhom : MvPolynomial.IsWeightedHomogeneous polynomialWeights F d)
    (hdegreeBound : 4 * F.totalDegree ≤ p - 1) :
    F ∣ discriminantPolynomial (p := p) := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have h6cast : (6 : ZMod p) ≠ 0 := by
    by_cases hpEq : p = 5
    · subst p
      intro h
      have hdvd : 5 ∣ 6 := (ZMod.natCast_eq_zero_iff 6 5).mp h
      norm_num at hdvd
    · have hpne6 : p ≠ 6 := by
        intro heq
        have hp := (inferInstance : isLargePrime p).Prime
        rw [heq] at hp
        exact (by decide : ¬ Nat.Prime 6) hp
      have hlt : 6 < p := by omega
      exact natCast_ne_zero_of_lt_prime (p := p) (n := 6) (by omega) hlt
  have hneg6 : (-6 : ZMod p) ≠ 0 := by
    intro h
    exact h6cast (by simpa using h)
  have hunit : IsUnit (MvPolynomial.C (-6 : ZMod p) : ResiduePolynomial p) :=
    (isUnit_iff_ne_zero.mpr hneg6).map MvPolynomial.C
  have htermE : F ∣ MvPolynomial.X (1 : Fin 2) *
      polynomialEulerDerivationMod (p := p) F := by
    rcases hEF with ⟨q, hq⟩
    exact ⟨MvPolynomial.X (1 : Fin 2) * q, by rw [hq]; ring⟩
  have htermD : F ∣ MvPolynomial.X (0 : Fin 2) *
      polynomialDerivationMod (p := p) F := by
    rcases hDF with ⟨q, hq⟩
    exact ⟨MvPolynomial.X (0 : Fin 2) * q, by rw [hq]; ring⟩
  have hrel : F ∣ MvPolynomial.X (1 : Fin 2) *
      polynomialEulerDerivationMod (p := p) F +
      MvPolynomial.X (0 : Fin 2) * polynomialDerivationMod (p := p) F :=
    dvd_add htermE htermD
  rw [euler_del_relation] at hrel
  rcases hF.prime.dvd_mul.mp hrel with hC | hprod
  · exact False.elim (hF.not_isUnit (isUnit_of_dvd_unit hC hunit))
  · rcases hF.prime.dvd_mul.mp hprod with hdelta | hFydiv
    · exact hdelta
    · by_cases hzero : MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1 F = 0
      · exact False.elim (no_irreducible_y_independent_self_divisor
          (p := p) F hF d hhom hdegreeBound hDF hzero)
      · have hdegY := pderiv_totalDegree_lt (p := p) F 1 hzero
        have hFdegY := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hFydiv hzero
        omega

theorem homogeneous_factor_discriminant_degree (F : ResiduePolynomial p)
    (hF : Irreducible F) (d : ℕ)
    (hhom : MvPolynomial.IsWeightedHomogeneous polynomialWeights F d)
    (hdeg : F.totalDegree ≤ 3)
    (hdiv : F ∣ discriminantPolynomial (p := p)) : F.totalDegree = 3 := by
  by_contra hne
  have hlt : F.totalDegree < 3 := by
    have hpos := irreducible_totalDegree_pos (p := p) F hF
    omega
  have hF0 : F ≠ 0 := hF.ne_zero
  have hsupport : F.support ≠ ∅ := by
    intro he
    exact hF0 (MvPolynomial.support_eq_empty.mp he)
  obtain ⟨m0, hm0⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
  have hweight0 : Finsupp.weight polynomialWeights m0 = d :=
    hhom (MvPolynomial.mem_support_iff.mp hm0)
  have hsum0 : m0.sum (fun _ e => e) ≤ 2 := by
    have := MvPolynomial.le_totalDegree hm0
    omega
  have hsame (m : Fin 2 →₀ ℕ) (hm : m ∈ F.support) : m = m0 := by
    have hweight : Finsupp.weight polynomialWeights m = d :=
      hhom (MvPolynomial.mem_support_iff.mp hm)
    have hsum : m.sum (fun _ e => e) ≤ 2 := by
      have := MvPolynomial.le_totalDegree hm
      omega
    have hweightEq : Finsupp.weight polynomialWeights m =
        Finsupp.weight polynomialWeights m0 := hweight.trans hweight0.symm
    simp only [polynomialWeight_formula] at hweightEq
    have h0 : m 0 + m 1 ≤ 2 := by simpa [exponent_sum_formula] using hsum
    have h00 : m0 0 + m0 1 ≤ 2 := by
      simpa [exponent_sum_formula] using hsum0
    have hweightEq' : 4 * m 0 + 6 * m 1 = 4 * m0 0 + 6 * m0 1 := hweightEq
    have hxy : m 0 = m0 0 ∧ m 1 = m0 1 := by
      omega
    ext i
    fin_cases i
    · exact hxy.1
    · exact hxy.2
  have hmono : F = MvPolynomial.monomial m0 (F.coeff m0) :=
    MvPolynomial.eq_monomial_of_support_subset_singleton hsame
  have hm0pos : m0 0 ≠ 0 ∨ m0 1 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    have hmzero : m0 = 0 := by
      ext i
      fin_cases i <;> simp [hzero]
    have hdegreezero : F.totalDegree = 0 := by
      rw [hmono, hmzero]
      simp [MvPolynomial.totalDegree]
    have := irreducible_totalDegree_pos (p := p) F hF
    omega
  rcases hm0pos with hx | hy
  · have hXdvd : MvPolynomial.X (0 : Fin 2) ∣ F := by
      rw [hmono]
      exact MvPolynomial.X_dvd_monomial.mpr (Or.inr hx)
    exact x_not_dvd_discriminant (dvd_trans hXdvd hdiv)
  · have hYdvd : MvPolynomial.X (1 : Fin 2) ∣ F := by
      rw [hmono]
      exact MvPolynomial.X_dvd_monomial.mpr (Or.inr hy)
    exact y_not_dvd_discriminant (dvd_trans hYdvd hdiv)

theorem discriminant_totalDegree :
    (discriminantPolynomial (p := p)).totalDegree = 3 := by
  have hupper : (discriminantPolynomial (p := p)).totalDegree ≤ 3 := by
    change MvPolynomial.totalDegree
      (MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 2) ≤ 3
    calc
      MvPolynomial.totalDegree
          (MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 2) ≤
          max (MvPolynomial.totalDegree (MvPolynomial.X (0 : Fin 2) ^ 3))
            (MvPolynomial.totalDegree (MvPolynomial.X (1 : Fin 2) ^ 2)) :=
        MvPolynomial.totalDegree_sub _ _
      _ ≤ 3 := by norm_num
  have hmem : Finsupp.single (0 : Fin 2) 3 ∈
      (discriminantPolynomial (p := p)).support := by
    rw [MvPolynomial.mem_support_iff]
    have hne : Finsupp.single (0 : Fin 2) 3 ≠ Finsupp.single 1 2 := by
      intro he
      have h0 := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
      norm_num [Finsupp.single_apply] at h0
    simp [discriminantPolynomial, MvPolynomial.coeff_X_pow, hne, hne.symm]
  have hlower := MvPolynomial.le_totalDegree hmem
  have hsum : (Finsupp.single (0 : Fin 2) 3).sum (fun _ e => e) = 3 := by
    simp
  rw [hsum] at hlower
  omega

theorem discriminant_ne_zero :
    discriminantPolynomial (p := p) ≠ 0 := by
  intro hzero
  have hdeg := congrArg MvPolynomial.totalDegree hzero
  rw [discriminant_totalDegree (p := p)] at hdeg
  simp at hdeg

theorem evaluate_discriminant_constantCoeff :
    PowerSeries.constantCoeff
      (evaluateResiduePolynomial (p := p) (discriminantPolynomial (p := p))) = 0 := by
  have hE4 : PowerSeries.constantCoeff
      (((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [← ModularFormMod.coeff_def,
      PIntegralModularForm.coeff_Reduce,
      PIntegralModularForm.coeff_Eis (by norm_num) (by norm_num) 0]
    norm_num [PIntegralModularForm.coeffToZMod_algebraMap, bernoulli]
  have hbernoulli6 : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    have hB5 : bernoulli' 5 = 0 :=
      bernoulli'_eq_zero_of_odd (by decide) (by decide)
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose,
      bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
      bernoulli'_four, hB5]
  have hE6 : PowerSeries.constantCoeff
      (((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [← ModularFormMod.coeff_def,
      PIntegralModularForm.coeff_Reduce,
      PIntegralModularForm.coeff_Eis (by norm_num) (by norm_num) 0]
    norm_num [PIntegralModularForm.coeffToZMod_algebraMap, hbernoulli6]
  have hx0 : evaluateResiduePolynomial (p := p) (MvPolynomial.X (0 : Fin 2)) =
      ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier := by
    simp [evaluateResiduePolynomial]
  have hx1 : evaluateResiduePolynomial (p := p) (MvPolynomial.X (1 : Fin 2)) =
      ((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier := by
    simp [evaluateResiduePolynomial]
  rw [discriminantPolynomial, map_sub, map_pow, map_pow, hx0, hx1]
  rw [map_sub, map_pow, map_pow, hE4, hE6]
  norm_num

theorem homogeneous_factor_of_discriminant_not_divides_Abar
    (F : ResiduePolynomial p) (hF : Irreducible F)
    (d : ℕ) (hhom : MvPolynomial.IsWeightedHomogeneous polynomialWeights F d)
    (hFdeg : F.totalDegree ≤ 3)
    (hFdelta : F ∣ discriminantPolynomial (p := p))
    (hFA : F ∣ Abar (p := p)) : False := by
  have hdegree := homogeneous_factor_discriminant_degree (p := p) F hF d hhom
    hFdeg hFdelta
  rcases hFdelta with ⟨Q, hdelta⟩
  have hQ0 : Q ≠ 0 := by
    intro hzero
    have : discriminantPolynomial (p := p) = 0 := by rw [hdelta, hzero]; simp
    have hdeg0 := congrArg MvPolynomial.totalDegree this
    rw [discriminant_totalDegree (p := p)] at hdeg0
    simp at hdeg0
  have hdegMul := MvPolynomial.totalDegree_mul_of_isDomain hF.ne_zero hQ0
  have hQdeg : Q.totalDegree = 0 := by
    have heq := congrArg MvPolynomial.totalDegree hdelta
    rw [discriminant_totalDegree (p := p),
      MvPolynomial.totalDegree_mul_of_isDomain hF.ne_zero hQ0, hdegree] at heq
    omega
  have hQC : Q = MvPolynomial.C (Q.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := Q)).mp hQdeg
  let ev0 : ResiduePolynomial p →+* ZMod p :=
    (PowerSeries.constantCoeff (R := ZMod p)).comp
      (evaluateResiduePolynomial (p := p))
  have hdelta0 : ev0 (discriminantPolynomial (p := p)) = 0 := by
    exact evaluate_discriminant_constantCoeff (p := p)
  have hQcoeff : ev0 Q = Q.coeff 0 := by
    rw [hQC]
    change PowerSeries.constantCoeff
      (evaluateResiduePolynomial (p := p) (MvPolynomial.C (Q.coeff 0))) =
        (MvPolynomial.C (Q.coeff 0)).coeff 0
    rw [show evaluateResiduePolynomial (p := p) (MvPolynomial.C (Q.coeff 0)) =
      PowerSeries.C (Q.coeff 0) by simp [evaluateResiduePolynomial]]
    simp
  have hQcoeffne : Q.coeff 0 ≠ 0 := by
    intro hzero
    have hzeroPoly : Q = 0 := by rw [hQC, hzero]; simp
    exact hQ0 hzeroPoly
  have hFeval_zero : ev0 F = 0 := by
    have heval := congrArg ev0 hdelta
    rw [map_mul, hdelta0, hQcoeff] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_right hQcoeffne
  rcases hFA with ⟨G, hA⟩
  have hAeval := congrArg ev0 hA
  rw [map_mul, hFeval_zero, zero_mul] at hAeval
  have hone : ev0 (Abar (p := p)) = 1 := by
    have h := congrArg (PowerSeries.constantCoeff (R := ZMod p))
      (evaluate_Abar (p := p))
    simpa [ev0] using h
  rw [hone] at hAeval
  exact one_ne_zero hAeval

set_option maxHeartbeats 2000000
/-- Lemma 1.40 (squarefreeness): `Ã` has no repeated factors. -/
theorem lemma_1_40_squarefree : Squarefree (Abar (p := p)) := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero (Abar_ne_zero (p := p))]
  intro F hF hF2
  have hF2pow : F ^ 2 ∣ Abar (p := p) := by
    simpa [pow_two] using hF2
  obtain ⟨n, G, hn2, hnp, hA, hG⟩ :=
    exists_exact_factorization (p := p) F hF hF2pow
  have hnpCast : (n : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_lt_prime (by omega) hnp
  have hFA : F ∣ Abar (p := p) := by
    refine ⟨F ^ (n - 1) * G, ?_⟩
    rw [hA]
    have hpow : F ^ n = F * F ^ (n - 1) := by
      calc
        F ^ n = F ^ ((n - 1) + 1) := by congr 1; omega
        _ = F ^ (n - 1) * F := pow_succ _ _
        _ = F * F ^ (n - 1) := by ring
    rw [hpow]
    ring
  have hFdegA := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hFA
    (Abar_ne_zero (p := p))
  have hAdeg := Abar_totalDegree_bound (p := p)
  have hFdegreeBound : 4 * F.totalDegree ≤ p - 1 := by nlinarith
  by_cases hDF : F ∣ polynomialDerivationMod (p := p) F
  · have hEF : F ∣ polynomialEulerDerivationMod (p := p) F :=
      exact_factor_dvd_euler (p := p) n F G hF (by omega) hnpCast hA hG
    obtain ⟨c, hEigen⟩ := euler_divisor_eigen (p := p) F hF hEF
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
      (p := p) F hF d hhom hFdegD3 hFdelta hFA
  · let K := (n : ZMod p) •
        (polynomialDerivationMod (p := p) F * G) +
        F * polynomialDerivationMod (p := p) G
    have hB : Bbar (p := p) = F ^ (n - 1) * K := by
      rw [← del_Abar_eq_Bbar (p := p), hA]
      exact delPolynomialMod_pow_mul_factor (p := p) n (by omega) F G
    have hK : ¬ F ∣ K :=
      delPolynomialMod_pow_mul_remainder_not_dvd (p := p) n F G hF hDF hG hnpCast
    have hnm1pos : 0 < n - 1 := by omega
    have hnm1p : ((n - 1 : ℕ) : ZMod p) ≠ 0 :=
      natCast_ne_zero_of_lt_prime hnm1pos (by omega)
    exact lemma_1_40_second_derivative_contradiction (p := p) n hn2 F G K hF
      hA hB hK hDF hnm1p (del_Bbar_eq_neg_X_mul_Abar (p := p))


end
end PIntegralModularForm.SwD
