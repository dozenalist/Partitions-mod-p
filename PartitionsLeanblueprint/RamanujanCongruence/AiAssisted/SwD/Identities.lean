import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.DelOperator
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.ZMod
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.ModularForms.RamanujanFormula

/-!
# The Hasse polynomial and the mod-p modular-form algebra

This file sets up the polynomial statements in Section 1.3 of Swinnerton-Dyer's
thesis. The modular forms in this development are stored one weight class at a
time, so Theorem 1.41 is stated componentwise: each weight component has a
polynomial representative, and equality of representatives is controlled by
the Hasse relation.
-/

open MvPolynomial PowerSeries MatrixGroups ModularForm UpperHalfPlane
  Function.Periodic EisensteinSeries Filter Real Complex
open scoped Topology

namespace PIntegralModularForm.SwD

noncomputable section

variable {p : ℕ} [isLargePrime p]

/-- The constant coefficient of the p-integral Eisenstein series of weight
`p - 1`. -/
def eisMinusOneConstant : CoeffRing p :=
  (PIntegralModularForm.Eis (p := p) ((p : ℤ) - 1)).coeff 0

/-- The constant coefficient of the p-integral Eisenstein series of weight
`p + 1`. -/
def eisPlusOneConstant : CoeffRing p :=
  (PIntegralModularForm.Eis (p := p) ((p : ℤ) + 1)).coeff 0

private theorem eisMinusOne_coeff_zero :
    eisMinusOneConstant (p := p) =
      algebraMap ℤ (CoeffRing p)
        ((2 * (p - 1 : ℚ) / bernoulli (p - 1)).den : ℤ) := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hpodd : Odd p := (Nat.Prime.odd_iff
    (inferInstance : isLargePrime p).Prime).mpr (by omega)
  have hk : 3 ≤ (p : ℤ) - 1 := by
    have hp4 : (4 : ℤ) ≤ p := by exact_mod_cast (show 4 ≤ p by omega)
    omega
  obtain ⟨n, hn⟩ := hpodd
  have hEvenNat : Even (p - 1) := by
    refine ⟨n, ?_⟩
    omega
  have hEven : Even ((p : ℤ) - 1) := by
    refine ⟨(n : ℤ), ?_⟩
    rw [hn]
    push_cast
    ring
  have htoNat : ((p : ℤ) - 1).toNat = p - 1 := by omega
  rw [eisMinusOneConstant, PIntegralModularForm.coeff_Eis hk hEven 0]
  congr 2
  rw [htoNat]
  push_cast
  ring

private theorem eisPlusOne_coeff_zero :
    eisPlusOneConstant (p := p) =
      algebraMap ℤ (CoeffRing p)
        ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).den : ℤ) := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hpodd : Odd p := (Nat.Prime.odd_iff
    (inferInstance : isLargePrime p).Prime).mpr (by omega)
  have hk : 3 ≤ (p : ℤ) + 1 := by omega
  obtain ⟨n, hn⟩ := hpodd
  have hEvenNat : Even (p + 1) := by
    refine ⟨n + 1, ?_⟩
    omega
  have hEven : Even ((p : ℤ) + 1) := by
    refine ⟨((n + 1 : ℕ) : ℤ), ?_⟩
    rw [hn]
    push_cast
    ring
  have htoNat : ((p : ℤ) + 1).toNat = p + 1 := by omega
  rw [eisPlusOneConstant, PIntegralModularForm.coeff_Eis hk hEven 0]
  congr 2
  rw [htoNat]
  push_cast
  ring

/-- The constant terms of both Eisenstein series are units in `Z_(p)`. -/
theorem eisMinusOneConstant_isUnit : IsUnit (eisMinusOneConstant (p := p)) := by
  rw [eisMinusOne_coeff_zero]
  have hnot : ((2 * (p - 1 : ℚ) / bernoulli (p - 1)).den : ℤ) ∉ primeIdeal p := by
    intro hdiv
    have hdivInt : (p : ℤ) ∣
        ((2 * (p - 1 : ℚ) / bernoulli (p - 1)).den : ℤ) := by
      rw [← Ideal.mem_span_singleton]
      exact hdiv
    have hnat : p ∣ (2 * (p - 1 : ℚ) / bernoulli (p - 1)).den := by
      exact_mod_cast hdivInt
    exact IntegerModularForm.nldvd_bernoulli_den p hnat
  exact IsLocalization.map_units (M := (primeIdeal p).primeCompl) (CoeffRing p)
    ⟨_, hnot⟩

theorem eisPlusOneConstant_isUnit : IsUnit (eisPlusOneConstant (p := p)) := by
  rw [eisPlusOne_coeff_zero]
  have hnot : ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).den : ℤ) ∉ primeIdeal p := by
    intro hdiv
    have hdivInt : (p : ℤ) ∣
        ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).den : ℤ) := by
      rw [← Ideal.mem_span_singleton]
      exact hdiv
    have hnat : p ∣ (2 * (p + 1 : ℚ) / bernoulli (p + 1)).den := by
      exact_mod_cast hdivInt
    have hzero : (algebraMap ℤ (ZMod p)
        ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).den : ℤ)) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (Int.natCast_dvd.mpr hnat)
    have hconst : ThetaOperator.eisLPlusOneConstant (ℓ := p) =
        algebraMap ℤ (ZMod p)
          ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).den : ℤ) := by
      rw [ThetaOperator.eisLPlusOneConstant, ThetaOperator.eisLPlusOne]
      have hp5 := (inferInstance : isLargePrime p).AtLeastFive
      have hpodd : Odd p := (Nat.Prime.odd_iff
        (inferInstance : isLargePrime p).Prime).mpr (by omega)
      have hEven : Even ((p + 1 : ℤ)) := by exact_mod_cast hpodd.add_one
      rw [IntegerModularForm.coeff_Eis (by omega) hEven 0]
      simp
    have htheta0 : ThetaOperator.eisLPlusOneConstant (ℓ := p) = 0 := by
      rw [hconst, hzero]
    exact (ThetaOperator.eisLPlusOneConstant_ne_zero (ℓ := p)) htheta0
  exact IsLocalization.map_units (M := (primeIdeal p).primeCompl) (CoeffRing p)
    ⟨_, hnot⟩

/-- Constant-term-one Eisenstein forms, matching the normalization in the
thesis. -/
def normalizedEisMinusOne : PIntegralModularForm p ((p : ℤ) - 1) :=
  (((eisMinusOneConstant_isUnit (p := p)).unit⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) •
    PIntegralModularForm.Eis (p := p) ((p : ℤ) - 1)

def normalizedEisPlusOne : PIntegralModularForm p ((p : ℤ) + 1) :=
  (((eisPlusOneConstant_isUnit (p := p)).unit⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) •
    PIntegralModularForm.Eis (p := p) ((p : ℤ) + 1)

@[simp]
theorem normalizedEisMinusOne_coeff_zero :
    (normalizedEisMinusOne (p := p)).coeff 0 = 1 := by
  let u : (CoeffRing p)ˣ := (eisMinusOneConstant_isUnit (p := p)).unit
  have hval : (u : CoeffRing p) = eisMinusOneConstant (p := p) :=
    (eisMinusOneConstant_isUnit (p := p)).unit_spec
  change ((u⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) *
    eisMinusOneConstant (p := p) = 1
  calc
    _ = ((u⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) * (u : CoeffRing p) := by rw [hval]
    _ = 1 := Units.inv_mul u

@[simp]
theorem normalizedEisPlusOne_coeff_zero :
    (normalizedEisPlusOne (p := p)).coeff 0 = 1 := by
  let u : (CoeffRing p)ˣ := (eisPlusOneConstant_isUnit (p := p)).unit
  have hval : (u : CoeffRing p) = eisPlusOneConstant (p := p) :=
    (eisPlusOneConstant_isUnit (p := p)).unit_spec
  change ((u⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) *
    eisPlusOneConstant (p := p) = 1
  calc
    _ = ((u⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) * (u : CoeffRing p) := by rw [hval]
    _ = 1 := Units.inv_mul u

/-- The polynomial ring `F_p[X,Y]`. -/
abbrev ResiduePolynomial (p : ℕ) := MvPolynomial (Fin 2) (ZMod p)

/-- The polynomial `A` of Definition 1.38, representing `E_(p-1)`. -/
def A : PIntegralModularForm.E4E6Polynomial p :=
  PIntegralModularForm.polynomial
    (normalizedEisMinusOne (p := p))

/-- The polynomial `B` of Definition 1.38, representing `E_(p+1)`. -/
def B : PIntegralModularForm.E4E6Polynomial p :=
  PIntegralModularForm.polynomial
    (normalizedEisPlusOne (p := p))

/-- Evaluating `A` at the `E₄` and `E₆` Fourier expansions gives `E_(p-1)`. -/
theorem evaluate_A :
    PIntegralModularForm.evaluateE4E6 (p := p) (A (p := p)) =
      (normalizedEisMinusOne (p := p)).fourier := by
  exact PIntegralModularForm.evaluate_polynomial
    (normalizedEisMinusOne (p := p))

/-- Evaluating `B` at the `E₄` and `E₆` Fourier expansions gives `E_(p+1)`. -/
theorem evaluate_B :
    PIntegralModularForm.evaluateE4E6 (p := p) (B (p := p)) =
      (normalizedEisPlusOne (p := p)).fourier := by
  exact PIntegralModularForm.evaluate_polynomial
    (normalizedEisPlusOne (p := p))


/-- Reduction of a `p`-integral polynomial to `F_p[X,Y]`. -/
def reducePolynomial (P : PIntegralModularForm.E4E6Polynomial p) : ResiduePolynomial p :=
  MvPolynomial.map (PIntegralModularForm.coeffToZMod (p := p)) P

/-- The reductions `Ã` and `B̃` of the polynomials from Definition 1.38. -/
def Abar : ResiduePolynomial p := reducePolynomial (p := p) (A (p := p))

def Bbar : ResiduePolynomial p := reducePolynomial (p := p) (B (p := p))

/-- The mod-`p` polynomial derivation `∂X = -4Y`, `∂Y = -6X²`. -/
def polynomialDerivationMod :
    Derivation (ZMod p) (ResiduePolynomial p) (ResiduePolynomial p) :=
  (((MvPolynomial.C (-4 : ZMod p) : ResiduePolynomial p) *
        (MvPolynomial.X 1 : ResiduePolynomial p)) •
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 0) +
    (((MvPolynomial.C (-6 : ZMod p) : ResiduePolynomial p) *
        (MvPolynomial.X 0 : ResiduePolynomial p) ^ 2) •
      MvPolynomial.pderiv (R := ZMod p) (σ := Fin 2) 1)

/-- The linear map underlying the mod-`p` polynomial derivation. -/
def delPolynomialMod : ResiduePolynomial p →ₗ[ZMod p] ResiduePolynomial p :=
  (polynomialDerivationMod (p := p)).toLinearMap



/-- Evaluate a polynomial at the reductions of the `E₄` and `E₆` Fourier
series. -/
def evaluateResiduePolynomial : ResiduePolynomial p →+*
    PowerSeries (ZMod p) :=
  MvPolynomial.eval₂Hom (PowerSeries.C : ZMod p →+* PowerSeries (ZMod p))
    (fun i => if i = 0 then
      ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier
      else
      ((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier)

theorem evaluateResiduePolynomial_reducePolynomial
    (P : PIntegralModularForm.E4E6Polynomial p) :
    evaluateResiduePolynomial (p := p) (reducePolynomial (p := p) P) =
      PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
        (PIntegralModularForm.evaluateE4E6 (p := p) P) := by
  let ψ := PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
  have hcoeff :
      (PowerSeries.C : ZMod p →+* PowerSeries (ZMod p)).comp
          (PIntegralModularForm.coeffToZMod (p := p)) =
        ψ.comp (PowerSeries.C : CoeffRing p →+* PowerSeries (CoeffRing p)) := by
    ext a
    simp [ψ]
  have hvars :
      (fun i : Fin 2 => if i = 0 then
        ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier else
        ((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier) =
      (fun i : Fin 2 => ψ (if i = 0 then
        (PIntegralModularForm.Eis (p := p) 4).fourier else
        (PIntegralModularForm.Eis (p := p) 6).fourier)) := by
    funext i
    fin_cases i <;> simp [ψ, PIntegralModularForm.fourier_Reduce]
  dsimp only [evaluateResiduePolynomial, reducePolynomial,
    PIntegralModularForm.evaluateE4E6,
    PIntegralModularForm.evaluateE4E6Hom]
  rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
  rw [hcoeff, hvars]

private theorem eisMinusOne_coeffToZMod_succ_zero (n : ℕ) :
    PIntegralModularForm.coeffToZMod (p := p)
      ((PIntegralModularForm.Eis (p := p) ((p : ℤ) - 1)).coeff (n + 1)) = 0 := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hpPrime := (inferInstance : isLargePrime p).Prime
  have hpodd : Odd p := (Nat.Prime.odd_iff hpPrime).mpr (by omega)
  obtain ⟨m, hm⟩ := hpodd
  have hk : 3 ≤ (p : ℤ) - 1 := by
    have hp4 : (4 : ℤ) ≤ p := by exact_mod_cast (show 4 ≤ p by omega)
    omega
  have hEven : Even ((p : ℤ) - 1) := by
    refine ⟨(m : ℤ), ?_⟩
    rw [hm]
    push_cast
    ring
  have htoNat : ((p : ℤ) - 1).toNat = p - 1 := by omega
  rw [PIntegralModularForm.coeff_Eis hk hEven (n + 1)]
  rw [PIntegralModularForm.coeffToZMod_algebraMap]
  simp only [if_neg (Nat.succ_ne_zero n)]
  let qn : ℚ := 2 * (p - 1 : ℚ) / bernoulli (p - 1)
  have hnumNat : p ∣ qn.num.natAbs := by
    have hldvd := ldvd_bernoulli_num p hpPrime hp5
    have hldvd' : qn.num ≡ 0 [ZMOD p] := by
      simpa [qn, Nat.cast_sub (by omega : 1 ≤ p)] using hldvd
    rw [← Int.natCast_dvd, ← Int.modEq_zero_iff_dvd]
    exact hldvd'
  have hnumInt : (p : ℤ) ∣ qn.num := by
    apply Int.dvd_natAbs.mp
    exact Int.natCast_dvd_natCast.mpr hnumNat
  have hnum : (qn.num : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hnumInt
  rw [htoNat]
  simp [qn, hnum]

private theorem normalizedEisMinusOne_reduce :
    PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      (normalizedEisMinusOne (p := p)).fourier = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_map]
      simp [normalizedEisMinusOne_coeff_zero]
  | succ n =>
      rw [PowerSeries.coeff_map]
      simp only [PowerSeries.coeff_one, Nat.succ_ne_zero]
      change PIntegralModularForm.coeffToZMod (p := p)
        (PowerSeries.coeff (n + 1)
          ((((eisMinusOneConstant_isUnit (p := p)).unit⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) •
            (PIntegralModularForm.Eis (p := p) ((p : ℤ) - 1)).fourier)) = 0
      rw [PowerSeries.smul_eq_C_mul, PowerSeries.coeff_C_mul, map_mul]
      have hzero := eisMinusOne_coeffToZMod_succ_zero (p := p) n
      have hzero' : PIntegralModularForm.coeffToZMod (p := p)
          (PowerSeries.coeff (n + 1)
            (PIntegralModularForm.Eis (p := p) ((p : ℤ) - 1)).fourier) = 0 := by
        exact hzero
      rw [hzero']
      simp

/-- Evaluating the reduction of the Hasse polynomial at the reduced Eisenstein
series gives the constant power series `1`. -/
theorem evaluate_Abar :
    evaluateResiduePolynomial (p := p) (Abar (p := p)) = 1 := by
  rw [Abar, evaluateResiduePolynomial_reducePolynomial,
    evaluate_A, normalizedEisMinusOne_reduce]

private theorem eisPlusOneConstant_toZMod :
    PIntegralModularForm.coeffToZMod (p := p) (eisPlusOneConstant (p := p)) =
      ThetaOperator.eisLPlusOneConstant (ℓ := p) := by
  rw [eisPlusOne_coeff_zero, PIntegralModularForm.coeffToZMod_algebraMap]
  unfold ThetaOperator.eisLPlusOneConstant ThetaOperator.eisLPlusOne
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hpPrime := (inferInstance : isLargePrime p).Prime
  have hpodd : Odd p := (Nat.Prime.odd_iff hpPrime).mpr (by omega)
  have hk : 3 ≤ (p : ℤ) + 1 := by omega
  have hEven : Even ((p : ℤ) + 1) := by
    obtain ⟨m, hm⟩ := hpodd
    refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
    rw [hm]
    push_cast
    ring
  have htoNat : ((p : ℤ) + 1).toNat = p + 1 := by omega
  rw [IntegerModularForm.coeff_Eis hk hEven 0]
  simp [htoNat]

private theorem eisPlusOneUnit_inv_toZMod :
    PIntegralModularForm.coeffToZMod (p := p)
      ((((eisPlusOneConstant_isUnit (p := p)).unit⁻¹ : (CoeffRing p)ˣ) : CoeffRing p)) =
      (ThetaOperator.eisLPlusOneConstant (ℓ := p))⁻¹ := by
  let u : (CoeffRing p)ˣ := (eisPlusOneConstant_isUnit (p := p)).unit
  have hu : PIntegralModularForm.coeffToZMod (p := p) (u : CoeffRing p) =
      ThetaOperator.eisLPlusOneConstant (ℓ := p) := by
    calc
      _ = PIntegralModularForm.coeffToZMod (p := p) (eisPlusOneConstant (p := p)) := by
        rw [(eisPlusOneConstant_isUnit (p := p)).unit_spec]
      _ = _ := eisPlusOneConstant_toZMod (p := p)
  have hmul := congrArg (PIntegralModularForm.coeffToZMod (p := p)) (Units.inv_mul u)
  have hmul' :
      PIntegralModularForm.coeffToZMod (p := p)
          (((u⁻¹ : (CoeffRing p)ˣ) : CoeffRing p)) *
        ThetaOperator.eisLPlusOneConstant (ℓ := p) = 1 := by
    simpa only [map_mul, map_one, hu] using hmul
  have hconstne : ThetaOperator.eisLPlusOneConstant (ℓ := p) ≠ 0 :=
    ThetaOperator.eisLPlusOneConstant_ne_zero (ℓ := p)
  have hunitInvEq :
      (eisPlusOneConstant_isUnit (p := p)).unit⁻¹ = u⁻¹ := rfl
  have hmapInvEq := congrArg (fun v : (CoeffRing p)ˣ =>
    PIntegralModularForm.coeffToZMod (p := p) (v : CoeffRing p)) hunitInvEq
  calc
    _ = (PIntegralModularForm.coeffToZMod (p := p)
          (((u⁻¹ : (CoeffRing p)ˣ) : CoeffRing p)) *
        ThetaOperator.eisLPlusOneConstant (ℓ := p)) *
          (ThetaOperator.eisLPlusOneConstant (ℓ := p))⁻¹ := by
            rw [hmapInvEq]
            field_simp [hconstne]
    _ = (ThetaOperator.eisLPlusOneConstant (ℓ := p))⁻¹ := by
      simpa [u] using congrArg (fun z : ZMod p =>
        z * (ThetaOperator.eisLPlusOneConstant (ℓ := p))⁻¹) hmul'

private theorem powerSeries_map_smul {R S : Type*} [CommSemiring R]
    [CommSemiring S] (φ : R →+* S) (a : R) (F : PowerSeries R) :
    PowerSeries.map φ (a • F) = φ a • PowerSeries.map φ F := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_smul]

private theorem map_eisPlusOne_fourier :
    PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      (PIntegralModularForm.Eis (p := p) ((p : ℤ) + 1)).fourier =
        (IntegerModularForm.Eis (p + 1)).reduce p := by
  apply PowerSeries.ext
  intro n
  simp [PIntegralModularForm.Eis, PIntegralModularForm.ofInteger,
    PowerSeries.coeff_map, PIntegralModularForm.coeffToZMod_algebraMap,
    IntegerModularForm.reduce_apply]

theorem normalizedEisPlusOne_reduce :
    PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      (normalizedEisPlusOne (p := p)).fourier =
        (ThetaOperator.E₂ (ℓ := p)).fourier := by
  rw [normalizedEisPlusOne]
  change PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      ((((eisPlusOneConstant_isUnit (p := p)).unit⁻¹ : (CoeffRing p)ˣ) : CoeffRing p) •
        (PIntegralModularForm.Eis (p := p) ((p : ℤ) + 1)).fourier) = _
  rw [powerSeries_map_smul, eisPlusOneUnit_inv_toZMod,
    map_eisPlusOne_fourier]
  simpa [ThetaOperator.eisLPlusOne] using
    (ThetaOperator.eisLPlusOne_reduce_fourier (ℓ := p)).symm

private theorem E₂_fourier_eq_e2Fourier :
    (ThetaOperator.E₂ (ℓ := p)).fourier =
      PowerSeries.map (Int.castRingHom (ZMod p))
        ThetaOperator.DelOperator.e2Fourier := by
  apply PowerSeries.ext
  intro n
  change (ThetaOperator.E₂ (ℓ := p)).coeff n = _
  rw [ThetaOperator.coeff_E₂]
  simp [ThetaOperator.DelOperator.e2Fourier]

private lemma e2Periodic_local :
    Function.Periodic
      (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + (1 : ℂ)).im := by simpa using hw
    let z : UpperHalfPlane := UpperHalfPlane.ofComplex w
    have hT := congr_fun EisensteinSeries.G2_T_transform z
    have hE : EisensteinSeries.E2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.E2 z := by
      simp_rw [ModularForm.SL_slash_def, modular_T_smul] at hT
      have hG : EisensteinSeries.G2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.G2 z := by
        have hden : denom
            (Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T))
            (z : ℂ) = 1 := by
          rw [ModularGroup.denom_apply]
          simp [ModularGroup.T]
        rw [hden] at hT
        simpa using hT
      simp [EisensteinSeries.E2, hG]
    have hzv : (1 : ℝ) +ᵥ z = UpperHalfPlane.ofComplex (w + 1) := by
      apply UpperHalfPlane.ext
      simp [z, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
        UpperHalfPlane.ofComplex_apply_of_im_pos hw']
      ring
    rw [hzv] at hE
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw', z, UpperHalfPlane.coe_vadd] using hE
  · have hwle : w.im ≤ 0 := le_of_not_gt hw
    have hw' : (w + (1 : ℂ)).im ≤ 0 := by simpa using hwle
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hwle,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw']

private theorem eisensteinFour_qExpansion :
    UpperHalfPlane.qExpansion 1
        (ModularForm.E (show 3 ≤ (4 : ℕ) by norm_num)) =
      PowerSeries.map (Int.castRingHom ℂ)
        (IntegerModularForm.Eis (4 : ℤ)).fourier := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map,
    EisensteinSeries.E_qExpansion_coeff (by norm_num) (by norm_num)]
  change (if n = 0 then 1 else
      -(2 * (4 : ℕ) / bernoulli 4 : ℂ) * ArithmeticFunction.sigma 3 n) =
    ((IntegerModularForm.Eis (4 : ℤ)).coeff n : ℂ)
  rw [IntegerModularForm.coeff_Eis_four]
  have hB : bernoulli 4 = -(1 : ℚ) / 30 := by decide +kernel
  by_cases hn : n = 0 <;> simp [hn, hB] <;> norm_num

private theorem e2_normalizedDeriv_eq_q_mul_deriv
    (z : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z =
      Function.Periodic.qParam 1 (z : ℂ) *
        deriv (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2)
          (Function.Periodic.qParam 1 (z : ℂ)) := by
  have hq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  have hFq : DifferentiableAt ℂ
      (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2)
      (Function.Periodic.qParam 1 (z : ℂ)) :=
    UpperHalfPlane.differentiableAt_cuspFunction one_pos e2Periodic_local
      E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2 hq
  have hlin : HasDerivAt (fun w : ℂ ↦ 2 * π * Complex.I * w)
      (2 * π * Complex.I) (z : ℂ) := by
    simpa [id] using
      (hasDerivAt_id (z : ℂ)).const_mul (2 * π * Complex.I)
  have hqderiv : HasDerivAt
      (fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w))
      (Function.Periodic.qParam 1 (z : ℂ) * (2 * π * Complex.I)) (z : ℂ) := by
    simpa [Function.comp_def, Function.Periodic.qParam] using
      (Complex.hasDerivAt_exp _).comp _ hlin
  have hqfun : (Function.Periodic.qParam 1 : ℂ → ℂ) =
      (fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w)) := by
    funext w
    simp [Function.Periodic.qParam]
  have hqderiv' : HasDerivAt (Function.Periodic.qParam 1)
      (Function.Periodic.qParam 1 (z : ℂ) * (2 * π * Complex.I)) (z : ℂ) := by
    simpa only [hqfun] using hqderiv
  have hcomp := hFq.hasDerivAt.comp _ hqderiv'
  have heq0 : (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (z : ℂ)]
      ((UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) ∘
        Function.Periodic.qParam 1) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simpa [Function.comp_def, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using
      (UpperHalfPlane.eq_cuspFunction ⟨w, hw⟩ one_ne_zero e2Periodic_local).symm
  have hcomp' := hcomp.congr_of_eventuallyEq heq0
  rw [Derivative.normalizedDerivOfComplex, hcomp'.deriv]
  simp only [Function.Periodic.qParam]
  field_simp

private theorem e2_normalizedDeriv_periodic :
    Function.Periodic
      (Derivative.normalizedDerivOfComplex EisensteinSeries.E2 ∘
        UpperHalfPlane.ofComplex) (1 : ℝ) := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + (1 : ℂ)).im := by simpa using hw
    let z : UpperHalfPlane := UpperHalfPlane.ofComplex w
    have hT := congr_fun EisensteinSeries.G2_T_transform z
    have hE : EisensteinSeries.E2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.E2 z := by
      simp_rw [ModularForm.SL_slash_def, modular_T_smul] at hT
      have hG : EisensteinSeries.G2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.G2 z := by
        have hden : denom
            (Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T))
            (z : ℂ) = 1 := by
          rw [ModularGroup.denom_apply]
          simp [ModularGroup.T]
        rw [hden] at hT
        simpa using hT
      simp [EisensteinSeries.E2, hG]
    have hzv : (1 : ℝ) +ᵥ z = UpperHalfPlane.ofComplex (w + 1) := by
      apply UpperHalfPlane.ext
      simp [z, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
        UpperHalfPlane.ofComplex_apply_of_im_pos hw']
      ring
    rw [hzv] at hE
    have hper : Function.Periodic
        (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := e2Periodic_local
    let g : ℂ → ℂ := EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex
    have hgper : Function.Periodic g (1 : ℝ) := hper
    have hgw : DifferentiableAt ℂ g w := by
      dsimp [g]
      have hloc := UpperHalfPlane.mdifferentiableAt_iff.mp
        (E2_mdifferentiable (UpperHalfPlane.ofComplex w))
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw] at hloc
      simpa [Function.comp_def] using hloc
    have hgw' : DifferentiableAt ℂ g (w + (1 : ℂ)) := by
      dsimp [g]
      have hloc := UpperHalfPlane.mdifferentiableAt_iff.mp
        (E2_mdifferentiable (UpperHalfPlane.ofComplex (w + 1)))
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw'] at hloc
      simpa [Function.comp_def] using hloc
    have hcomp := (hgw'.hasDerivAt).comp w
      ((hasDerivAt_id w).add_const (1 : ℂ))
    have heq : g =ᶠ[𝓝 w] g ∘ (fun x : ℂ ↦ x + (1 : ℂ)) :=
      Filter.Eventually.of_forall (fun x ↦ (hgper x).symm)
    have hder := hcomp.congr_of_eventuallyEq heq
    have hd : deriv g w = deriv g (w + (1 : ℂ)) := by
      simpa [Function.comp_def] using hder.deriv
    simpa [Derivative.normalizedDerivOfComplex, Function.comp_def,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw', g] using hd.symm
  · have hwle : w.im ≤ 0 := le_of_not_gt hw
    have hw' : (w + (1 : ℂ)).im ≤ 0 := by simpa using hwle
    simp [Function.comp_apply, Derivative.normalizedDerivOfComplex,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hwle,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw']

private theorem iteratedDeriv_q_mul_deriv_local (F : ℂ → ℂ)
    (hF : AnalyticAt ℂ F 0) (n : ℕ) :
    iteratedDeriv n (fun q : ℂ ↦ q * deriv F q) 0 =
      n * iteratedDeriv n F 0 := by
  cases n with
  | zero => simp
  | succ n =>
      change iteratedDeriv (n + 1) ((fun q : ℂ ↦ q) * deriv F) 0 = _
      rw [iteratedDeriv_mul (f := fun q : ℂ ↦ q) (g := deriv F)
        (by fun_prop) hF.deriv.contDiffAt]
      rw [Finset.sum_eq_single 1]
      · simp [iteratedDeriv_fun_id, iteratedDeriv_succ']
      · intro b hb hb1
        simp [iteratedDeriv_fun_id, hb1]
      · simp

private theorem e2_qExpansion_normalizedDeriv :
    UpperHalfPlane.qExpansion 1
        (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) =
      PowerSeries.X * PowerSeries.derivative
        (UpperHalfPlane.qExpansion 1 EisensteinSeries.E2) := by
  let F : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2
  have hFani : AnalyticAt ℂ F 0 := by
    exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos e2Periodic_local
      E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2
  have hprod : Tendsto (fun q : ℂ ↦ q * deriv F q) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.mul hFani.deriv.continuousAt.tendsto)
  have hDper := e2_normalizedDeriv_periodic
  have hDmdiff := Derivative.normalizedDerivOfComplex_mdifferentiable
    E2_mdifferentiable
  have hDzero : IsZeroAtImInfty
      (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) := by
    rw [IsZeroAtImInfty, ZeroAtFilter]
    rw [show Derivative.normalizedDerivOfComplex EisensteinSeries.E2 =
        (fun z : UpperHalfPlane ↦
          Function.Periodic.qParam 1 (z : ℂ) * deriv F
            (Function.Periodic.qParam 1 (z : ℂ))) from
      funext e2_normalizedDeriv_eq_q_mul_deriv]
    exact hprod.comp (qParam_tendsto_atImInfty one_pos)
  have hDbdd : IsBoundedAtImInfty
      (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) := by
    rw [show Derivative.normalizedDerivOfComplex EisensteinSeries.E2 =
        (fun z : UpperHalfPlane ↦
          Function.Periodic.qParam 1 (z : ℂ) * deriv F
            (Function.Periodic.qParam 1 (z : ℂ))) from
      funext e2_normalizedDeriv_eq_q_mul_deriv]
    exact (hprod.comp (qParam_tendsto_atImInfty one_pos)).isBigO_one
      (F := ℝ)
  have hDani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1
        (Derivative.normalizedDerivOfComplex EisensteinSeries.E2)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hDper hDmdiff
      hDbdd
  have hD0 : UpperHalfPlane.cuspFunction 1
      (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) 0 = 0 := by
    rw [UpperHalfPlane.cuspFunction_apply_zero one_pos hDani hDper]
    exact hDzero.valueAtInfty_eq_zero
  have hcf : UpperHalfPlane.cuspFunction 1
      (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) =ᶠ[𝓝 0]
        (fun q : ℂ ↦ q * deriv F q) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    by_cases hq0 : q = 0
    · subst q
      simp [hD0]
    · have hnorm : ‖q‖ < 1 := by
        simpa [Metric.mem_ball] using hq
      have him : 0 < (Function.Periodic.invQParam 1 q).im :=
        Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hnorm hq0
      rw [UpperHalfPlane.cuspFunction,
        Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq0]
      simpa [F, UpperHalfPlane.ofComplex_apply_of_im_pos him,
        Function.Periodic.qParam_right_inv one_pos.ne' hq0] using
        e2_normalizedDeriv_eq_q_mul_deriv (UpperHalfPlane.ofComplex
          (Function.Periodic.invQParam 1 q))
  apply PowerSeries.ext
  intro n
  rw [UpperHalfPlane.qExpansion_coeff]
  rw [hcf.iteratedDeriv_eq n]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
      rw [iteratedDeriv_q_mul_deriv_local F hFani]
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        UpperHalfPlane.qExpansion_coeff]
      simp [Nat.factorial_succ]
      ring

private theorem e2RamanujanFourier_eq_neg_Eis_four :
    ThetaOperator.DelOperator.e2RamanujanFourier =
      -(IntegerModularForm.Eis 4).fourier := by
  have hE2ani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos e2Periodic_local
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hE2sqani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (EisensteinSeries.E2 ^ 2)) 0 := by
    rw [pow_two, UpperHalfPlane.cuspFunction_mul hE2ani.continuousAt
      hE2ani.continuousAt]
    exact hE2ani.mul hE2ani
  have hE4ani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1
        (ModularForm.E (show 3 ≤ (4 : ℕ) by norm_num))) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero
      (ModularForm.E (show 3 ≤ (4 : ℕ) by norm_num)) one_pos
      one_mem_strictPeriods_SL
  have hsubani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1
        (EisensteinSeries.E2 ^ 2 -
          ModularForm.E (show 3 ≤ (4 : ℕ) by norm_num))) 0 := by
    rw [UpperHalfPlane.cuspFunction_sub hE2sqani.continuousAt
      hE4ani.continuousAt]
    exact hE2sqani.sub hE4ani
  have hformula := congrArg (UpperHalfPlane.qExpansion 1)
    Derivative.normalizedDerivOfComplex_E₂
  rw [e2_qExpansion_normalizedDeriv,
    UpperHalfPlane.qExpansion_smul hsubani,
    UpperHalfPlane.qExpansion_sub hE2sqani hE4ani] at hformula
  rw [pow_two, UpperHalfPlane.qExpansion_mul hE2ani hE2ani,
    ThetaOperator.DelOperator.qexp_e2, eisensteinFour_qExpansion] at hformula
  let M : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ)
    ThetaOperator.DelOperator.e2Fourier
  have hformula' : PowerSeries.X * PowerSeries.derivative M =
      (12⁻¹ : ℂ) •
        (M ^ 2 - PowerSeries.map (Int.castRingHom ℂ)
          (IntegerModularForm.Eis 4).fourier) := by
    simpa [M, pow_two] using hformula
  have hmapD : PowerSeries.map (Int.castRingHom ℂ)
      (PowerSeries.derivative ThetaOperator.DelOperator.e2Fourier) =
        PowerSeries.derivative M := by
    ext n
    simp [M, PowerSeries.coeff_derivative, PowerSeries.coeff_map]
  have hcomplex : PowerSeries.map (Int.castRingHom ℂ)
      ThetaOperator.DelOperator.e2RamanujanFourier =
        -PowerSeries.map (Int.castRingHom ℂ)
          (IntegerModularForm.Eis 4).fourier := by
    calc
      _ = (12 : ℕ) • (PowerSeries.X * PowerSeries.derivative M) - M * M := by
        simp only [ThetaOperator.DelOperator.e2RamanujanFourier,
          map_sub, map_nsmul, map_mul, PowerSeries.map_X]
        rw [hmapD]
      _ = -PowerSeries.map (Int.castRingHom ℂ)
          (IntegerModularForm.Eis 4).fourier := by
        have hnat : (12 : ℕ) • (PowerSeries.X * PowerSeries.derivative M) =
            (12 : ℂ) • (PowerSeries.X * PowerSeries.derivative M) := by
          exact (Nat.cast_smul_eq_nsmul (R := ℂ) 12 _).symm
        rw [hnat, hformula']
        simp only [smul_smul]
        norm_num
        ring
  exact PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
    (by simpa only [map_neg] using hcomplex)

private theorem powerSeries_map_derivative {R S : Type*} [CommSemiring R]
    [CommSemiring S] (φ : R →+* S) (F : PowerSeries R) :
    PowerSeries.map φ (PowerSeries.derivative F) =
      PowerSeries.derivative (PowerSeries.map φ F) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]

private theorem pE2Fourier_reduce :
    PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      (PIntegralModularForm.pE2Fourier (p := p)) =
      PowerSeries.map (Int.castRingHom (ZMod p))
        ThetaOperator.DelOperator.e2Fourier := by
  apply PowerSeries.ext
  intro n
  simp [PIntegralModularForm.pE2Fourier, PowerSeries.coeff_map,
    PIntegralModularForm.coeffToZMod_algebraMap]

private theorem map_Eis_four_reduce (k : ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod p))
        (IntegerModularForm.Eis k).fourier =
      ((PIntegralModularForm.Eis (p := p) k).Reduce).fourier := by
  rw [PIntegralModularForm.fourier_Reduce]
  apply PowerSeries.ext
  intro n
  simp [PIntegralModularForm.Eis, PIntegralModularForm.ofInteger,
    PowerSeries.coeff_map, PIntegralModularForm.coeffToZMod_algebraMap]

private theorem normalizedEisPlusOne_del_reduce :
    PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
        (PIntegralModularForm.del (normalizedEisPlusOne (p := p))).fourier =
      -((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier := by
  have hM : PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      (normalizedEisPlusOne (p := p)).fourier =
        PowerSeries.map (Int.castRingHom (ZMod p))
          ThetaOperator.DelOperator.e2Fourier := by
    rw [normalizedEisPlusOne_reduce, E₂_fourier_eq_e2Fourier]
  rw [PIntegralModularForm.del_fourier, PIntegralModularForm.fourierDel]
  simp only [map_sub, map_nsmul, map_zsmul, map_mul, PowerSeries.map_X,
    powerSeries_map_derivative]
  rw [hM, pE2Fourier_reduce]
  rw [← Int.cast_smul_eq_zsmul (R := ZMod p) ((p : ℤ) + 1)
    (PowerSeries.map (Int.castRingHom (ZMod p))
      ThetaOperator.DelOperator.e2Fourier *
      PowerSeries.map (Int.castRingHom (ZMod p))
        ThetaOperator.DelOperator.e2Fourier)]
  have hcast : (((p : ℤ) + 1 : ℤ) : ZMod p) = 1 := by
    norm_cast
    simp
  rw [hcast]
  rw [← map_Eis_four_reduce (p := p) 4]
  have hram := congrArg (PowerSeries.map (Int.castRingHom (ZMod p)))
    e2RamanujanFourier_eq_neg_Eis_four
  have hram' : PowerSeries.map (Int.castRingHom (ZMod p))
      ThetaOperator.DelOperator.e2RamanujanFourier =
        -PowerSeries.map (Int.castRingHom (ZMod p))
          (IntegerModularForm.Eis 4).fourier := by
    simpa [ThetaOperator.DelOperator.e2RamanujanFourier,
      powerSeries_map_derivative] using hram
  have h12 : PowerSeries.map (Int.castRingHom (ZMod p))
      (12 : PowerSeries ℤ) = (12 : PowerSeries (ZMod p)) := by
    exact map_natCast (PowerSeries.map (Int.castRingHom (ZMod p))) 12
  simpa [ThetaOperator.DelOperator.e2RamanujanFourier,
    powerSeries_map_derivative, PowerSeries.map_X, h12,
    nsmul_eq_mul] using hram'

private theorem normalizedEisMinusOne_del_reduce :
    PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      ((PIntegralModularForm.del (normalizedEisMinusOne (p := p))).fourier) =
      (ThetaOperator.E₂ (ℓ := p)).fourier := by
  rw [PIntegralModularForm.del_fourier, PIntegralModularForm.fourierDel]
  simp only [map_sub, map_nsmul, map_zsmul, map_mul, PowerSeries.map_X,
    powerSeries_map_derivative, pE2Fourier_reduce]
  rw [normalizedEisMinusOne_reduce, ← E₂_fourier_eq_e2Fourier]
  simp only [PowerSeries.derivative_one, mul_zero, smul_zero, zero_sub, mul_one]
  have hcast : (((p : ℤ) - 1 : ℤ) : ZMod p) = -1 := by
    norm_cast
    simp
  rw [← Int.cast_smul_eq_zsmul (R := ZMod p) ((p : ℤ) - 1)
    (ThetaOperator.E₂ (ℓ := p)).fourier]
  rw [hcast]
  simp

private theorem reduced_del_B_eval :
    evaluateResiduePolynomial (p := p)
        (reducePolynomial (p := p) (delPolynomial (p := p) (B (p := p)))) =
      evaluateResiduePolynomial (p := p)
        (reducePolynomial (p := p)
          (-((MvPolynomial.X (0 : Fin 2) : PIntegralModularForm.E4E6Polynomial p) *
            A (p := p)))) := by
  have hB : delPolynomial (p := p) (B (p := p)) =
      PIntegralModularForm.polynomial (p := p)
        (PIntegralModularForm.del (normalizedEisPlusOne (p := p))) := by
    simpa [B] using
      (PIntegralModularForm.del_polynomial_compatible
        (p := p) (f := normalizedEisPlusOne (p := p)))
  have hX : evaluateResiduePolynomial (p := p)
      (MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) =
        ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier := by
    simp [evaluateResiduePolynomial]
  have hA : evaluateResiduePolynomial (p := p) (Abar (p := p)) = 1 := by
    rw [Abar, evaluateResiduePolynomial_reducePolynomial,
      evaluate_A, normalizedEisMinusOne_reduce]
  have hred : reducePolynomial (p := p)
      (-((MvPolynomial.X (0 : Fin 2) : PIntegralModularForm.E4E6Polynomial p) *
        A (p := p))) =
      -((MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) * Abar (p := p)) := by
    simp [reducePolynomial, Abar]
  have htarget : evaluateResiduePolynomial (p := p)
      (reducePolynomial (p := p)
        (-((MvPolynomial.X (0 : Fin 2) : PIntegralModularForm.E4E6Polynomial p) *
          A (p := p)))) =
      -((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier := by
    rw [hred]
    simp only [map_neg, map_mul]
    rw [hX, hA]
    simp
  calc
    _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
        (PIntegralModularForm.evaluateE4E6 (p := p)
          (PIntegralModularForm.polynomial (p := p)
            (PIntegralModularForm.del (normalizedEisPlusOne (p := p))))) := by
          rw [hB, evaluateResiduePolynomial_reducePolynomial]
    _ = -((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier := by
          rw [PIntegralModularForm.evaluate_polynomial,
            normalizedEisPlusOne_del_reduce]
    _ = evaluateResiduePolynomial (p := p)
        (reducePolynomial (p := p)
          (-((MvPolynomial.X (0 : Fin 2) : PIntegralModularForm.E4E6Polynomial p) *
            A (p := p)))) := htarget.symm

private theorem reduced_del_A_eval :
    evaluateResiduePolynomial (p := p)
        (reducePolynomial (p := p) (delPolynomial (p := p) (A (p := p)))) =
      evaluateResiduePolynomial (p := p) (Bbar (p := p)) := by
  have hA : delPolynomial (p := p) (A (p := p)) =
      PIntegralModularForm.polynomial (p := p)
        (PIntegralModularForm.del (normalizedEisMinusOne (p := p))) := by
    simpa [A] using
      (PIntegralModularForm.del_polynomial_compatible
        (p := p) (f := normalizedEisMinusOne (p := p)))
  rw [hA]
  change evaluateResiduePolynomial (p := p)
      (reducePolynomial (p := p) (PIntegralModularForm.polynomial
        (PIntegralModularForm.del (normalizedEisMinusOne (p := p))))) =
    evaluateResiduePolynomial (p := p)
      (reducePolynomial (p := p) (PIntegralModularForm.polynomial
        (normalizedEisPlusOne (p := p))))
  rw [evaluateResiduePolynomial_reducePolynomial,
    PIntegralModularForm.evaluate_polynomial,
    evaluateResiduePolynomial_reducePolynomial,
    PIntegralModularForm.evaluate_polynomial,
    normalizedEisMinusOne_del_reduce, normalizedEisPlusOne_reduce]

private def gCoeffMatrix (k : ℤ) :
    Matrix (Fin (dim k)) (Fin (dim k))
      (PIntegralModularForm.CoeffRing p) :=
  fun n i => (PIntegralModularForm.G (p := p) i).coeff n

private def pBasisCoeffMatrix (k : ℤ) :
    Matrix (Fin (dim k)) (Fin (dim k))
      (PIntegralModularForm.CoeffRing p) :=
  fun n i => (PIntegralModularForm.PBasis (p := p) k i).coeff n

private theorem pBasisCoeffMatrix_eq (k : ℤ) :
    pBasisCoeffMatrix (p := p) k =
      gCoeffMatrix (p := p) k * PIntegralModularForm.pBasisMatrix (p := p) k := by
  ext n i
  simp [pBasisCoeffMatrix, gCoeffMatrix,
    PIntegralModularForm.PBasis_apply_eq_change,
    PIntegralModularForm.coeff_sum, PIntegralModularForm.coeff_smul,
    Matrix.mul_apply, mul_comm]

private theorem gCoeffMatrix_det_isUnit (k : ℤ) :
    IsUnit (gCoeffMatrix (p := p) k).det := by
  have htri : (gCoeffMatrix (p := p) k).IsLowerTriangular := by
    intro i j hij
    exact PIntegralModularForm.coeff_G_lt hij
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp [gCoeffMatrix, PIntegralModularForm.coeff_G_diagonal]

private theorem pBasisCoeffMatrix_det_isUnit (k : ℤ) :
    IsUnit (pBasisCoeffMatrix (p := p) k).det := by
  rw [pBasisCoeffMatrix_eq, Matrix.det_mul]
  exact (gCoeffMatrix_det_isUnit (p := p) k).mul
    (PIntegralModularForm.pBasisMatrix_isUnit_det (p := p) k)

private def reducedPBasisCoeffMatrix (k : ℤ) :
    Matrix (Fin (dim k)) (Fin (dim k))
      (ZMod p) :=
  (PIntegralModularForm.coeffToZMod (p := p)).mapMatrix
    (pBasisCoeffMatrix (p := p) k)

private theorem reducedPBasisCoeffMatrix_det_isUnit (k : ℤ) :
    IsUnit (reducedPBasisCoeffMatrix (p := p) k).det := by
  rw [reducedPBasisCoeffMatrix, ← RingHom.map_det]
  exact (pBasisCoeffMatrix_det_isUnit (p := p) k).map
    (PIntegralModularForm.coeffToZMod (p := p))

private theorem reducedPBasis_fourier_linearIndependent {k : ℤ}
    (c : Fin (dim k) → ZMod p)
    (h : ∑ i : Fin (dim k),
        c i • PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
          (PIntegralModularForm.PBasis (p := p) k i).fourier = 0) :
    c = 0 := by
  let M := reducedPBasisCoeffMatrix (p := p) k
  have hdet : M.det ≠ 0 :=
    (reducedPBasisCoeffMatrix_det_isUnit (p := p) k).ne_zero
  have hmul : Matrix.mulVec M c = 0 := by
    funext n
    have hn := congrArg (fun F : PowerSeries (ZMod p) => F.coeff n) h
    simpa [M, reducedPBasisCoeffMatrix, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, PowerSeries.coeff_map, PowerSeries.smul_eq_C_mul,
      PowerSeries.coeff_C_mul, pBasisCoeffMatrix, mul_comm] using hn
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hmul

variable {k : ℤ}

private theorem fourier_sum_forms {α : Type*} (s : Finset α)
    (f : α → PIntegralModularForm p k) :
    (∑ a ∈ s, f a).fourier = ∑ a ∈ s, (f a).fourier := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private theorem fourier_smul_form (a : CoeffRing p)
    (f : PIntegralModularForm p k) : (a • f).fourier = a • f.fourier := rfl

private theorem map_fourier_basis_expansion (f : PIntegralModularForm p k) :
    PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p)) f.fourier =
      ∑ i : Fin (dim k),
        PIntegralModularForm.coeffToZMod (p := p)
          ((PIntegralModularForm.PBasis (p := p) k).repr f i) •
          PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
            (PIntegralModularForm.PBasis (p := p) k i).fourier := by
  have hrepr := congrArg (fun g : PIntegralModularForm p k => g.fourier)
    ((PIntegralModularForm.PBasis (p := p) k).sum_repr f)
  simp only [fourier_sum_forms, fourier_smul_form] at hrepr
  rw [← hrepr, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact powerSeries_map_smul (PIntegralModularForm.coeffToZMod (p := p))
    ((PIntegralModularForm.PBasis (p := p) k).repr f i)
    (PIntegralModularForm.PBasis (p := p) k i).fourier

private theorem repr_formOfCoordinates_local
    (c : Fin (dim k) → CoeffRing p) (i : Fin (dim k)) :
    (PIntegralModularForm.PBasis (p := p) k).repr
      (PIntegralModularForm.formOfCoordinates (p := p) c) i = c i := by
  change (PIntegralModularForm.PBasis (p := p) k).repr
    (∑ j : Fin (dim k), c j • PIntegralModularForm.PBasis (p := p) k j) i = c i
  exact congrFun ((PIntegralModularForm.PBasis (p := p) k).repr_sum_self c) i

/-- In a fixed weight, reduction of homogeneous E4/E6 polynomials is
determined by its evaluated q-expansion. The PBasis coefficient matrix has
unit determinant over `Z_(p)`, so its reduction remains invertible. -/
theorem reducePolynomial_eq_of_eval_eq {k : ℤ}
    (P Q : PIntegralModularForm.E4E6Polynomial p)
    (hP : ∀ m ∈ P.support, PIntegralModularForm.weightedDegree m = k)
    (hQ : ∀ m ∈ Q.support, PIntegralModularForm.weightedDegree m = k)
    (hEval : evaluateResiduePolynomial (p := p) (reducePolynomial (p := p) P) =
      evaluateResiduePolynomial (p := p) (reducePolynomial (p := p) Q)) :
    reducePolynomial (p := p) P = reducePolynomial (p := p) Q := by
  classical
  obtain ⟨c, hc⟩ := PIntegralModularForm.homogeneous_isPBasisPolynomial
    (p := p) (k := k) P hP
  obtain ⟨d, hd⟩ := PIntegralModularForm.homogeneous_isPBasisPolynomial
    (p := p) (k := k) Q hQ
  have hfourier : PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      (PIntegralModularForm.evaluateE4E6 (p := p) P) =
      PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
      (PIntegralModularForm.evaluateE4E6 (p := p) Q) := by
    rw [← evaluateResiduePolynomial_reducePolynomial (p := p) P,
      ← evaluateResiduePolynomial_reducePolynomial (p := p) Q]
    exact hEval
  have hsum :
      (∑ i : Fin (dim k),
          PIntegralModularForm.coeffToZMod (p := p) (c i) •
            PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
              (PIntegralModularForm.PBasis (p := p) k i).fourier) =
      ∑ i : Fin (dim k),
          PIntegralModularForm.coeffToZMod (p := p) (d i) •
            PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
              (PIntegralModularForm.PBasis (p := p) k i).fourier := by
    calc
      _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
          (PIntegralModularForm.evaluateE4E6 (p := p) P) := by
            rw [hc, PIntegralModularForm.evaluate_polynomialOfCoordinates,
              map_fourier_basis_expansion]
            apply Finset.sum_congr rfl
            intro i hi
            rw [repr_formOfCoordinates_local]
      _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
          (PIntegralModularForm.evaluateE4E6 (p := p) Q) := hfourier
      _ = _ := by
            rw [hd, PIntegralModularForm.evaluate_polynomialOfCoordinates,
              map_fourier_basis_expansion]
            apply Finset.sum_congr rfl
            intro i hi
            rw [repr_formOfCoordinates_local]
  have hzero : ∑ i : Fin (dim k),
      (PIntegralModularForm.coeffToZMod (p := p) (c i) -
        PIntegralModularForm.coeffToZMod (p := p) (d i)) •
          PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
            (PIntegralModularForm.PBasis (p := p) k i).fourier = 0 := by
    calc
      _ = (∑ i : Fin (dim k),
            PIntegralModularForm.coeffToZMod (p := p) (c i) •
              PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
                (PIntegralModularForm.PBasis (p := p) k i).fourier) -
          ∑ i : Fin (dim k),
            PIntegralModularForm.coeffToZMod (p := p) (d i) •
              PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
                (PIntegralModularForm.PBasis (p := p) k i).fourier := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [sub_smul]
      _ = 0 := sub_eq_zero.mpr hsum
  have hcoords := reducedPBasis_fourier_linearIndependent (p := p)
    (k := k) (fun i => PIntegralModularForm.coeffToZMod (p := p) (c i) -
      PIntegralModularForm.coeffToZMod (p := p) (d i)) hzero
  have hcoeff : ∀ i : Fin (dim k),
      PIntegralModularForm.coeffToZMod (p := p) (c i) =
        PIntegralModularForm.coeffToZMod (p := p) (d i) := by
    intro i
    have hi := congrFun hcoords i
    exact sub_eq_zero.mp hi
  rw [hc, hd]
  simp only [PIntegralModularForm.polynomialOfCoordinates, reducePolynomial,
    map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [PIntegralModularForm.E4E6PolynomialTerm, hcoeff i]

/-- Lemma 1.39 (first identity): `∂Ã = B̄`. First identify the normalized
q-expansions, then use the PBasis coefficient matrix to lift equality of
reduced evaluations to equality of homogeneous polynomials. -/
theorem lemma_1_39_first :
    reducePolynomial (delPolynomial A (p := p)) = Bbar (p := p) := by
  have hP : ∀ m ∈ (delPolynomial (p := p) (A (p := p))).support,
      PIntegralModularForm.weightedDegree m = (p : ℤ) + 1 := by
    obtain ⟨c, hc⟩ :=
      PIntegralModularForm.delPolynomial_polynomial_isPBasisPolynomial
        (p := p) (f := normalizedEisMinusOne (p := p))
    intro m hm
    have hm' : m ∈
        (delPolynomial (p := p)
          (PIntegralModularForm.polynomial (normalizedEisMinusOne (p := p)))).support := by
      simpa [A] using hm
    rw [hc] at hm'
    have hdegree := PIntegralModularForm.polynomialOfCoordinates_isHomogeneous
      (p := p) c hm'
    omega
  have hQ : ∀ m ∈ (B (p := p)).support,
      PIntegralModularForm.weightedDegree m = (p : ℤ) + 1 := by
    intro m hm
    simpa [B] using
      (PIntegralModularForm.polynomial_isHomogeneous
        (p := p) (normalizedEisPlusOne (p := p)) hm)
  change reducePolynomial (p := p) (delPolynomial (p := p) (A (p := p))) =
    reducePolynomial (p := p) (B (p := p))
  exact reducePolynomial_eq_of_eval_eq (p := p)
    (delPolynomial (p := p) (A (p := p))) (B (p := p)) hP hQ
    (reduced_del_A_eval (p := p))

/-- Lemma 1.39 (second identity): `∂B̄ = -XĀ`. We use the Ramanujan
formula after reducing `E_(p+1)` to `E₂`, then apply fixed-weight PBasis
uniqueness to pass from q-expansions back to homogeneous polynomials. -/
theorem lemma_1_39_second :
    reducePolynomial (delPolynomial B (p := p)) =
      -(MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) * Abar (p := p) := by
  let Q : PIntegralModularForm.E4E6Polynomial p :=
    -((MvPolynomial.X (0 : Fin 2)) * A (p := p))
  have hP : ∀ m ∈ (delPolynomial (p := p) (B (p := p))).support,
      PIntegralModularForm.weightedDegree m = (p : ℤ) + 3 := by
    obtain ⟨c, hc⟩ :=
      PIntegralModularForm.delPolynomial_polynomial_isPBasisPolynomial
        (p := p) (f := normalizedEisPlusOne (p := p))
    intro m hm
    have hm' : m ∈
        (delPolynomial (p := p)
          (PIntegralModularForm.polynomial
            (normalizedEisPlusOne (p := p)))).support := by
      simpa [B] using hm
    rw [hc] at hm'
    have hdegree := PIntegralModularForm.polynomialOfCoordinates_isHomogeneous
      (p := p) c hm'
    omega
  have hA : ∀ n ∈ (A (p := p)).support,
      PIntegralModularForm.weightedDegree n = (p : ℤ) - 1 := by
    intro n hn
    simpa [A] using
      (PIntegralModularForm.polynomial_isHomogeneous
        (p := p) (normalizedEisMinusOne (p := p)) hn)
  have hshift (n : Fin 2 →₀ ℕ) :
      PIntegralModularForm.weightedDegree (Finsupp.single 0 1 + n) =
        PIntegralModularForm.weightedDegree n + 4 := by
    simp [PIntegralModularForm.weightedDegree, Finsupp.add_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
    ring
  have hQ : ∀ m ∈ Q.support,
      PIntegralModularForm.weightedDegree m = (p : ℤ) + 3 := by
    intro m hm
    have hm' : m ∈ ((MvPolynomial.X 0) * A (p := p)).support := by
      rw [MvPolynomial.mem_support_iff] at hm ⊢
      simpa [Q] using hm
    rw [MvPolynomial.support_X_mul] at hm'
    obtain ⟨n, hn, hmn⟩ := Finset.mem_map.mp hm'
    have heq : m = Finsupp.single 0 1 + n := by
      simpa [addLeftEmbedding_apply] using hmn.symm
    rw [heq, hshift n, hA n hn]
    omega
  have hpoly := reducePolynomial_eq_of_eval_eq (p := p)
    (k := (p : ℤ) + 3)
    (delPolynomial (p := p) (B (p := p))) Q hP hQ
    (reduced_del_B_eval (p := p))
  calc
    reducePolynomial (p := p) (delPolynomial (p := p) (B (p := p))) =
        reducePolynomial (p := p) Q := hpoly
    _ = -(MvPolynomial.X (0 : Fin 2) : ResiduePolynomial p) * Abar (p := p) := by
      simp [Q, reducePolynomial, Abar]


end
end PIntegralModularForm.SwD
