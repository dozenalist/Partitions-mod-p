import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Basic
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basis
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.ThetaOperator.EisLPlusOne
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Derivative

open MatrixGroups ModularForm Derivative IntegerModularForm ModularFormMod
open Filter Function.Periodic UpperHalfPlane Real Complex
open scoped Topology

noncomputable section

namespace ThetaOperator.DelOperator

private lemma normalizedDeriv_bdd_at_infty {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex f) := by
  let F : ℂ → ℂ := cuspFunction 1 f
  have hΓ : (1 : ℝ) ∈ Subgroup.strictPeriods 𝒮ℒ := by simp
  have han : AnalyticAt ℂ F 0 := by
    exact ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have hprod : Tendsto (fun q : ℂ ↦ q * deriv F q) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.mul han.deriv.continuousAt.tendsto)
  have hprod_bdd : IsBoundedAtImInfty
      (fun z : ℍ ↦ qParam 1 (z : ℂ) * deriv F (qParam 1 (z : ℂ))) := by
    have ht : Tendsto
        (fun z : ℍ ↦ qParam 1 (z : ℂ) * deriv F (qParam 1 (z : ℂ)))
        atImInfty (𝓝 0) := by
      change Tendsto ((fun q : ℂ ↦ q * deriv F q) ∘
        (fun z : ℍ ↦ qParam 1 z)) atImInfty (𝓝 0)
      exact hprod.comp (qParam_tendsto_atImInfty one_pos)
    exact ht.isBigO_one (F := ℝ)
  have hderiv : ∀ z : ℍ,
      Derivative.normalizedDerivOfComplex f z =
        qParam 1 (z : ℂ) * deriv F (qParam 1 (z : ℂ)) := by
    intro z
    have hq : ‖qParam 1 (z : ℂ)‖ < 1 :=
      Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
    have hFq : DifferentiableAt ℂ F (qParam 1 (z : ℂ)) :=
      ModularFormClass.differentiableAt_cuspFunction f one_pos hΓ hq
    have hlin : HasDerivAt (fun w : ℂ ↦ 2 * π * Complex.I * w)
        (2 * π * Complex.I) (z : ℂ) := by
      simpa [id] using
        (hasDerivAt_id (z : ℂ)).const_mul (2 * π * Complex.I)
    have hqderiv : HasDerivAt
        (fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w))
        (qParam 1 (z : ℂ) * (2 * π * Complex.I)) (z : ℂ) := by
      simpa [Function.comp_def, Function.Periodic.qParam] using
        (Complex.hasDerivAt_exp _).comp _ hlin
    have hqfun : (qParam 1 : ℂ → ℂ) =
        (fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w)) := by
      funext w
      simp [Function.Periodic.qParam]
    have hqderiv' : HasDerivAt (qParam 1)
        (qParam 1 (z : ℂ) * (2 * π * Complex.I)) (z : ℂ) := by
      simpa only [hqfun] using hqderiv
    have hcomp := hFq.hasDerivAt.comp _ hqderiv'
    rw [hqfun] at hcomp
    have heq0 : (f ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)] (F ∘ qParam 1) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
      simpa [F, Function.comp_def, ofComplex_apply_of_im_pos hw] using
        (SlashInvariantFormClass.eq_cuspFunction f ⟨w, hw⟩ hΓ one_ne_zero).symm
    have heq : (f ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
        (F ∘ fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w)) := by
      rw [← hqfun]
      exact heq0
    have hcomp' := hcomp.congr_of_eventuallyEq heq
    rw [Derivative.normalizedDerivOfComplex, hcomp'.deriv]
    simp only [Function.Periodic.qParam]
    field_simp; norm_num; ring
  rw [show Derivative.normalizedDerivOfComplex f =
      (fun z : ℍ ↦ qParam 1 (z : ℂ) * deriv F (qParam 1 (z : ℂ))) from funext hderiv]
  exact hprod_bdd

/-! The characteristic-zero operator from Theorem 1.33. -/

variable {k : ℤ}

def del (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ (k + 2) where
  toFun := Derivative.serreDerivative k f
  slash_action_eq' γ hγ := by
    obtain ⟨γ, rfl⟩ := hγ
    apply Derivative.serreDerivative_slash_invariant f.holo'
    exact f.1.slash_action_eq' γ ⟨γ, rfl⟩
  holo' := Derivative.serreDerivative_mdifferentiable (k : ℂ) f.holo'
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ hγ
    have hslash :
        Derivative.serreDerivative k f ∣[k + 2] γ =
          Derivative.serreDerivative k f := by
      simpa only [ModularForm.toSlashInvariantForm_coe] using
        (Derivative.serreDerivative_slash_invariant f.holo'
          (f.1.slash_action_eq' γ ⟨γ, rfl⟩) (γ := γ))
    rw [hslash]
    rw [Derivative.serreDerivative_eq]
    have hterm : IsBoundedAtImInfty
        (((k : ℂ) * (12 : ℂ)⁻¹) •
          ((EisensteinSeries.E2 : ℍ → ℂ) * (f : ℍ → ℂ))) := by
      exact (EisensteinSeries.isBoundedAtImInfty_E2.mul
        (ModularFormClass.bdd_at_infty f)).const_smul_left _
    simpa [IsBoundedAtImInfty, Filter.BoundedAtFilter, smul_eq_mul,
      Pi.smul_apply, mul_assoc] using
      (normalizedDeriv_bdd_at_infty f).sub hterm

@[simp]
theorem del_apply (f : ModularForm 𝒮ℒ k) (z : UpperHalfPlane) :
    del f z = Derivative.serreDerivative k f z := rfl

/-!
The Serre derivative of an integral modular form is canonically a complex
modular form. It need not have integral Fourier coefficients in general, so
the codomain here is `ModularForm`, rather than `IntegerModularForm`.
-/



private lemma normalizedDeriv_eq_q_mul_deriv {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (z : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex f z =
      qParam 1 (z : ℂ) * deriv (cuspFunction 1 f) (qParam 1 (z : ℂ)) := by
  have hq : ‖qParam 1 (z : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  have hFq : DifferentiableAt ℂ (cuspFunction 1 (f : UpperHalfPlane → ℂ))
      (qParam 1 (z : ℂ)) :=
    ModularFormClass.differentiableAt_cuspFunction f one_pos
      one_mem_strictPeriods_SL hq
  have hlin : HasDerivAt (fun w : ℂ ↦ 2 * π * Complex.I * w)
      (2 * π * Complex.I) (z : ℂ) := by
    simpa [id] using
      (hasDerivAt_id (z : ℂ)).const_mul (2 * π * Complex.I)
  have hqderiv : HasDerivAt
      (fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w))
      (qParam 1 (z : ℂ) * (2 * π * Complex.I)) (z : ℂ) := by
    simpa [Function.comp_def, Function.Periodic.qParam] using
      (Complex.hasDerivAt_exp _).comp _ hlin
  have hqfun : (qParam 1 : ℂ → ℂ) =
      (fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w)) := by
    funext w
    simp [Function.Periodic.qParam]
  have hqderiv' : HasDerivAt (qParam 1)
      (qParam 1 (z : ℂ) * (2 * π * Complex.I)) (z : ℂ) := by
    simpa only [hqfun] using hqderiv
  have hcomp := hFq.hasDerivAt.comp _ hqderiv'
  rw [hqfun] at hcomp
  have heq0 : (f ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      ((cuspFunction 1 f) ∘ qParam 1) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simpa [Function.comp_def, ofComplex_apply_of_im_pos hw] using
      (SlashInvariantFormClass.eq_cuspFunction f ⟨w, hw⟩
        one_mem_strictPeriods_SL one_ne_zero).symm
  have heq : (f ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      ((cuspFunction 1 f) ∘ fun w : ℂ ↦ Complex.exp (2 * π * Complex.I * w)) := by
    rw [← hqfun]
    exact heq0
  have hcomp' := hcomp.congr_of_eventuallyEq heq
  rw [Derivative.normalizedDerivOfComplex, hcomp'.deriv]
  simp only [Function.Periodic.qParam]
  field_simp; norm_num; ring

private lemma iteratedDeriv_q_mul_deriv (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) (n : ℕ) :
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

/-!
The factor `12` clears the denominator in the Serre derivative.  We use the
integral q-expansion

`E₂ = 1 - 24 * ∑ n, σ₁(n) Xⁿ`

in the definition below.  Thus the Fourier coefficients are integral before
we attach the complex modular form `12 • del f.carrier`.
-/

def e2Fourier : PowerSeries ℤ :=
  PowerSeries.mk (fun n ↦ if n = 0 then 1 else -24 * ArithmeticFunction.sigma 1 n)

/-!
The Fourier-series numerator of Ramanujan's weight-two identity.  The
following bridge isolates exactly the finite-dimensional part of the
coefficient-truncation proof: once this series is known to be the Fourier
expansion of an integral weight-four modular form, Sturm injectivity identifies
that form with `-Eis 4`.
-/

def e2RamanujanFourier : PowerSeries ℤ :=
  12 • (PowerSeries.X * PowerSeries.derivative e2Fourier) -
    e2Fourier * e2Fourier

theorem e2RamanujanFourier_eq_neg_Eis_four
    (g : IntegerModularForm 4)
    (hg : g.fourier = e2RamanujanFourier) :
    e2RamanujanFourier = -(IntegerModularForm.Eis 4).fourier := by
  have hgeq : g = -(IntegerModularForm.Eis 4) := by
    apply IntegerModularForm.coeff_trunc_injective
    funext i
    have hdim : dim (4 : ℤ) = 1 := by
      have heven : Even (4 : ℤ) := ⟨2, by norm_num⟩
      simp [dim, heven, Int.ModEq]
    have hi_lt : i.1 < 1 := hdim ▸ i.2
    have hi0 : i.1 = 0 := by omega
    have hpos : 0 < dim (4 : ℤ) := by omega
    have hi : i = ⟨0, hpos⟩ := by
      apply Fin.ext
      exact hi0
    rw [hi]
    simp only [IntegerModularForm.coeff_trunc_apply]
    change g.fourier.coeff 0 = (-(IntegerModularForm.Eis 4)).fourier.coeff 0
    rw [hg]
    simp [e2RamanujanFourier, e2Fourier]
  calc
    e2RamanujanFourier = g.fourier := hg.symm
    _ = (-(IntegerModularForm.Eis 4)).fourier := congrArg
      IntegerModularForm.fourier hgeq


private lemma e2_periodic : Function.Periodic
    (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + (1 : ℂ)).im := by simpa using hw
    let z : UpperHalfPlane := UpperHalfPlane.ofComplex w
    have hT := congr_fun EisensteinSeries.G2_T_transform z
    have hE : EisensteinSeries.E2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.E2 z := by
      simp_rw [SL_slash_def, modular_T_smul] at hT
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

set_option maxHeartbeats 800000 in

private lemma normalizedDeriv_periodic {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Function.Periodic
      (Derivative.normalizedDerivOfComplex f ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
  let g : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hgper : Function.Periodic g (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + (1 : ℂ)).im := by simpa using hw
    have hgw : DifferentiableAt ℂ g w := by
      dsimp [g]
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hw] using
        (UpperHalfPlane.mdifferentiableAt_iff.mp
          (f.holo' (UpperHalfPlane.ofComplex w)))
    have hgw' : DifferentiableAt ℂ g (w + (1 : ℂ)) := by
      dsimp [g]
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hw'] using
        (UpperHalfPlane.mdifferentiableAt_iff.mp
          (f.holo' (UpperHalfPlane.ofComplex (w + (1 : ℂ)))))
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

theorem qexp_normalizedDeriv {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex f) =
      PowerSeries.X * PowerSeries.derivative (UpperHalfPlane.qExpansion 1 f) := by
  let F : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 f
  have hFani : AnalyticAt ℂ F 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL
  have hDper := normalizedDeriv_periodic f
  have hDani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hDper
      (Derivative.normalizedDerivOfComplex_mdifferentiable f.holo')
      (normalizedDeriv_bdd_at_infty f)
  have hDzero : IsZeroAtImInfty (Derivative.normalizedDerivOfComplex f) := by
    rw [IsZeroAtImInfty, ZeroAtFilter]
    rw [show Derivative.normalizedDerivOfComplex f =
        (fun z : UpperHalfPlane ↦
          qParam 1 (z : ℂ) * deriv F (qParam 1 (z : ℂ))) from
      funext (normalizedDeriv_eq_q_mul_deriv f)]
    have hprod : Tendsto (fun q : ℂ ↦ q * deriv F q) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id.mul hFani.deriv.continuousAt.tendsto)
    exact hprod.comp (qParam_tendsto_atImInfty one_pos)
  have hD0 :
      UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) 0 = 0 := by
    rw [UpperHalfPlane.cuspFunction_apply_zero one_pos hDani hDper]
    exact hDzero.valueAtInfty_eq_zero
  have hcf :
      UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) =ᶠ[𝓝 0]
        (fun q : ℂ ↦ q * deriv F q) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    by_cases hq0 : q = 0
    · subst q
      simp [hD0]
    · have hnorm : ‖q‖ < 1 := by
        simpa [Metric.mem_ball] using hq
      have him : 0 < (invQParam 1 q).im :=
        Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hnorm hq0
      rw [UpperHalfPlane.cuspFunction,
        Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq0]
      simpa [F, UpperHalfPlane.ofComplex_apply_of_im_pos him,
        Function.Periodic.qParam_right_inv one_pos.ne' hq0] using
        normalizedDeriv_eq_q_mul_deriv f
          (UpperHalfPlane.ofComplex (invQParam 1 q))
  ext n
  rw [UpperHalfPlane.qExpansion_coeff]
  rw [hcf.iteratedDeriv_eq n]
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
      rw [iteratedDeriv_q_mul_deriv F hFani]
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        UpperHalfPlane.qExpansion_coeff]
      simp [Nat.factorial_succ]
      ring


theorem qexp_e2 :
      UpperHalfPlane.qExpansion 1 EisensteinSeries.E2 =
      PowerSeries.map (Int.castRingHom ℂ) e2Fourier := by
  let c : ℕ → ℂ := fun n ↦
    if n = 0 then 1 else -24 * ArithmeticFunction.sigma 1 n
  have han : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos e2_periodic
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hsum : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ ↦ c m •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (EisensteinSeries.E2 τ) := by
    intro τ
    simpa only [c, Function.Periodic.qParam, ofReal_one, div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z := τ)
  let E2fun : TypeCat.Fun UpperHalfPlane ℂ := ⟨EisensteinSeries.E2⟩
  have han' : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 E2fun) 0 := by
    simpa [E2fun] using han
  have hsum' : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ ↦ c m •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E2fun τ) := by
    simpa [E2fun] using hsum
  let rhs : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) e2Fourier
  change UpperHalfPlane.qExpansion 1 EisensteinSeries.E2 = rhs
  have hunique := UpperHalfPlane.qExpansion_coeff_unique
    (h := (1 : ℝ)) (c := c) E2fun one_pos han' hsum'
  apply @PowerSeries.ext ℂ _ (UpperHalfPlane.qExpansion 1 EisensteinSeries.E2) rhs
  intro n
  dsimp [rhs]
  simp only [e2Fourier, PowerSeries.coeff_mk]
  simpa [E2fun, c] using
    (hunique n).symm

def normalizedDelFourier {k : ℤ} (f : IntegerModularForm k) : PowerSeries ℤ :=
  12 • (PowerSeries.X * PowerSeries.derivative f.fourier) -
    k • (e2Fourier * f.fourier)

private lemma map_derivative_int (a : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.derivative a) =
      PowerSeries.derivative (PowerSeries.map (Int.castRingHom ℂ) a) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]

private lemma twelve_smul_sub (A B : PowerSeries ℂ) (k : ℤ) :
    12 • (A - ((k : ℂ) * (12 : ℂ)⁻¹) • B) =
      12 • A - k • B := by
  have h12 : ((12 : ℕ) : PowerSeries ℂ) = PowerSeries.C (12 : ℂ) := by
    simpa using (map_natCast (PowerSeries.C : ℂ →+* PowerSeries ℂ) 12).symm
  have hk : (k : PowerSeries ℂ) = PowerSeries.C (k : ℂ) := by
    simp only [map_intCast]
  simp only [nsmul_eq_mul, zsmul_eq_mul, PowerSeries.smul_eq_C_mul]
  rw [h12, hk]
  have hscalar : PowerSeries.C ((k : ℂ) * (12 : ℂ)⁻¹) *
      PowerSeries.C (12 : ℂ) = PowerSeries.C (k : ℂ) := by
    rw [← (PowerSeries.C : ℂ →+* PowerSeries ℂ).map_mul]
    congr 1
    field_simp
  calc
    PowerSeries.C (12 : ℂ) * (A -
        PowerSeries.C ((k : ℂ) * (12 : ℂ)⁻¹) * B) =
        PowerSeries.C (12 : ℂ) * A -
          (PowerSeries.C ((k : ℂ) * (12 : ℂ)⁻¹) *
            PowerSeries.C (12 : ℂ)) * B := by ring
    _ = PowerSeries.C (12 : ℂ) * A - PowerSeries.C (k : ℂ) * B := by
      rw [hscalar]

private lemma normalizedDel_carrier_eq (f : IntegerModularForm k) :
    (12 • del f.carrier).qexp =
      PowerSeries.map (Int.castRingHom ℂ) (normalizedDelFourier f) := by
  let fF : UpperHalfPlane → ℂ := f.carrier
  let dF : UpperHalfPlane → ℂ := Derivative.normalizedDerivOfComplex f.carrier
  let pF : UpperHalfPlane → ℂ := EisensteinSeries.E2 * fF
  let c : ℂ := (k : ℂ) * (12 : ℂ)⁻¹
  have hFani : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 fF) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f.carrier one_pos
      one_mem_strictPeriods_SL
  have hEani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos e2_periodic
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hDani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 dF) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos
      (normalizedDeriv_periodic f.carrier)
      (Derivative.normalizedDerivOfComplex_mdifferentiable f.carrier.holo')
      (normalizedDeriv_bdd_at_infty f.carrier)
  have hPani : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 pF) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hEani.continuousAt hFani.continuousAt]
    fun_prop
  have hcPani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (c • pF)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hPani.continuousAt]
    exact hPani.const_smul
  have hDq : UpperHalfPlane.qExpansion 1 dF =
      PowerSeries.X * PowerSeries.derivative (UpperHalfPlane.qExpansion 1 fF) := by
    simpa [dF, fF] using qexp_normalizedDeriv f.carrier
  have hqdel : (del f.carrier).qexp =
      UpperHalfPlane.qExpansion 1 dF - c • UpperHalfPlane.qExpansion 1 pF := by
    rw [ModularForm.qexp_eq' (del f.carrier)]
    have hdel_fun : (del f.carrier : UpperHalfPlane → ℂ) = dF - c • pF := by
      funext z
      change Derivative.serreDerivative (k : ℂ) (f.carrier : UpperHalfPlane → ℂ) z = _
      simp [dF, pF, fF, c, Derivative.serreDerivative_apply,
        smul_eq_mul, Pi.smul_apply, mul_assoc]
    rw [hdel_fun]
    rw [UpperHalfPlane.qExpansion_sub hDani hcPani,
      UpperHalfPlane.qExpansion_smul hPani c]
  have hpq : UpperHalfPlane.qExpansion 1 pF =
      UpperHalfPlane.qExpansion 1 EisensteinSeries.E2 *
        UpperHalfPlane.qExpansion 1 fF := by
    simpa [pF] using UpperHalfPlane.qExpansion_mul hEani hFani
  have hfq : UpperHalfPlane.qExpansion 1 fF =
      PowerSeries.map (Int.castRingHom ℂ) f.fourier := by
    simpa [fF, ModularForm.qexp_eq'] using f.carrier_eq
  rw [map_nsmul]
  rw [hqdel, hDq, hpq, qexp_e2, hfq]
  simp only [normalizedDelFourier, map_sub, map_nsmul, map_zsmul, map_mul,
    PowerSeries.map_X, map_derivative_int]
  dsimp [c]
  simpa using twelve_smul_sub
    (PowerSeries.X * PowerSeries.derivative
      (PowerSeries.map (Int.castRingHom ℂ) f.fourier))
    (PowerSeries.map (Int.castRingHom ℂ) e2Fourier *
      PowerSeries.map (Int.castRingHom ℂ) f.fourier) k

/-- The q-expansion of the scaled Serre derivative on an arbitrary complex
modular form. This is the analytic identity used to construct its
`p`-integral version. -/
theorem qExpansion_twelve_del {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    UpperHalfPlane.qExpansion 1 (12 • del f) =
      12 • (PowerSeries.X * PowerSeries.derivative
        (UpperHalfPlane.qExpansion 1 f)) -
      k • (PowerSeries.map (Int.castRingHom ℂ) e2Fourier *
        UpperHalfPlane.qExpansion 1 f) := by
  let fF : UpperHalfPlane → ℂ := f
  let dF : UpperHalfPlane → ℂ := Derivative.normalizedDerivOfComplex f
  let pF : UpperHalfPlane → ℂ := EisensteinSeries.E2 * fF
  let c : ℂ := (k : ℂ) * (12 : ℂ)⁻¹
  have hFani : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 fF) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      one_mem_strictPeriods_SL
  have hEani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos e2_periodic
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hDani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 dF) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos
      (normalizedDeriv_periodic f)
      (Derivative.normalizedDerivOfComplex_mdifferentiable f.holo')
      (normalizedDeriv_bdd_at_infty f)
  have hPani : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 pF) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hEani.continuousAt hFani.continuousAt]
    fun_prop
  have hcPani : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (c • pF)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hPani.continuousAt]
    exact hPani.const_smul
  have hDq : UpperHalfPlane.qExpansion 1 dF =
      PowerSeries.X * PowerSeries.derivative (UpperHalfPlane.qExpansion 1 fF) := by
    simpa [dF, fF] using qexp_normalizedDeriv f
  have hdelQ : (del f).qexp =
      UpperHalfPlane.qExpansion 1 dF - c • UpperHalfPlane.qExpansion 1 pF := by
    rw [ModularForm.qexp_eq' (del f)]
    have hdel_fun : (del f : UpperHalfPlane → ℂ) = dF - c • pF := by
      funext z
      change Derivative.serreDerivative (k : ℂ) (f : UpperHalfPlane → ℂ) z =
        Derivative.normalizedDerivOfComplex f z -
          c * (EisensteinSeries.E2 z * f z)
      rw [Derivative.serreDerivative_apply]
      dsimp [c]
      ring
    rw [hdel_fun, UpperHalfPlane.qExpansion_sub hDani hcPani,
      UpperHalfPlane.qExpansion_smul hPani c]
  have hdel : UpperHalfPlane.qExpansion 1 (del f) =
      UpperHalfPlane.qExpansion 1 dF - c • UpperHalfPlane.qExpansion 1 pF := by
    rw [← ModularForm.qexp_eq' (del f)]
    exact hdelQ
  have hpq : UpperHalfPlane.qExpansion 1 pF =
      UpperHalfPlane.qExpansion 1 EisensteinSeries.E2 *
        UpperHalfPlane.qExpansion 1 fF := by
    simpa [pF] using UpperHalfPlane.qExpansion_mul hEani hFani
  calc
    UpperHalfPlane.qExpansion 1 (12 • del f) =
        12 • UpperHalfPlane.qExpansion 1 (del f) := by
      calc
        UpperHalfPlane.qExpansion 1 (12 • del f) =
            UpperHalfPlane.qExpansion 1 ((12 : ℂ) • del f) := by
          congr 1
          exact (Nat.cast_smul_eq_nsmul ℂ 12
            (del f : UpperHalfPlane → ℂ)).symm
        _ = (12 : ℂ) • UpperHalfPlane.qExpansion 1 (del f) :=
          ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL
            (12 : ℂ) (del f)
        _ = 12 • UpperHalfPlane.qExpansion 1 (del f) :=
          Nat.cast_smul_eq_nsmul ℂ 12 _
    _ = 12 • ((PowerSeries.X * PowerSeries.derivative
          (UpperHalfPlane.qExpansion 1 f)) -
          c • (PowerSeries.map (Int.castRingHom ℂ) e2Fourier *
            UpperHalfPlane.qExpansion 1 f)) := by
      rw [hdel, hDq, hpq, qexp_e2]
    _ = 12 • (PowerSeries.X * PowerSeries.derivative
          (UpperHalfPlane.qExpansion 1 f)) -
          k • (PowerSeries.map (Int.castRingHom ℂ) e2Fourier *
            UpperHalfPlane.qExpansion 1 f) := by
      simpa [c] using twelve_smul_sub
        (PowerSeries.X * PowerSeries.derivative (UpperHalfPlane.qExpansion 1 f))
        (PowerSeries.map (Int.castRingHom ℂ) e2Fourier *
          UpperHalfPlane.qExpansion 1 f) k

def normalizedDel (f : IntegerModularForm k) : IntegerModularForm (k + 2) where
  fourier := normalizedDelFourier f
  carrier := 12 • del f.carrier
  carrier_eq := normalizedDel_carrier_eq f

@[simp]
theorem normalizedDel_fourier (f : IntegerModularForm k) :
    (normalizedDel f).fourier = normalizedDelFourier f := rfl

@[simp]
theorem normalizedDel_carrier (f : IntegerModularForm k) :
    (normalizedDel f).carrier = 12 • del f.carrier := rfl

/-!
The two low-weight Ramanujan identities are finite-dimensional identities of
integral modular forms.  The Sturm truncation map is injective, and the
target weights 6 and 8 both have one-dimensional truncation, so only the
constant coefficient has to be checked.
-/

theorem normalizedDel_Eis_four :
    normalizedDel (IntegerModularForm.Eis 4) =
      (-4 : ℤ) • IntegerModularForm.Eis 6 := by
  apply IntegerModularForm.coeff_trunc_injective
  funext i
  have hdim : dim (4 + 2 : ℤ) = 1 := by
    rw [show (4 + 2 : ℤ) = 6 by norm_num]
    have heven : Even (6 : ℤ) := ⟨3, by norm_num⟩
    simp [dim, heven, Int.ModEq]
  have hi_lt : i.1 < 1 := hdim ▸ i.2
  have hi0 : i.1 = 0 := by omega
  have hpos : 0 < dim (4 + 2 : ℤ) := by omega
  have hi : i = ⟨0, hpos⟩ := by
    apply Fin.ext
    exact hi0
  rw [hi]
  simp only [IntegerModularForm.coeff_trunc_apply]
  change (normalizedDelFourier (IntegerModularForm.Eis 4)).coeff 0 =
    (-4 : ℤ) * (IntegerModularForm.Eis 6).fourier.coeff 0
  have hconst : PowerSeries.constantCoeff (4 : PowerSeries ℤ) = (4 : ℤ) :=
    map_natCast (PowerSeries.constantCoeff : PowerSeries ℤ →+* ℤ) 4
  have hE4 : PowerSeries.constantCoeff (IntegerModularForm.Eis 4).fourier = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact IntegerModularForm.Eis_four_zero
  have hE6 : PowerSeries.constantCoeff (IntegerModularForm.Eis 6).fourier = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact IntegerModularForm.Eis_six_zero
  simp [normalizedDelFourier, e2Fourier, hconst, hE4]

theorem normalizedDel_Eis_six :
    normalizedDel (IntegerModularForm.Eis 6) =
      (-6 : ℤ) • (IntegerModularForm.Eis 4).pow 2 := by
  apply IntegerModularForm.coeff_trunc_injective
  funext i
  have hdim : dim (6 + 2 : ℤ) = 1 := by
    rw [show (6 + 2 : ℤ) = 8 by norm_num]
    have heven : Even (8 : ℤ) := ⟨4, by norm_num⟩
    simp [dim, heven, Int.ModEq]
  have hi_lt : i.1 < 1 := hdim ▸ i.2
  have hi0 : i.1 = 0 := by omega
  have hpos : 0 < dim (6 + 2 : ℤ) := by omega
  have hi : i = ⟨0, hpos⟩ := by
    apply Fin.ext
    exact hi0
  rw [hi]
  simp only [IntegerModularForm.coeff_trunc_apply]
  change (normalizedDelFourier (IntegerModularForm.Eis 6)).coeff 0 =
    (-6 : ℤ) * ((IntegerModularForm.Eis 4).pow 2).fourier.coeff 0
  have hconst : PowerSeries.constantCoeff (6 : PowerSeries ℤ) = (6 : ℤ) :=
    map_natCast (PowerSeries.constantCoeff : PowerSeries ℤ →+* ℤ) 6
  have hE4 : PowerSeries.constantCoeff (IntegerModularForm.Eis 4).fourier = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact IntegerModularForm.Eis_four_zero
  have hE6 : PowerSeries.constantCoeff (IntegerModularForm.Eis 6).fourier = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact IntegerModularForm.Eis_six_zero
  simp [normalizedDelFourier, e2Fourier, hconst, hE4, hE6]


/-! The q-expansion form of `q d/dq`. -/

variable {ℓ : ℕ} [isLargePrime ℓ]
variable {r : ZMod (ℓ - 1)}
variable {f : ModularFormMod ℓ r}

def thetaSeries (f : ModularFormMod ℓ r) : PowerSeries (ZMod ℓ) :=
  PowerSeries.X * PowerSeries.derivative f.fourier

@[simp]
theorem coeff_thetaSeries (f : ModularFormMod ℓ r) (n : ℕ) :
    (thetaSeries f).coeff n = n • f.coeff n := by
  cases n with
  | zero => simp [thetaSeries]
  | succ n =>
      simp [thetaSeries, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative, ModularFormMod.coeff_def, mul_comm]

/-!
`delLift` is the exact q-expansion identity used in Corollary 1.37.  It is
the interface between the analytic operator above and the integral model in
this project: `d` is an integral lift of `del f`, while `lift` is an integral
lift of `f`.
-/

structure DelLift (f : ModularFormMod ℓ r) where
  weight : ℤ
  lift : IntegerModularForm weight
  delLift : IntegerModularForm (weight + 2)
  lift_eq : lift.reduce ℓ = f.fourier
  identity :
    (12 : ZMod ℓ) • thetaSeries f =
      delLift.reduce ℓ +
        (weight : ZMod ℓ) •
          ((Eis (ℓ + 1)).mul lift).reduce ℓ

theorem cast_weight_shift (w : ℤ) :
    ((ℓ + 1 + w : ℤ) : ZMod (ℓ - 1)) =
      ((w + 2 : ℤ) : ZMod (ℓ - 1)) := by
  have hℓ : (ℓ : ZMod (ℓ - 1)) = 1 := by
    rcases Nat.exists_eq_add_one.2 <| Nat.pos_of_neZero ℓ with ⟨n, rfl⟩
    simp only [Nat.cast_add, CharP.cast_eq_zero, Nat.cast_one, zero_add]
  push_cast
  rw [hℓ]
  ring

theorem isUnit_twelve : IsUnit (12 : ZMod ℓ) := by
  have hℓ5 : 5 ≤ ℓ := (inferInstance : isLargePrime ℓ).AtLeastFive
  rw [isUnit_iff_ne_zero]
  change ((12 : ℕ) : ZMod ℓ) ≠ 0
  intro hzero
  have hdiv : ℓ ∣ 12 := (ZMod.natCast_eq_zero_iff 12 ℓ).mp hzero
  have hfactor : ℓ ∣ 2 ^ 2 * 3 := by norm_num at hdiv ⊢; exact hdiv
  rcases (inferInstance : isLargePrime ℓ).Prime.dvd_mul.mp hfactor with h2 | h3
  · have h2' : ℓ ∣ 2 := (inferInstance : isLargePrime ℓ).Prime.dvd_of_dvd_pow h2
    have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    omega
  · have hle : ℓ ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega

def thetaFromDelLift (c : DelLift f) :
    ModularFormMod ℓ ((c.weight + 2 : ℤ) : ZMod (ℓ - 1)) := by
  let d : ModularFormMod ℓ ((c.weight + 2 : ℤ) : ZMod (ℓ - 1)) :=
    c.delLift.Reduce ℓ
  let e : ModularFormMod ℓ ((c.weight + 2 : ℤ) : ZMod (ℓ - 1)) :=
    ((Eis (ℓ + 1)).mul c.lift).Reduce ℓ |>.Mcast (cast_weight_shift c.weight)
  exact (12 : ZMod ℓ)⁻¹ • (d + (c.weight : ZMod ℓ) • e)

theorem thetaFromDelLift_fourier (c : DelLift f) :
    (thetaFromDelLift c).fourier = thetaSeries f := by
  let d : ModularFormMod ℓ ((c.weight + 2 : ℤ) : ZMod (ℓ - 1)) :=
    c.delLift.Reduce ℓ
  let e : ModularFormMod ℓ ((c.weight + 2 : ℤ) : ZMod (ℓ - 1)) :=
    ((Eis (ℓ + 1)).mul c.lift).Reduce ℓ |>.Mcast (cast_weight_shift c.weight)
  have he : e.fourier = ((Eis (ℓ + 1)).mul c.lift).reduce ℓ := by
    simp [e]
  have hd : d.fourier = c.delLift.reduce ℓ := by
    rfl
  simp only [thetaFromDelLift, ModularFormMod.fourier_smul,
    ModularFormMod.fourier_add, ModularFormMod.fourier_Mcast,
    IntegerModularForm.fourier_Reduce]
  have h := congrArg (fun x : PowerSeries (ZMod ℓ) =>
    (12 : ZMod ℓ)⁻¹ • x) c.identity
  simpa [smul_smul, (isUnit_twelve (ℓ := ℓ)).ne_zero] using h.symm

theorem theta_preserves_modularity_of_delLift (c : DelLift f) :
    ∃ g : ModularFormMod ℓ ((c.weight + 2 : ℤ) : ZMod (ℓ - 1)),
      g.fourier = thetaSeries f := by
  exact ⟨thetaFromDelLift c, thetaFromDelLift_fourier c⟩

theorem theta_preserves_modularity (f : ModularFormMod ℓ r) :
    ∃ g : ModularFormMod ℓ (r + 2 : ZMod (ℓ - 1)),
      g.fourier = thetaSeries f := by
  obtain ⟨w, _hw, lift, hlift⟩ := f.Exists_reduce
  let d : ModularFormMod ℓ ((w + 2 : ℤ) : ZMod (ℓ - 1)) :=
    (normalizedDel lift).Reduce ℓ
  let e : ModularFormMod ℓ ((w + 2 : ℤ) : ZMod (ℓ - 1)) :=
    ((IntegerModularForm.Eis (ℓ + 1)).mul lift).Reduce ℓ |>.Mcast
      (cast_weight_shift w)
  let a : ZMod ℓ :=
    ThetaOperator.eisLPlusOneConstant (ℓ := ℓ)
  let e2 : ModularFormMod ℓ (2 : ZMod (ℓ - 1)) := ThetaOperator.E₂
  let b : ModularFormMod ℓ ((w + 2 : ℤ) : ZMod (ℓ - 1)) :=
    (a⁻¹ * (w : ZMod ℓ)) • e
  let g : ModularFormMod ℓ ((w + 2 : ℤ) : ZMod (ℓ - 1)) :=
    (12 : ZMod ℓ)⁻¹ • (d + b)
  have map_derivative_zmod (a : PowerSeries ℤ) :
      PowerSeries.map (Int.castRingHom (ZMod ℓ)) (PowerSeries.derivative a) =
        PowerSeries.derivative
          (PowerSeries.map (Int.castRingHom (ZMod ℓ)) a) := by
    ext n
    simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]
  have hd : d.fourier =
      12 • thetaSeries f - (w : ZMod ℓ) •
        (PowerSeries.map (Int.castRingHom (ZMod ℓ)) e2Fourier * f.fourier) := by
    dsimp [d]
    change PowerSeries.map (Int.castRingHom (ZMod ℓ))
      (normalizedDelFourier lift) = _
    simp only [normalizedDelFourier, map_sub, map_nsmul, map_zsmul, map_mul,
      PowerSeries.map_X, map_derivative_zmod]
    have hlift' :
        PowerSeries.map (Int.castRingHom (ZMod ℓ)) lift.fourier = f.fourier := hlift
    rw [hlift']
    simp only [thetaSeries, Int.cast_smul_eq_zsmul]
  have he2 : e2.fourier =
      PowerSeries.map (Int.castRingHom (ZMod ℓ)) e2Fourier := by
    ext n
    change (e2 : ModularFormMod ℓ (2 : ZMod (ℓ - 1))).coeff n = _
    rw [ThetaOperator.coeff_E₂]
    simp [e2Fourier]
  have hE :
      ((IntegerModularForm.Eis (ℓ + 1)).Reduce ℓ).fourier =
        a • e2.fourier := by
    have h := congrArg ModularFormMod.fourier
      (ThetaOperator.eisLPlusOne_reduce (ℓ := ℓ))
    simpa [a, e2, ThetaOperator.eisLPlusOne] using h
  have he : e.fourier = a • (e2.fourier * f.fourier) := by
    dsimp [e]
    simp only [IntegerModularForm.reduce_mul]
    have hE' : (IntegerModularForm.Eis (ℓ + 1)).reduce ℓ =
        a • e2.fourier := by simpa using hE
    rw [hE']
    rw [hlift]
    simp only [smul_mul_assoc]
  refine ⟨g.Mcast (by simpa), ?_⟩
  change (12 : ZMod ℓ)⁻¹ •
      (d.fourier + (a⁻¹ * (w : ZMod ℓ)) • e.fourier) = thetaSeries f
  rw [hd, he, ← he2]
  have ha : a ≠ 0 := by
    simpa [a] using (ThetaOperator.eisLPlusOneConstant_ne_zero (ℓ := ℓ))
  have h12 : (12 : ZMod ℓ) ≠ 0 := (isUnit_twelve (ℓ := ℓ)).ne_zero
  simp only [smul_sub, smul_add, smul_smul]
  field_simp [ha, h12]
  simp only [one_div, nsmul_eq_mul, Nat.cast_ofNat, sub_add_cancel]
  have h12PS : (12 : PowerSeries (ZMod ℓ)) =
      PowerSeries.C (12 : ZMod ℓ) := by
    simpa using
      (map_natCast (PowerSeries.C : ZMod ℓ →+* PowerSeries (ZMod ℓ)) 12).symm
  rw [h12PS, ← PowerSeries.smul_eq_C_mul, smul_smul]
  simp [h12]

end ThetaOperator.DelOperator
