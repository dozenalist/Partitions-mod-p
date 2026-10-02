import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.FiltrationTheta.Statements
import Mathlib.Algebra.MvPolynomial.PDeriv


open ModularFormMod
open EisensteinSeries

noncomputable section

namespace FiltrationTheta.DelOperator

open FiltrationTheta
open IntegerModularForm

variable {ℓ : ℕ} [isLargePrime ℓ]
variable {k : ZMod (ℓ - 1)}

abbrev Polynomial (ℓ : ℕ) := MvPolynomial (Fin 2) (ZMod ℓ)

/-! The derivation used in the proof of Proposition 1.44.  We use the
coefficient ring `ZMod ℓ`, while all integral lifts remain the
`IntegerModularForm`s from the project. -/

def derivation : Derivation (ZMod ℓ) (Polynomial ℓ) (Polynomial ℓ) :=
  (((MvPolynomial.C (-4 : ZMod ℓ) : Polynomial ℓ) *
        (MvPolynomial.X 1 : Polynomial ℓ)) •
      (MvPolynomial.pderiv (R := ZMod ℓ) (σ := Fin 2) 0)) +
    (((MvPolynomial.C (-6 : ZMod ℓ) : Polynomial ℓ) *
        (MvPolynomial.X 0 : Polynomial ℓ)^2) •
      (MvPolynomial.pderiv (R := ZMod ℓ) (σ := Fin 2) 1))

def operator : Polynomial ℓ →ₗ[ZMod ℓ] Polynomial ℓ :=
  (derivation (ℓ := ℓ)).toLinearMap

@[simp]
theorem operator_apply (P : Polynomial ℓ) :
    operator P =
      ((MvPolynomial.C (-4 : ZMod ℓ) : Polynomial ℓ) * MvPolynomial.X 1) *
          MvPolynomial.pderiv 0 P +
        ((MvPolynomial.C (-6 : ZMod ℓ) : Polynomial ℓ) * (MvPolynomial.X 0)^2) *
          MvPolynomial.pderiv 1 P := by
  simp [operator, derivation, mul_assoc]

@[simp]
theorem operator_X_zero :
    operator (MvPolynomial.X 0 : Polynomial ℓ) =
      (-4 : ZMod ℓ) • MvPolynomial.X 1 := by
  simp [operator_apply, Algebra.smul_def]

@[simp]
theorem operator_X_one :
    operator (MvPolynomial.X 1 : Polynomial ℓ) =
      (-6 : ZMod ℓ) • (MvPolynomial.X 0)^2 := by
  simp [operator_apply, Algebra.smul_def]

theorem operator_leibniz (P Q : Polynomial ℓ) :
    operator (P * Q) = P * operator Q + Q * operator P := by
  exact (derivation (ℓ := ℓ)).leibniz P Q

theorem operator_one : operator (1 : Polynomial ℓ) = 0 := by
  exact (derivation (ℓ := ℓ)).map_one_eq_zero

@[simp]
theorem operator_apply_smul (P : Polynomial ℓ) :
    operator P =
      (-4 : ZMod ℓ) • (MvPolynomial.X 1 * MvPolynomial.pderiv 0 P) +
        (-6 : ZMod ℓ) • ((MvPolynomial.X 0)^2 * MvPolynomial.pderiv 1 P) := by
  rw [operator_apply]
  simp only [Algebra.smul_def, MvPolynomial.C_mul']
  ring

theorem weightedDegree_add_single_zero (m : Fin 2 →₀ ℕ) :
    weightedDegree (m + Finsupp.single 0 1) = weightedDegree m + 4 := by
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

theorem weightedDegree_add_single_one (m : Fin 2 →₀ ℕ) :
    weightedDegree (m + Finsupp.single 1 1) = weightedDegree m + 6 := by
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

theorem weightedDegree_add_two_single_zero (m : Fin 2 →₀ ℕ) :
    weightedDegree (m + Finsupp.single 0 2) = weightedDegree m + 8 := by
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

theorem weightedDegree_first_delta_shift (m : Fin 2 →₀ ℕ) :
    weightedDegree (Finsupp.single 1 1 + m) =
      weightedDegree (m + Finsupp.single 0 1) + 2 := by
  rw [weightedDegree_add_single_zero]
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

theorem weightedDegree_second_delta_shift (m : Fin 2 →₀ ℕ) :
    weightedDegree (Finsupp.single 0 2 + m) =
      weightedDegree (m + Finsupp.single 1 1) + 2 := by
  rw [weightedDegree_add_single_one]
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

theorem weightClass_first_delta_shift (m : Fin 2 →₀ ℕ) :
    weightClass (Finsupp.single 1 1 + m) =
      weightClass (m + Finsupp.single 0 1) + (2 : ZMod (ℓ - 1)) := by
  change (weightedDegree (Finsupp.single 1 1 + m) : ZMod (ℓ - 1)) =
    (weightedDegree (m + Finsupp.single 0 1) : ZMod (ℓ - 1)) + 2
  rw [weightedDegree_first_delta_shift]
  norm_num

theorem weightClass_second_delta_shift (m : Fin 2 →₀ ℕ) :
    weightClass (Finsupp.single 0 2 + m) =
      weightClass (m + Finsupp.single 1 1) + (2 : ZMod (ℓ - 1)) := by
  change (weightedDegree (Finsupp.single 0 2 + m) : ZMod (ℓ - 1)) =
    (weightedDegree (m + Finsupp.single 1 1) : ZMod (ℓ - 1)) + 2
  rw [weightedDegree_second_delta_shift]
  norm_num

theorem pderiv_support_source {i : Fin 2} {P : Polynomial ℓ}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ (MvPolynomial.pderiv i P).support) :
    m + Finsupp.single i 1 ∈ P.support := by
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [MvPolynomial.coeff_pderiv] at hm
  intro hzero
  apply hm
  simp [hzero]

theorem support_X_mul_mem {i : Fin 2} {P : Polynomial ℓ}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ (MvPolynomial.X i * P).support) :
    ∃ n ∈ P.support, m = Finsupp.single i 1 + n := by
  rw [MvPolynomial.support_X_mul] at hm
  obtain ⟨n, hn, hnm⟩ := Finset.mem_map.1 hm
  exact ⟨n, hn, hnm.symm⟩

theorem support_X_sq_mul_mem {P : Polynomial ℓ} {m : Fin 2 →₀ ℕ}
    (hm : m ∈ ((MvPolynomial.X 0)^2 * P).support) :
    ∃ n ∈ P.support, m = Finsupp.single 0 2 + n := by
  have hrewrite : (MvPolynomial.X 0)^2 * P =
      MvPolynomial.X 0 * (MvPolynomial.X 0 * P) := by ring
  rw [hrewrite, MvPolynomial.support_X_mul] at hm
  obtain ⟨n, hn, hnm⟩ := Finset.mem_map.1 hm
  obtain ⟨q, hq, hnq⟩ := support_X_mul_mem hn
  refine ⟨q, hq, ?_⟩
  have hnm' : m = Finsupp.single 0 1 + n := by
    simpa [addLeftEmbedding_apply] using hnm.symm
  rw [hnm', hnq]
  rw [← add_assoc]
  congr 1
  ext j
  fin_cases j <;> simp

theorem operator_homogeneous {k : ZMod (ℓ - 1)}
    (P : ResidueWeightedPolynomial k) :
    ∀ m ∈ (operator P.polynomial).support, weightClass m = k + 2 := by
  intro m hm
  rw [operator_apply_smul] at hm
  have hsum := MvPolynomial.support_add hm
  simp only [Finset.mem_union] at hsum
  rcases hsum with hfirst | hsecond
  · have hfirst' : m ∈ (MvPolynomial.X 1 * MvPolynomial.pderiv 0 P.polynomial).support :=
      MvPolynomial.support_smul hfirst
    obtain ⟨n, hn, hmn⟩ := support_X_mul_mem hfirst'
    have hsource : n + Finsupp.single 0 1 ∈ P.polynomial.support :=
      pderiv_support_source hn
    rw [hmn, weightClass_first_delta_shift, P.homogeneous _ hsource]
  · have hsecond' : m ∈ ((MvPolynomial.X 0)^2 * MvPolynomial.pderiv 1 P.polynomial).support :=
      MvPolynomial.support_smul hsecond
    obtain ⟨n, hn, hmn⟩ := support_X_sq_mul_mem hsecond'
    have hsource : n + Finsupp.single 1 1 ∈ P.polynomial.support :=
      pderiv_support_source hn
    rw [hmn, weightClass_second_delta_shift, P.homogeneous _ hsource]

/-! This is the polynomial divisibility step in Proposition 1.44.  The
unit hypothesis on `C c` is the precise algebraic form of the fact that a
nonzero element of `ZMod ℓ` is invertible. -/

theorem hasse_divisibility_iff
    {A B D P : Polynomial ℓ} {c : ZMod ℓ}
    (hcop : IsCoprime A B) (hc : IsUnit (MvPolynomial.C c : Polynomial ℓ)) :
    A ∣ A * D + MvPolynomial.C c * B * P ↔ c = 0 ∨ A ∣ P := by
  constructor
  · intro hdiv
    by_cases hzero : c = 0
    · exact Or.inl hzero
    · right
      have hA : A ∣ A * D := ⟨D, rfl⟩
      have hscaled : A ∣ MvPolynomial.C c * B * P := by
        have hsum : A ∣ MvPolynomial.C c * B * P + A * D := by
          simpa [add_comm] using hdiv
        exact (dvd_add_left hA).mp hsum
      have hcop' : IsCoprime A (MvPolynomial.C c * B) :=
        (isCoprime_mul_unit_left_right hc A B).2 hcop
      exact hcop'.dvd_of_dvd_mul_left hscaled
  · rintro (rfl | hP)
    · exact ⟨D, by simp⟩
    · obtain ⟨Q, hQ⟩ := hP
      refine ⟨D + MvPolynomial.C c * B * Q, ?_⟩
      rw [hQ]
      ring

theorem isUnit_twelve : IsUnit (12 : ZMod ℓ) := by
  rw [isUnit_iff_ne_zero]
  change ((12 : ℕ) : ZMod ℓ) ≠ 0
  intro hzero
  have hdiv : ℓ ∣ 12 := (ZMod.natCast_eq_zero_iff 12 ℓ).mp hzero
  have hfactor : ℓ ∣ 2 ^ 2 * 3 := by norm_num at hdiv ⊢; exact hdiv
  have hlarge := (inferInstance : isLargePrime ℓ).AtLeastFive
  rcases (inferInstance : isLargePrime ℓ).Prime.dvd_mul.mp hfactor with h2 | h3
  · have h2' : ℓ ∣ 2 := (inferInstance : isLargePrime ℓ).Prime.dvd_of_dvd_pow h2
    have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    omega
  · have h3' : ℓ ∣ 3 := h3
    have hle : ℓ ≤ 3 := Nat.le_of_dvd (by norm_num) h3'
    omega

def operatorPolynomial {k : ZMod (ℓ - 1)}
    (P : ResidueWeightedPolynomial k) :
    ResidueWeightedPolynomial (k + 2) :=
  { polynomial := operator P.polynomial
    homogeneous := operator_homogeneous P }

theorem residueHomogeneous_mul
    {a b : ZMod (ℓ - 1)}
    {P Q : Polynomial ℓ}
    (hP : residueHomogeneous P a) (hQ : residueHomogeneous Q b) :
    residueHomogeneous (P * Q) (a + b) := by
  intro m hm
  have hm' := MvPolynomial.support_mul P Q hm
  rcases Finset.mem_add.mp hm' with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
  rw [← hP m₁ hm₁, ← hQ m₂ hm₂]
  simp [weightClass, weightedDegree, Finsupp.add_apply]
  ring

def numeratorPolynomial {k : ZMod (ℓ - 1)}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ) :
    ResidueWeightedPolynomial (k + 2) :=
  { polynomial := A.polynomial * (operatorPolynomial P).polynomial +
        c • (B.polynomial * P.polynomial)
    homogeneous := by
      intro m hm
      have hm' := MvPolynomial.support_add hm
      rcases Finset.mem_union.mp hm' with hm' | hm'
      · have hmul := residueHomogeneous_mul A.homogeneous
          (operatorPolynomial P).homogeneous m hm'
        simpa [add_zero] using hmul
      · have hmul := residueHomogeneous_mul B.homogeneous P.homogeneous
          m (MvPolynomial.support_smul hm')
        simpa [add_comm, add_left_comm, add_assoc] using hmul }

theorem numeratorPolynomial_homogeneous {k : ZMod (ℓ - 1)}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ) :
    ∀ m ∈ (numeratorPolynomial A B P c).polynomial.support,
      weightClass m = k + 2 := by
  exact (numeratorPolynomial A B P c).homogeneous

theorem numeratorPolynomial_eq
    {k : ZMod (ℓ - 1)}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ) :
    (numeratorPolynomial A B P c).polynomial =
      A.polynomial * operator P.polynomial +
        MvPolynomial.C c * B.polynomial * P.polynomial := by
  simp [numeratorPolynomial, operatorPolynomial, Algebra.smul_def, mul_assoc]

/-! An exact integral lift is stronger than `Exists_reduce`: it records the
integer weight, rather than only its residue class.  This is the precise
interface needed to turn the polynomial calculation into `HasWeight`. -/

def HasExactIntegralReduction (f : ModularFormMod ℓ k) (w : ℤ) : Prop :=
  ∃ g : IntegerModularForm w, g.reduce ℓ = f.fourier

theorem hasWeight_of_exact_integral_reduction
    (f : ModularFormMod ℓ k) (w : ℤ)
    (h : HasExactIntegralReduction f w) :
    HasWeight f w := by
  obtain ⟨g, hg⟩ := h
  change f.fourier ∈ Set.range (@IntegerModularForm.reduce w ℓ)
  exact ⟨g, hg⟩

theorem theta_hasWeight_target_of_exact_integral_reduction
    (f : ModularFormMod ℓ k)
    (h : HasExactIntegralReduction f.Theta (ThetaTargetWeight f)) :
    HasWeight f.Theta (ThetaTargetWeight f) := by
  exact hasWeight_of_exact_integral_reduction f.Theta
    (ThetaTargetWeight f) h

/-! The next two statements isolate the two remaining analytic bridges from
the PDF.  They are deliberately propositions, not axioms: a later file can
prove them from the q-expansion identities for `E₂`, `E₄`, and `E₆` and then
apply the already-proved algebra above. -/

def HasThetaPolynomialIdentity {k : ZMod (ℓ - 1)}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ)
    (f : ModularFormMod ℓ k) : Prop :=
  evalResiduePolynomial P = f ∧
    evalResiduePolynomial (numeratorPolynomial A B P c) = f.Theta

def HasThetaExactLift (f : ModularFormMod ℓ k) : Prop :=
  HasExactIntegralReduction f.Theta (ThetaTargetWeight f)

theorem theta_hasWeight_target_of_theta_exact_lift
    (f : ModularFormMod ℓ k) (h : HasThetaExactLift f) :
    HasWeight f.Theta (ThetaTargetWeight f) := by
  exact theta_hasWeight_target_of_exact_integral_reduction f h

def HasThetaRamanujanIdentity {k : ZMod (ℓ - 1)}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ)
    (f : ModularFormMod ℓ k) : Prop :=
  evalResiduePolynomial P = f ∧
    (12 : ZMod ℓ) • f.Theta.fourier =
      (evalResiduePolynomial (numeratorPolynomial A B P c)).fourier

def HasExactNumeratorLift {k : ZMod (ℓ - 1)}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ)
    (f : ModularFormMod ℓ k) : Prop :=
  ∃ g : IntegerModularForm (ThetaTargetWeight f),
    g.reduce ℓ =
      (evalResiduePolynomial (numeratorPolynomial A B P c)).fourier

theorem theta_hasExactIntegralReduction_of_ramanujan_identity
    (f : ModularFormMod ℓ k)
    {A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))}
    {B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1))}
    {P : ResidueWeightedPolynomial k} {c : ZMod ℓ}
    (hidentity : HasThetaRamanujanIdentity A B P c f)
    (hlift : HasExactNumeratorLift A B P c f)
    (h12 : IsUnit (12 : ZMod ℓ)) :
    HasExactIntegralReduction f.Theta (ThetaTargetWeight f) := by
  obtain ⟨g, hg⟩ := hlift
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective ((12 : ZMod ℓ)⁻¹)
  refine ⟨a • g, ?_⟩
  rcases hidentity with ⟨hP, htheta⟩
  calc
    (a • g).reduce ℓ = a • g.reduce ℓ := by
      exact (IntegerModularForm.reduce ℓ).map_smul a g
    _ = a • (evalResiduePolynomial (numeratorPolynomial A B P c)).fourier := by
      rw [hg]
    _ = a • ((12 : ZMod ℓ) • f.Theta.fourier) := by
      rw [htheta]
    _ = f.Theta.fourier := by
      rw [← Int.cast_smul_eq_zsmul (ZMod ℓ), smul_smul, ha]
      simp [h12.ne_zero]

theorem filtration_cast_zero_iff_prime_divides
    (f : ModularFormMod ℓ k) :
    (f.Filtration : ZMod ℓ) = 0 ↔ PrimeDividesFiltration f := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

theorem theta_hasLowerWeight_iff_of_drop_criterion
    (f : ModularFormMod ℓ k)
    (hdrop : HasLowerWeight f.Theta (ThetaTargetWeight f) ↔
      (f.Filtration : ZMod ℓ) = 0) :
    HasLowerWeight f.Theta (ThetaTargetWeight f) ↔
      PrimeDividesFiltration f := by
  rw [hdrop, filtration_cast_zero_iff_prime_divides]

end FiltrationTheta.DelOperator
