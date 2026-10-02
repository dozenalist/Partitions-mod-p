import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.DelOperator

open ModularFormMod
open EisensteinSeries

noncomputable section

namespace FiltrationTheta

open DelOperator
open IntegerModularForm

variable {ℓ : ℕ} [isLargePrime ℓ]
variable {k : ZMod (ℓ - 1)}

/-!
## Exact integral lifts of homogeneous residue polynomials

`residuePolynomial_has_integral_lift` lifts coefficients, but it forgets the
integer weight.  The following construction keeps that weight whenever the
support of the residue polynomial is homogeneous for an integer weight.
-/

noncomputable def intRepresentative (a : ZMod ℓ) : ℤ :=
  Classical.choose (ZMod.intCast_surjective a)

theorem intRepresentative_cast (a : ZMod ℓ) :
    (intRepresentative (ℓ := ℓ) a : ZMod ℓ) = a := by
  exact Classical.choose_spec (ZMod.intCast_surjective a)

def ExactWeightedSupport (P : ResidueWeightedPolynomial k) (w : ℤ) : Prop :=
  ∀ m ∈ P.polynomial.support, weightedDegree m = w

noncomputable def exactIntegralLift
    (P : ResidueWeightedPolynomial k) (w : ℤ)
    (hP : ExactWeightedSupport P w) : IntegerModularForm w :=
  ∑ m : P.polynomial.support,
    intRepresentative (ℓ := ℓ) (P.polynomial.coeff m.1) •
      (integralMonomial m.1).Icast (hP m.1 m.2)

theorem exactIntegralLift_reduce
    (P : ResidueWeightedPolynomial k) (w : ℤ)
    (hP : ExactWeightedSupport P w) :
    (exactIntegralLift P w hP).reduce ℓ =
      (evalResiduePolynomial P).fourier := by
  classical
  unfold exactIntegralLift evalResiduePolynomial
  simp only [map_sum, map_smul, IntegerModularForm.reduce_Icast,
    IntegerModularForm.reduce_apply, IntegerModularForm.fourier_zsmul]
  change _ = ModularFormMod.fourierAddHom
    (∑ m : P.polynomial.support,
      P.polynomial.coeff m.1 •
        (modularMonomial m.1).Mcast (P.homogeneous m.1 m.2))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [ModularFormMod.fourierAddHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, ModularFormMod.fourier_smul,
    ModularFormMod.fourier_Mcast]
  have hcast := intRepresentative_cast (ℓ := ℓ)
    (P.polynomial.coeff m.1)
  calc
    intRepresentative (ℓ := ℓ) (P.polynomial.coeff m.1) •
        (integralMonomial m.1).reduce ℓ =
      (intRepresentative (ℓ := ℓ) (P.polynomial.coeff m.1) : ZMod ℓ) •
        (integralMonomial m.1).reduce ℓ := by
          simp only [Int.cast_smul_eq_zsmul]
    _ = P.polynomial.coeff m.1 •
        (integralMonomial m.1).reduce ℓ := by rw [hcast]
    _ = _ := by rfl

theorem hasExactIntegralReduction_of_exactWeightedSupport
    (P : ResidueWeightedPolynomial k) (w : ℤ)
    (hkw : k = (w : ZMod (ℓ - 1)))
    (hP : ExactWeightedSupport P w) :
    HasExactIntegralReduction ((evalResiduePolynomial P).Mcast hkw) w := by
  refine ⟨exactIntegralLift P w hP, ?_⟩
  exact exactIntegralLift_reduce P w hP

/-! The polynomial operator raises the *integer* weighted degree by two. -/

theorem operator_weighted_homogeneous {w : ℤ}
    (P : ResidueWeightedPolynomial k)
    (hP : ExactWeightedSupport P w) :
    ∀ m ∈ (operator P.polynomial).support,
      weightedDegree m = w + 2 := by
  intro m hm
  rw [operator_apply_smul] at hm
  have hsum := MvPolynomial.support_add hm
  simp only [Finset.mem_union] at hsum
  rcases hsum with hfirst | hsecond
  · have hfirst' : m ∈
        (MvPolynomial.X 1 * MvPolynomial.pderiv 0 P.polynomial).support :=
      MvPolynomial.support_smul hfirst
    obtain ⟨n, hn, hmn⟩ := support_X_mul_mem hfirst'
    have hsource : n + Finsupp.single 0 1 ∈ P.polynomial.support :=
      pderiv_support_source hn
    rw [hmn, weightedDegree_first_delta_shift]
    rw [hP _ hsource]
  · have hsecond' : m ∈
        ((MvPolynomial.X 0)^2 * MvPolynomial.pderiv 1 P.polynomial).support :=
      MvPolynomial.support_smul hsecond
    obtain ⟨n, hn, hmn⟩ := support_X_sq_mul_mem hsecond'
    have hsource : n + Finsupp.single 1 1 ∈ P.polynomial.support :=
      pderiv_support_source hn
    rw [hmn, weightedDegree_second_delta_shift]
    rw [hP _ hsource]

theorem numerator_weighted_homogeneous {a b w : ℤ}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ)
    (hA : ExactWeightedSupport A a)
    (hB : ExactWeightedSupport B b)
    (hP : ExactWeightedSupport P w)
    (ha : a + 2 = b) :
    ExactWeightedSupport (numeratorPolynomial A B P c) (w + a + 2) := by
  intro m hm
  have hm' := MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hm' with hm' | hm'
  · have hmul := MvPolynomial.support_mul A.polynomial
        (operator P.polynomial) hm'
    rcases Finset.mem_add.mp hmul with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
    have hA' := hA m₁ hm₁
    have hOp := operator_weighted_homogeneous P hP m₂ hm₂
    calc
      weightedDegree (m₁ + m₂) = weightedDegree m₁ + weightedDegree m₂ := by
        simp [weightedDegree, Finsupp.add_apply]
        ring
      _ = a + (w + 2) := by rw [hA', hOp]
      _ = w + a + 2 := by ring
  · have hm'' := MvPolynomial.support_mul B.polynomial P.polynomial
      (MvPolynomial.support_smul hm')
    rcases Finset.mem_add.mp hm'' with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
    have hB' := hB m₁ hm₁
    have hP' := hP m₂ hm₂
    calc
      weightedDegree (m₁ + m₂) = weightedDegree m₁ + weightedDegree m₂ := by
        simp [weightedDegree, Finsupp.add_apply]
        ring
      _ = b + w := by rw [hB', hP']
      _ = w + a + 2 := by rw [← ha]; ring

theorem hasExactNumeratorLift_of_exactWeightedSupport
    {a b w : ℤ}
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ)
    (hA : ExactWeightedSupport A a)
    (hB : ExactWeightedSupport B b)
    (hP : ExactWeightedSupport P w)
    (ha : a + 2 = b) :
    ∃ g : IntegerModularForm (w + a + 2),
      g.reduce ℓ = (evalResiduePolynomial (numeratorPolynomial A B P c)).fourier := by
  let hN := numerator_weighted_homogeneous A B P c hA hB hP ha
  refine ⟨exactIntegralLift (numeratorPolynomial A B P c) (w + a + 2) hN, ?_⟩
  exact exactIntegralLift_reduce (numeratorPolynomial A B P c) (w + a + 2) hN

end FiltrationTheta
