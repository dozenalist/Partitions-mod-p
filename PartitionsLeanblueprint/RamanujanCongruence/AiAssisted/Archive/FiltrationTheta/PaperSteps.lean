import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.FiltrationTheta.ExactLift

open ModularFormMod
open EisensteinSeries

noncomputable section

namespace FiltrationTheta

open DelOperator

variable {ℓ : ℕ} [isLargePrime ℓ]
variable {k : ZMod (ℓ - 1)}

/-!
## The two certificates used in the proof of Proposition 1.44

The proof in the paper has two logically separate inputs.  The first is the
Ramanujan identity together with an integral lift of its numerator.  The
second is the graded statement that divisibility by the Hasse polynomial is
equivalent to a drop in filtration.  These structures are explicit data; no
class instance hides either assumption.
-/

structure ThetaRamanujanCertificate (f : ModularFormMod ℓ k) where
  A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))
  B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1))
  P : ResidueWeightedPolynomial k
  c : ZMod ℓ
  hA : ExactWeightedSupport A ((ℓ : ℤ) - 1)
  hB : ExactWeightedSupport B ((ℓ : ℤ) + 1)
  hP : ExactWeightedSupport P f.Filtration
  identity : HasThetaRamanujanIdentity A B P c f

structure ThetaDropCertificate (f : ModularFormMod ℓ k) : Prop where
  drop : HasLowerWeight f.Theta (ThetaTargetWeight f) ↔
      (f.Filtration : ZMod ℓ) = 0

/-! ## Explicit interfaces for the remaining analytic arguments

These are deliberately stated as theorems with visible hypotheses and
conclusions.  They are the four facts supplied by the analytic part of the
paper; the algebraic consequences below do not hide them in a typeclass. -/

/-- The exact integral lift of the theta form at the target weight. -/
theorem paper_exact_theta_lift
    (f : ModularFormMod ℓ k) :
    ∃ g : IntegerModularForm (ThetaTargetWeight f),
      g.reduce ℓ = f.Theta.fourier := by
  sorry

/-- A representative of `f` whose monomials all have its exact integral
filtration as weighted degree. -/
theorem paper_exact_residue_representative
    (f : ModularFormMod ℓ k) :
    ∃ P : ResidueWeightedPolynomial k,
      ExactWeightedSupport P f.Filtration ∧
        evalResiduePolynomial P = f := by
  sorry

/-- The reduced Ramanujan identity for an exact representative. -/
theorem paper_ramanujan_identity
    (f : ModularFormMod ℓ k)
    (P : ResidueWeightedPolynomial k)
    (hP : ExactWeightedSupport P f.Filtration)
    (hPf : evalResiduePolynomial P = f) :
    ∃ (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
      (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
      (c : ZMod ℓ),
      ExactWeightedSupport A ((ℓ : ℤ) - 1) ∧
        ExactWeightedSupport B ((ℓ : ℤ) + 1) ∧
          HasThetaRamanujanIdentity A B P c f := by
  sorry

/-- The Hasse-kernel statement together with the filtration-drop criterion. -/
theorem paper_hasse_kernel_and_theta_drop
    (f : ModularFormMod ℓ k) :
    (∀ (A : HassePolynomialData (ℓ := ℓ))
      (j : ZMod (ℓ - 1)) (P Q : ResidueWeightedPolynomial j),
      evalResiduePolynomial P = evalResiduePolynomial Q ↔
        P.polynomial - Q.polynomial ∈ HasseIdeal A) ∧
      (HasLowerWeight f.Theta (ThetaTargetWeight f) ↔
        (f.Filtration : ZMod ℓ) = 0) := by
  sorry

theorem numerator_lift_of_exact_support
    (f : ModularFormMod ℓ k)
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)))
    (P : ResidueWeightedPolynomial k) (c : ZMod ℓ)
    (hA : ExactWeightedSupport A ((ℓ : ℤ) - 1))
    (hB : ExactWeightedSupport B ((ℓ : ℤ) + 1))
    (hP : ExactWeightedSupport P f.Filtration) :
    HasExactNumeratorLift A B P c f := by
  have ha : ((ℓ : ℤ) - 1) + 2 = (ℓ : ℤ) + 1 := by ring
  let hN := numerator_weighted_homogeneous A B P c hA hB hP ha
  have hN' : ExactWeightedSupport (numeratorPolynomial A B P c)
      (f.Filtration + ((ℓ : ℤ) + 1)) := by
    convert hN using 1 <;> ring
  refine ⟨exactIntegralLift (numeratorPolynomial A B P c)
      (f.Filtration + ((ℓ : ℤ) + 1)) hN', ?_⟩
  exact exactIntegralLift_reduce (numeratorPolynomial A B P c)
    (f.Filtration + ((ℓ : ℤ) + 1)) hN'

theorem theta_hasWeight_target_of_certificate
    (f : ModularFormMod ℓ k)
    (hcert : ThetaRamanujanCertificate f) :
    HasWeight f.Theta (ThetaTargetWeight f) := by
  apply theta_hasWeight_target_of_exact_integral_reduction f
  exact theta_hasExactIntegralReduction_of_ramanujan_identity f
    hcert.identity
    (numerator_lift_of_exact_support f hcert.A hcert.B hcert.P hcert.c
      hcert.hA hcert.hB hcert.hP)
    isUnit_twelve

theorem theta_hasLowerWeight_iff_prime_divides_of_certificate
    (f : ModularFormMod ℓ k)
    (hcert : ThetaDropCertificate f) :
    HasLowerWeight f.Theta (ThetaTargetWeight f) ↔
      PrimeDividesFiltration f := by
  exact theta_hasLowerWeight_iff_of_drop_criterion f hcert.drop

end FiltrationTheta
