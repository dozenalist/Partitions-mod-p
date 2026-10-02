import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.ThetaOperator.DelOperator
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.FiltrationTheta.ExactLift
import Mathlib.Algebra.Squarefree.Basic

open IntegerModularForm ModularFormMod

noncomputable section

namespace ThetaOperator

open FiltrationTheta

variable {ℓ : ℕ} [isLargePrime ℓ]

/-!
# Definition 1.38 and Theorems 1.39--1.41

The paper writes the coefficient ring as `ℤ_(p)`.  In this project the
coefficient-level statements are expressed over `ZMod ℓ`, while the weights
are retained as integers through `ExactWeightedSupport`.  The two forms in
Definition 1.38 are therefore represented by residue-homogeneous polynomials
whose supports have the indicated exact integral weights.
-/

def hasseForm (ℓ : ℕ) [isLargePrime ℓ] : ModularFormMod ℓ 0 := by
  have hcast : (((ℓ - 1 : ℕ) : ℤ) : ZMod (ℓ - 1)) = 0 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_self _
  exact ((IntegerModularForm.El ℓ).Reduce ℓ).Mcast hcast

def eisLPlusOneForm (ℓ : ℕ) [isLargePrime ℓ] :
    ModularFormMod ℓ (2 : ZMod (ℓ - 1)) :=
  E₂ (ℓ := ℓ)

abbrev Polynomial (ℓ : ℕ) := MvPolynomial (Fin 2) (ZMod ℓ)

/-! This is the polynomial form of the del operator already used in the
theta argument: `∂X = -4Y` and `∂Y = -6X²`. -/

abbrev delPolynomial : Polynomial ℓ →ₗ[ZMod ℓ] Polynomial ℓ :=
  FiltrationTheta.DelOperator.operator

def delResiduePolynomial {k : ZMod (ℓ - 1)}
    (P : ResidueWeightedPolynomial k) :
    ResidueWeightedPolynomial (k + 2) :=
  { polynomial := delPolynomial P.polynomial
    homogeneous := FiltrationTheta.DelOperator.operator_homogeneous P }

theorem delResiduePolynomial_exactWeightedSupport
    {k : ZMod (ℓ - 1)} {w : ℤ}
    (P : ResidueWeightedPolynomial k)
    (hP : ExactWeightedSupport P w) :
    ExactWeightedSupport (delResiduePolynomial P) (w + 2) := by
  intro m hm
  simpa [delResiduePolynomial, delPolynomial] using
    (FiltrationTheta.operator_weighted_homogeneous P hP m hm)

def Definition138Pair
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)))
    (B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1))) : Prop :=
  ExactWeightedSupport A ((ℓ : ℤ) - 1) ∧
    ExactWeightedSupport B ((ℓ : ℤ) + 1) ∧
      evalResiduePolynomial A = hasseForm ℓ ∧
        evalResiduePolynomial B = eisLPlusOneForm ℓ

/-! Definition 1.38, with uniqueness stated for the chosen exact-weight
representatives. -/

theorem definition_1_38 :
    ∃! p : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)) ×
        ResidueWeightedPolynomial (2 : ZMod (ℓ - 1)),
      Definition138Pair p.1 p.2 := by
  sorry

/-! Lemma 1.39. -/

theorem theorem_1_39
    {A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))}
    {B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1))}
    (hAB : Definition138Pair A B) :
    delPolynomial A.polynomial = B.polynomial ∧
      delPolynomial B.polynomial =
        -(MvPolynomial.X 0 * A.polynomial) := by
  sorry

/-! Lemma 1.40. -/

theorem theorem_1_40
    {A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))}
    {B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1))}
    (hAB : Definition138Pair A B) :
    Squarefree A.polynomial ∧ IsCoprime A.polynomial B.polynomial := by
  sorry

def Theorem141Statement
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))) : Prop :=
  (∀ k (f : ModularFormMod ℓ k),
    ∃ P : ResidueWeightedPolynomial k, evalResiduePolynomial P = f) ∧
    (∀ k (P Q : ResidueWeightedPolynomial k),
      evalResiduePolynomial P = evalResiduePolynomial Q ↔
        P.polynomial - Q.polynomial ∈
          Ideal.span {A.polynomial - MvPolynomial.C 1})

/-! Theorem 1.41, in the componentwise graded form used by this project. -/

theorem theorem_1_41
    {A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))}
    {B : ResidueWeightedPolynomial (2 : ZMod (ℓ - 1))}
    (hAB : Definition138Pair A B) :
    Theorem141Statement A := by
  sorry

end ThetaOperator
