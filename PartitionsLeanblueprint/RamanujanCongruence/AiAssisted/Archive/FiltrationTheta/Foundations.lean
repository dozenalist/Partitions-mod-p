import PartitionsLeanblueprint.RamanujanCongruence.PreliminaryResults
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.MaximalReduce
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Filtration and the theta operator

This file formalizes Proposition 1.44 from the attached notes.  The notes use
the presentation

`𝔽ₚ[X, Y] / (A - 1)`

of modular forms modulo `ℓ`, where `A` is the Hasse polynomial.  The present
development represents a modular form by its Fourier expansion and defines
`Filtration` through `ModularFormMod.hasWeight`.  The definitions below are
the corresponding Fourier-expansion formulation of the notions used in the
paper; the two remaining theorem statements are the two parts of Proposition
1.44.
-/

open ModularFormMod
open EisensteinSeries

noncomputable section

namespace FiltrationTheta

variable {ℓ : ℕ} [isLargePrime ℓ]
variable {k : ZMod (ℓ - 1)}

/-! ## Integral generators and their reductions -/

open IntegerModularForm

/-- The weight of the monomial `X^m₀ Y^m₁`, using the weights `4` and `6`.

This is an integer-valued definition because the integral modular forms in the
project are indexed by `ℤ`.  No localization such as `ℤ_(ℓ)` is used. -/
def weightedDegree (m : Fin 2 →₀ ℕ) : ℤ :=
  4 * (m 0 : ℤ) + 6 * (m 1 : ℤ)

/-- The integral modular form obtained by evaluating a weighted monomial at
`E₄` and `E₆`. -/
noncomputable def integralMonomial (m : Fin 2 →₀ ℕ) :
    IntegerModularForm (weightedDegree m) := by
  let g := (Eis 4).pow (m 0)
  let h := (Eis 6).pow (m 1)
  exact Icast (by
    dsimp [g, h, weightedDegree]
    push_cast
    ring) (g.mul h)

theorem integralMonomial_zero :
    integralMonomial (0 : Fin 2 →₀ ℕ) =
      (1 : IntegerModularForm 0).Icast (by
        change (0 : ℤ) = weightedDegree 0
        simp [weightedDegree]) := by
  ext n
  simp [integralMonomial, IntegerModularForm.mul, IntegerModularForm.Icast,
    IntegerModularForm.const, weightedDegree]
  rfl

/-- A polynomial over `ℤ` supported in one weighted degree. -/
structure IntegralWeightedPolynomial (w : ℤ) where
  polynomial : MvPolynomial (Fin 2) ℤ
  homogeneous : ∀ m ∈ polynomial.support, weightedDegree m = w

/-- Evaluation of an integral weighted polynomial at the integral forms
`E₄` and `E₆`. -/
noncomputable def evalIntegralPolynomial {w : ℤ}
    (P : IntegralWeightedPolynomial w) : IntegerModularForm w :=
  ∑ m : P.polynomial.support,
    P.polynomial.coeff m •
      (integralMonomial m.1).Icast (P.homogeneous m.1 m.2)

/-- The residue class of a monomial's weight modulo `ℓ - 1`. -/
def weightClass (m : Fin 2 →₀ ℕ) : ZMod (ℓ - 1) :=
  (weightedDegree m : ZMod (ℓ - 1))

/-- A polynomial over `𝔽_ℓ` supported in one weight class. -/
structure ResidueWeightedPolynomial (k : ZMod (ℓ - 1)) where
  polynomial : MvPolynomial (Fin 2) (ZMod ℓ)
  homogeneous : ∀ m ∈ polynomial.support, weightClass m = k

/-- Reduction of an integral monomial to a modular form modulo `ℓ`. -/
noncomputable def modularMonomial (m : Fin 2 →₀ ℕ) :
    ModularFormMod ℓ (weightClass m) :=
  (integralMonomial m).Reduce ℓ

theorem modularMonomial_zero :
    modularMonomial (0 : Fin 2 →₀ ℕ) =
      (1 : ModularFormMod ℓ 0).Mcast (by
        change 0 = ((4 * (0 : ℤ) + 6 * (0 : ℤ) : ℤ) : ZMod (ℓ - 1))
        norm_num) := by
  rw [modularMonomial, integralMonomial_zero]
  rw [IntegerModularForm.Reduce_Icast]
  ext n
  simp [ModularFormMod.coeff_def, ModularFormMod.Mcast,
    ModularFormMod.one_def, ModularFormMod.fourier_const,
    ModularFormMod.const, PowerSeries.coeff_C]
  change (if n = 0 then (1 : ZMod ℓ) else 0) =
    (1 : PowerSeries (ZMod ℓ)).coeff n
  simp

/-- Evaluation of a residue-homogeneous polynomial at the reductions of
`E₄` and `E₆`. -/
noncomputable def evalResiduePolynomial {k : ZMod (ℓ - 1)}
    (P : ResidueWeightedPolynomial k) : ModularFormMod ℓ k :=
  ∑ m : P.polynomial.support,
    P.polynomial.coeff m •
      (modularMonomial m.1).Mcast (P.homogeneous m.1 m.2)

noncomputable def residueMonomialEval (m : Fin 2 →₀ ℕ) (a : ZMod ℓ) :
    ModularFormMod ℓ k :=
  if h : weightClass m = k then
    a • (modularMonomial m).Mcast h
  else 0

theorem evalResiduePolynomial_eq_finsupp_sum
    (P : ResidueWeightedPolynomial k) :
    evalResiduePolynomial P =
      (AddMonoidAlgebra.coeff P.polynomial).sum
        (residueMonomialEval (k := k)) := by
  classical
  unfold evalResiduePolynomial
  rw [MvPolynomial.sum_def]
  conv_rhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp [residueMonomialEval]
  rw [dif_pos (P.homogeneous m.1 m.2)]

theorem evalResiduePolynomial_eq_of_polynomial_eq
    (P Q : ResidueWeightedPolynomial k)
    (h : P.polynomial = Q.polynomial) :
    evalResiduePolynomial P = evalResiduePolynomial Q := by
  cases P with
  | mk pp hp =>
    cases Q with
    | mk qq hq =>
      dsimp at h ⊢
      subst qq
      rfl

theorem residueMonomialEval_zero (m : Fin 2 →₀ ℕ) :
    residueMonomialEval (k := k) m 0 = 0 := by
  classical
  simp [residueMonomialEval]

theorem residueMonomialEval_add (m : Fin 2 →₀ ℕ) (a b : ZMod ℓ) :
    residueMonomialEval (k := k) m (a + b) =
      residueMonomialEval (k := k) m a +
        residueMonomialEval (k := k) m b := by
  classical
  by_cases h : weightClass m = k <;>
    simp [residueMonomialEval, h, add_smul]

theorem evalResiduePolynomial_add
    (P Q : ResidueWeightedPolynomial k) :
    ∃ R : ResidueWeightedPolynomial k,
      evalResiduePolynomial R =
        evalResiduePolynomial P + evalResiduePolynomial Q := by
  classical
  let R : ResidueWeightedPolynomial k :=
    { polynomial := P.polynomial + Q.polynomial
      homogeneous := by
        intro m hm
        have hm' := MvPolynomial.support_add hm
        rcases Finset.mem_union.mp hm' with hm' | hm'
        · exact P.homogeneous m hm'
        · exact Q.homogeneous m hm' }
  refine ⟨R, ?_⟩
  rw [evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum]
  change
    (AddMonoidAlgebra.coeff P.polynomial +
        AddMonoidAlgebra.coeff Q.polynomial).sum
        (residueMonomialEval (k := k)) =
      (AddMonoidAlgebra.coeff P.polynomial).sum
          (residueMonomialEval (k := k)) +
        (AddMonoidAlgebra.coeff Q.polynomial).sum
          (residueMonomialEval (k := k))
  rw [Finsupp.sum_add_index]
  · intro m hm
    exact residueMonomialEval_zero m
  · intro m hm
    exact residueMonomialEval_add m

theorem evalResiduePolynomial_add_poly
    (P Q : ResidueWeightedPolynomial k) :
    evalResiduePolynomial
        { polynomial := P.polynomial + Q.polynomial
          homogeneous := by
            intro m hm
            have hm' := MvPolynomial.support_add hm
            rcases Finset.mem_union.mp hm' with hm' | hm'
            · exact P.homogeneous m hm'
            · exact Q.homogeneous m hm' } =
      evalResiduePolynomial P + evalResiduePolynomial Q := by
  classical
  rw [evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum]
  change
    (AddMonoidAlgebra.coeff P.polynomial +
        AddMonoidAlgebra.coeff Q.polynomial).sum
        (residueMonomialEval (k := k)) =
      (AddMonoidAlgebra.coeff P.polynomial).sum
          (residueMonomialEval (k := k)) +
        (AddMonoidAlgebra.coeff Q.polynomial).sum
          (residueMonomialEval (k := k))
  rw [Finsupp.sum_add_index]
  · intro m hm
    exact residueMonomialEval_zero m
  · intro m hm
    exact residueMonomialEval_add m

theorem evalResiduePolynomial_smul
    (a : ZMod ℓ) (P : ResidueWeightedPolynomial k) :
    ∃ R : ResidueWeightedPolynomial k,
      evalResiduePolynomial R = a • evalResiduePolynomial P := by
  classical
  let R : ResidueWeightedPolynomial k :=
    { polynomial := a • P.polynomial
      homogeneous := by
        intro m hm
        have hm' := MvPolynomial.support_smul hm
        exact P.homogeneous m hm' }
  refine ⟨R, ?_⟩
  rw [evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum]
  change
    (a • AddMonoidAlgebra.coeff P.polynomial).sum
        (residueMonomialEval (k := k)) =
      a • (AddMonoidAlgebra.coeff P.polynomial).sum
        (residueMonomialEval (k := k))
  rw [Finsupp.sum_smul_index (fun m => residueMonomialEval_zero m)]
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro m hm
  by_cases h : weightClass m = k <;>
    simp [residueMonomialEval, h, smul_smul]

theorem evalResiduePolynomial_smul_poly
    (a : ZMod ℓ) (P : ResidueWeightedPolynomial k) :
    evalResiduePolynomial
        { polynomial := a • P.polynomial
          homogeneous := by
            intro m hm
            exact P.homogeneous m (MvPolynomial.support_smul hm) } =
      a • evalResiduePolynomial P := by
  rw [evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum]
  change
    (a • AddMonoidAlgebra.coeff P.polynomial).sum
        (residueMonomialEval (k := k)) =
      a • (AddMonoidAlgebra.coeff P.polynomial).sum
        (residueMonomialEval (k := k))
  rw [Finsupp.sum_smul_index (fun m => residueMonomialEval_zero m)]
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro m hm
  by_cases h : weightClass m = k <;>
    simp [residueMonomialEval, h, smul_smul]

def residuePolynomialSub
    (P Q : ResidueWeightedPolynomial k) : ResidueWeightedPolynomial k :=
  { polynomial := P.polynomial - Q.polynomial
    homogeneous := by
      intro m hm
      rw [MvPolynomial.mem_support_iff] at hm
      by_cases hP : P.polynomial.coeff m = 0
      · have hQ : Q.polynomial.coeff m ≠ 0 := by
          intro hQ
          apply hm
          simp [MvPolynomial.coeff_sub, hP, hQ]
        exact Q.homogeneous m (MvPolynomial.mem_support_iff.mpr hQ)
      · exact P.homogeneous m (MvPolynomial.mem_support_iff.mpr hP) }

theorem evalResiduePolynomial_sub_poly
    (P Q : ResidueWeightedPolynomial k) :
    evalResiduePolynomial (residuePolynomialSub P Q) =
      evalResiduePolynomial P - evalResiduePolynomial Q := by
  rw [evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum]
  change
    (AddMonoidAlgebra.coeff P.polynomial -
        AddMonoidAlgebra.coeff Q.polynomial).sum
        (residueMonomialEval (k := k)) =
      (AddMonoidAlgebra.coeff P.polynomial).sum
          (residueMonomialEval (k := k)) -
        (AddMonoidAlgebra.coeff Q.polynomial).sum
          (residueMonomialEval (k := k))
  rw [Finsupp.sum_sub_index]
  intro m a b
  by_cases h : weightClass m = k <;>
    simp [residueMonomialEval, h, sub_smul]

theorem evalResiduePolynomial_monomial
    (m : Fin 2 →₀ ℕ) (a : ZMod ℓ) (h : weightClass m = k) :
    let P : ResidueWeightedPolynomial k :=
      { polynomial := MvPolynomial.monomial m a
        homogeneous := by
          classical
          by_cases ha : a = 0
          · simp [ha]
          · intro n hn
            rw [MvPolynomial.support_monomial, if_neg ha] at hn
            have hnm : n = m := by simpa using hn
            rw [hnm]
            exact h }
    evalResiduePolynomial P = a • (modularMonomial m).Mcast h := by
  classical
  dsimp
  by_cases ha : a = 0
  · simp [evalResiduePolynomial, ha]
  · simp only [evalResiduePolynomial]
    have hm : m ∈ (MvPolynomial.monomial m a).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial]
      simp [ha]
    rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp [MvPolynomial.coeff_monomial, h]
    · intro b hb hne
      have hbm : (b : Fin 2 →₀ ℕ) ≠ m := by
        intro hbm
        exact hne (Subtype.ext hbm)
      have hmb : ¬m = (b : Fin 2 →₀ ℕ) := fun hmb => hbm hmb.symm
      simp [MvPolynomial.coeff_monomial, hmb]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim

theorem modularMonomial_add (m n : Fin 2 →₀ ℕ) :
    (modularMonomial (ℓ := ℓ) m).mul (modularMonomial (ℓ := ℓ) n) =
      (modularMonomial (ℓ := ℓ) (m + n)).Mcast (by
        simp [weightClass, weightedDegree, Finsupp.add_apply]
        ring) := by
  apply ModularFormMod.fourier_inj
  change (integralMonomial m).reduce ℓ * (integralMonomial n).reduce ℓ =
    (integralMonomial (m + n)).reduce ℓ
  simp only [IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk]
  simp [integralMonomial, IntegerModularForm.Icast, weightedDegree,
    Finsupp.add_apply, pow_add, mul_assoc, mul_left_comm, mul_comm]

def residueHomogeneous (p : MvPolynomial (Fin 2) (ZMod ℓ))
    (k : ZMod (ℓ - 1)) : Prop :=
  ∀ m ∈ p.support, weightClass m = k

theorem evalResiduePolynomial_zero :
    ∃ P : ResidueWeightedPolynomial k, evalResiduePolynomial P = 0 := by
  let P : ResidueWeightedPolynomial k :=
    { polynomial := 0
      homogeneous := by simp }
  refine ⟨P, ?_⟩
  simp [P, evalResiduePolynomial]

theorem evalResiduePolynomial_monomial_mul
    {j : ZMod (ℓ - 1)} (m n : Fin 2 →₀ ℕ) (a b : ZMod ℓ)
    (hm : weightClass m = k) (hn : weightClass n = j) :
    ∃ R : ResidueWeightedPolynomial (k + j),
      evalResiduePolynomial R =
        (a • (modularMonomial m).Mcast hm).mul
          (b • (modularMonomial n).Mcast hn) := by
  by_cases ha : a = 0
  · subst a
    obtain ⟨R, hR⟩ := evalResiduePolynomial_zero (k := k + j)
    refine ⟨R, ?_⟩
    rw [hR]
    simp
  by_cases hb : b = 0
  · subst b
    obtain ⟨R, hR⟩ := evalResiduePolynomial_zero (k := k + j)
    refine ⟨R, ?_⟩
    rw [hR]
    simp
  let hmn : weightClass (ℓ := ℓ) m + weightClass (ℓ := ℓ) n =
      weightClass (ℓ := ℓ) (m + n) := by
    simp [weightClass, weightedDegree, Finsupp.add_apply]
    ring
  let R : ResidueWeightedPolynomial (k + j) :=
    { polynomial := MvPolynomial.monomial (m + n) (a * b)
      homogeneous := by
        intro r hr
        rw [MvPolynomial.support_monomial, if_neg (mul_ne_zero ha hb)] at hr
        have hr' : r = m + n := by simpa using hr
        rw [hr']
        rw [← hmn, hm, hn] }
  refine ⟨R, ?_⟩
  rw [evalResiduePolynomial_monomial]
  apply ModularFormMod.fourier_inj
  change
    ((a * b) • (modularMonomial (m + n)).Mcast (by
        rw [← hmn, hm, hn])).fourier =
      ((a • (modularMonomial m).Mcast hm).mul
        (b • (modularMonomial n).Mcast hn)).fourier
  have hmul := congrArg ModularFormMod.fourier
    (modularMonomial_add (ℓ := ℓ) m n)
  simp only [ModularFormMod.fourier_mul, ModularFormMod.fourier_smul,
    ModularFormMod.fourier_Mcast] at hmul ⊢
  rw [← hmul]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem evalResiduePolynomial_monomial_mul_polynomial
    {j : ZMod (ℓ - 1)} (m : Fin 2 →₀ ℕ) (a : ZMod ℓ)
    (hm : weightClass m = k) (Q : ResidueWeightedPolynomial j) :
    ∃ R : ResidueWeightedPolynomial (k + j),
      evalResiduePolynomial R =
        (a • (modularMonomial m).Mcast hm).mul
          (evalResiduePolynomial Q) := by
  classical
  let motive : MvPolynomial (Fin 2) (ZMod ℓ) → Prop := fun q =>
    ∀ hq : residueHomogeneous q j,
      ∃ R : ResidueWeightedPolynomial (k + j),
        evalResiduePolynomial R =
          (a • (modularMonomial m).Mcast hm).mul
            (evalResiduePolynomial
              { polynomial := q
                homogeneous := hq })
  have hmain : ∀ q, motive q := by
    intro q
    refine MvPolynomial.monomial_add_induction_on q ?_ ?_
    · intro b hq
      by_cases hb : b = 0
      · subst b
        obtain ⟨R, hR⟩ := evalResiduePolynomial_zero (k := k + j)
        refine ⟨R, ?_⟩
        rw [hR]
        simp [evalResiduePolynomial, hq]
      · have h0 : (0 : Fin 2 →₀ ℕ) ∈
            (MvPolynomial.C b : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          simp [MvPolynomial.support_C, hb]
        have hj0 : weightClass (0 : Fin 2 →₀ ℕ) = j := hq 0 h0
        let Q' : ResidueWeightedPolynomial j :=
          { polynomial := MvPolynomial.C b
            homogeneous := hq }
        obtain ⟨R, hR⟩ := evalResiduePolynomial_monomial_mul
          (k := k) (j := j) m 0 a b hm hj0
        have hC : evalResiduePolynomial Q' =
            b • (modularMonomial (0 : Fin 2 →₀ ℕ)).Mcast hj0 := by
          simpa only [Q', MvPolynomial.C_apply] using
            (evalResiduePolynomial_monomial (k := j) 0 b hj0)
        refine ⟨R, ?_⟩
        rw [hC]
        exact hR
    · intro n b q hn hb ih hq
      have hq' : residueHomogeneous q j := by
        intro r hr
        have hrnot : r ∉
            (MvPolynomial.monomial n b : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          rw [MvPolynomial.support_monomial, if_neg hb]
          intro hrn
          have hrn' : r = n := by simpa using hrn
          apply hn
          apply MvPolynomial.mem_support_iff.mpr
          subst r
          exact MvPolynomial.mem_support_iff.mp hr
        have hrs : r ∈
            (q.support \
              (MvPolynomial.monomial n b : MvPolynomial (Fin 2) (ZMod ℓ)).support) := by
          exact Finset.mem_sdiff.mpr ⟨hr, hrnot⟩
        have hsum := MvPolynomial.support_sdiff_support_subset_support_add
          q (MvPolynomial.monomial n b) hrs
        have hsum' : r ∈
            (MvPolynomial.monomial n b + q : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          rw [add_comm]
          exact hsum
        exact hq r hsum'
      have hnm : weightClass n = j := by
        have hn0 : q.coeff n = 0 := by
          by_contra hn0
          apply hn
          exact MvPolynomial.mem_support_iff.mpr hn0
        have hmem : n ∈
            (MvPolynomial.monomial n b + q : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
            MvPolynomial.coeff_monomial]
          simp [hb, hn0]
        exact hq n hmem
      obtain ⟨Rn, hnR⟩ := evalResiduePolynomial_monomial_mul
        (k := k) (j := j) m n a b hm hnm
      obtain ⟨Rq, hqR⟩ := ih hq'
      obtain ⟨R, hR⟩ := evalResiduePolynomial_add Rn Rq
      refine ⟨R, ?_⟩
      rw [hR, hnR, hqR]
      have hsum := evalResiduePolynomial_add_poly
        (k := j)
        ({ polynomial := MvPolynomial.monomial n b
           homogeneous := by
             intro r hr
             rw [MvPolynomial.support_monomial, if_neg hb] at hr
             have hr' : r = n := by simpa using hr
             rw [hr']
             exact hnm } : ResidueWeightedPolynomial j)
        ({ polynomial := q
           homogeneous := by
             intro r hr
             exact hq' r hr } : ResidueWeightedPolynomial j)
      have hsum' :
          evalResiduePolynomial
              { polynomial := MvPolynomial.monomial n b + q
                homogeneous := hq } =
            evalResiduePolynomial
                ({ polynomial := MvPolynomial.monomial n b
                   homogeneous := by
                     intro r hr
                     rw [MvPolynomial.support_monomial, if_neg hb] at hr
                     have hr' : r = n := by simpa using hr
                     rw [hr']
                     exact hnm } : ResidueWeightedPolynomial j) +
              evalResiduePolynomial
                ({ polynomial := q
                   homogeneous := by
                     intro r hr
                     exact hq' r hr } : ResidueWeightedPolynomial j) := by
        simpa using hsum
      rw [hsum']
      have hmuladd :
          (a • (modularMonomial m).Mcast hm).mul
              (evalResiduePolynomial
                ({ polynomial := MvPolynomial.monomial n b
                   homogeneous := by
                     intro r hr
                     rw [MvPolynomial.support_monomial, if_neg hb] at hr
                     have hr' : r = n := by simpa using hr
                     rw [hr']
                     exact hnm } : ResidueWeightedPolynomial j) +
                evalResiduePolynomial
                  ({ polynomial := q
                     homogeneous := by
                       intro r hr
                       exact hq' r hr } : ResidueWeightedPolynomial j)) =
            (a • (modularMonomial m).Mcast hm).mul
                (evalResiduePolynomial
                  ({ polynomial := MvPolynomial.monomial n b
                     homogeneous := by
                       intro r hr
                       rw [MvPolynomial.support_monomial, if_neg hb] at hr
                       have hr' : r = n := by simpa using hr
                       rw [hr']
                       exact hnm } : ResidueWeightedPolynomial j)) +
              (a • (modularMonomial m).Mcast hm).mul
                (evalResiduePolynomial
                  ({ polynomial := q
                     homogeneous := by
                       intro r hr
                       exact hq' r hr } : ResidueWeightedPolynomial j)) := by
        apply ModularFormMod.fourier_inj
        simp only [ModularFormMod.fourier_mul, ModularFormMod.fourier_add]
        rw [mul_add]
      have hmono :
          evalResiduePolynomial
              ({ polynomial := MvPolynomial.monomial n b
                 homogeneous := by
                   intro r hr
                   rw [MvPolynomial.support_monomial, if_neg hb] at hr
                   have hr' : r = n := by simpa using hr
                   rw [hr']
                   exact hnm } : ResidueWeightedPolynomial j) =
            b • (modularMonomial n).Mcast hnm := by
        simpa using (evalResiduePolynomial_monomial (k := j) n b hnm)
      rw [← hmono]
      exact hmuladd.symm
  exact hmain Q.polynomial Q.homogeneous

theorem modularFormMod_mul_add
    {j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k)
    (g h : ModularFormMod ℓ j) :
    f.mul (g + h) = f.mul g + f.mul h := by
  apply ModularFormMod.fourier_inj
  simp only [ModularFormMod.fourier_mul, ModularFormMod.fourier_add]
  rw [mul_add]

theorem modularFormMod_add_mul
    {j : ZMod (ℓ - 1)} (f g : ModularFormMod ℓ k)
    (h : ModularFormMod ℓ j) :
    (f + g).mul h = f.mul h + g.mul h := by
  apply ModularFormMod.fourier_inj
  simp only [ModularFormMod.fourier_mul, ModularFormMod.fourier_add]
  rw [add_mul]

theorem evalResiduePolynomial_mul
    {j : ZMod (ℓ - 1)} (P : ResidueWeightedPolynomial k)
    (Q : ResidueWeightedPolynomial j) :
    ∃ R : ResidueWeightedPolynomial (k + j),
      evalResiduePolynomial R =
        (evalResiduePolynomial P).mul (evalResiduePolynomial Q) := by
  classical
  let motive : MvPolynomial (Fin 2) (ZMod ℓ) → Prop := fun p =>
    ∀ hp : residueHomogeneous p k,
      ∃ R : ResidueWeightedPolynomial (k + j),
        evalResiduePolynomial R =
          (evalResiduePolynomial
            { polynomial := p, homogeneous := hp }).mul
            (evalResiduePolynomial Q)
  have hmain : ∀ p, motive p := by
    intro p
    refine MvPolynomial.monomial_add_induction_on p ?_ ?_
    · intro a hp
      by_cases ha : a = 0
      · subst a
        obtain ⟨R, hR⟩ := evalResiduePolynomial_zero (k := k + j)
        refine ⟨R, ?_⟩
        rw [hR]
        simp [evalResiduePolynomial]
      · have h0 : (0 : Fin 2 →₀ ℕ) ∈
            (MvPolynomial.C a : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          simp [MvPolynomial.support_C, ha]
        have hk0 : weightClass (0 : Fin 2 →₀ ℕ) = k := hp 0 h0
        let P' : ResidueWeightedPolynomial k :=
          { polynomial := MvPolynomial.C a
            homogeneous := hp }
        obtain ⟨R, hR⟩ := evalResiduePolynomial_monomial_mul_polynomial
          (k := k) (j := j) 0 a hk0 Q
        have hC : evalResiduePolynomial P' =
            a • (modularMonomial (0 : Fin 2 →₀ ℕ)).Mcast hk0 := by
          simpa only [P', MvPolynomial.C_apply] using
            (evalResiduePolynomial_monomial (k := k) 0 a hk0)
        refine ⟨R, ?_⟩
        rw [hC]
        exact hR
    · intro n b p hn hb ih hp
      have hp' : residueHomogeneous p k := by
        intro r hr
        have hrnot : r ∉
            (MvPolynomial.monomial n b : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          rw [MvPolynomial.support_monomial, if_neg hb]
          intro hrn
          have hrn' : r = n := by simpa using hrn
          apply hn
          apply MvPolynomial.mem_support_iff.mpr
          subst r
          exact MvPolynomial.mem_support_iff.mp hr
        have hrs : r ∈
            (p.support \
              (MvPolynomial.monomial n b : MvPolynomial (Fin 2) (ZMod ℓ)).support) := by
          exact Finset.mem_sdiff.mpr ⟨hr, hrnot⟩
        have hsum := MvPolynomial.support_sdiff_support_subset_support_add
          p (MvPolynomial.monomial n b) hrs
        have hsum' : r ∈
            (MvPolynomial.monomial n b + p : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          rw [add_comm]
          exact hsum
        exact hp r hsum'
      have hnp : weightClass n = k := by
        have hn0 : p.coeff n = 0 := by
          by_contra hn0
          apply hn
          exact MvPolynomial.mem_support_iff.mpr hn0
        have hmem : n ∈
            (MvPolynomial.monomial n b + p : MvPolynomial (Fin 2) (ZMod ℓ)).support := by
          rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
            MvPolynomial.coeff_monomial]
          simp [hb, hn0]
        exact hp n hmem
      obtain ⟨Rn, hnR⟩ := evalResiduePolynomial_monomial_mul_polynomial
        (k := k) (j := j) n b hnp Q
      obtain ⟨Rp, hpR⟩ := ih hp'
      obtain ⟨R, hR⟩ := evalResiduePolynomial_add Rn Rp
      refine ⟨R, ?_⟩
      rw [hR, hnR, hpR]
      have hsum := evalResiduePolynomial_add_poly
        (k := k)
        ({ polynomial := MvPolynomial.monomial n b
           homogeneous := by
             intro r hr
             rw [MvPolynomial.support_monomial, if_neg hb] at hr
             have hr' : r = n := by simpa using hr
             rw [hr']
             exact hnp } : ResidueWeightedPolynomial k)
        ({ polynomial := p
           homogeneous := by
             intro r hr
             exact hp' r hr } : ResidueWeightedPolynomial k)
      have hsum' :
          evalResiduePolynomial
              { polynomial := MvPolynomial.monomial n b + p
                homogeneous := hp } =
            evalResiduePolynomial
                ({ polynomial := MvPolynomial.monomial n b
                   homogeneous := by
                     intro r hr
                     rw [MvPolynomial.support_monomial, if_neg hb] at hr
                     have hr' : r = n := by simpa using hr
                     rw [hr']
                     exact hnp } : ResidueWeightedPolynomial k) +
              evalResiduePolynomial
                ({ polynomial := p
                   homogeneous := by
                     intro r hr
                     exact hp' r hr } : ResidueWeightedPolynomial k) := by
        simpa using hsum
      rw [hsum']
      have hmuladd := modularFormMod_add_mul
        (k := k) (j := j)
        (evalResiduePolynomial
          ({ polynomial := MvPolynomial.monomial n b
             homogeneous := by
               intro r hr
               rw [MvPolynomial.support_monomial, if_neg hb] at hr
               have hr' : r = n := by simpa using hr
               rw [hr']
               exact hnp } : ResidueWeightedPolynomial k))
        (evalResiduePolynomial
          ({ polynomial := p
             homogeneous := by
               intro r hr
               exact hp' r hr } : ResidueWeightedPolynomial k))
        (evalResiduePolynomial Q)
      have hmono :
          evalResiduePolynomial
              ({ polynomial := MvPolynomial.monomial n b
                 homogeneous := by
                   intro r hr
                   rw [MvPolynomial.support_monomial, if_neg hb] at hr
                   have hr' : r = n := by simpa using hr
                   rw [hr']
                   exact hnp } : ResidueWeightedPolynomial k) =
            b • (modularMonomial n).Mcast hnp := by
        simpa using (evalResiduePolynomial_monomial (k := k) n b hnp)
      rw [← hmono]
      exact hmuladd.symm
  exact hmain P.polynomial P.homogeneous

theorem integralMonomial_has_residuePolynomial
    (m : Fin 2 →₀ ℕ) :
    ∃ P : ResidueWeightedPolynomial (weightClass m),
      evalResiduePolynomial P = (integralMonomial m).Reduce ℓ := by
  let P : ResidueWeightedPolynomial (weightClass m) :=
    { polynomial := MvPolynomial.monomial m (1 : ZMod ℓ)
      homogeneous := by
        intro n hn
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero] at hn
        have hnm : n = m := by simpa using hn
        rw [hnm] }
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [evalResiduePolynomial_monomial (k := weightClass m)
    m (1 : ZMod ℓ) rfl]
  apply ModularFormMod.fourier_inj
  simp only [ModularFormMod.fourier_smul, ModularFormMod.fourier_Mcast]
  simp only [one_smul]
  rfl

theorem reduce_eis_four_pow (r : ℕ) :
    ((IntegerModularForm.Eis 4).pow r).Reduce ℓ =
      (modularMonomial (Finsupp.single (0 : Fin 2) r)).Mcast (by
        simp [weightClass, weightedDegree, Finsupp.single_apply]
        ring) := by
  apply ModularFormMod.fourier_inj
  simp only [IntegerModularForm.fourier_Reduce, ModularFormMod.fourier_Mcast]
  unfold modularMonomial
  simp only [IntegerModularForm.fourier_Reduce]
  rw [IntegerModularForm.reduce_pow]
  simp only [IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk]
  simp [modularMonomial, integralMonomial, weightedDegree,
    Finsupp.single_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne,
    IntegerModularForm.Icast, IntegerModularForm.fourier_Reduce]

theorem reduce_integralMonomial_single_zero (r : ℕ) :
    (integralMonomial (Finsupp.single (0 : Fin 2) r)).Reduce ℓ =
      (((IntegerModularForm.Eis 4).pow r).Icast (by
        simp [weightedDegree, Finsupp.single_apply]
        ring)).Reduce ℓ := by
  apply ModularFormMod.fourier_inj
  have h := congrArg ModularFormMod.fourier
    (reduce_eis_four_pow (ℓ := ℓ) r).symm
  rw [ModularFormMod.fourier_Mcast] at h
  simpa [modularMonomial, IntegerModularForm.fourier_Reduce,
    IntegerModularForm.fourier_Icast] using h

theorem reduce_eis_six_pow (r : ℕ) :
    ((IntegerModularForm.Eis 6).pow r).Reduce ℓ =
      (modularMonomial (Finsupp.single (1 : Fin 2) r)).Mcast (by
        simp [weightClass, weightedDegree, Finsupp.single_apply]
        ring) := by
  apply ModularFormMod.fourier_inj
  simp only [IntegerModularForm.fourier_Reduce, ModularFormMod.fourier_Mcast]
  unfold modularMonomial
  simp only [IntegerModularForm.fourier_Reduce]
  rw [IntegerModularForm.reduce_pow]
  simp only [IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk]
  simp [modularMonomial, integralMonomial, weightedDegree,
    Finsupp.single_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne,
    IntegerModularForm.Icast, IntegerModularForm.fourier_Reduce]

theorem reduce_integralMonomial_single_one (r : ℕ) :
    (integralMonomial (Finsupp.single (1 : Fin 2) r)).Reduce ℓ =
      (((IntegerModularForm.Eis 6).pow r).Icast (by
        simp [weightedDegree, Finsupp.single_apply]
        ring)).Reduce ℓ := by
  apply ModularFormMod.fourier_inj
  have h := congrArg ModularFormMod.fourier
    (reduce_eis_six_pow (ℓ := ℓ) r).symm
  rw [ModularFormMod.fourier_Mcast] at h
  simpa [modularMonomial, IntegerModularForm.fourier_Reduce,
    IntegerModularForm.fourier_Icast] using h

theorem evalResiduePolynomial_one :
    ∃ P : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)),
      evalResiduePolynomial P = (1 : ModularFormMod ℓ 0) := by
  have h0 : weightClass (0 : Fin 2 →₀ ℕ) = (0 : ZMod (ℓ - 1)) := by
    simp [weightClass, weightedDegree]
  let P : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)) :=
    { polynomial := MvPolynomial.monomial (0 : Fin 2 →₀ ℕ) (1 : ZMod ℓ)
      homogeneous := by
        intro n hn
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero] at hn
        have hnm : n = 0 := by simpa using hn
        rw [hnm]
        exact h0 }
  refine ⟨P, ?_⟩
  change evalResiduePolynomial
      { polynomial := MvPolynomial.monomial (0 : Fin 2 →₀ ℕ) (1 : ZMod ℓ)
        homogeneous := _ } = (1 : ModularFormMod ℓ 0)
  rw [evalResiduePolynomial_monomial (k := (0 : ZMod (ℓ - 1)))
    (0 : Fin 2 →₀ ℕ) (1 : ZMod ℓ) h0]
  apply ModularFormMod.fourier_inj
  simp [ModularFormMod.fourier_smul, ModularFormMod.fourier_Mcast,
    modularMonomial_zero]

def residuePolynomialOne :
    ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)) :=
  { polynomial := MvPolynomial.monomial (0 : Fin 2 →₀ ℕ) 1
    homogeneous := by
      intro m hm
      simp at hm
      subst m
      simp [weightClass, weightedDegree] }

theorem evalResiduePolynomial_one_poly :
    evalResiduePolynomial (residuePolynomialOne (ℓ := ℓ)) =
      (1 : ModularFormMod ℓ 0) := by
  have h0 : weightClass (0 : Fin 2 →₀ ℕ) = (0 : ZMod (ℓ - 1)) := by
    simp [weightClass, weightedDegree]
  change evalResiduePolynomial
      { polynomial := MvPolynomial.monomial (0 : Fin 2 →₀ ℕ) (1 : ZMod ℓ)
        homogeneous := _ } = (1 : ModularFormMod ℓ 0)
  rw [evalResiduePolynomial_monomial (k := (0 : ZMod (ℓ - 1)))
    (0 : Fin 2 →₀ ℕ) (1 : ZMod ℓ) h0]
  apply ModularFormMod.fourier_inj
  simp [ModularFormMod.fourier_smul, ModularFormMod.fourier_Mcast,
    modularMonomial_zero]

/-- A residue-homogeneous polynomial is induced by an integral polynomial.

This definition records the integral-coefficient convention used in this
project: the source polynomial has coefficients in `ℤ`, and only then are its
coefficients reduced to `ZMod ℓ`. -/
def HasIntegralLift {k : ZMod (ℓ - 1)}
    (P : ResidueWeightedPolynomial k) : Prop :=
  ∃ Q : MvPolynomial (Fin 2) ℤ,
    P.polynomial = Q.map (Int.castRingHom (ZMod ℓ))

/-- Every polynomial over `ZMod ℓ` has an integral coefficient lift. -/
theorem residuePolynomial_has_integral_lift
    {k : ZMod (ℓ - 1)} (P : ResidueWeightedPolynomial k) :
    HasIntegralLift P := by
  obtain ⟨Q, hQ⟩ := MvPolynomial.map_surjective (f := Int.castRingHom (ZMod ℓ))
    (fun a => ZMod.intCast_surjective a) P.polynomial
  exact ⟨Q, hQ.symm⟩

/-! ## The Hasse relation and the polynomial presentation -/

/-- The polynomial relation `A(Q, R) = 1` from Theorem 1.41. -/
def SatisfiesHasseRelation
    (A : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))) : Prop :=
  evalResiduePolynomial A = (1 : ModularFormMod ℓ 0)

/-- The integral-coefficient Hasse datum used below.  Its polynomial is over
`ZMod ℓ`, but the lift is required to come from a polynomial over `ℤ`, in
accordance with `IntegerModularForm`. -/
structure HassePolynomialData where
  polynomial : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1))
  integral_lift : HasIntegralLift polynomial
  relation : SatisfiesHasseRelation polynomial

/-- The ideal generated by the Hasse relation `A - 1`. -/
def HasseIdeal (A : HassePolynomialData (ℓ := ℓ)) :
    Ideal (MvPolynomial (Fin 2) (ZMod ℓ)) :=
  Ideal.span {A.polynomial.polynomial - MvPolynomial.C 1}

theorem hasse_relation_mem_hasseIdeal
    (A : HassePolynomialData (ℓ := ℓ)) :
    A.polynomial.polynomial - MvPolynomial.C 1 ∈ HasseIdeal A := by
  exact Ideal.subset_span (by simp)

theorem mem_hasseIdeal_iff_exists_multiplier
    (A : HassePolynomialData (ℓ := ℓ))
    (p : MvPolynomial (Fin 2) (ZMod ℓ)) :
    p ∈ HasseIdeal A ↔
      ∃ q, q * (A.polynomial.polynomial - MvPolynomial.C 1) = p := by
  rw [HasseIdeal, Ideal.mem_span_singleton']

def residuePolynomialHasseSub
    (A : HassePolynomialData (ℓ := ℓ)) :
    ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)) :=
  residuePolynomialSub A.polynomial residuePolynomialOne

theorem evalResiduePolynomial_hasse_sub
    (A : HassePolynomialData (ℓ := ℓ)) :
    evalResiduePolynomial (residuePolynomialHasseSub A) = 0 := by
  rw [residuePolynomialHasseSub, evalResiduePolynomial_sub_poly,
    A.relation, evalResiduePolynomial_one_poly]
  exact sub_self _

/-- The quotient ring appearing in Theorem 1.41. -/
def HasseQuotient (A : HassePolynomialData (ℓ := ℓ)) :=
  MvPolynomial (Fin 2) (ZMod ℓ) ⧸ HasseIdeal A

/-- The componentwise form of the polynomial presentation.  The project
currently stores modular forms in their weight component rather than as an
ungraded direct-sum algebra, so the theorem is stated componentwise. -/
def Theorem141Statement : Prop :=
  ∃ A : HassePolynomialData (ℓ := ℓ),
    (∀ k (f : ModularFormMod ℓ k),
      ∃ P : ResidueWeightedPolynomial k, evalResiduePolynomial P = f) ∧
    (∀ k (P Q : ResidueWeightedPolynomial k),
      evalResiduePolynomial P = evalResiduePolynomial Q ↔
        P.polynomial - Q.polynomial ∈ HasseIdeal A)

/-! ## The theorem statements used to establish Theorem 1.41 -/

/-- Every modular form in a fixed residue-weight component has an integral
Fourier lift in the sense of `IntegerModularForm`. -/
theorem modularFormMod_has_integral_lift (f : ModularFormMod ℓ k) :
    ∃ w : ℤ, ∃ g : IntegerModularForm w,
      ∃ h : (w : ZMod (ℓ - 1)) = k,
        f = (g.Reduce ℓ).Mcast h := by
  obtain ⟨w, hwk, g, hg⟩ := f.Exists_reduce
  refine ⟨w, g, hwk, ?_⟩
  apply ModularFormMod.fourier_inj
  rw [ModularFormMod.fourier_Mcast, IntegerModularForm.fourier_Reduce, hg]

/-! The integral basis supplied by `IntegerModularForm/Basis.lean` is the
starting point for the polynomial-surjectivity argument. -/

theorem integralForm_has_G_basis_expansion {w : ℤ}
    (g : IntegerModularForm w) :
    ∃ c : Fin (dim w) → ℤ,
      g = ∑ i, c i • IntegerModularForm.G i :=
  IntegerModularForm.exists_G_combo g

/-! The next identity is the bridge needed to turn the `G`-basis into an
`E₄,E₆` polynomial basis after reduction modulo a large prime. -/

theorem delta_eq_eis_four_six :
    (1728 : ℤ) • IntegerModularForm.Delta =
      ((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num) -
        ((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num) := by
  apply IntegerModularForm.carrier_inj
  have h4n : Even (4 : ℕ) := ⟨2, by norm_num⟩
  have h6n : Even (6 : ℕ) := ⟨3, by norm_num⟩
  have hB5 : bernoulli' 5 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have hB6 : bernoulli' 6 = (1 / 42 : ℚ) := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four, hB5]
  have hE4 : (IntegerModularForm.Eis 4).carrier =
      ModularForm.E (by norm_num : 3 ≤ 4) := by
    apply ModularForm.qexp_injective
    rw [(IntegerModularForm.Eis 4).carrier_eq]
    ext n
    rw [ModularForm.qexp_eq']
    change ((IntegerModularForm.Eis 4).coeff n : ℂ) = _
    rw [IntegerModularForm.coeff_Eis_four,
      EisensteinSeries.E_qExpansion_coeff (by norm_num) h4n]
    split_ifs with hn
    · norm_num [bernoulli, bernoulli'_four]
    · norm_num [bernoulli, bernoulli'_four]
  have hE6 : (IntegerModularForm.Eis 6).carrier =
      ModularForm.E (by norm_num : 3 ≤ 6) := by
    apply ModularForm.qexp_injective
    rw [(IntegerModularForm.Eis 6).carrier_eq]
    ext n
    rw [ModularForm.qexp_eq']
    change ((IntegerModularForm.Eis 6).coeff n : ℂ) = _
    rw [IntegerModularForm.coeff_Eis_six,
      EisensteinSeries.E_qExpansion_coeff (by norm_num) h6n]
    split_ifs with hn
    · norm_num [bernoulli, hB6]
    · norm_num [bernoulli, hB6]
  ext z
  simp [IntegerModularForm.Delta]
  change (1728 : ℂ) * ModularForm.discriminant z =
    ((IntegerModularForm.Eis 4) z) ^ 3 -
      ((IntegerModularForm.Eis 6) z) ^ 2
  have hE4z : (IntegerModularForm.Eis 4).carrier z =
      ModularForm.E (by norm_num : 3 ≤ 4) z :=
    congrArg (fun f => f z) hE4
  have hE6z : (IntegerModularForm.Eis 6).carrier z =
      ModularForm.E (by norm_num : 3 ≤ 6) z :=
    congrArg (fun f => f z) hE6
  have hE4z' : (IntegerModularForm.Eis 4) z =
      ModularForm.E (by norm_num : 3 ≤ 4) z := by
    simpa only [IntegerModularForm.coe_def] using hE4z
  have hE6z' : (IntegerModularForm.Eis 6) z =
      ModularForm.E (by norm_num : 3 ≤ 6) z := by
    simpa only [IntegerModularForm.coe_def] using hE6z
  rw [hE4z', hE6z']
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

/-! Reducing the integral identity gives the relation used when replacing a
power of `Δ` in the basis by an `E₄,E₆` polynomial. -/
theorem reduce_delta_identity :
    (1728 : ZMod ℓ) • (IntegerModularForm.Delta.Reduce ℓ) =
      (((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num)).Reduce ℓ -
        (((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num)).Reduce ℓ := by
  have h := congrArg (fun g : IntegerModularForm (12 : ℤ) => g.Reduce ℓ)
    delta_eq_eis_four_six
  rw [show (1728 : ZMod ℓ) = ((1728 : ℤ) : ZMod ℓ) by norm_num,
    Int.cast_smul_eq_zsmul]
  simpa only [map_smul, map_sub] using h

theorem isUnit_1728 : IsUnit (1728 : ZMod ℓ) := by
  rw [isUnit_iff_ne_zero]
  change ((1728 : ℕ) : ZMod ℓ) ≠ 0
  intro hzero
  have h : ℓ ∣ 1728 :=
    (ZMod.natCast_eq_zero_iff 1728 ℓ).mp hzero
  have hℓ5 := (inferInstance : isLargePrime ℓ).AtLeastFive
  have h' : ℓ ∣ 2 ^ 6 * 3 ^ 3 := by
    norm_num at h ⊢
    exact h
  rcases (inferInstance : isLargePrime ℓ).Prime.dvd_mul.mp h' with h2 | h3
  · have h2' : ℓ ∣ 2 := (inferInstance : isLargePrime ℓ).Prime.dvd_of_dvd_pow h2
    have : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    omega
  · have h3' : ℓ ∣ 3 := (inferInstance : isLargePrime ℓ).Prime.dvd_of_dvd_pow h3
    have : ℓ ≤ 3 := Nat.le_of_dvd (by norm_num) h3'
    omega

theorem reduce_delta_identity_solved :
    IntegerModularForm.Delta.Reduce ℓ =
      (1728 : ZMod ℓ)⁻¹ •
        ((((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num)).Reduce ℓ -
          (((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num)).Reduce ℓ) := by
  have hne : (1728 : ZMod ℓ) ≠ 0 := (isUnit_1728 (ℓ := ℓ)).ne_zero
  calc
    IntegerModularForm.Delta.Reduce ℓ =
        (1 : ZMod ℓ) • IntegerModularForm.Delta.Reduce ℓ := by
      exact (one_smul (ZMod ℓ) (IntegerModularForm.Delta.Reduce ℓ)).symm
    _ = ((1728 : ZMod ℓ)⁻¹ * 1728) •
        IntegerModularForm.Delta.Reduce ℓ := by
      rw [inv_mul_cancel₀ hne]
    _ = (1728 : ZMod ℓ)⁻¹ •
        ((1728 : ZMod ℓ) • IntegerModularForm.Delta.Reduce ℓ) := by
      rw [mul_smul]
    _ = (1728 : ZMod ℓ)⁻¹ •
        ((((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num)).Reduce ℓ -
          (((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num)).Reduce ℓ) := by
      rw [reduce_delta_identity]

theorem delta_has_residuePolynomial :
    ∃ P : ResidueWeightedPolynomial ((12 : ℤ) : ZMod (ℓ - 1)),
      evalResiduePolynomial P = IntegerModularForm.Delta.Reduce ℓ := by
  let e4 : Fin 2 →₀ ℕ := Finsupp.single 0 3
  let e6 : Fin 2 →₀ ℕ := Finsupp.single 1 2
  have h4w : weightClass e4 = ((12 : ℤ) : ZMod (ℓ - 1)) := by
    simp [e4, weightClass, weightedDegree, Finsupp.single_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  have h6w : weightClass e6 = ((12 : ℤ) : ZMod (ℓ - 1)) := by
    simp [e6, weightClass, weightedDegree, Finsupp.single_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  let P4 : ResidueWeightedPolynomial ((12 : ℤ) : ZMod (ℓ - 1)) :=
    { polynomial := MvPolynomial.monomial e4 1
      homogeneous := by
        intro m hm
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero] at hm
        have hm' : m = e4 := by simpa using hm
        rw [hm']
        exact h4w }
  let P6 : ResidueWeightedPolynomial ((12 : ℤ) : ZMod (ℓ - 1)) :=
    { polynomial := MvPolynomial.monomial e6 1
      homogeneous := by
        intro m hm
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero] at hm
        have hm' : m = e6 := by simpa using hm
        rw [hm']
        exact h6w }
  have hP4 : evalResiduePolynomial P4 =
      (((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num)).Reduce ℓ := by
    have hmono := evalResiduePolynomial_monomial
      (k := ((12 : ℤ) : ZMod (ℓ - 1))) e4 (1 : ZMod ℓ) h4w
    have hred := reduce_integralMonomial_single_zero (ℓ := ℓ) 3
    dsimp [P4]
    rw [hmono]
    simp only [one_smul]
    apply ModularFormMod.fourier_inj
    simp only [ModularFormMod.fourier_Mcast]
    have hh := congrArg ModularFormMod.fourier hred
    simpa [e4, modularMonomial, IntegerModularForm.fourier_Reduce,
      IntegerModularForm.fourier_Icast] using hh
  have hP6 : evalResiduePolynomial P6 =
      (((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num)).Reduce ℓ := by
    have hmono := evalResiduePolynomial_monomial
      (k := ((12 : ℤ) : ZMod (ℓ - 1))) e6 (1 : ZMod ℓ) h6w
    have hred := reduce_integralMonomial_single_one (ℓ := ℓ) 2
    dsimp [P6]
    rw [hmono]
    simp only [one_smul]
    apply ModularFormMod.fourier_inj
    simp only [ModularFormMod.fourier_Mcast]
    have hh := congrArg ModularFormMod.fourier hred
    simpa [e6, modularMonomial, IntegerModularForm.fourier_Reduce,
      IntegerModularForm.fourier_Icast] using hh
  obtain ⟨P6neg, hP6neg⟩ := evalResiduePolynomial_smul
    (k := ((12 : ℤ) : ZMod (ℓ - 1))) (-1 : ZMod ℓ) P6
  obtain ⟨Pdiff, hPdiff⟩ := evalResiduePolynomial_add P4 P6neg
  obtain ⟨P, hP⟩ := evalResiduePolynomial_smul
    (k := ((12 : ℤ) : ZMod (ℓ - 1))) (1728 : ZMod ℓ)⁻¹ Pdiff
  refine ⟨P, ?_⟩
  rw [hP, hPdiff, hP6neg, hP4, hP6]
  rw [smul_add]
  calc
    _ = (1728 : ZMod ℓ)⁻¹ •
        ((((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num)).Reduce ℓ -
          (((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num)).Reduce ℓ) := by
      rw [sub_eq_add_neg]
      rw [smul_add]
      congr 1
      simp [smul_smul]
    _ = IntegerModularForm.Delta.Reduce ℓ := by
      rw [reduce_delta_identity_solved]

def residuePolynomialCast {a b : ZMod (ℓ - 1)}
    (P : ResidueWeightedPolynomial a) (h : a = b) :
    ResidueWeightedPolynomial b :=
  { polynomial := P.polynomial
    homogeneous := by
      intro m hm
      rw [← h]
      exact P.homogeneous m hm }

theorem evalResiduePolynomial_cast {a b : ZMod (ℓ - 1)}
    (P : ResidueWeightedPolynomial a) (h : a = b) :
    evalResiduePolynomial (residuePolynomialCast P h) =
      (evalResiduePolynomial P).Mcast h := by
  subst b
  apply ModularFormMod.fourier_inj
  rw [evalResiduePolynomial_eq_finsupp_sum,
    evalResiduePolynomial_eq_finsupp_sum]
  simp [residuePolynomialCast]

theorem evalResiduePolynomial_pow
    (P : ResidueWeightedPolynomial k) (n : ℕ) :
    ∃ R : ResidueWeightedPolynomial ((n : ZMod (ℓ - 1)) * k),
      evalResiduePolynomial R = (evalResiduePolynomial P).pow n := by
  induction n with
  | zero =>
      obtain ⟨R, hR⟩ := evalResiduePolynomial_one (ℓ := ℓ)
      have hzero : ((0 : ℕ) : ZMod (ℓ - 1)) * k =
          (0 : ZMod (ℓ - 1)) := by simp
      let T := residuePolynomialCast R hzero.symm
      refine ⟨T, ?_⟩
      rw [evalResiduePolynomial_cast, hR]
      simp [hzero, ModularFormMod.one_def]
  | succ n ih =>
      obtain ⟨R, hR⟩ := ih
      obtain ⟨S, hS⟩ := evalResiduePolynomial_mul R P
      have hweight :
          (n : ZMod (ℓ - 1)) * k + k =
            ((n + 1 : ℕ) : ZMod (ℓ - 1)) * k := by
        simp [Nat.cast_add, Nat.cast_one, add_mul]
      let T := residuePolynomialCast S hweight
      refine ⟨T, ?_⟩
      rw [evalResiduePolynomial_cast, hS, hR]
      apply ModularFormMod.fourier_inj
      simp [ModularFormMod.fourier_Mcast, pow_succ, mul_assoc]

theorem eis_four_delta_pow_has_residuePolynomial (r c : ℕ) :
    ∃ P : ResidueWeightedPolynomial
        (weightClass (Finsupp.single (0 : Fin 2) r) +
          ((c : ZMod (ℓ - 1)) * ((12 : ℤ) : ZMod (ℓ - 1)))),
      evalResiduePolynomial P =
        ((integralMonomial (Finsupp.single (0 : Fin 2) r)).Reduce ℓ).mul
          ((IntegerModularForm.Delta.Reduce ℓ).pow c) := by
  obtain ⟨P, hP⟩ := integralMonomial_has_residuePolynomial
    (ℓ := ℓ) (Finsupp.single (0 : Fin 2) r)
  obtain ⟨D, hD⟩ := delta_has_residuePolynomial (ℓ := ℓ)
  obtain ⟨Dc, hDc⟩ := evalResiduePolynomial_pow (ℓ := ℓ) D c
  obtain ⟨R, hR⟩ := evalResiduePolynomial_mul P Dc
  refine ⟨R, ?_⟩
  rw [hR, hP, hDc, hD]
  rfl

theorem eis_four_delta_Icast_has_residuePolynomial {w : ℤ}
    (r c : ℕ) (h : (r : ℤ) * 4 + (c : ℤ) * 12 = w) :
    ∃ P : ResidueWeightedPolynomial (w : ZMod (ℓ - 1)),
      evalResiduePolynomial P =
        ((((IntegerModularForm.Eis 4).pow r).mul
          (IntegerModularForm.Delta.pow c)).Icast h).Reduce ℓ := by
  obtain ⟨R, hR⟩ := eis_four_delta_pow_has_residuePolynomial
    (ℓ := ℓ) r c
  have hq :
      weightClass (Finsupp.single (0 : Fin 2) r) +
          ((c : ZMod (ℓ - 1)) * ((12 : ℤ) : ZMod (ℓ - 1))) =
        (w : ZMod (ℓ - 1)) := by
    calc
      weightClass (Finsupp.single (0 : Fin 2) r) +
          ((c : ZMod (ℓ - 1)) * ((12 : ℤ) : ZMod (ℓ - 1))) =
          (((r : ℤ) * 4 + (c : ℤ) * 12 : ℤ) : ZMod (ℓ - 1)) := by
            simp [weightClass, weightedDegree, Finsupp.single_apply,
              Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
            ring
      _ = (w : ZMod (ℓ - 1)) := by rw [h]
  let T := residuePolynomialCast R hq
  refine ⟨T, ?_⟩
  rw [evalResiduePolynomial_cast, hR]
  rw [IntegerModularForm.Reduce_Icast,
    IntegerModularForm.Reduce_mul, IntegerModularForm.Reduce_pow]
  apply ModularFormMod.fourier_inj
  rw [show (integralMonomial (Finsupp.single (0 : Fin 2) r)).Reduce ℓ =
      (((IntegerModularForm.Eis 4).pow r).Icast (by
        simp [weightedDegree, Finsupp.single_apply]
        ring)).Reduce ℓ by
    exact reduce_integralMonomial_single_zero (ℓ := ℓ) r]
  rw [ModularFormMod.fourier_Mcast]
  simp [ModularFormMod.Mcast, ModularFormMod.fourier_Mcast,
    ModularFormMod.fourier_mul,
    ModularFormMod.fourier_pow, IntegerModularForm.Icast,
    IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk,
    map_pow, h]

theorem G_twelve_has_residuePolynomial {w : ℤ}
    (c : Fin (dim w)) :
    ∃ P : ResidueWeightedPolynomial
        ((w - (w %% 12) : ℤ) : ZMod (ℓ - 1)),
      evalResiduePolynomial P =
        (IntegerModularForm.G_twelve c.1 c.2).Reduce ℓ := by
  have hdim : dim w > 0 := Nat.zero_lt_of_lt c.isLt
  have hle := IntegerModularForm.le_dim_sub_mod_without_two w
  have hcsub : c.1 < dim (w - (w %% 12)) := lt_of_lt_of_le c.isLt hle
  by_cases hk : 0 ≤ w - (w %% 12)
  · let r : ℕ := (w - (w %% 12)).toNat / 4 - 3 * c.1
    have hr : (r : ℤ) * 4 + (c.1 : ℤ) * 12 = w - (w %% 12) := by
      dsimp [r]
      have hdiv : 4 ∣ w - (w %% 12) := by
        exact dvd_trans (by norm_num) (IntegerModularForm.dvd_sub_mod_without_two w)
      have hdivNat : 4 ∣ (w - (w %% 12)).toNat := by
        have hxeq : ((w - (w %% 12)).toNat : ℤ) =
            w - (w %% 12) := Int.toNat_of_nonneg hk
        rw [← hxeq] at hdiv
        exact_mod_cast hdiv
      lift (w - (w %% 12)) to ℕ using hk with k'
      simp
      norm_cast
      have hdiv' : 4 ∣ k' := hdivNat
      have hc := hcsub
      simp [dim] at hc
      grind
    obtain ⟨P, hP⟩ := eis_four_delta_Icast_has_residuePolynomial
      (ℓ := ℓ) r c.1 hr
    refine ⟨P, ?_⟩
    simpa only [IntegerModularForm.G_twelve,
      IntegerModularForm.G_twelve', dif_pos hk] using hP
  · obtain ⟨P, hP⟩ := evalResiduePolynomial_zero
      (k := ((w - (w %% 12) : ℤ) : ZMod (ℓ - 1)))
    refine ⟨P, ?_⟩
    rw [hP]
    have hk' : ¬ ((w %% 12) ≤ w) := by omega
    simp only [IntegerModularForm.G_twelve,
      IntegerModularForm.G_twelve', dif_neg hk]
    simp

theorem G_dim_one_has_residuePolynomial {b : ℤ}
    (hb : b ∈ ({0, 4, 6, 8, 10, 14} : Set ℤ)) :
    ∃ P : ResidueWeightedPolynomial (b : ZMod (ℓ - 1)),
      evalResiduePolynomial P =
        (IntegerModularForm.G_dim_one b).Reduce ℓ := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨P, hP⟩ := integralMonomial_has_residuePolynomial
      (ℓ := ℓ) (0 : Fin 2 →₀ ℕ)
    let Q : ResidueWeightedPolynomial ((0 : ℤ) : ZMod (ℓ - 1)) :=
      residuePolynomialCast P (by
      simp [weightClass, weightedDegree])
    refine ⟨Q, ?_⟩
    rw [evalResiduePolynomial_cast, hP]
    apply ModularFormMod.fourier_inj
    simp [ModularFormMod.Mcast, IntegerModularForm.G_dim_one,
      integralMonomial_zero, IntegerModularForm.reduce,
      LinearMap.coe_mk, AddHom.coe_mk]
  · obtain ⟨P, hP⟩ := integralMonomial_has_residuePolynomial
      (ℓ := ℓ) (Finsupp.single (0 : Fin 2) 1)
    let Q : ResidueWeightedPolynomial ((4 : ℤ) : ZMod (ℓ - 1)) :=
      residuePolynomialCast P (by
      simp [weightClass, weightedDegree, Finsupp.single_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne])
    refine ⟨Q, ?_⟩
    rw [evalResiduePolynomial_cast, hP]
    apply ModularFormMod.fourier_inj
    simp [ModularFormMod.Mcast, IntegerModularForm.G_dim_one,
      integralMonomial, IntegerModularForm.Icast,
      IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk,
      map_pow]
  · obtain ⟨P, hP⟩ := integralMonomial_has_residuePolynomial
      (ℓ := ℓ) (Finsupp.single (1 : Fin 2) 1)
    let Q : ResidueWeightedPolynomial ((6 : ℤ) : ZMod (ℓ - 1)) :=
      residuePolynomialCast P (by
      simp [weightClass, weightedDegree, Finsupp.single_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne])
    refine ⟨Q, ?_⟩
    rw [evalResiduePolynomial_cast, hP]
    apply ModularFormMod.fourier_inj
    simp [ModularFormMod.Mcast, IntegerModularForm.G_dim_one,
      integralMonomial, IntegerModularForm.Icast,
      IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk,
      map_pow]
  · obtain ⟨P, hP⟩ := integralMonomial_has_residuePolynomial
      (ℓ := ℓ) (Finsupp.single (0 : Fin 2) 2)
    let Q : ResidueWeightedPolynomial ((8 : ℤ) : ZMod (ℓ - 1)) :=
      residuePolynomialCast P (by
      simp [weightClass, weightedDegree, Finsupp.single_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne])
    refine ⟨Q, ?_⟩
    rw [evalResiduePolynomial_cast, hP]
    apply ModularFormMod.fourier_inj
    simp [ModularFormMod.Mcast, IntegerModularForm.G_dim_one,
      integralMonomial, IntegerModularForm.Icast,
      IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk,
      map_pow]
  · obtain ⟨P, hP⟩ := integralMonomial_has_residuePolynomial
      (ℓ := ℓ) (Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1)
    let Q : ResidueWeightedPolynomial ((10 : ℤ) : ZMod (ℓ - 1)) :=
      residuePolynomialCast P (by
      simp [weightClass, weightedDegree, Finsupp.add_apply,
        Finsupp.single_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne])
    refine ⟨Q, ?_⟩
    rw [evalResiduePolynomial_cast, hP]
    apply ModularFormMod.fourier_inj
    simp [ModularFormMod.Mcast, IntegerModularForm.G_dim_one,
      integralMonomial, IntegerModularForm.Icast,
      IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk,
      Finsupp.add_apply, _root_.pow_one, map_pow]
  · obtain ⟨P, hP⟩ := integralMonomial_has_residuePolynomial
      (ℓ := ℓ) (Finsupp.single (0 : Fin 2) 2 +
        Finsupp.single (1 : Fin 2) 1)
    let Q : ResidueWeightedPolynomial ((14 : ℤ) : ZMod (ℓ - 1)) :=
      residuePolynomialCast P (by
      simp [weightClass, weightedDegree, Finsupp.add_apply,
        Finsupp.single_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne])
    refine ⟨Q, ?_⟩
    rw [evalResiduePolynomial_cast, hP]
    apply ModularFormMod.fourier_inj
    simp [ModularFormMod.Mcast, IntegerModularForm.G_dim_one,
      integralMonomial, IntegerModularForm.Icast,
      IntegerModularForm.reduce, LinearMap.coe_mk, AddHom.coe_mk,
      Finsupp.add_apply, _root_.pow_one, map_pow]

theorem G_has_residuePolynomial {w : ℤ}
    (c : Fin (dim w)) :
    ∃ P : ResidueWeightedPolynomial (w : ZMod (ℓ - 1)),
      evalResiduePolynomial P =
        (IntegerModularForm.G c).Reduce ℓ := by
  have hdim : dim w > 0 := Nat.zero_lt_of_lt c.isLt
  have hb := IntegerModularForm.of_dim_pos w hdim
  obtain ⟨P0, hP0⟩ := G_dim_one_has_residuePolynomial
    (ℓ := ℓ) hb
  obtain ⟨P12, hP12⟩ := G_twelve_has_residuePolynomial
    (ℓ := ℓ) c
  obtain ⟨R, hR⟩ := evalResiduePolynomial_mul P0 P12
  have hq :
      ((w %% 12 : ℤ) : ZMod (ℓ - 1)) +
          (((w - (w %% 12) : ℤ) : ZMod (ℓ - 1))) =
        (w : ZMod (ℓ - 1)) := by
    push_cast
    ring
  let T := residuePolynomialCast R hq
  refine ⟨T, ?_⟩
  rw [evalResiduePolynomial_cast, hR, hP0, hP12]
  apply ModularFormMod.fourier_inj
  simp [IntegerModularForm.G, IntegerModularForm.Icast,
    IntegerModularForm.reduce, ModularFormMod.Mcast,
    LinearMap.coe_mk, AddHom.coe_mk]

theorem evalResiduePolynomial_sum {n : ℕ}
    (P : Fin n → ResidueWeightedPolynomial k) :
    ∃ Q : ResidueWeightedPolynomial k,
      evalResiduePolynomial Q = ∑ i, evalResiduePolynomial (P i) := by
  classical
  have hmain : ∀ s : Finset (Fin n),
      ∃ Q : ResidueWeightedPolynomial k,
        evalResiduePolynomial Q = ∑ i ∈ s, evalResiduePolynomial (P i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨Q, hQ⟩ := evalResiduePolynomial_zero (k := k)
        refine ⟨Q, ?_⟩
        rw [hQ]
        simp
    | @insert a s ha ih =>
        obtain ⟨Qs, hQs⟩ := ih
        obtain ⟨Q, hQ⟩ := evalResiduePolynomial_add Qs (P a)
        refine ⟨Q, ?_⟩
        rw [hQ, hQs]
        rw [Finset.sum_insert ha]
        simp [add_comm]
  obtain ⟨Q, hQ⟩ := hmain Finset.univ
  refine ⟨Q, ?_⟩
  simpa using hQ

/-- Surjectivity of polynomial evaluation in every graded component. -/
theorem residuePolynomial_eval_surjective
    (A : HassePolynomialData (ℓ := ℓ)) :
    ∀ k (f : ModularFormMod ℓ k),
      ∃ P : ResidueWeightedPolynomial k, evalResiduePolynomial P = f := by
  /-
  Proof note: obtain the integral lift directly from `Exists_reduce`.  This
  avoids the indirect reduction bridge used by the older formulation.  After
  the lift, expand in the level-one
  basis and reduce the coefficients modulo `ℓ`.  The remaining step is the
  polynomial presentation of that integral basis in the two Eisenstein
  generators over the present `ℤ`-based API.
  -/
  intro k f
  obtain ⟨w, hwk, g, hg⟩ := f.Exists_reduce
  have hgf : (g.Reduce ℓ).Mcast hwk = f := by
    apply ModularFormMod.fourier_inj
    rw [ModularFormMod.fourier_Mcast, IntegerModularForm.fourier_Reduce, hg]
  obtain ⟨c, hc⟩ := integralForm_has_G_basis_expansion g
  let PG : Fin (dim w) → ResidueWeightedPolynomial (w : ZMod (ℓ - 1)) :=
    fun i => Classical.choose (G_has_residuePolynomial (ℓ := ℓ) i)
  have hPG (i : Fin (dim w)) :
      evalResiduePolynomial (PG i) =
        (IntegerModularForm.G i).Reduce ℓ := by
    exact Classical.choose_spec (G_has_residuePolynomial (ℓ := ℓ) i)
  let PT : Fin (dim w) → ResidueWeightedPolynomial (w : ZMod (ℓ - 1)) :=
    fun i => Classical.choose (evalResiduePolynomial_smul
      (k := (w : ZMod (ℓ - 1))) (c i : ZMod ℓ) (PG i))
  have hPT (i : Fin (dim w)) :
      evalResiduePolynomial (PT i) =
        (c i : ZMod ℓ) • evalResiduePolynomial (PG i) := by
    exact Classical.choose_spec (evalResiduePolynomial_smul
      (k := (w : ZMod (ℓ - 1))) (c i : ZMod ℓ) (PG i))
  obtain ⟨Psum, hPsum⟩ := evalResiduePolynomial_sum (ℓ := ℓ) PT
  have hPsum' : evalResiduePolynomial Psum =
      ∑ i, (c i : ZMod ℓ) •
        (IntegerModularForm.G i).Reduce ℓ := by
    rw [hPsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hPT i, hPG i]
  have hsum :
      (∑ i, (c i : ZMod ℓ) •
          (IntegerModularForm.G i).Reduce ℓ) = g.Reduce ℓ := by
    apply ModularFormMod.fourier_inj
    rw [hc]
    simp [IntegerModularForm.fourier_Reduce,
      ModularFormMod.fourier_smul, ModularFormMod.fourier_zsmul,
      Int.cast_smul_eq_zsmul]
  let Pfinal := residuePolynomialCast Psum hwk
  refine ⟨Pfinal, ?_⟩
  rw [evalResiduePolynomial_cast, hPsum', hsum]
  exact hgf

/-! The Hasse polynomial is represented by the integral Eisenstein series
`El`, whose reduction has unit Fourier expansion. -/
theorem exists_hassePolynomialData :
    ∃ A : HassePolynomialData (ℓ := ℓ),
      HasIntegralLift A.polynomial ∧
        SatisfiesHasseRelation A.polynomial := by
  classical
  let P₀ : ResidueWeightedPolynomial (0 : ZMod (ℓ - 1)) :=
    { polynomial := MvPolynomial.C 1
      homogeneous := by
        intro m hm
        simp [MvPolynomial.support_C] at hm
        subst m
        simp [weightClass, weightedDegree] }
  let A₀ : HassePolynomialData (ℓ := ℓ) :=
    { polynomial := P₀
      integral_lift := residuePolynomial_has_integral_lift P₀
      relation := by
        dsimp [SatisfiesHasseRelation, P₀, evalResiduePolynomial]
        have h0 : (0 : Fin 2 →₀ ℕ) ∈
            (MvPolynomial.support (1 : MvPolynomial (Fin 2) (ZMod ℓ))) := by
          simp
        rw [Finset.sum_eq_single ⟨0, h0⟩]
        · ext n
          simp [modularMonomial_zero, ModularFormMod.coeff_def,
            ModularFormMod.Mcast, ModularFormMod.one_def]
        · intro b hb hne
          have hb' : (b : Fin 2 →₀ ℕ) ∈
              ({0} : Finset (Fin 2 →₀ ℕ)) := by
            simpa [MvPolynomial.support_one] using b.property
          have hb0 : (b : Fin 2 →₀ ℕ) = 0 := by
            simpa using hb'
          exact (hne (Subtype.ext hb0)).elim
        · intro hnot
          exact (hnot (by simp [h0])).elim }
  have hcast : (((ℓ - 1 : ℕ) : ℤ) : ZMod (ℓ - 1)) = 0 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_self _
  obtain ⟨P, hP⟩ := residuePolynomial_eval_surjective A₀
    (0 : ZMod (ℓ - 1))
    (((IntegerModularForm.El ℓ).Reduce ℓ).Mcast hcast)
  let A : HassePolynomialData (ℓ := ℓ) :=
    { polynomial := P
      integral_lift := residuePolynomial_has_integral_lift P
      relation := by
        dsimp [SatisfiesHasseRelation]
        rw [hP]
        apply ModularFormMod.fourier_inj
        rw [ModularFormMod.fourier_Mcast, IntegerModularForm.fourier_Reduce,
          IntegerModularForm.reduce_El]
        rfl }
  exact ⟨A, A.integral_lift, A.relation⟩

/-!
## Foundations

This module contains the definitions and proved algebraic and basis lemmas used
by the componentwise formulation of Theorem 1.41.
-/

end FiltrationTheta
