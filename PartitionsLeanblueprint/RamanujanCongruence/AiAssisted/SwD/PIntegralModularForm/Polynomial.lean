import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.Basis
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial coordinates for p-integral modular forms

For a fixed weight, `PBasis` gives a preferred family of homogeneous
`E4`/`E6` monomials. We use its coordinates to construct the corresponding
weighted-homogeneous polynomial over `Z_(p)`.
-/

open MvPolynomial PowerSeries UpperHalfPlane

namespace PIntegralModularForm

noncomputable section

variable {p : ℕ} [isLargePrime p] {k : ℤ}

/-- The polynomial ring `Z_(p)[X,Y]`, with `X` corresponding to `E₄` and
`Y` corresponding to `E₆`. -/
abbrev E4E6Polynomial (p : ℕ) [Fact (Nat.Prime p)] :=
  MvPolynomial (Fin 2) (CoeffRing p)

/-- Evaluate `X` and `Y` at the Fourier expansions of the p-integral
Eisenstein series `E₄` and `E₆`. The result is a power series; for a
weight-homogeneous polynomial this is the Fourier expansion of the
corresponding modular form. -/
def evaluateE4E6Hom : E4E6Polynomial p →+* PowerSeries (CoeffRing p) :=
  MvPolynomial.eval₂Hom (PowerSeries.C : CoeffRing p →+* PowerSeries (CoeffRing p))
    (fun i => if i = 0 then (Eis (p := p) 4).fourier
      else (Eis (p := p) 6).fourier)

def evaluateE4E6 (P : E4E6Polynomial p) : PowerSeries (CoeffRing p) :=
  evaluateE4E6Hom (p := p) P

/-- A monomial in the two variables, with exponents taken from the
weight-`k` E₄/E₆ monomial basis. -/
def E4E6PolynomialTerm (c : Fin (dim k)) (a : CoeffRing p) :
    E4E6Polynomial p :=
  MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2)) ^ (pExponent c).1.1 *
    (MvPolynomial.X (1 : Fin 2)) ^ (pExponent c).1.2

theorem E4E6PolynomialTerm_eq_monomial (c : Fin (dim k)) (a : CoeffRing p) :
    E4E6PolynomialTerm (p := p) c a =
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) (pExponent c).1.1 +
          Finsupp.single (1 : Fin 2) (pExponent c).1.2) a := by
  rw [E4E6PolynomialTerm, MvPolynomial.C_mul_X_pow_eq_monomial,
    ← MvPolynomial.monomial_add_single]

/-- The weighted degree of a monomial, with weights 4 and 6 on the two
variables. -/
def weightedDegree (m : Fin 2 →₀ ℕ) : ℤ :=
  4 * (m 0 : ℤ) + 6 * (m 1 : ℤ)

theorem weightedDegree_pExponent (c : Fin (dim k)) :
    weightedDegree
      (Finsupp.single (0 : Fin 2) (pExponent c).1.1 +
        Finsupp.single (1 : Fin 2) (pExponent c).1.2) = k := by
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  exact (pExponent c).2

theorem E4E6PolynomialTerm_weight {c : Fin (dim k)} {a : CoeffRing p}
    {m : Fin 2 →₀ ℕ}
    (hm : m ∈ (E4E6PolynomialTerm (p := p) c a).support) :
    weightedDegree m = k := by
  rw [E4E6PolynomialTerm_eq_monomial] at hm
  have hmeq : m = Finsupp.single (0 : Fin 2) (pExponent c).1.1 +
      Finsupp.single (1 : Fin 2) (pExponent c).1.2 := by
    have h := MvPolynomial.support_monomial_subset hm
    simpa using h
  rw [hmeq]
  exact weightedDegree_pExponent c

@[simp]
theorem evaluateE4E6_polynomialTerm (c : Fin (dim k)) (a : CoeffRing p) :
    evaluateE4E6 (p := p) (E4E6PolynomialTerm (p := p) c a) =
      a • ((Eis (p := p) 4).fourier ^ (pExponent c).1.1 *
        (Eis (p := p) 6).fourier ^ (pExponent c).1.2) := by
  simp [evaluateE4E6, evaluateE4E6Hom, E4E6PolynomialTerm,
    mul_comm, mul_left_comm]
  rw [PowerSeries.smul_eq_C_mul]
  ring

/-- Turn coordinates in the p-local monomial basis into a polynomial. -/
def polynomialOfCoordinates (c : Fin (dim k) → CoeffRing p) :
    E4E6Polynomial p :=
  ∑ i : Fin (dim k), E4E6PolynomialTerm (p := p) i (c i)

/-- A polynomial in the weight-`k` monomial family selected by `PBasis`. -/
def IsPBasisPolynomial (P : E4E6Polynomial p) : Prop :=
  ∃ c : Fin (dim k) → CoeffRing p, P = polynomialOfCoordinates (p := p) c

/-- Every monomial occurring in a `PBasis` polynomial has weighted degree
`k`. -/
theorem polynomialOfCoordinates_isHomogeneous
    (c : Fin (dim k) → CoeffRing p) {m : Fin 2 →₀ ℕ}
    (hm : m ∈ (polynomialOfCoordinates (p := p) c).support) :
    weightedDegree m = k := by
  classical
  have hsubset :
      (polynomialOfCoordinates (p := p) c).support ⊆
        (Finset.univ : Finset (Fin (dim k))).biUnion
          (fun i => (E4E6PolynomialTerm (p := p) i (c i)).support) := by
    rw [polynomialOfCoordinates]
    exact MvPolynomial.support_sum
  rcases Finset.mem_biUnion.mp (hsubset hm) with ⟨i, hi, hmi⟩
  exact E4E6PolynomialTerm_weight hmi

private def pExponentMonomial (i : Fin (dim k)) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) (pExponent i).1.1 +
    Finsupp.single (1 : Fin 2) (pExponent i).1.2

private theorem pExponent_injective :
    Function.Injective (pExponent (k := k)) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (fun e : E4E6Exponent k => e.1.2) hij
  rw [pExponent_snd, pExponent_snd] at h
  omega

private theorem pExponentMonomial_injective :
    Function.Injective (pExponentMonomial (k := k)) := by
  intro i j hij
  apply pExponent_injective (k := k)
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hij
    simpa [pExponentMonomial, Finsupp.add_apply] using h
  · have h := congrArg (fun m : Fin 2 →₀ ℕ => m 1) hij
    simpa [pExponentMonomial, Finsupp.add_apply] using h

/-- Any polynomial supported on monomials of weighted degree `k` is a
linear combination of the monomials selected by `PBasis`. -/
theorem homogeneous_isPBasisPolynomial (P : E4E6Polynomial p)
    (hP : ∀ m ∈ P.support, weightedDegree m = k) :
    IsPBasisPolynomial (p := p) (k := k) P := by
  classical
  let c : Fin (dim k) → CoeffRing p := fun i => P.coeff (pExponentMonomial i)
  refine ⟨c, ?_⟩
  apply MvPolynomial.ext
  intro m
  have hcoeff : (polynomialOfCoordinates (p := p) c).coeff m =
      ∑ i : Fin (dim k),
        if pExponentMonomial (k := k) i = m then c i else 0 := by
    simp only [polynomialOfCoordinates, MvPolynomial.coeff_sum,
      E4E6PolynomialTerm_eq_monomial, MvPolynomial.coeff_monomial,
      pExponentMonomial]
    rfl
  rw [hcoeff]
  by_cases hm : m ∈ P.support
  · have hweight := hP m hm
    change 4 * (m 0 : ℤ) + 6 * (m 1 : ℤ) = k at hweight
    obtain ⟨i, hi⟩ := pExponent_surjective (k := k)
      (⟨(m 0, m 1), hweight⟩ : E4E6Exponent k)
    have hpair : (pExponent i).1 = (m 0, m 1) := by
      simpa using congrArg Subtype.val hi
    have hmonomial : pExponentMonomial (k := k) i = m := by
      apply Finsupp.ext
      intro v
      fin_cases v
      · simpa [pExponentMonomial, Finsupp.add_apply] using
          congrArg Prod.fst hpair
      · simpa [pExponentMonomial, Finsupp.add_apply] using
          congrArg Prod.snd hpair
    have hsum : (∑ j : Fin (dim k),
        if pExponentMonomial (k := k) j = m then c j else 0) = c i := by
      rw [Fintype.sum_eq_single i]
      · simp [hmonomial]
      · intro j hji
        have hneq : pExponentMonomial (k := k) j ≠ m := by
          intro heq
          exact hji (pExponentMonomial_injective (k := k)
            (heq.trans hmonomial.symm))
        simp [hneq]
    rw [hsum]
    simp [c, hmonomial]
  · have hzero : P.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    have hsum : (∑ i : Fin (dim k),
        if pExponentMonomial (k := k) i = m then c i else 0) = 0 := by
      apply Fintype.sum_eq_zero
      intro i
      by_cases heq : pExponentMonomial (k := k) i = m
      · have hci : c i = 0 := by
          dsimp [c]
          rw [heq]
          exact hzero
        simp [heq, hci]
      · simp [heq]
    rw [hsum, hzero]

/-- The polynomial attached to a p-integral modular form. Its coefficients
are the coordinates of the form in `PBasis`. -/
def polynomial (f : PIntegralModularForm p k) : E4E6Polynomial p :=
  polynomialOfCoordinates (p := p) ((PBasis (p := p) k).repr f)

theorem polynomial_isPBasisPolynomial (f : PIntegralModularForm p k) :
    IsPBasisPolynomial (p := p) (k := k) (polynomial (p := p) f) :=
  ⟨(PBasis (p := p) k).repr f, rfl⟩

theorem polynomial_isHomogeneous (f : PIntegralModularForm p k)
    {m : Fin 2 →₀ ℕ} (hm : m ∈ (polynomial (p := p) f).support) :
    weightedDegree m = k := by
  exact polynomialOfCoordinates_isHomogeneous
    (p := p) ((PBasis (p := p) k).repr f) (by simpa [polynomial] using hm)

private theorem fourier_sum_pIntegral {α : Type*} (s : Finset α)
    (f : α → PIntegralModularForm p k) :
    (∑ a ∈ s, f a).fourier = ∑ a ∈ s, (f a).fourier := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private theorem fourier_smul_pIntegral (a : CoeffRing p)
    (f : PIntegralModularForm p k) : (a • f).fourier = a • f.fourier := rfl

/-- The modular form represented by a coordinate vector in `PBasis`. -/
def formOfCoordinates (c : Fin (dim k) → CoeffRing p) :
    PIntegralModularForm p k :=
  ∑ i : Fin (dim k), c i • PBasis (p := p) k i

private theorem fourier_formOfCoordinates
    (c : Fin (dim k) → CoeffRing p) :
    (formOfCoordinates (p := p) c).fourier =
      ∑ i : Fin (dim k), c i • (PBasis (p := p) k i).fourier := by
  simp [formOfCoordinates, fourier_sum_pIntegral, fourier_smul_pIntegral]

/-- The basis-coordinate evaluation in modular forms is inverse to `PBasis.repr`. -/
theorem formOfCoordinates_repr (f : PIntegralModularForm p k) :
    formOfCoordinates (p := p) ((PBasis (p := p) k).repr f) = f :=
  (PBasis (p := p) k).sum_repr f

/-- Evaluation of a polynomial assembled from basis monomials gives the
corresponding linear combination of basis forms. -/
theorem evaluate_polynomialOfCoordinates
    (c : Fin (dim k) → CoeffRing p) :
    evaluateE4E6 (p := p) (polynomialOfCoordinates (p := p) c) =
      (formOfCoordinates (p := p) c).fourier := by
  change evaluateE4E6Hom (p := p)
    (∑ i : Fin (dim k), E4E6PolynomialTerm (p := p) i (c i)) = _
  rw [map_sum]
  change (∑ i : Fin (dim k),
    evaluateE4E6 (p := p) (E4E6PolynomialTerm (p := p) i (c i))) = _
  calc
    (∑ i : Fin (dim k),
        evaluateE4E6 (p := p) (E4E6PolynomialTerm (p := p) i (c i))) =
      ∑ i : Fin (dim k), c i •
        ((Eis (p := p) 4).fourier ^ (pExponent i).1.1 *
          (Eis (p := p) 6).fourier ^ (pExponent i).1.2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [evaluateE4E6_polynomialTerm]
    _ = (formOfCoordinates (p := p) c).fourier := by
      rw [fourier_formOfCoordinates]
      apply Finset.sum_congr rfl
      intro i hi
      rw [PBasis_apply_eq_PMonomial, fourier_PMonomial]

/-- The polynomial associated to `f`, evaluated at the Fourier expansions of
`E₄` and `E₆`, is the Fourier expansion of `f`. -/
theorem evaluate_polynomial (f : PIntegralModularForm p k) :
    evaluateE4E6 (p := p) (polynomial (p := p) f) = f.fourier := by
  have hrepr : f.fourier =
      ∑ i : Fin (dim k), ((PBasis (p := p) k).repr f i) •
        (PBasis (p := p) k i).fourier := by
    have h := congrArg (fun g : PIntegralModularForm p k => g.fourier)
      ((PBasis (p := p) k).sum_repr f)
    simpa [fourier_sum_pIntegral, fourier_smul_pIntegral] using h.symm
  rw [polynomial, evaluate_polynomialOfCoordinates, fourier_formOfCoordinates]
  exact hrepr.symm

/-- After mapping coefficients into `ℂ`, evaluation at `E₄` and `E₆` has the
same q-expansion as the original modular form. -/
theorem qExpansion_evaluate_polynomial (f : PIntegralModularForm p k) :
    qExpansion 1 f.carrier =
      PowerSeries.map (toComplex p)
        (evaluateE4E6 (p := p) (polynomial (p := p) f)) := by
  rw [evaluate_polynomial, f.carrier_eq]

private theorem repr_formOfCoordinates
    (c : Fin (dim k) → CoeffRing p) (i : Fin (dim k)) :
    (PBasis (p := p) k).repr (formOfCoordinates (p := p) c) i = c i := by
  change (PBasis (p := p) k).repr
    (∑ j : Fin (dim k), c j • PBasis (p := p) k j) i = c i
  exact congrFun ((PBasis (p := p) k).repr_sum_self c) i

/-- Uniqueness of the polynomial coordinates: if a polynomial assembled from
the `PBasis` monomials evaluates to `f`, it is the polynomial returned by
`polynomial f`. -/
theorem polynomial_unique (f : PIntegralModularForm p k)
    (c : Fin (dim k) → CoeffRing p)
    (h : evaluateE4E6 (p := p) (polynomialOfCoordinates (p := p) c) = f.fourier) :
    polynomialOfCoordinates (p := p) c = polynomial (p := p) f := by
  have hfourier : (formOfCoordinates (p := p) c).fourier = f.fourier := by
    rw [← evaluate_polynomialOfCoordinates]
    exact h
  have hform : formOfCoordinates (p := p) c = f := by
    apply PIntegralModularForm.ext
    intro n
    exact congrArg (fun F : PowerSeries (CoeffRing p) => F.coeff n) hfourier
  have hcoords : c = fun i => (PBasis (p := p) k).repr f i := by
    funext i
    have hi := congrArg (fun g : PIntegralModularForm p k =>
      (PBasis (p := p) k).repr g i) hform
    simpa only [repr_formOfCoordinates] using hi
  simp [polynomial, polynomialOfCoordinates, hcoords]

/-- Among polynomials in the weight-`k` `PBasis` monomial family, the
polynomial evaluating to `f` is unique. -/
theorem polynomial_unique_of_eval (f : PIntegralModularForm p k)
    {P : E4E6Polynomial p} (hP : IsPBasisPolynomial (p := p) (k := k) P)
    (h : evaluateE4E6 (p := p) P = f.fourier) :
    P = polynomial (p := p) f := by
  rcases hP with ⟨c, hPc⟩
  rw [hPc] at h ⊢
  exact polynomial_unique (p := p) f c h

/-- Existence and uniqueness of the weight-`k` `PBasis` polynomial for `f`. -/
theorem existsUnique_polynomial (f : PIntegralModularForm p k) :
    ∃! P : E4E6Polynomial p,
      IsPBasisPolynomial (p := p) (k := k) P ∧
        evaluateE4E6 (p := p) P = f.fourier := by
  refine ⟨polynomial (p := p) f, ⟨polynomial_isPBasisPolynomial f,
    evaluate_polynomial f⟩, ?_⟩
  intro P hP
  exact polynomial_unique_of_eval (p := p) f hP.1 hP.2

end
end PIntegralModularForm
