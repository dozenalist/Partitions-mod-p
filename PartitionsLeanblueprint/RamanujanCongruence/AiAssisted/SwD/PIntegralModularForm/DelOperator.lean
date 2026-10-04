import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.Polynomial
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.ThetaOperator.DelOperator
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The scaled Serre derivative on p-integral modular forms

We use the normalization `12 θ - k E₂`, as in
`ThetaOperator.DelOperator.normalizedDel`. This normalization preserves
`Z_(p)`-integrality and induces the polynomial derivation
`X ↦ -4Y`, `Y ↦ -6X²`.
-/

open MvPolynomial PowerSeries UpperHalfPlane

namespace PIntegralModularForm

noncomputable section

variable {p : ℕ} [isLargePrime p] {k : ℤ}

private theorem powerSeries_map_derivative {R S : Type*} [CommSemiring R]
    [CommSemiring S] (φ : R →+* S) (F : PowerSeries R) :
    PowerSeries.map φ (PowerSeries.derivative F) =
      PowerSeries.derivative (PowerSeries.map φ F) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]

private theorem map_integer_smul (z : ℤ) (F : PowerSeries ℤ) :
    PowerSeries.map (algebraMap ℤ (CoeffRing p)) (z • F) =
      (algebraMap ℤ (CoeffRing p) z) •
        PowerSeries.map (algebraMap ℤ (CoeffRing p)) F := by
  rw [zsmul_eq_mul, map_mul]
  simp [PowerSeries.smul_eq_C_mul]

/-- The integral q-expansion of `E₂`, mapped into the p-local coefficient ring. -/
def pE2Fourier : PowerSeries (CoeffRing p) :=
  PowerSeries.map (algebraMap ℤ (CoeffRing p))
    ThetaOperator.DelOperator.e2Fourier

/-- The Fourier-series formula for the scaled Serre derivative of weight `k`. -/
def fourierDel (k : ℤ) (F : PowerSeries (CoeffRing p)) :
    PowerSeries (CoeffRing p) :=
  12 • (PowerSeries.X * PowerSeries.derivative F) -
    k • (pE2Fourier (p := p) * F)

/-- The scaled Serre derivative on p-integral modular forms. -/
def del (f : PIntegralModularForm p k) : PIntegralModularForm p (k + 2) where
  fourier := fourierDel (p := p) k f.fourier
  carrier := 12 • ThetaOperator.DelOperator.del f.carrier
  carrier_eq := by
    have hanalytic := ThetaOperator.DelOperator.qExpansion_twelve_del f.carrier
    calc
      qExpansion 1 (12 • ThetaOperator.DelOperator.del f.carrier) =
          12 • (PowerSeries.X * PowerSeries.derivative
            (qExpansion 1 f.carrier)) -
          k • (PowerSeries.map (Int.castRingHom ℂ)
            ThetaOperator.DelOperator.e2Fourier * qExpansion 1 f.carrier) :=
        hanalytic
      _ = PowerSeries.map (toComplex p)
          (fourierDel (p := p) k f.fourier) := by
        rw [f.carrier_eq]
        simp only [fourierDel, map_sub, map_nsmul, map_zsmul,
          map_mul, PowerSeries.map_X]
        rw [← powerSeries_map_derivative]
        have he2 : PowerSeries.map (toComplex p) (pE2Fourier (p := p)) =
            PowerSeries.map (Int.castRingHom ℂ)
              ThetaOperator.DelOperator.e2Fourier := by
          apply PowerSeries.ext
          intro n
          simp [pE2Fourier, PowerSeries.coeff_map, toComplex]
        rw [he2]

@[simp]
theorem del_fourier (f : PIntegralModularForm p k) :
    (del f).fourier = fourierDel (p := p) k f.fourier := rfl

@[simp]
theorem del_carrier (f : PIntegralModularForm p k) :
    (del f).carrier = 12 • ThetaOperator.DelOperator.del f.carrier := rfl

private theorem fourierDel_add (k : ℤ) (A B : PowerSeries (CoeffRing p)) :
    fourierDel (p := p) k (A + B) =
      fourierDel (p := p) k A + fourierDel (p := p) k B := by
  simp [fourierDel, PowerSeries.derivative.map_add, mul_add,
    smul_add, sub_eq_add_neg]
  abel

private theorem fourierDel_mul (k j : ℤ)
    (A B : PowerSeries (CoeffRing p)) :
    fourierDel (p := p) (k + j) (A * B) =
      fourierDel (p := p) k A * B + A * fourierDel (p := p) j B := by
  have hderiv := (PowerSeries.derivative :
    Derivation (CoeffRing p) (PowerSeries (CoeffRing p))
      (PowerSeries (CoeffRing p))).leibniz A B
  simp only [fourierDel, hderiv, zsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- The Leibniz rule for the p-integral scaled Serre derivative. The casts
account for the different parenthesizations of the graded weight indices. -/
theorem del_mul {j : ℤ} (f : PIntegralModularForm p k)
    (g : PIntegralModularForm p j) :
    del (f.mul g) =
      castWeight (by omega : (k + 2) + j = (k + j) + 2)
        ((del f).mul g) +
      castWeight (by omega : k + (j + 2) = (k + j) + 2)
        (f.mul (del g)) := by
  apply PIntegralModularForm.ext
  intro n
  have hseries := fourierDel_mul (p := p) k j f.fourier g.fourier
  change (fourierDel (p := p) (k + j) (f.fourier * g.fourier)).coeff n =
    (fourierDel (p := p) k f.fourier * g.fourier +
      f.fourier * fourierDel (p := p) j g.fourier).coeff n
  exact congrArg (fun F : PowerSeries (CoeffRing p) => F.coeff n) hseries

/-- The polynomial-side del operator, packaged as a derivation. -/
def polynomialDerivation :
    Derivation (CoeffRing p) (E4E6Polynomial p) (E4E6Polynomial p) :=
  (((MvPolynomial.C (-4 : CoeffRing p) : E4E6Polynomial p) *
        (MvPolynomial.X 1 : E4E6Polynomial p)) •
      MvPolynomial.pderiv (R := CoeffRing p) (σ := Fin 2) 0) +
    (((MvPolynomial.C (-6 : CoeffRing p) : E4E6Polynomial p) *
        (MvPolynomial.X 0 : E4E6Polynomial p) ^ 2) •
      MvPolynomial.pderiv (R := CoeffRing p) (σ := Fin 2) 1)

/-- The linear map underlying `polynomialDerivation`. -/
def delPolynomial : E4E6Polynomial p →ₗ[CoeffRing p] E4E6Polynomial p :=
  (polynomialDerivation (p := p)).toLinearMap

@[simp]
theorem delPolynomial_apply (P : E4E6Polynomial p) :
    delPolynomial (p := p) P =
      ((MvPolynomial.C (-4 : CoeffRing p) : E4E6Polynomial p) *
          MvPolynomial.X 1) * MvPolynomial.pderiv 0 P +
        ((MvPolynomial.C (-6 : CoeffRing p) : E4E6Polynomial p) *
          (MvPolynomial.X 0) ^ 2) * MvPolynomial.pderiv 1 P := by
  simp [delPolynomial, polynomialDerivation, mul_assoc]

theorem delPolynomial_apply_smul (P : E4E6Polynomial p) :
    delPolynomial (p := p) P =
      (-4 : CoeffRing p) •
          (MvPolynomial.X 1 * MvPolynomial.pderiv 0 P) +
        (-6 : CoeffRing p) •
          ((MvPolynomial.X 0) ^ 2 * MvPolynomial.pderiv 1 P) := by
  rw [delPolynomial_apply]
  simp only [Algebra.smul_def, MvPolynomial.C_mul']
  ring

@[simp]
theorem delPolynomial_X_zero :
    delPolynomial (p := p) (MvPolynomial.X 0 : E4E6Polynomial p) =
      (-4 : CoeffRing p) • MvPolynomial.X 1 := by
  simp [delPolynomial_apply, Algebra.smul_def]

@[simp]
theorem delPolynomial_X_one :
    delPolynomial (p := p) (MvPolynomial.X 1 : E4E6Polynomial p) =
      (-6 : CoeffRing p) • (MvPolynomial.X 0 : E4E6Polynomial p) ^ 2 := by
  simp [delPolynomial_apply, Algebra.smul_def]

theorem delPolynomial_leibniz (P Q : E4E6Polynomial p) :
    delPolynomial (p := p) (P * Q) =
      P * delPolynomial (p := p) Q + Q * delPolynomial (p := p) P :=
  (polynomialDerivation (p := p)).leibniz P Q

@[simp]
theorem delPolynomial_one :
    delPolynomial (p := p) (1 : E4E6Polynomial p) = 0 :=
  (polynomialDerivation (p := p)).map_one_eq_zero

private theorem weightedDegree_add_single_zero (m : Fin 2 →₀ ℕ) :
    weightedDegree (m + Finsupp.single 0 1) = weightedDegree m + 4 := by
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

private theorem weightedDegree_add_single_one (m : Fin 2 →₀ ℕ) :
    weightedDegree (m + Finsupp.single 1 1) = weightedDegree m + 6 := by
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

private theorem weightedDegree_first_delta_shift (m : Fin 2 →₀ ℕ) :
    weightedDegree (Finsupp.single 1 1 + m) =
      weightedDegree (m + Finsupp.single 0 1) + 2 := by
  rw [weightedDegree_add_single_zero]
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

private theorem weightedDegree_second_delta_shift (m : Fin 2 →₀ ℕ) :
    weightedDegree (Finsupp.single 0 2 + m) =
      weightedDegree (m + Finsupp.single 1 1) + 2 := by
  rw [weightedDegree_add_single_one]
  simp [weightedDegree, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne]
  ring

private theorem pderiv_support_source {i : Fin 2} {P : E4E6Polynomial p}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ (MvPolynomial.pderiv i P).support) :
    m + Finsupp.single i 1 ∈ P.support := by
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [MvPolynomial.coeff_pderiv] at hm
  intro hzero
  apply hm
  simp [hzero]

private theorem support_X_mul_mem {i : Fin 2} {P : E4E6Polynomial p}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ (MvPolynomial.X i * P).support) :
    ∃ n ∈ P.support, m = Finsupp.single i 1 + n := by
  rw [MvPolynomial.support_X_mul] at hm
  obtain ⟨n, hn, hnm⟩ := Finset.mem_map.1 hm
  exact ⟨n, hn, hnm.symm⟩

private theorem support_X_sq_mul_mem {P : E4E6Polynomial p}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ ((MvPolynomial.X 0) ^ 2 * P).support) :
    ∃ n ∈ P.support, m = Finsupp.single 0 2 + n := by
  have hrewrite : (MvPolynomial.X 0) ^ 2 * P =
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

private theorem delPolynomial_homogeneous {k : ℤ}
    (P : E4E6Polynomial p)
    (hP : ∀ m ∈ P.support, weightedDegree m = k) :
    ∀ m ∈ (delPolynomial (p := p) P).support,
      weightedDegree m = k + 2 := by
  intro m hm
  rw [delPolynomial_apply_smul] at hm
  have hsum := MvPolynomial.support_add hm
  simp only [Finset.mem_union] at hsum
  rcases hsum with hfirst | hsecond
  · have hfirst' : m ∈
      (MvPolynomial.X 1 * MvPolynomial.pderiv 0 P).support :=
        MvPolynomial.support_smul hfirst
    obtain ⟨n, hn, hmn⟩ := support_X_mul_mem hfirst'
    have hsource : n + Finsupp.single 0 1 ∈ P.support :=
      pderiv_support_source hn
    rw [hmn, weightedDegree_first_delta_shift, hP _ hsource]
  · have hsecond' : m ∈
      ((MvPolynomial.X 0) ^ 2 * MvPolynomial.pderiv 1 P).support :=
        MvPolynomial.support_smul hsecond
    obtain ⟨n, hn, hmn⟩ := support_X_sq_mul_mem hsecond'
    have hsource : n + Finsupp.single 1 1 ∈ P.support :=
      pderiv_support_source hn
    rw [hmn, weightedDegree_second_delta_shift, hP _ hsource]

private theorem delFourier_ofInteger {n : ℤ}
    (f : IntegerModularForm n) :
    fourierDel (p := p) n (ofInteger (p := p) f).fourier =
      PowerSeries.map (algebraMap ℤ (CoeffRing p))
        (ThetaOperator.DelOperator.normalizedDelFourier f) := by
  unfold fourierDel ThetaOperator.DelOperator.normalizedDelFourier pE2Fourier
  change
    12 • (PowerSeries.X * PowerSeries.derivative
      (PowerSeries.map (algebraMap ℤ (CoeffRing p)) f.fourier)) -
      n • (PowerSeries.map (algebraMap ℤ (CoeffRing p))
        ThetaOperator.DelOperator.e2Fourier *
        PowerSeries.map (algebraMap ℤ (CoeffRing p)) f.fourier) =
    PowerSeries.map (algebraMap ℤ (CoeffRing p))
      (12 • (PowerSeries.X * PowerSeries.derivative f.fourier) -
        n • (ThetaOperator.DelOperator.e2Fourier * f.fourier))
  simp only [map_sub, map_nsmul, map_zsmul, map_mul, PowerSeries.map_X]
  rw [← powerSeries_map_derivative]

theorem fourierDel_Eis_four :
    fourierDel (p := p) 4 (Eis (p := p) 4).fourier =
      (-4 : CoeffRing p) • (Eis (p := p) 6).fourier := by
  calc
    fourierDel (p := p) 4 (Eis (p := p) 4).fourier =
        PowerSeries.map (algebraMap ℤ (CoeffRing p))
          (ThetaOperator.DelOperator.normalizedDelFourier
            (IntegerModularForm.Eis 4)) := by
      simpa [Eis] using delFourier_ofInteger (p := p)
        (IntegerModularForm.Eis 4)
    _ = PowerSeries.map (algebraMap ℤ (CoeffRing p))
          ((-4 : ℤ) • (IntegerModularForm.Eis 6).fourier) := by
      have h := congrArg IntegerModularForm.fourier
        ThetaOperator.DelOperator.normalizedDel_Eis_four
      rw [IntegerModularForm.fourier_zsmul] at h
      simpa [ThetaOperator.DelOperator.normalizedDel_fourier] using
        congrArg (PowerSeries.map (algebraMap ℤ (CoeffRing p))) h
    _ = (-4 : CoeffRing p) • (Eis (p := p) 6).fourier := by
      simpa [Eis, ofInteger] using
        map_integer_smul (p := p) (-4 : ℤ) (IntegerModularForm.Eis 6).fourier

theorem fourierDel_Eis_six :
    fourierDel (p := p) 6 (Eis (p := p) 6).fourier =
      (-6 : CoeffRing p) •
        ((Eis (p := p) 4).fourier ^ 2) := by
  calc
    fourierDel (p := p) 6 (Eis (p := p) 6).fourier =
        PowerSeries.map (algebraMap ℤ (CoeffRing p))
          (ThetaOperator.DelOperator.normalizedDelFourier
            (IntegerModularForm.Eis 6)) := by
      simpa [Eis] using delFourier_ofInteger (p := p)
        (IntegerModularForm.Eis 6)
    _ = PowerSeries.map (algebraMap ℤ (CoeffRing p))
          ((-6 : ℤ) • ((IntegerModularForm.Eis 4).fourier ^ 2)) := by
      have h := congrArg IntegerModularForm.fourier
        ThetaOperator.DelOperator.normalizedDel_Eis_six
      rw [IntegerModularForm.fourier_zsmul] at h
      simpa [ThetaOperator.DelOperator.normalizedDel_fourier] using
        congrArg (PowerSeries.map (algebraMap ℤ (CoeffRing p))) h
    _ = (-6 : CoeffRing p) • (Eis (p := p) 4).fourier ^ 2 := by
      rw [map_integer_smul, map_pow]
      simp [Eis, ofInteger]

/-- Evaluate the first polynomial generator at the E4 Fourier series. -/
@[simp]
private theorem evaluateE4E6_X0 :
    evaluateE4E6 (p := p) (MvPolynomial.X (0 : Fin 2)) =
      (Eis (p := p) 4).fourier := by
  simp [evaluateE4E6, evaluateE4E6Hom]

@[simp]
private theorem evaluateE4E6_X1 :
    evaluateE4E6 (p := p) (MvPolynomial.X (1 : Fin 2)) =
      (Eis (p := p) 6).fourier := by
  simp [evaluateE4E6, evaluateE4E6Hom]

theorem evaluate_delPolynomial_X_zero :
    evaluateE4E6 (p := p)
      (delPolynomial (p := p) (MvPolynomial.X 0 : E4E6Polynomial p)) =
        fourierDel (p := p) 4 (evaluateE4E6 (p := p)
          (MvPolynomial.X 0 : E4E6Polynomial p)) := by
  rw [delPolynomial_X_zero]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [evaluateE4E6, evaluateE4E6Hom, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  rw [evaluateE4E6_X0]
  simpa [PowerSeries.smul_eq_C_mul] using
    (fourierDel_Eis_four (p := p)).symm

/-- The polynomial and q-series del operators agree on the E6 generator. -/
theorem evaluate_delPolynomial_X_one :
    evaluateE4E6 (p := p)
      (delPolynomial (p := p) (MvPolynomial.X 1 : E4E6Polynomial p)) =
        fourierDel (p := p) 6 (evaluateE4E6 (p := p)
          (MvPolynomial.X 1 : E4E6Polynomial p)) := by
  rw [delPolynomial_X_one]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [evaluateE4E6, evaluateE4E6Hom, map_mul, map_pow,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  rw [evaluateE4E6_X1]
  simpa [PowerSeries.smul_eq_C_mul] using
    (fourierDel_Eis_six (p := p)).symm

private theorem delPolynomial_eval_C (a : CoeffRing p) :
    evaluateE4E6 (p := p)
      (delPolynomial (p := p) (MvPolynomial.C a : E4E6Polynomial p)) =
        fourierDel (p := p) 0
          (evaluateE4E6 (p := p) (MvPolynomial.C a)) := by
  simp [delPolynomial, polynomialDerivation, fourierDel, pE2Fourier,
    evaluateE4E6, evaluateE4E6Hom, PowerSeries.derivative_C]

private theorem delPolynomial_eval_add {n : ℤ} {P Q : E4E6Polynomial p}
    (hP : evaluateE4E6 (p := p) (delPolynomial (p := p) P) =
      fourierDel (p := p) n (evaluateE4E6 (p := p) P))
    (hQ : evaluateE4E6 (p := p) (delPolynomial (p := p) Q) =
      fourierDel (p := p) n (evaluateE4E6 (p := p) Q)) :
    evaluateE4E6 (p := p) (delPolynomial (p := p) (P + Q)) =
      fourierDel (p := p) n (evaluateE4E6 (p := p) (P + Q)) := by
  change evaluateE4E6Hom (p := p) (delPolynomial (p := p) (P + Q)) =
    fourierDel (p := p) n (evaluateE4E6Hom (p := p) (P + Q))
  change evaluateE4E6Hom (p := p) (delPolynomial (p := p) P) =
      fourierDel (p := p) n (evaluateE4E6Hom (p := p) P) at hP
  change evaluateE4E6Hom (p := p) (delPolynomial (p := p) Q) =
      fourierDel (p := p) n (evaluateE4E6Hom (p := p) Q) at hQ
  calc
    evaluateE4E6Hom (p := p) (delPolynomial (p := p) (P + Q)) =
        evaluateE4E6Hom (p := p) (delPolynomial (p := p) P) +
          evaluateE4E6Hom (p := p) (delPolynomial (p := p) Q) := by
            rw [map_add (delPolynomial (p := p)), map_add (evaluateE4E6Hom (p := p))]
    _ = fourierDel (p := p) n (evaluateE4E6Hom (p := p) P) +
          fourierDel (p := p) n (evaluateE4E6Hom (p := p) Q) := by rw [hP, hQ]
    _ = fourierDel (p := p) n
          (evaluateE4E6Hom (p := p) P + evaluateE4E6Hom (p := p) Q) :=
            (fourierDel_add (p := p) n _ _).symm
    _ = fourierDel (p := p) n (evaluateE4E6Hom (p := p) (P + Q)) := by
            rw [map_add (evaluateE4E6Hom (p := p))]

private theorem delPolynomial_eval_mul {n m : ℤ} {P Q : E4E6Polynomial p}
    (hP : evaluateE4E6 (p := p) (delPolynomial (p := p) P) =
      fourierDel (p := p) n (evaluateE4E6 (p := p) P))
    (hQ : evaluateE4E6 (p := p) (delPolynomial (p := p) Q) =
      fourierDel (p := p) m (evaluateE4E6 (p := p) Q)) :
    evaluateE4E6 (p := p) (delPolynomial (p := p) (P * Q)) =
      fourierDel (p := p) (n + m)
        (evaluateE4E6 (p := p) (P * Q)) := by
  change evaluateE4E6Hom (p := p) (delPolynomial (p := p) (P * Q)) =
    fourierDel (p := p) (n + m) (evaluateE4E6Hom (p := p) (P * Q))
  change evaluateE4E6Hom (p := p) (delPolynomial (p := p) P) =
      fourierDel (p := p) n (evaluateE4E6Hom (p := p) P) at hP
  change evaluateE4E6Hom (p := p) (delPolynomial (p := p) Q) =
      fourierDel (p := p) m (evaluateE4E6Hom (p := p) Q) at hQ
  calc
    evaluateE4E6Hom (p := p) (delPolynomial (p := p) (P * Q)) =
        evaluateE4E6Hom (p := p)
          (P * delPolynomial (p := p) Q + Q * delPolynomial (p := p) P) := by
            rw [delPolynomial_leibniz]
    _ = evaluateE4E6Hom (p := p) P *
          evaluateE4E6Hom (p := p) (delPolynomial (p := p) Q) +
        evaluateE4E6Hom (p := p) Q *
          evaluateE4E6Hom (p := p) (delPolynomial (p := p) P) := by
            rw [map_add, map_mul, map_mul]
    _ = fourierDel (p := p) n (evaluateE4E6Hom (p := p) P) *
          evaluateE4E6Hom (p := p) Q +
        evaluateE4E6Hom (p := p) P *
          fourierDel (p := p) m (evaluateE4E6Hom (p := p) Q) := by
            rw [hP, hQ]
            ring
    _ = fourierDel (p := p) (n + m)
          (evaluateE4E6Hom (p := p) P * evaluateE4E6Hom (p := p) Q) := by
            symm
            exact fourierDel_mul (p := p) n m
              (evaluateE4E6Hom (p := p) P) (evaluateE4E6Hom (p := p) Q)
    _ = fourierDel (p := p) (n + m)
          (evaluateE4E6Hom (p := p) (P * Q)) := by
            rw [map_mul (evaluateE4E6Hom (p := p))]

private theorem delPolynomial_eval_X0_pow (a : ℕ) :
    evaluateE4E6 (p := p)
      (delPolynomial (p := p) ((MvPolynomial.X (0 : Fin 2) : E4E6Polynomial p) ^ a)) =
        fourierDel (p := p) (4 * (a : ℤ))
          (evaluateE4E6 (p := p)
            ((MvPolynomial.X (0 : Fin 2) : E4E6Polynomial p) ^ a)) := by
  induction a with
  | zero => simp [fourierDel, evaluateE4E6, evaluateE4E6Hom]
  | succ a ih =>
      have hmul := delPolynomial_eval_mul (p := p) ih
        (evaluate_delPolynomial_X_zero (p := p))
      simpa [pow_succ, Nat.cast_succ, mul_add, add_comm, add_left_comm,
        add_assoc, evaluateE4E6, evaluateE4E6Hom] using hmul

private theorem delPolynomial_eval_X1_pow (b : ℕ) :
    evaluateE4E6 (p := p)
      (delPolynomial (p := p) ((MvPolynomial.X (1 : Fin 2) : E4E6Polynomial p) ^ b)) =
        fourierDel (p := p) (6 * (b : ℤ))
          (evaluateE4E6 (p := p)
            ((MvPolynomial.X (1 : Fin 2) : E4E6Polynomial p) ^ b)) := by
  induction b with
  | zero => simp [fourierDel, evaluateE4E6, evaluateE4E6Hom]
  | succ b ih =>
      have hmul := delPolynomial_eval_mul (p := p) ih
        (evaluate_delPolynomial_X_one (p := p))
      simpa [pow_succ, Nat.cast_succ, mul_add, add_comm, add_left_comm,
        add_assoc, evaluateE4E6, evaluateE4E6Hom] using hmul

private theorem delPolynomial_eval_term (c : Fin (dim k)) (a : CoeffRing p) :
    evaluateE4E6 (p := p)
      (delPolynomial (p := p) (E4E6PolynomialTerm (p := p) c a)) =
        fourierDel (p := p) k
          (evaluateE4E6 (p := p) (E4E6PolynomialTerm (p := p) c a)) := by
  let a4 := (pExponent c).1.1
  let a6 := (pExponent c).1.2
  have h4 := delPolynomial_eval_X0_pow (p := p) a4
  have h6 := delPolynomial_eval_X1_pow (p := p) a6
  have hmul := delPolynomial_eval_mul (p := p) h4 h6
  have hconst := delPolynomial_eval_C (p := p) a
  have hterm := delPolynomial_eval_mul (p := p) hconst hmul
  have hw := weightedDegree_pExponent (c := c)
  have hw' : 4 * (a4 : ℤ) + 6 * (a6 : ℤ) = k := by
    simpa [a4, a6, weightedDegree] using hw
  have hshape : E4E6PolynomialTerm (p := p) c a =
      MvPolynomial.C a *
        ((MvPolynomial.X (0 : Fin 2)) ^ a4 *
          (MvPolynomial.X (1 : Fin 2)) ^ a6) := by
    simp [E4E6PolynomialTerm, a4, a6, mul_assoc]
  rw [hshape]
  simpa [hw'] using hterm

private theorem fourierDel_sum (s : Finset (Fin (dim k)))
    (F : Fin (dim k) → PowerSeries (CoeffRing p)) :
    fourierDel (p := p) k (∑ i ∈ s, F i) =
      ∑ i ∈ s, fourierDel (p := p) k (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fourierDel]
  | @insert i s hi ih => simp [hi, fourierDel_add, ih]

private theorem fourierDel_fin_sum
    (F : Fin (dim k) → PowerSeries (CoeffRing p)) :
    fourierDel (p := p) k (∑ i : Fin (dim k), F i) =
      ∑ i : Fin (dim k), fourierDel (p := p) k (F i) := by
  exact fourierDel_sum (p := p) (k := k) Finset.univ F

/-- Compatibility on every homogeneous polynomial assembled from the
`PBasis` monomials. -/
theorem evaluate_delPolynomial_polynomialOfCoordinates
    (c : Fin (dim k) → CoeffRing p) :
    evaluateE4E6 (p := p)
        (delPolynomial (p := p) (polynomialOfCoordinates (p := p) c)) =
      fourierDel (p := p) k
        (evaluateE4E6 (p := p) (polynomialOfCoordinates (p := p) c)) := by
  classical
  change evaluateE4E6Hom (p := p)
      (delPolynomial (p := p) (∑ i : Fin (dim k),
        E4E6PolynomialTerm (p := p) i (c i))) =
    fourierDel (p := p) k
      (evaluateE4E6Hom (p := p) (∑ i : Fin (dim k),
        E4E6PolynomialTerm (p := p) i (c i)) )
  have hDsum := map_sum (delPolynomial (p := p))
    (fun i : Fin (dim k) => E4E6PolynomialTerm (p := p) i (c i)) Finset.univ
  have hevalDsum := map_sum (evaluateE4E6Hom (p := p))
    (fun i : Fin (dim k) => delPolynomial (p := p)
      (E4E6PolynomialTerm (p := p) i (c i))) Finset.univ
  have hevalsum := map_sum (evaluateE4E6Hom (p := p))
    (fun i : Fin (dim k) => E4E6PolynomialTerm (p := p) i (c i)) Finset.univ
  rw [hDsum, hevalDsum, hevalsum, fourierDel_fin_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact delPolynomial_eval_term (p := p) i (c i)

/-- Compatibility between the polynomial derivation and the p-integral
modular-form operator, expressed through E4/E6 evaluation. -/
theorem evaluate_delPolynomial_polynomial (f : PIntegralModularForm p k) :
    evaluateE4E6 (p := p)
        (delPolynomial (p := p) (polynomial (p := p) f)) =
      (del f).fourier := by
  calc
    evaluateE4E6 (p := p)
        (delPolynomial (p := p) (polynomial (p := p) f)) =
      fourierDel (p := p) k
        (evaluateE4E6 (p := p) (polynomial (p := p) f)) := by
          rw [polynomial]
          exact evaluate_delPolynomial_polynomialOfCoordinates (p := p)
            ((PBasis (p := p) k).repr f)
    _ = (del f).fourier := by rw [evaluate_polynomial, del_fourier]

/-- The polynomial derivation sends the polynomial associated to a weight-`k`
form into the PBasis polynomial family of weight `k + 2`. -/
theorem delPolynomial_polynomial_isPBasisPolynomial
    (f : PIntegralModularForm p k) :
    IsPBasisPolynomial (p := p) (k := k + 2)
      (delPolynomial (p := p) (polynomial (p := p) f)) := by
  apply homogeneous_isPBasisPolynomial (p := p) (k := k + 2)
  exact delPolynomial_homogeneous (p := p) (k := k)
    (polynomial (p := p) f)
    (fun m hm => polynomial_isHomogeneous f hm)

/-- The unique polynomial coordinates intertwine the two del operators as
polynomials, without quotienting by E4/E6 evaluation. -/
theorem del_polynomial_compatible (f : PIntegralModularForm p k) :
    delPolynomial (p := p) (polynomial (p := p) f) =
      polynomial (p := p) (del f) := by
  apply polynomial_unique_of_eval (p := p) (k := k + 2) (del f)
  · exact delPolynomial_polynomial_isPBasisPolynomial (p := p) f
  · rw [evaluate_delPolynomial_polynomial]

end
end PIntegralModularForm
