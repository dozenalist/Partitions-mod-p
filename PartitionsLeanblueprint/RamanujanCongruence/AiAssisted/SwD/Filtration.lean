import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.MaximalReduce
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.Identities
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.SquarefreeAbar
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.Reduce_of_reduce





noncomputable section

variable {p : ℕ} [isLargePrime p] {k : ZMod (p - 1)}

namespace PIntegralModularForm.SwD

open IntegerModularForm
open MvPolynomial PowerSeries


private lemma mul_component_eq_component_mul
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {Sigma : Type*}
    (w : Sigma → ℕ) {A Q : MvPolynomial Sigma R} {a d : ℕ}
    (hA : MvPolynomial.IsWeightedHomogeneous w A a) :
    A * MvPolynomial.weightedHomogeneousComponent w d Q =
      MvPolynomial.weightedHomogeneousComponent w (a + d) (A * Q) := by
  classical
  ext m
  rw [MvPolynomial.coeff_mul,
    MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_mul]
  by_cases hm : Finsupp.weight w m = a + d
  · simp only [ite_eq_left hm]
    apply Finset.sum_congr rfl
    intro uv huv
    rcases Finset.mem_antidiagonal.mp huv with hsum
    by_cases hAcoeff : A.coeff uv.1 = 0
    · simp [hAcoeff]
    by_cases hQcoeff : Q.coeff uv.2 = 0
    · simp [hQcoeff, MvPolynomial.coeff_weightedHomogeneousComponent]
    have hAweight : Finsupp.weight w uv.1 = a := hA hAcoeff
    have hQweight : Finsupp.weight w uv.2 = d := by
      rw [← hsum, (Finsupp.weight w).map_add, hAweight] at hm
      exact add_left_cancel hm
    simp [hQweight, MvPolynomial.coeff_weightedHomogeneousComponent]
  · simp only [ite_eq_right hm]
    apply Finset.sum_eq_zero
    intro uv huv
    rcases Finset.mem_antidiagonal.mp huv with hsum
    by_cases hAcoeff : A.coeff uv.1 = 0
    · simp [hAcoeff]
    by_cases hQcoeff : Q.coeff uv.2 = 0
    · simp [hQcoeff, MvPolynomial.coeff_weightedHomogeneousComponent]
    have hAweight : Finsupp.weight w uv.1 = a := hA hAcoeff
    have hQweight : Finsupp.weight w uv.2 ≠ d := by
      intro hQweight
      apply hm
      rw [← hsum, (Finsupp.weight w).map_add, hAweight, hQweight]
    have hzero : (MvPolynomial.weightedHomogeneousComponent w d Q).coeff uv.2 = 0 := by
      simp [MvPolynomial.coeff_weightedHomogeneousComponent, hQweight]
    simp [hzero]


private lemma quotient_isWeightedHomogeneous
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {Sigma : Type*}
    (w : Sigma → ℕ) {A Q P : MvPolynomial Sigma R} {a k : ℕ}
    (hA : MvPolynomial.IsWeightedHomogeneous w A a) (hAne : A ≠ 0)
    (hP : MvPolynomial.IsWeightedHomogeneous w P k) (hPQ : A * Q = P) :
    MvPolynomial.IsWeightedHomogeneous w Q (k - a) := by
  intro m hm
  have hQmne : MvPolynomial.weightedHomogeneousComponent w
      (Finsupp.weight w m) Q ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun T : MvPolynomial Sigma R => T.coeff m) hzero
    have hcoeff' : Q.coeff m = 0 := by
      rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hcoeff
      simpa using hcoeff
    exact hm hcoeff'
  have hprodne : A * MvPolynomial.weightedHomogeneousComponent w
      (Finsupp.weight w m) Q ≠ 0 := mul_ne_zero hAne hQmne
  have hcompne : MvPolynomial.weightedHomogeneousComponent w
      (a + Finsupp.weight w m) P ≠ 0 := by
    rw [← hPQ, ← mul_component_eq_component_mul w hA]
    exact hprodne
  have hdegree : a + Finsupp.weight w m = k := by
    by_contra hne
    have hzero := MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
      (a + Finsupp.weight w m) hP hne
    exact hcompne hzero
  omega

private lemma top_component_ne
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {Sigma : Type*}
    (w : Sigma → ℕ) {P : MvPolynomial Sigma R} (hP : P ≠ 0) :
    MvPolynomial.weightedHomogeneousComponent w
      (MvPolynomial.weightedTotalDegree w P) P ≠ 0 := by
  obtain ⟨m, hm, hdegree⟩ := Finset.exists_mem_eq_sup P.support
    (by simpa [Finset.nonempty_iff_ne_empty, MvPolynomial.support_eq_empty] using hP)
    (Finsupp.weight w)
  intro hzero
  have hcoeff := congrArg (fun T : MvPolynomial Sigma R => T.coeff m) hzero
  have hweight : Finsupp.weight w m = MvPolynomial.weightedTotalDegree w P :=
    hdegree.symm
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, ite_eq_left hweight] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hm) hcoeff


private lemma dvd_of_homogeneous_relation
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {Sigma : Type*}
    (w : Sigma → ℕ) {A P Q : MvPolynomial Sigma R} {a j k : ℕ}
    (hA : MvPolynomial.IsWeightedHomogeneous w A a) (hAne : A ≠ 0)
    (hP : MvPolynomial.IsWeightedHomogeneous w P k) (hPne : P ≠ 0)
    (hQ : MvPolynomial.IsWeightedHomogeneous w Q j) (hjk : j < k)
    (ha : 0 < a) (hrel : P - Q ∈ Ideal.span {A - 1}) : A ∣ P := by
  obtain ⟨T, hT⟩ := (Ideal.mem_span_singleton').mp hrel
  have hRne : T ≠ 0 := by
    intro hzero
    have hPQ : P = Q := by
      have hz : 0 * (A - 1) = P - Q := by simpa [hzero] using hT
      exact sub_eq_zero.mp hz.symm
    have hQ' : MvPolynomial.IsWeightedHomogeneous w P j := by
      simpa [hPQ] using hQ
    have hkj : k = j := MvPolynomial.IsWeightedHomogeneous.inj_right hPne hP hQ'
    omega
  let d := MvPolynomial.weightedTotalDegree w T
  have hR' : T * A - T = P - Q := by
    calc
      T * A - T = T * (A - 1) := by ring
      _ = P - Q := hT
  have htopR : MvPolynomial.weightedHomogeneousComponent w d T ≠ 0 :=
    top_component_ne w hRne
  have hdle : d + a ≤ k := by
    by_contra hnot
    have hdk : k < d + a := Nat.lt_of_not_ge hnot
    have hzeroP := MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
      (d + a) hP (by omega)
    have hzeroQ := MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
      (d + a) hQ (by omega)
    have hzeroR : MvPolynomial.weightedHomogeneousComponent w (d + a) T = 0 := by
      apply MvPolynomial.weightedHomogeneousComponent_eq_zero
      dsimp [d]
      omega
    have hprod_eq : MvPolynomial.weightedHomogeneousComponent w
        (d + a) (T * A) = A * MvPolynomial.weightedHomogeneousComponent w d T := by
      calc
        MvPolynomial.weightedHomogeneousComponent w (d + a) (T * A) =
            MvPolynomial.weightedHomogeneousComponent w (a + d) (A * T) := by
          rw [mul_comm T A, add_comm]
        _ = A * MvPolynomial.weightedHomogeneousComponent w d T := by
          rw [← mul_component_eq_component_mul w hA]
    have hprod : MvPolynomial.weightedHomogeneousComponent w
        (d + a) (T * A) ≠ 0 := by
      rw [hprod_eq]
      exact mul_ne_zero hAne htopR
    have hcomp := congrArg (MvPolynomial.weightedHomogeneousComponent w (d + a)) hR'
    simp only [map_sub, hzeroP, hzeroQ, hzeroR, sub_zero] at hcomp
    exact hprod hcomp
  have hdk : d < k := by omega
  have hcomp := congrArg (MvPolynomial.weightedHomogeneousComponent w k) hR'
  have hzeroQ := MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne k hQ
    (by omega)
  have hzeroR := MvPolynomial.weightedHomogeneousComponent_eq_zero
    (w := w) (n := k) (φ := T) (by simpa [d] using hdk)
  simp only [map_sub,
    MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hP,
    hzeroQ, hzeroR, sub_zero] at hcomp
  have hprod_eq : MvPolynomial.weightedHomogeneousComponent w k (T * A) =
      A * MvPolynomial.weightedHomogeneousComponent w (k - a) T := by
    calc
      MvPolynomial.weightedHomogeneousComponent w k (T * A) =
          MvPolynomial.weightedHomogeneousComponent w k (A * T) := by rw [mul_comm]
      _ = MvPolynomial.weightedHomogeneousComponent w (a + (k - a)) (A * T) := by
        congr 2
        omega
      _ = A * MvPolynomial.weightedHomogeneousComponent w (k - a) T := by
        rw [← mul_component_eq_component_mul w hA]
  refine ⟨MvPolynomial.weightedHomogeneousComponent w (k - a) T, ?_⟩
  calc
    P = MvPolynomial.weightedHomogeneousComponent w k P := by
      symm
      exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hP
    _ = MvPolynomial.weightedHomogeneousComponent w k (T * A) := by
      calc
        _ = P := MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hP
        _ = MvPolynomial.weightedHomogeneousComponent w k (T * A) := hcomp.symm
    _ = A * MvPolynomial.weightedHomogeneousComponent w (k - a) T := hprod_eq

noncomputable def intRepresentative (a : ZMod p) : ℤ :=
  Classical.choose (ZMod.intCast_surjective a)

private theorem intRepresentative_cast (a : ZMod p) :
    (intRepresentative (p := p) a : ZMod p) = a := by
  exact Classical.choose_spec (ZMod.intCast_surjective a)

noncomputable def integralMonomial (m : Fin 2 →₀ ℕ) :
    IntegerModularForm (PIntegralModularForm.weightedDegree m) := by
  let g := (IntegerModularForm.Eis 4).pow (m 0)
  let h := (IntegerModularForm.Eis 6).pow (m 1)
  exact IntegerModularForm.Icast (by
    dsimp [g, h, PIntegralModularForm.weightedDegree]
    ring) (g.mul h)

noncomputable def exactIntegralLift
    (Q : ResiduePolynomial p) (w : ℤ)
    (hQ : ∀ m ∈ Q.support, PIntegralModularForm.weightedDegree m = w) :
    IntegerModularForm w :=
  Q.support.attach.sum fun m =>
    intRepresentative (p := p) (Q.coeff m.1) •
      (integralMonomial m.1).Icast (hQ m.1 m.2)

private theorem exactIntegralLift_reduce
    (Q : ResiduePolynomial p) (w : ℤ)
    (hQ : ∀ m ∈ Q.support, PIntegralModularForm.weightedDegree m = w) :
    (exactIntegralLift Q w hQ).reduce p =
      evaluateResiduePolynomial Q := by
  classical
  unfold exactIntegralLift evaluateResiduePolynomial
  simp only [map_sum, map_smul, IntegerModularForm.reduce_Icast]
  change _ = MvPolynomial.eval₂ PowerSeries.C
    (fun i => if i = 0 then ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier
      else ((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier) Q
  rw [MvPolynomial.eval₂_eq]
  rw [Finset.sum_attach (s := Q.support)
    (f := fun m => intRepresentative (p := p) (Q.coeff m) •
      (integralMonomial m).reduce p)]
  apply Finset.sum_congr rfl
  intro m hm
  have hcast := intRepresentative_cast (p := p) (Q.coeff m)
  calc
    intRepresentative (p := p) (Q.coeff m) •
        (integralMonomial m).reduce p =
      (intRepresentative (p := p) (Q.coeff m) : ZMod p) •
        (integralMonomial m).reduce p := by
          simp only [Int.cast_smul_eq_zsmul]
    _ = Q.coeff m • (integralMonomial m).reduce p := by rw [hcast]
    _ = _ := by
      have hE4 : ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier =
          (IntegerModularForm.Eis 4).reduce p := by
        change ((PIntegralModularForm.ofInteger (p := p)
          (IntegerModularForm.Eis 4)).Reduce).fourier =
            (IntegerModularForm.Eis 4).reduce p
        rw [PIntegralModularForm.Reduce_ofInteger]
        rw [IntegerModularForm.fourier_Reduce]
      have hE6 : ((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier =
          (IntegerModularForm.Eis 6).reduce p := by
        change ((PIntegralModularForm.ofInteger (p := p)
          (IntegerModularForm.Eis 6)).Reduce).fourier =
            (IntegerModularForm.Eis 6).reduce p
        rw [PIntegralModularForm.Reduce_ofInteger]
        rw [IntegerModularForm.fourier_Reduce]
      rw [PowerSeries.smul_eq_C_mul]
      congr 1
      simp only [integralMonomial, IntegerModularForm.reduce_Icast,
        IntegerModularForm.reduce_mul, IntegerModularForm.reduce_pow]
      change _ = m.prod (fun i n => (if i = 0 then
        ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier else
        ((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier) ^ n)
      rw [Finsupp.prod_fintype m
        (fun i n => (if i = 0 then
          ((PIntegralModularForm.Eis (p := p) 4).Reduce).fourier else
          ((PIntegralModularForm.Eis (p := p) 6).Reduce).fourier) ^ n)
        (by intro i; simp)]
      simp [Fin.prod_univ_two, hE4, hE6]

private lemma homogeneous_nat_of_integer
    {p : ℕ} {P : ResiduePolynomial p} {w : ℤ}
    (hP : ∀ m ∈ P.support,
      PIntegralModularForm.weightedDegree m = w) (hPne : P ≠ 0) :
    MvPolynomial.IsWeightedHomogeneous polynomialWeights P
      (MvPolynomial.weightedTotalDegree polynomialWeights P) := by
  have hsupport : P.support.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty, MvPolynomial.support_eq_empty] using hPne
  obtain ⟨m₀, hm₀⟩ := hsupport
  intro m hm
  have hm_mem : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hm
  have hm₀_mem : m₀ ∈ P.support := hm₀
  have hm' := hP m hm_mem
  have hm₀' := hP m₀ hm₀_mem
  have hcast : (Finsupp.weight polynomialWeights m : ℤ) =
      (Finsupp.weight polynomialWeights m₀ : ℤ) := by
    calc
      (Finsupp.weight polynomialWeights m : ℤ) =
          PIntegralModularForm.weightedDegree m := by
            simp [PIntegralModularForm.weightedDegree, polynomialWeights,
              Finsupp.weight_eq_sum]
            ring
      _ = w := hm'
      _ = PIntegralModularForm.weightedDegree m₀ := hm₀'.symm
      _ = (Finsupp.weight polynomialWeights m₀ : ℤ) := by
            simp [PIntegralModularForm.weightedDegree, polynomialWeights,
              Finsupp.weight_eq_sum]
            ring
  have heq : ∀ m ∈ P.support,
      Finsupp.weight polynomialWeights m = Finsupp.weight polynomialWeights m₀ := by
    intro m hm
    have hm' := hP m hm
    have hcast : (Finsupp.weight polynomialWeights m : ℤ) =
        (Finsupp.weight polynomialWeights m₀ : ℤ) := by
      calc
        (Finsupp.weight polynomialWeights m : ℤ) =
            PIntegralModularForm.weightedDegree m := by
              simp [PIntegralModularForm.weightedDegree, polynomialWeights,
                Finsupp.weight_eq_sum]
              ring
        _ = w := hm'
        _ = PIntegralModularForm.weightedDegree m₀ := hm₀'.symm
        _ = (Finsupp.weight polynomialWeights m₀ : ℤ) := by
              simp [PIntegralModularForm.weightedDegree, polynomialWeights,
                Finsupp.weight_eq_sum]
              ring
    exact_mod_cast hcast
  have htotal : ((MvPolynomial.weightedTotalDegree polynomialWeights P : ℕ) : ℤ) =
      (Finsupp.weight polynomialWeights m₀ : ℤ) := by
    have htotalNat : MvPolynomial.weightedTotalDegree polynomialWeights P =
        Finsupp.weight polynomialWeights m₀ := by
      unfold MvPolynomial.weightedTotalDegree
      apply le_antisymm
      · exact Finset.sup_le (fun m hm => le_of_eq (heq m hm))
      · exact Finset.le_sup hm₀
    exact_mod_cast htotalNat
  calc
    Finsupp.weight polynomialWeights m = Finsupp.weight polynomialWeights m₀ :=
      heq m (MvPolynomial.mem_support_iff.mpr hm)
    _ = MvPolynomial.weightedTotalDegree polynomialWeights P := by
      exact_mod_cast htotal.symm

private lemma totalDegree_cast_of_integer
    {p : ℕ} {P : ResiduePolynomial p} {w : ℤ}
    (hP : ∀ m ∈ P.support,
      PIntegralModularForm.weightedDegree m = w) (hPne : P ≠ 0) :
    ((MvPolynomial.weightedTotalDegree polynomialWeights P : ℕ) : ℤ) = w := by
  have hsupport : P.support.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty, MvPolynomial.support_eq_empty] using hPne
  obtain ⟨m, hm⟩ := hsupport
  have hhom := homogeneous_nat_of_integer hP hPne
  calc
    ((MvPolynomial.weightedTotalDegree polynomialWeights P : ℕ) : ℤ) =
        (Finsupp.weight polynomialWeights m : ℤ) := by
      exact_mod_cast (hhom (MvPolynomial.mem_support_iff.mp hm)).symm
    _ = PIntegralModularForm.weightedDegree m := by
          simp [PIntegralModularForm.weightedDegree, polynomialWeights,
            Finsupp.weight_eq_sum]
          ring
    _ = w := hP m hm


/-- Proposition 1.44(1): the reduction of a `p`-integral form has filtration
strictly below its original weight exactly when the reduced Hasse polynomial
divides the reduction of its canonical `E₄`/`E₆` polynomial representative.

Here `PIntegralModularForm.polynomial f` is the unique polynomial `Φ` from
the proposition, and `reducePolynomial` supplies `Φ̄`. -/
theorem Filtration_Reduce_lt_iff {k} (f : PIntegralModularForm p k) (hf : f.Reduce ≠ 0) :
    f.Reduce.Filtration < k ↔ Abar ∣ reducePolynomial f.polynomial := by
  let P : ResiduePolynomial p := reducePolynomial f.polynomial
  have hP_eval : evaluateResiduePolynomial P = f.Reduce.fourier := by
    calc
      evaluateResiduePolynomial P =
          PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
            (PIntegralModularForm.evaluateE4E6 f.polynomial) := by
        exact evaluateResiduePolynomial_reducePolynomial f.polynomial
      _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p)) f.fourier := by
        rw [PIntegralModularForm.evaluate_polynomial]
      _ = f.Reduce.fourier := rfl
  have hPne : P ≠ 0 := by
    intro hzero
    apply hf
    apply ModularFormMod.fourier_inj
    rw [← hP_eval, hzero]
    simp [evaluateResiduePolynomial]
  have hPint : ∀ m ∈ P.support,
      PIntegralModularForm.weightedDegree m = k := by
    intro m hm
    have hm' : m ∈ f.polynomial.support := by
      exact MvPolynomial.support_map_subset
        (f := PIntegralModularForm.coeffToZMod (p := p)) f.polynomial hm
    exact PIntegralModularForm.polynomial_isHomogeneous f hm'
  have hPnat := homogeneous_nat_of_integer hPint hPne
  have hPdeg := totalDegree_cast_of_integer hPint hPne
  have hA := Abar_isWeightedHomogeneous (p := p)
  have hAne : Abar (p := p) ≠ 0 := Abar_ne_zero (p := p)
  have hapos : 0 < p - 1 := by
    have hp5 := (inferInstance : isLargePrime p).AtLeastFive
    omega
  have : NeZero f.Reduce := ⟨hf⟩
  constructor
  · intro hlt
    obtain ⟨g, hg⟩ := (ModularFormMod.Filtration_spec f.Reduce).exists_reduce
    let gLift : PIntegralModularForm p f.Reduce.Filtration :=
      PIntegralModularForm.ofInteger g
    let Q : ResiduePolynomial p := reducePolynomial gLift.polynomial
    have hQ_eval : evaluateResiduePolynomial Q = g.reduce p := by
      calc
        evaluateResiduePolynomial Q =
            PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
              (PIntegralModularForm.evaluateE4E6 gLift.polynomial) := by
          exact evaluateResiduePolynomial_reducePolynomial gLift.polynomial
        _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p)) gLift.fourier := by
          rw [PIntegralModularForm.evaluate_polynomial]
        _ = (gLift.Reduce).fourier := rfl
        _ = (g.Reduce p).fourier := by
          exact congrArg ModularFormMod.fourier
            (PIntegralModularForm.Reduce_ofInteger (p := p) g)
        _ = g.reduce p := rfl
    have hQne : Q ≠ 0 := by
      intro hzero
      have : g.reduce p = 0 := by
        rw [← hQ_eval, hzero]
        simp [evaluateResiduePolynomial]
      apply hf
      apply ModularFormMod.fourier_inj
      rw [hg, this]
      rfl
    have hQint : ∀ m ∈ Q.support,
        PIntegralModularForm.weightedDegree m = f.Reduce.Filtration := by
      intro m hm
      have hm' : m ∈ gLift.polynomial.support := by
        exact MvPolynomial.support_map_subset
          (f := PIntegralModularForm.coeffToZMod (p := p)) gLift.polynomial hm
      exact PIntegralModularForm.polynomial_isHomogeneous gLift hm'
    have hQnat := homogeneous_nat_of_integer hQint hQne
    have hQdeg := totalDegree_cast_of_integer hQint hQne
    have hclass : (f.Reduce.Filtration : ZMod (p - 1)) = (k : ZMod (p - 1)) := by
      obtain ⟨hclass, _⟩ := Reduce_of_reduce (f := f.Reduce) (b := g) hg.symm
      exact hclass
    let P' : ResidueWeightedPolynomial (p := p) (k : ZMod (p - 1)) :=
      { polynomial := P
        homogeneous := by
          intro m hm
          exact congrArg (fun z : ℤ => (z : ZMod (p - 1))) (hPint m hm) }
    let Q' : ResidueWeightedPolynomial (p := p) (k : ZMod (p - 1)) :=
      { polynomial := Q
        homogeneous := by
          intro m hm
          exact (congrArg (fun z : ℤ => (z : ZMod (p - 1)))
            (hQint m hm)).trans hclass }
    have hrel : P - Q ∈ Ideal.span {Abar (p := p) - 1} := by
      simpa [P', Q', hasseIdeal] using
        (hasseIdeal_complete (p := p) P' Q'
          (hP_eval.trans (hg.trans hQ_eval.symm)))
    have hltNat : MvPolynomial.weightedTotalDegree polynomialWeights Q <
        MvPolynomial.weightedTotalDegree polynomialWeights P := by
      have hQdeg' := hQdeg
      have hPdeg' := hPdeg
      omega
    exact dvd_of_homogeneous_relation polynomialWeights hA hAne hPnat hPne hQnat
      hltNat hapos hrel
  · intro hdiv
    obtain ⟨Q, hPQ⟩ := hdiv
    have hQne : Q ≠ 0 := by
      intro hzero
      apply hPne
      change reducePolynomial f.polynomial = 0
      rw [hPQ]
      simp [hzero]
    have hQnat : MvPolynomial.IsWeightedHomogeneous polynomialWeights Q
        (MvPolynomial.weightedTotalDegree polynomialWeights P - (p - 1)) :=
      quotient_isWeightedHomogeneous polynomialWeights hA hAne hPnat hPQ.symm
    let dQ : ℕ := MvPolynomial.weightedTotalDegree polynomialWeights P - (p - 1)
    have hAQ : MvPolynomial.IsWeightedHomogeneous polynomialWeights
        (Abar (p := p) * Q) (p - 1 + dQ) := by
      simpa [dQ] using hA.mul hQnat
    have hAQ' : MvPolynomial.IsWeightedHomogeneous polynomialWeights P (p - 1 + dQ) := by
      change MvPolynomial.IsWeightedHomogeneous polynomialWeights
        (reducePolynomial f.polynomial) (p - 1 + dQ)
      rw [hPQ]
      exact hAQ
    have hdegree : p - 1 + dQ = MvPolynomial.weightedTotalDegree polynomialWeights P := by
      have hdegree' := MvPolynomial.IsWeightedHomogeneous.inj_right hPne hPnat hAQ'
      exact hdegree'.symm
    have hdQlt : dQ < MvPolynomial.weightedTotalDegree polynomialWeights P := by
      omega
    have hQint : ∀ m ∈ Q.support,
        PIntegralModularForm.weightedDegree m = (dQ : ℤ) := by
      intro m hm
      have hm' := hQnat (MvPolynomial.mem_support_iff.mp hm)
      have hcast : (Finsupp.weight polynomialWeights m : ℤ) = (dQ : ℤ) := by
        exact_mod_cast hm'
      calc
        PIntegralModularForm.weightedDegree m =
            (Finsupp.weight polynomialWeights m : ℤ) := by
              simp [PIntegralModularForm.weightedDegree, polynomialWeights,
                Finsupp.weight_eq_sum]
              ring
        _ = (dQ : ℤ) := hcast
    let g := exactIntegralLift Q (dQ : ℤ) hQint
    have hQ_eval : g.reduce p = evaluateResiduePolynomial Q :=
      exactIntegralLift_reduce Q (dQ : ℤ) hQint
    have hEvalQ : evaluateResiduePolynomial Q = evaluateResiduePolynomial P := by
      change evaluateResiduePolynomial Q =
        evaluateResiduePolynomial (reducePolynomial f.polynomial)
      calc
        evaluateResiduePolynomial Q = 1 * evaluateResiduePolynomial Q := by simp
        _ = evaluateResiduePolynomial (Abar (p := p)) *
              evaluateResiduePolynomial Q := by rw [evaluate_Abar]
        _ = evaluateResiduePolynomial (Abar (p := p) * Q) := by rw [map_mul]
        _ = evaluateResiduePolynomial (reducePolynomial f.polynomial) := by
          rw [← hPQ]
    have hweight : f.Reduce.hasWeight (dQ : ℤ) := by
      change f.Reduce.fourier ∈ Set.range (@IntegerModularForm.reduce (dQ : ℤ) p)
      exact ⟨g, hQ_eval.trans (hEvalQ.trans hP_eval)⟩
    have hle := ModularFormMod.Filtration_le hweight
    have hlt : (dQ : ℤ) < k := by
      have hPdeg' := hPdeg
      omega
    exact lt_of_le_of_lt hle hlt


end PIntegralModularForm.SwD


namespace PIntegralModularForm.SwD

open IntegerModularForm

variable {p : ℕ} [isLargePrime p] {n : ℤ}

/-- The p-integral numerator in the Ramanujan identity, at weight
`n + p + 1`. -/
noncomputable def thetaNumerator (g : PIntegralModularForm p n) :
    PIntegralModularForm p (n + (p : ℤ) + 1) := by
  exact PIntegralModularForm.castWeight (by ring)
      ((normalizedEisMinusOne (p := p)).mul (PIntegralModularForm.del g)) +
      (n : PIntegralModularForm.CoeffRing p) •
        PIntegralModularForm.castWeight (by ring)
          ((normalizedEisPlusOne (p := p)).mul g)

private theorem thetaNumerator_polynomial (g : PIntegralModularForm p n) :
    PIntegralModularForm.polynomial (thetaNumerator g) =
      A (p := p) *
          PIntegralModularForm.delPolynomial (p := p)
            (PIntegralModularForm.polynomial g) +
        (n : PIntegralModularForm.CoeffRing p) •
          (B (p := p) * PIntegralModularForm.polynomial g) := by
  symm
  apply PIntegralModularForm.polynomial_unique_of_eval
  · apply PIntegralModularForm.homogeneous_isPBasisPolynomial
    intro m hm
    have hm' := MvPolynomial.support_add hm
    rcases Finset.mem_union.mp hm' with hm' | hm'
    · have hmul := MvPolynomial.support_mul (A (p := p))
        (PIntegralModularForm.delPolynomial (p := p)
          (PIntegralModularForm.polynomial g)) hm'
      rcases Finset.mem_add.mp hmul with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
      have hA : PIntegralModularForm.weightedDegree m₁ = (p : ℤ) - 1 := by
        simpa [A] using PIntegralModularForm.polynomial_isHomogeneous
          (normalizedEisMinusOne (p := p)) hm₁
      have hD : PIntegralModularForm.weightedDegree m₂ = n + 2 := by
        rw [PIntegralModularForm.del_polynomial_compatible] at hm₂
        exact PIntegralModularForm.polynomial_isHomogeneous (PIntegralModularForm.del g) hm₂
      calc
        PIntegralModularForm.weightedDegree (m₁ + m₂) =
            PIntegralModularForm.weightedDegree m₁ +
              PIntegralModularForm.weightedDegree m₂ := by
          simp [PIntegralModularForm.weightedDegree, Finsupp.add_apply]
          ring
        _ = n + (p : ℤ) + 1 := by rw [hA, hD]; ring
    · have hmB : m ∈
          (B (p := p) * PIntegralModularForm.polynomial g).support :=
        MvPolynomial.support_smul hm'
      have hmul := MvPolynomial.support_mul (B (p := p))
        (PIntegralModularForm.polynomial g) hmB
      rcases Finset.mem_add.mp hmul with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
      have hB : PIntegralModularForm.weightedDegree m₁ = (p : ℤ) + 1 := by
        simpa [B] using PIntegralModularForm.polynomial_isHomogeneous
          (normalizedEisPlusOne (p := p)) hm₁
      have hP : PIntegralModularForm.weightedDegree m₂ = n :=
        PIntegralModularForm.polynomial_isHomogeneous g hm₂
      calc
        PIntegralModularForm.weightedDegree (m₁ + m₂) =
            PIntegralModularForm.weightedDegree m₁ +
              PIntegralModularForm.weightedDegree m₂ := by
          simp [PIntegralModularForm.weightedDegree, Finsupp.add_apply]
          ring
        _ = n + (p : ℤ) + 1 := by rw [hB, hP]; ring
  · calc
      PIntegralModularForm.evaluateE4E6 (p := p)
          (A (p := p) * PIntegralModularForm.delPolynomial (p := p)
            (PIntegralModularForm.polynomial g) +
          (n : PIntegralModularForm.CoeffRing p) •
            (B (p := p) * PIntegralModularForm.polynomial g)) =
          (normalizedEisMinusOne (p := p)).fourier *
              (PIntegralModularForm.del g).fourier +
            (n : PIntegralModularForm.CoeffRing p) •
              ((normalizedEisPlusOne (p := p)).fourier * g.fourier) := by
        unfold PIntegralModularForm.evaluateE4E6
        rw [MvPolynomial.smul_eq_C_mul]
        rw [map_add, map_mul, map_mul]
        simp only [PIntegralModularForm.evaluateE4E6Hom,
          MvPolynomial.eval₂Hom_C]
        rw [map_mul]
        rw [PowerSeries.smul_eq_C_mul]
        change PIntegralModularForm.evaluateE4E6 (p := p) (A (p := p)) *
              PIntegralModularForm.evaluateE4E6 (p := p)
                (PIntegralModularForm.delPolynomial (p := p)
                  (PIntegralModularForm.polynomial g)) +
            PowerSeries.C (n : PIntegralModularForm.CoeffRing p) *
              (PIntegralModularForm.evaluateE4E6 (p := p) (B (p := p)) *
                PIntegralModularForm.evaluateE4E6 (p := p)
                  (PIntegralModularForm.polynomial g)) = _
        rw [evaluate_A, evaluate_B,
          PIntegralModularForm.evaluate_delPolynomial_polynomial,
          PIntegralModularForm.evaluate_polynomial]
      _ = (thetaNumerator g).fourier := by
        simp [thetaNumerator, PIntegralModularForm.castWeight,
          PIntegralModularForm.fourier_add, PIntegralModularForm.fourier_mul]

private theorem reducePolynomial_thetaNumerator (g : PIntegralModularForm p n) :
    reducePolynomial (p := p) (PIntegralModularForm.polynomial (thetaNumerator g)) =
      Abar (p := p) * reducePolynomial (p := p)
          (PIntegralModularForm.delPolynomial (p := p)
            (PIntegralModularForm.polynomial g)) +
        MvPolynomial.C (n : ZMod p) *
          (Bbar (p := p) * reducePolynomial (p := p)
            (PIntegralModularForm.polynomial g)) := by
  rw [thetaNumerator_polynomial]
  simp [reducePolynomial, Abar, Bbar, MvPolynomial.smul_eq_C_mul]

private theorem thetaNumerator_fourier_reduce (g : PIntegralModularForm p n) :
    (thetaNumerator g).Reduce.fourier =
      (12 : ZMod p) • ThetaOperator.DelOperator.thetaSeries g.Reduce := by
  let φ := PIntegralModularForm.coeffToZMod (p := p)
  have hderiv (F : PowerSeries (PIntegralModularForm.CoeffRing p)) :
      PowerSeries.map φ (PowerSeries.derivative F) =
        PowerSeries.derivative (PowerSeries.map φ F) := by
    ext m
    simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]
  have hminus : PowerSeries.map φ (normalizedEisMinusOne (p := p)).fourier = 1 := by
    have h := evaluate_Abar (p := p)
    rw [Abar, evaluateResiduePolynomial_reducePolynomial, evaluate_A] at h
    exact h
  have hplus : PowerSeries.map φ (normalizedEisPlusOne (p := p)).fourier =
      (ThetaOperator.E₂ (ℓ := p)).fourier :=
    normalizedEisPlusOne_reduce (p := p)
  have hE₂ : (ThetaOperator.E₂ (ℓ := p)).fourier =
      PowerSeries.map (Int.castRingHom (ZMod p))
        ThetaOperator.DelOperator.e2Fourier := by
    apply PowerSeries.ext
    intro m
    change (ThetaOperator.E₂ (ℓ := p)).coeff m = _
    rw [ThetaOperator.coeff_E₂]
    simp [ThetaOperator.DelOperator.e2Fourier]
  have hpE₂ : PowerSeries.map φ (PIntegralModularForm.pE2Fourier (p := p)) =
      (ThetaOperator.E₂ (ℓ := p)).fourier := by
    rw [hE₂]
    apply PowerSeries.ext
    intro m
    simp [PIntegralModularForm.pE2Fourier, PowerSeries.coeff_map]
  have hdel : PowerSeries.map φ (PIntegralModularForm.del g).fourier =
      12 • (PowerSeries.X * PowerSeries.derivative (PowerSeries.map φ g.fourier)) -
        (n : ZMod p) •
          ((ThetaOperator.E₂ (ℓ := p)).fourier * PowerSeries.map φ g.fourier) := by
    rw [PIntegralModularForm.del_fourier, PIntegralModularForm.fourierDel]
    simp only [map_sub, map_nsmul, map_zsmul, map_mul, PowerSeries.map_X,
      hderiv, hpE₂]
    simp only [Int.cast_smul_eq_zsmul]
  have hsmul (a : PIntegralModularForm.CoeffRing p)
      (F : PowerSeries (PIntegralModularForm.CoeffRing p)) :
      PowerSeries.map φ (a • F) = φ a • PowerSeries.map φ F := by
    ext m
    simp [PowerSeries.coeff_map]
  change PowerSeries.map φ
      ((normalizedEisMinusOne (p := p)).fourier * (PIntegralModularForm.del g).fourier +
        (n : PIntegralModularForm.CoeffRing p) •
          ((normalizedEisPlusOne (p := p)).fourier * g.fourier)) = _
  rw [map_add, map_mul, hsmul, map_mul, hminus, hdel, hplus]
  change _ = (12 : ZMod p) •
    (PowerSeries.X * PowerSeries.derivative (g.Reduce).fourier)
  rw [PIntegralModularForm.fourier_Reduce]
  simp [φ, nsmul_eq_mul]
  change PowerSeries.C (12 : ZMod p) * _ = _
  exact (PowerSeries.smul_eq_C_mul _ _).symm

end PIntegralModularForm.SwD

namespace SwD

open PIntegralModularForm.SwD

private theorem filtration_nonneg (f : ModularFormMod p k) (hf : f ≠ 0) :
    0 ≤ f.Filtration := by
  have : NeZero f := ⟨hf⟩
  apply le_csInf (ModularFormMod.nonempty_hasWeight_set f)
  intro j hj
  obtain ⟨g, hg⟩ := hj.exists_reduce
  by_contra! hjneg
  have hg0 : g ≠ 0 := by
    intro hzero
    apply hf
    apply ModularFormMod.fourier_inj
    rw [hzero, map_zero] at hg
    simpa using hg
  exact hg0 (by
    apply IntegerModularForm.carrier_inj
    ext z
    rw [ModularFormClass.levelOne_neg_weight_eq_zero hjneg]
    rfl)

private theorem hasWeight_smul {r : ZMod (p - 1)} (f : ModularFormMod p r) (a : ZMod p)
    {j : ℤ} (hj : f.hasWeight j) : (a • f).hasWeight j := by
  obtain ⟨g, hg⟩ := hj.exists_reduce
  refine ⟨intRepresentative (p := p) a • g, ?_⟩
  change PowerSeries.map (Int.castRingHom (ZMod p))
      (intRepresentative (p := p) a • g.fourier) = a • f.fourier
  rw [map_zsmul]
  rw [← Int.cast_smul_eq_zsmul (ZMod p)]
  rw [intRepresentative_cast, hg]
  rfl

private theorem filtration_smul_eq {r : ZMod (p - 1)}
    (f : ModularFormMod p r) (hf : f ≠ 0)
    (a : ZMod p) (ha : a ≠ 0) : (a • f).Filtration = f.Filtration := by
  have : NeZero f := ⟨hf⟩
  have hscale : a • f ≠ 0 := by
    intro h
    have hfourier : a • f.fourier = 0 := by
      simpa using congrArg ModularFormMod.fourier h
    rcases smul_eq_zero.mp hfourier with ha0 | hf0
    · exact ha ha0
    · exact hf (ModularFormMod.fourier_inj hf0)
  have : NeZero (a • f) := ⟨hscale⟩
  apply le_antisymm
  · exact ModularFormMod.Filtration_le
      (hasWeight_smul f a (ModularFormMod.Filtration_spec f))
  · have hweight := hasWeight_smul (a • f) a⁻¹
      (ModularFormMod.Filtration_spec (a • f))
    have hweight' : f.hasWeight (a • f).Filtration := by
      simpa [smul_smul, ha] using hweight
    exact ModularFormMod.Filtration_le hweight'

private noncomputable def filtrationLift (f : ModularFormMod p k) :
    PIntegralModularForm p f.Filtration :=
  PIntegralModularForm.ofInteger f.Filtration_choose

private theorem filtrationLift_fourier (f : ModularFormMod p k) :
    (filtrationLift f).Reduce.fourier = f.fourier := by
  change (PIntegralModularForm.ofInteger f.Filtration_choose).Reduce.fourier = _
  rw [PIntegralModularForm.Reduce_ofInteger,
    IntegerModularForm.fourier_Reduce]
  exact (ModularFormMod.Filtration_choose_spec f).symm

private theorem thetaNumerator_hasWeight {k} (g : PIntegralModularForm p k) :
    (thetaNumerator g).Reduce.hasWeight (k + (p : ℤ) + 1) := by
  let Q : ResiduePolynomial p :=
    reducePolynomial (p := p)
      (PIntegralModularForm.polynomial (thetaNumerator g))
  have hQ : ∀ m ∈ Q.support,
      PIntegralModularForm.weightedDegree m = k + (p : ℤ) + 1 := by
    intro m hm
    have hm' : m ∈ (PIntegralModularForm.polynomial (thetaNumerator g)).support :=
      MvPolynomial.support_map_subset
        (f := PIntegralModularForm.coeffToZMod (p := p))
        (PIntegralModularForm.polynomial (thetaNumerator g)) hm
    exact PIntegralModularForm.polynomial_isHomogeneous (thetaNumerator g) hm'
  let H : IntegerModularForm (k + (p : ℤ) + 1) :=
    exactIntegralLift Q (k + (p : ℤ) + 1) hQ
  refine ⟨H, ?_⟩
  rw [exactIntegralLift_reduce]
  calc
    evaluateResiduePolynomial Q =
        PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
          (PIntegralModularForm.evaluateE4E6 (p := p)
            (PIntegralModularForm.polynomial (thetaNumerator g))) := by
      exact evaluateResiduePolynomial_reducePolynomial (p := p)
        (PIntegralModularForm.polynomial (thetaNumerator g))
    _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
          (thetaNumerator g).fourier := by
      rw [PIntegralModularForm.evaluate_polynomial]
    _ = (thetaNumerator g).Reduce.fourier := rfl

private theorem theta_hasWeight_of_lift (f : ModularFormMod p k)
    (g : PIntegralModularForm p f.Filtration)
    (hg : g.Reduce.fourier = f.fourier) :
    f.Theta.hasWeight (f.Filtration + (p : ℤ) + 1) := by
  obtain ⟨H, hH⟩ := thetaNumerator_hasWeight (p := p) g
  have hthetaSeries : ThetaOperator.DelOperator.thetaSeries g.Reduce =
      f.Theta.fourier := by
    rw [ThetaOperator.DelOperator.thetaSeries, hg,
      ModularFormMod.fourier_Theta]
    rfl
  have hHtheta : H.reduce p = (12 : ZMod p) • f.Theta.fourier := by
    calc
      H.reduce p = (thetaNumerator g).Reduce.fourier := hH
      _ = (12 : ZMod p) • ThetaOperator.DelOperator.thetaSeries g.Reduce :=
        thetaNumerator_fourier_reduce (p := p) g
      _ = (12 : ZMod p) • f.Theta.fourier := by rw [hthetaSeries]
  let c : ℤ := intRepresentative (p := p) ((12 : ZMod p)⁻¹)
  have hc : (c : ZMod p) = (12 : ZMod p)⁻¹ :=
    intRepresentative_cast (p := p) _
  refine ⟨c • H, ?_⟩
  calc
    (c • H).reduce p = (c : ZMod p) • H.reduce p := by
      change PowerSeries.map (Int.castRingHom (ZMod p)) (c • H.fourier) = _
      rw [map_zsmul]
      simp only [Int.cast_smul_eq_zsmul]
      rfl
    _ = (12 : ZMod p)⁻¹ • ((12 : ZMod p) • f.Theta.fourier) := by
      rw [hc, hHtheta]
    _ = f.Theta.fourier := by
      have h12 : (12 : ZMod p) ≠ 0 :=
        (ThetaOperator.DelOperator.isUnit_twelve (ℓ := p)).ne_zero
      simp [smul_smul, h12]

private theorem thetaNumerator_A_divides_iff (f : ModularFormMod p k)
    (hf : f ≠ 0) :
    Abar (p := p) ∣ reducePolynomial (p := p)
      (PIntegralModularForm.polynomial
        (thetaNumerator (filtrationLift f))) ↔
      (f.Filtration : ZMod p) = 0 := by
  let g := filtrationLift f
  let P : ResiduePolynomial p :=
    reducePolynomial (p := p) (PIntegralModularForm.polynomial g)
  let D : ResiduePolynomial p :=
    reducePolynomial (p := p)
      (PIntegralModularForm.delPolynomial (p := p)
        (PIntegralModularForm.polynomial g))
  let Q : ResiduePolynomial p :=
    reducePolynomial (p := p)
      (PIntegralModularForm.polynomial (thetaNumerator g))
  have hg : g.Reduce.fourier = f.fourier := filtrationLift_fourier f
  have hg0 : g.Reduce ≠ 0 := by
    intro hz
    apply hf
    apply ModularFormMod.fourier_inj
    have hzero : g.Reduce.fourier = 0 := by
      exact congrArg ModularFormMod.fourier hz
    rw [hg] at hzero
    exact hzero
  have hfilg : g.Reduce.Filtration = f.Filtration := by
    apply ModularFormMod.Filtration_ext
    intro i
    simpa only [ModularFormMod.coeff_def] using
      congrArg (fun S : PowerSeries (ZMod p) => S.coeff i) hg
  have hPnot : ¬ Abar (p := p) ∣ P := by
    intro hdiv
    have hlt := (Filtration_Reduce_lt_iff g hg0).2 (by simpa [P] using hdiv)
    rw [hfilg] at hlt
    exact (lt_irrefl _ hlt)
  have hformula : Q = Abar (p := p) * D +
      MvPolynomial.C (f.Filtration : ZMod p) * (Bbar (p := p) * P) := by
    simpa [P, D, Q, g] using
      (reducePolynomial_thetaNumerator (p := p) (g := g))
  constructor
  · intro hdiv
    have hdivQ : Abar (p := p) ∣ Q := by simpa [Q, g] using hdiv
    obtain ⟨R, hR⟩ := hdivQ
    have hscalar : Abar (p := p) ∣
        MvPolynomial.C (f.Filtration : ZMod p) * (Bbar (p := p) * P) := by
      refine ⟨R - D, ?_⟩
      calc
        MvPolynomial.C (f.Filtration : ZMod p) * (Bbar (p := p) * P) =
            Q - Abar (p := p) * D := by rw [hformula]; ring
        _ = Abar (p := p) * R - Abar (p := p) * D := by rw [hR]
        _ = Abar (p := p) * (R - D) := by ring
    by_cases hc : (f.Filtration : ZMod p) = 0
    · exact hc
    · have hC : IsUnit
          (MvPolynomial.C (f.Filtration : ZMod p) : ResiduePolynomial p) :=
        IsUnit.map (MvPolynomial.C : ZMod p →+* ResiduePolynomial p)
          (isUnit_iff_ne_zero.mpr hc)
      have hBP : Abar (p := p) ∣ Bbar (p := p) * P :=
        hC.dvd_mul_left.mp hscalar
      have hPdiv : Abar (p := p) ∣ P :=
        (lemma_1_40_coprime (p := p)).dvd_of_dvd_mul_left hBP
      exact (hPnot hPdiv).elim
  · intro hc
    change Abar (p := p) ∣ Q
    rw [hformula, hc]
    exact ⟨D, by simp⟩

private theorem thetaNumerator_reducePolynomial_eq_zero
    (f : ModularFormMod p k) (htheta : f.Theta = 0) :
    reducePolynomial (p := p)
      (PIntegralModularForm.polynomial
        (thetaNumerator (filtrationLift f))) = 0 := by
  let g := filtrationLift f
  let N := thetaNumerator g
  have hg : g.Reduce.fourier = f.fourier := filtrationLift_fourier f
  have hthetaSeries : ThetaOperator.DelOperator.thetaSeries g.Reduce =
      f.Theta.fourier := by
    rw [ThetaOperator.DelOperator.thetaSeries, hg,
      ModularFormMod.fourier_Theta]
    rfl
  have hthetaZero : ThetaOperator.DelOperator.thetaSeries g.Reduce = 0 := by
    rw [hthetaSeries, htheta]
    simp
  have hN : N.Reduce.fourier = 0 := by
    rw [show N = thetaNumerator g from rfl,
      thetaNumerator_fourier_reduce, hthetaZero]
    simp
  have hEval :
      evaluateResiduePolynomial (p := p)
          (reducePolynomial (p := p) (PIntegralModularForm.polynomial N)) =
        evaluateResiduePolynomial (p := p)
          (reducePolynomial (p := p) (0 : PIntegralModularForm.E4E6Polynomial p)) := by
    calc
      _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p))
          (PIntegralModularForm.evaluateE4E6 (p := p)
            (PIntegralModularForm.polynomial N)) := by
          exact evaluateResiduePolynomial_reducePolynomial (p := p)
            (PIntegralModularForm.polynomial N)
      _ = PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p)) N.fourier := by
          rw [PIntegralModularForm.evaluate_polynomial]
      _ = N.Reduce.fourier := rfl
      _ = 0 := hN
      _ = evaluateResiduePolynomial (p := p)
          (reducePolynomial (p := p) (0 : PIntegralModularForm.E4E6Polynomial p)) := by
          simp [evaluateResiduePolynomial, reducePolynomial]
  simpa [reducePolynomial] using
    (reducePolynomial_eq_of_eval_eq (p := p)
      (k := f.Filtration + (p : ℤ) + 1)
      (PIntegralModularForm.polynomial N) 0
      (by
        intro m hm
        exact PIntegralModularForm.polynomial_isHomogeneous N hm)
      (by
        intro m hm
        simp at hm)
      hEval)

private theorem filtration_smul_twelve {r : ZMod (p - 1)} (f : ModularFormMod p r)
    (hf : f ≠ 0) : ((12 : ZMod p) • f).Filtration = f.Filtration := by
  have h12 : (12 : ZMod p) ≠ 0 :=
    (ThetaOperator.DelOperator.isUnit_twelve (ℓ := p)).ne_zero
  exact filtration_smul_eq f hf (12 : ZMod p) h12

private theorem theta_filtration_drop_iff (f : ModularFormMod p k)
    (hf : f ≠ 0) (htheta : f.Theta ≠ 0) :
    f.Theta.Filtration < f.Filtration + (p : ℤ) + 1 ↔
      (p : ℤ) ∣ f.Filtration := by
  have : NeZero f.Theta := ⟨htheta⟩
  let g := filtrationLift f
  have hg : g.Reduce.fourier = f.fourier := filtrationLift_fourier f
  have hthetaSeries : ThetaOperator.DelOperator.thetaSeries g.Reduce =
      f.Theta.fourier := by
    rw [ThetaOperator.DelOperator.thetaSeries, hg,
      ModularFormMod.fourier_Theta]
    rfl
  have hfour : (thetaNumerator g).Reduce.fourier =
      (12 : ZMod p) • f.Theta.fourier := by
    calc
      (thetaNumerator g).Reduce.fourier =
          (12 : ZMod p) • ThetaOperator.DelOperator.thetaSeries g.Reduce :=
        thetaNumerator_fourier_reduce (p := p) g
      _ = (12 : ZMod p) • f.Theta.fourier := by rw [hthetaSeries]
  have h12 : (12 : ZMod p) ≠ 0 :=
    (ThetaOperator.DelOperator.isUnit_twelve (ℓ := p)).ne_zero
  have hfil : (thetaNumerator g).Reduce.Filtration = f.Theta.Filtration := by
    calc
      (thetaNumerator g).Reduce.Filtration =
          ((12 : ZMod p) • f.Theta).Filtration := by
        apply ModularFormMod.Filtration_ext
        intro i
        simpa only [ModularFormMod.coeff_def, ModularFormMod.fourier_smul] using
          congrArg (fun S : PowerSeries (ZMod p) => S.coeff i) hfour
      _ = f.Theta.Filtration := filtration_smul_twelve f.Theta htheta
  have hNne : (thetaNumerator g).Reduce ≠ 0 := by
    intro hz
    have hzero : (12 : ZMod p) • f.Theta.fourier = 0 := by
      rw [← hfour, hz]
      simp
    rcases smul_eq_zero.mp hzero with h120 | hθ0
    · exact h12 h120
    · exact htheta (ModularFormMod.fourier_inj hθ0)
  have hpart1 := Filtration_Reduce_lt_iff (thetaNumerator g) hNne
  have hdrop : f.Theta.Filtration < f.Filtration + (p : ℤ) + 1 ↔
      Abar (p := p) ∣ reducePolynomial (p := p)
        (PIntegralModularForm.polynomial (thetaNumerator g)) := by
    constructor
    · intro hlt
      apply hpart1.1
      rw [hfil]
      exact hlt
    · intro hdiv
      have hlt := hpart1.2 hdiv
      rw [hfil] at hlt
      exact hlt
  exact hdrop.trans <| by
    simpa [g] using
      (thetaNumerator_A_divides_iff (p := p) f hf).trans
        (ZMod.intCast_zmod_eq_zero_iff_dvd f.Filtration p)


theorem Filt_Theta_bound (f : ModularFormMod p k) :
    f.Theta.Filtration ≤ f.Filtration + (p + 1) := by
  by_cases htheta : f.Theta = 0
  · rw [htheta, ModularFormMod.Filtration_zero]
    by_cases hf : f = 0
    · simp [hf]; omega
    · have hnonneg := filtration_nonneg f hf
      omega
  · have : NeZero f.Theta := ⟨htheta⟩
    have hweight := theta_hasWeight_of_lift (p := p) f
      (filtrationLift f) (filtrationLift_fourier f)
    have hle := ModularFormMod.Filtration_le hweight
    omega


theorem Filt_Theta_iff (f : ModularFormMod p k) :
    f.Theta.Filtration = f.Filtration + (p + 1) ↔ ¬ ↑p ∣ f.Filtration := by
  by_cases hf : f = 0
  · subst f
    simp [ModularFormMod.Filtration_zero]; omega
  · by_cases htheta : f.Theta = 0
    · have hnonneg := filtration_nonneg f hf
      have hdiv0 : Abar (p := p) ∣
          reducePolynomial (p := p)
            (PIntegralModularForm.polynomial
              (thetaNumerator (filtrationLift f))) := by
        rw [thetaNumerator_reducePolynomial_eq_zero (p := p) f htheta]
        exact dvd_zero _
      have hmod := (thetaNumerator_A_divides_iff (p := p) f hf).1 hdiv0
      have hdiv : (p : ℤ) ∣ f.Filtration :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd f.Filtration p).mp hmod
      constructor
      · intro heq
        rw [htheta, ModularFormMod.Filtration_zero] at heq
        omega
      · intro hnot
        exact (hnot hdiv).elim
    · have : NeZero f.Theta := ⟨htheta⟩
      have hdropWeight := theta_filtration_drop_iff (p := p) f hf htheta
      constructor
      · intro heq hdiv
        have hlt := hdropWeight.2 hdiv
        rw [heq] at hlt
        omega
      · intro hnot
        have hnlt : ¬ f.Theta.Filtration < f.Filtration + (p : ℤ) + 1 := by
          intro hlt
          exact hnot (hdropWeight.1 hlt)
        have hbound := Filt_Theta_bound f
        omega
