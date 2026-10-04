import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.CoprimeAbarBbar
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.ZMod.UnitsCyclic

set_option maxHeartbeats 1000000


namespace PIntegralModularForm.SwD

open scoped Pointwise

noncomputable section

variable {p : ℕ} [isLargePrime p]

private def scalePolynomial (z : ZMod p) :
    ResiduePolynomial p →+* ResiduePolynomial p :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.C (z ^ polynomialWeights i) * MvPolynomial.X i)

private theorem scalePolynomial_C (z : ZMod p) (c : ZMod p) :
    scalePolynomial (p := p) z (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [scalePolynomial]

private theorem scalePolynomial_X (z : ZMod p) (i : Fin 2) :
    scalePolynomial (p := p) z (MvPolynomial.X i) =
      MvPolynomial.C (z ^ polynomialWeights i) * MvPolynomial.X i := by
  simp [scalePolynomial, MvPolynomial.eval₂Hom_X']

private theorem scalePolynomial_monomial (z : ZMod p) (m : Fin 2 →₀ ℕ)
    (c : ZMod p) :
    scalePolynomial (p := p) z (MvPolynomial.monomial m c) =
      MvPolynomial.C (z ^ Finsupp.weight polynomialWeights m) *
        MvPolynomial.monomial m c := by
  simp [scalePolynomial, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq,
    polynomialWeights, Finsupp.weight_eq_sum, Finsupp.prod_fintype,
    Fin.prod_univ_two, mul_pow, pow_mul, pow_add, mul_comm, mul_left_comm, mul_assoc]

private theorem scalePolynomial_coeff (z : ZMod p) (F : ResiduePolynomial p)
    (m : Fin 2 →₀ ℕ) :
    (scalePolynomial (p := p) z F).coeff m =
      z ^ Finsupp.weight polynomialWeights m * F.coeff m := by
  classical
  rw [MvPolynomial.as_sum F, map_sum]
  rw [MvPolynomial.coeff_sum]
  simp only [scalePolynomial_monomial, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ F.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro x hx hxm
      simp [hxm]
    · intro hnot
      exact (hnot hm).elim
  · have hcoeff : F.coeff m = 0 := by
      by_contra hcoeff
      exact hm (MvPolynomial.mem_support_iff.mpr hcoeff)
    rw [Finset.sum_eq_zero]
    · simp [hcoeff]
    · intro x hx
      have hxm : x ≠ m := by
        intro hxm
        subst x
        exact hm hx
      simp [hxm]

private theorem scalePolynomial_homogeneous (z : ZMod p)
    (F : ResiduePolynomial p) (d : ℕ)
    (hF : MvPolynomial.IsWeightedHomogeneous polynomialWeights F d) :
    scalePolynomial (p := p) z F = MvPolynomial.C (z ^ d) * F := by
  refine MvPolynomial.IsWeightedHomogeneous.induction_on
    (motive := fun P _ => scalePolynomial (p := p) z P = MvPolynomial.C (z ^ d) * P)
    ?_ ?_ ?_ hF
  · simp
  · intro P Q hP hQ hP' hQ'
    rw [map_add, hP', hQ', mul_add]
  · intro m c hm
    rw [scalePolynomial_monomial, hm]

private theorem scalePolynomial_comp_inv (u : (ZMod p)ˣ) :
    (scalePolynomial (p := p) (u : ZMod p)).comp
        (scalePolynomial (p := p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) =
      RingHom.id (ResiduePolynomial p) := by
  apply MvPolynomial.ringHom_ext'
  · apply RingHom.ext
    intro r
    change scalePolynomial (p := p) (u : ZMod p)
      (scalePolynomial (p := p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p) (MvPolynomial.C r)) =
        MvPolynomial.C r
    rw [scalePolynomial_C, scalePolynomial_C]
  · intro i
    fin_cases i
    · rw [RingHom.comp_apply, scalePolynomial_X, map_mul, scalePolynomial_C,
        scalePolynomial_X]
      simp only [RingHom.id_apply]
      change MvPolynomial.C (((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 4) *
          (MvPolynomial.C ((u : ZMod p) ^ 4) * MvPolynomial.X 0) = MvPolynomial.X 0
      have hbase : (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * (u : ZMod p)) = 1 := by
        exact Units.inv_mul u
      have hpow : (((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 4) *
          ((u : ZMod p) ^ 4) = 1 := by
        rw [← mul_pow]
        rw [hbase]
        simp
      calc
        _  =
            (MvPolynomial.C (σ := Fin 2) (((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 4) *
              MvPolynomial.C ((u : ZMod p) ^ 4)) * MvPolynomial.X 0 := by
          exact (mul_assoc _ _ _).symm
        _ = MvPolynomial.C (1 : ZMod p) * MvPolynomial.X 0 := by
          rw [← MvPolynomial.C_mul, hpow]
        _ = MvPolynomial.X 0 := by simp
    · rw [RingHom.comp_apply, scalePolynomial_X, map_mul, scalePolynomial_C,
        scalePolynomial_X]
      simp only [RingHom.id_apply]
      change MvPolynomial.C (((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 6) *
          (MvPolynomial.C ((u : ZMod p) ^ 6) * MvPolynomial.X 1) = MvPolynomial.X 1
      have hbase : (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * (u : ZMod p)) = 1 := by
        exact Units.inv_mul u
      have hpow : (((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 6) *
          ((u : ZMod p) ^ 6) = 1 := by
        rw [← mul_pow]
        rw [hbase]
        simp
      calc
        _ =
            (MvPolynomial.C (σ := Fin 2) (((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 6) *
              MvPolynomial.C ((u : ZMod p) ^ 6)) * MvPolynomial.X 1 := by
          exact (mul_assoc _ _ _).symm
        _ = MvPolynomial.C (1 : ZMod p) * MvPolynomial.X 1 := by
          rw [← MvPolynomial.C_mul, hpow]
        _ = MvPolynomial.X 1 := by simp

private def scalePolynomialEquiv (u : (ZMod p)ˣ) :
    ResiduePolynomial p ≃+* ResiduePolynomial p :=
  RingEquiv.ofRingHom (scalePolynomial (p := p) (u : ZMod p))
    (scalePolynomial (p := p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p))
    (scalePolynomial_comp_inv (p := p) u) (by
      convert scalePolynomial_comp_inv (p := p) (u⁻¹) using 1 <;> simp)

private theorem weightedComponent_scalePolynomial (z : ZMod p)
    (F : ResiduePolynomial p) (d : ℕ) :
    MvPolynomial.weightedHomogeneousComponent polynomialWeights d
        (scalePolynomial (p := p) z F) =
      scalePolynomial (p := p)
        z
        (MvPolynomial.weightedHomogeneousComponent polynomialWeights d F) := by
  classical
  ext m
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hm : Finsupp.weight polynomialWeights m = d
  · simp [hm, scalePolynomial_coeff, MvPolynomial.coeff_weightedHomogeneousComponent]
  · simp [hm, scalePolynomial_coeff, MvPolynomial.coeff_weightedHomogeneousComponent]

private theorem weightedComponent_mul_top (F G : ResiduePolynomial p) :
    MvPolynomial.weightedHomogeneousComponent polynomialWeights
      (MvPolynomial.weightedTotalDegree polynomialWeights F +
        MvPolynomial.weightedTotalDegree polynomialWeights G) (F * G) =
      MvPolynomial.weightedHomogeneousComponent polynomialWeights
        (MvPolynomial.weightedTotalDegree polynomialWeights F) F *
      MvPolynomial.weightedHomogeneousComponent polynomialWeights
        (MvPolynomial.weightedTotalDegree polynomialWeights G) G := by
  classical
  let m := MvPolynomial.weightedTotalDegree polynomialWeights F
  let n := MvPolynomial.weightedTotalDegree polynomialWeights G
  have hHF := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := polynomialWeights) m F
  have hHG := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := polynomialWeights) n G
  have hHFG := hHF.mul hHG
  ext d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hd : Finsupp.weight polynomialWeights d = m + n
  · rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    have hd' : Finsupp.weight polynomialWeights d =
        MvPolynomial.weightedTotalDegree polynomialWeights F +
          MvPolynomial.weightedTotalDegree polynomialWeights G := by
      simpa [m, n] using hd
    simp only [hd']
    apply Finset.sum_congr rfl
    intro uv huv
    by_cases hu : F.coeff uv.1 = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hu]
    by_cases hv : G.coeff uv.2 = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hv]
    have huS : uv.1 ∈ F.support := MvPolynomial.mem_support_iff.mpr hu
    have hvS : uv.2 ∈ G.support := MvPolynomial.mem_support_iff.mpr hv
    have huLe := MvPolynomial.le_weightedTotalDegree polynomialWeights huS
    have hvLe := MvPolynomial.le_weightedTotalDegree polynomialWeights hvS
    have hsum : Finsupp.weight polynomialWeights uv.1 +
        Finsupp.weight polynomialWeights uv.2 = m + n := by
      have huv' : uv.1 + uv.2 = d := Finset.mem_antidiagonal.mp huv
      rw [← (Finsupp.weight polynomialWeights).map_add, huv']
      exact hd
    have huEq : Finsupp.weight polynomialWeights uv.1 = m := by omega
    have hvEq : Finsupp.weight polynomialWeights uv.2 = n := by omega
    simp [m, n, MvPolynomial.coeff_weightedHomogeneousComponent, huEq, hvEq]
  · have hcoeff :
      (MvPolynomial.weightedHomogeneousComponent polynomialWeights m F *
        MvPolynomial.weightedHomogeneousComponent polynomialWeights n G).coeff d = 0 := by
      by_contra hne
      have := hHFG hne
      exact hd this
    simp [m, n, MvPolynomial.coeff_weightedHomogeneousComponent, hd, hcoeff]

private theorem weightedComponent_top_ne_zero (F : ResiduePolynomial p) (hF : F ≠ 0) :
    MvPolynomial.weightedHomogeneousComponent polynomialWeights
      (MvPolynomial.weightedTotalDegree polynomialWeights F) F ≠ 0 := by
  obtain ⟨m, hm, hdegree⟩ := Finset.exists_mem_eq_sup F.support
    (by simpa [Finset.nonempty_iff_ne_empty, MvPolynomial.support_eq_empty] using hF)
    (Finsupp.weight polynomialWeights)
  intro hzero
  have hcoeff := congrArg (fun Q : ResiduePolynomial p => Q.coeff m) hzero
  have hdegree' : Finsupp.weight polynomialWeights m =
      MvPolynomial.weightedTotalDegree polynomialWeights F := by
    unfold MvPolynomial.weightedTotalDegree
    exact hdegree.symm
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hdegree'] at hcoeff
  have hmcoeff : F.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  exact hmcoeff hcoeff

private theorem weightedTotalDegree_mul (F G : ResiduePolynomial p)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    MvPolynomial.weightedTotalDegree polynomialWeights (F * G) =
      MvPolynomial.weightedTotalDegree polynomialWeights F +
        MvPolynomial.weightedTotalDegree polynomialWeights G := by
  classical
  let m := MvPolynomial.weightedTotalDegree polynomialWeights F
  let n := MvPolynomial.weightedTotalDegree polynomialWeights G
  have htop := weightedComponent_mul_top (p := p) F G
  have hFm := weightedComponent_top_ne_zero (p := p) F hF
  have hGn := weightedComponent_top_ne_zero (p := p) G hG
  have hprod :
      MvPolynomial.weightedHomogeneousComponent polynomialWeights m F *
        MvPolynomial.weightedHomogeneousComponent polynomialWeights n G ≠ 0 :=
    mul_ne_zero hFm hGn
  rw [← htop] at hprod
  have hhom := (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := polynomialWeights) (m + n) (F * G))
  have hle : m + n ≤ MvPolynomial.weightedTotalDegree polynomialWeights (F * G) := by
    obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hprod
    have hdSupport : d ∈
        (MvPolynomial.weightedHomogeneousComponent polynomialWeights (m + n) (F * G)).support :=
      MvPolynomial.mem_support_iff.mpr hd
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hdSupport
    simp only [Finset.mem_filter] at hdSupport
    exact le_trans (by rw [hdSupport.2])
      (MvPolynomial.le_weightedTotalDegree polynomialWeights hdSupport.1)
  have hupper : MvPolynomial.weightedTotalDegree polynomialWeights (F * G) ≤ m + n := by
    unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro d hd
    have hd' : d ∈ F.support + G.support := MvPolynomial.support_mul F G hd
    rcases Finset.mem_add.mp hd' with ⟨u, hu, v, hv, huv⟩
    calc
      Finsupp.weight polynomialWeights d =
          Finsupp.weight polynomialWeights u + Finsupp.weight polynomialWeights v := by
        rw [← huv, (Finsupp.weight polynomialWeights).map_add]
      _ ≤ m + n := add_le_add
        (MvPolynomial.le_weightedTotalDegree polynomialWeights hu)
        (MvPolynomial.le_weightedTotalDegree polynomialWeights hv)
  exact le_antisymm (by simpa [m, n] using hupper) (by simpa [m, n] using hle)

private theorem isUnit_of_weightedHomogeneous_zero (F : ResiduePolynomial p)
    (hF0 : F ≠ 0)
    (hF : MvPolynomial.IsWeightedHomogeneous polynomialWeights F 0) : IsUnit F := by
  have hconst : F = MvPolynomial.C (F.coeff 0) := by
    apply MvPolynomial.ext
    intro m
    by_cases hm : m = 0
    · subst m
      simp
    · by_cases hcoeff : F.coeff m = 0
      · rw [hcoeff]
        have hm' : (0 : Fin 2 →₀ ℕ) ≠ m := Ne.symm hm
        simp [MvPolynomial.coeff_C, hm']
      · have hweight := hF hcoeff
        have hweight' : 4 * m 0 + 6 * m 1 = 0 := by
          simpa [Finsupp.weight_eq_sum, polynomialWeights] using hweight
        have hm0 : m 0 = 0 := by omega
        have hm1 : m 1 = 0 := by omega
        have hmzero : m = 0 := by
          ext i
          fin_cases i <;> simp [hm0, hm1]
        exact (hm hmzero).elim
  have hcoeff : F.coeff 0 ≠ 0 := by
    intro hcoeff
    apply hF0
    rw [hconst, hcoeff]
    simp
  rw [hconst]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

private theorem not_isUnit_of_weightedHomogeneous_pos (F : ResiduePolynomial p)
    {d : ℕ} (hd : 0 < d)
    (hF : MvPolynomial.IsWeightedHomogeneous polynomialWeights F d) :
    ¬ IsUnit F := by
  intro hunit
  obtain ⟨c, hc, hFc⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := F)).mp hunit
  have hcoeff : F.coeff 0 ≠ 0 := by
    rw [hFc]
    simpa using (isUnit_iff_ne_zero.mp hc)
  have hweight := hF hcoeff
  simp [polynomialWeights] at hweight
  omega

private theorem weightedTotalDegree_Abar_sub_one :
    MvPolynomial.weightedTotalDegree polynomialWeights
        (Abar (p := p) - 1) = p - 1 := by
  have hA := Abar_isWeightedHomogeneous (p := p)
  have hp1 : 0 < p - 1 := by
    have hp5 := (inferInstance : isLargePrime p).AtLeastFive
    omega
  apply le_antisymm
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    by_cases hm0 : m = 0
    · subst m
      simp
    · have hmcoeff : (Abar (p := p) - 1).coeff m ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hm
      have hm0' : (0 : Fin 2 →₀ ℕ) ≠ m := Ne.symm hm0
      have heq : (Abar (p := p) - 1).coeff m = (Abar (p := p)).coeff m := by
        simp [MvPolynomial.coeff_one, hm0']
      have hAcoeff : (Abar (p := p)).coeff m ≠ 0 := by
        rwa [heq] at hmcoeff
      have hweight := hA hAcoeff
      exact le_of_eq hweight
  · obtain ⟨m, hmcoeff⟩ := MvPolynomial.exists_coeff_ne_zero (Abar_ne_zero (p := p))
    have hmweight := hA hmcoeff
    have hm0 : m ≠ 0 := by
      intro hm0
      subst m
      simp at hmweight
      omega
    have hm0' : (0 : Fin 2 →₀ ℕ) ≠ m := Ne.symm hm0
    have heq : (Abar (p := p) - 1).coeff m = (Abar (p := p)).coeff m := by
      simp [MvPolynomial.coeff_one, hm0']
    have hFcoeff : (Abar (p := p) - 1).coeff m ≠ 0 := by
      rwa [heq]
    calc
      p - 1 = Finsupp.weight polynomialWeights m := hmweight.symm
      _ ≤ MvPolynomial.weightedTotalDegree polynomialWeights (Abar (p := p) - 1) :=
        MvPolynomial.le_weightedTotalDegree polynomialWeights
          (MvPolynomial.mem_support_iff.mpr hFcoeff)

private theorem weightedComponent_Abar_sub_one :
    MvPolynomial.weightedHomogeneousComponent polynomialWeights (p - 1)
        (Abar (p := p) - 1) = Abar (p := p) := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hA := Abar_isWeightedHomogeneous (p := p)
  have hOne := MvPolynomial.isWeightedHomogeneous_one
      (R := ZMod p) polynomialWeights
  have hOneComp := MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
      (w := polynomialWeights) (p := (1 : ResiduePolynomial p)) (n := p - 1)
      (m := 0) hOne (by omega)
  simp only [map_sub,
    MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hA,
    hOneComp, sub_zero]

private theorem scalePolynomial_support (u : (ZMod p)ˣ) (F : ResiduePolynomial p) :
    (scalePolynomial (p := p) (u : ZMod p) F).support = F.support := by
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff,
    scalePolynomial_coeff]
  have hpow : (u : ZMod p) ^ Finsupp.weight polynomialWeights m ≠ 0 :=
    pow_ne_zero _ (Units.ne_zero u)
  simp [hpow]

private theorem primitiveUnit_pow_ne_one (u : (ZMod p)ˣ)
    (hu : orderOf u = p - 1) {n : ℕ} (hnpos : 0 < n) (hnlt : n < p - 1) :
    (u : ZMod p) ^ n ≠ 1 := by
  intro h
  have hpow : u ^ n = 1 := Units.ext h
  have hdiv : orderOf u ∣ n := (orderOf_dvd_iff_pow_eq_one).2 hpow
  rw [hu] at hdiv
  rcases hdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := by omega
    rw [hkzero] at hk
    simp at hk
    omega
  have hp1 : 0 < p - 1 := by
    have hp5 := (inferInstance : isLargePrime p).AtLeastFive
    omega
  have hle : p - 1 ≤ n := by
    rw [hk]
    calc
      p - 1 = (p - 1) * 1 := by simp
      _ ≤ (p - 1) * k := Nat.mul_le_mul_left _ (by omega)
  omega


theorem Irreducible_Abar_sub_one : Irreducible (Abar (p := p) - 1) := by
  let F : ResiduePolynomial p := Abar (p := p) - 1
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hdpos : 0 < p - 1 := by omega
  have hA := Abar_isWeightedHomogeneous (p := p)
  have hA0 : (Abar (p := p)).coeff 0 = 0 := by
    by_contra hcoeff
    have hweight := hA hcoeff
    simp [polynomialWeights] at hweight
    omega
  have hFtop :
      MvPolynomial.weightedHomogeneousComponent polynomialWeights (p - 1) F =
        Abar (p := p) := by
    simpa [F] using weightedComponent_Abar_sub_one (p := p)
  have hFne : F ≠ 0 := by
    intro hzero
    have hcomp := congrArg
      (MvPolynomial.weightedHomogeneousComponent polynomialWeights (p - 1)) hzero
    rw [hFtop] at hcomp
    have hAzero : Abar (p := p) = 0 := by simpa using hcomp
    exact Abar_ne_zero (p := p) hAzero
  obtain ⟨mA, hmA⟩ := MvPolynomial.exists_coeff_ne_zero (Abar_ne_zero (p := p))
  have hmAweight := hA hmA
  have hmA0 : mA ≠ 0 := by
    intro hm
    subst mA
    simp at hmAweight
    omega
  have hFcoeffA : F.coeff mA ≠ 0 := by
    have hmA0' : (0 : Fin 2 →₀ ℕ) ≠ mA := Ne.symm hmA0
    have heq : F.coeff mA = (Abar (p := p)).coeff mA := by
      simp [F, MvPolynomial.coeff_one, hmA0']
    rwa [heq]
  have hFnotunit : ¬ IsUnit F := by
    intro hunit
    have hdegree :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced (P := F)).mp hunit
    have hconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := F)).mp hdegree.2
    have hcoeffzero : F.coeff mA = 0 := by
      rw [hconst]
      simp [MvPolynomial.coeff_C, hmA0.symm]
    exact hFcoeffA hcoeffzero

  change Irreducible F
  refine ⟨hFnotunit, ?_⟩
  intro a b hab
  by_cases ha : IsUnit a
  · exact Or.inl ha
  by_cases hb : IsUnit b
  · exact Or.inr hb
  have ha0 : a ≠ 0 := by
    intro hzero
    apply hFne
    rw [hab, hzero]
    simp
  obtain ⟨φ, hφirr, hφdiv⟩ := WfDvdMonoid.exists_irreducible_factor ha ha0
  rcases hφdiv with ⟨c, hac⟩
  let ψ : ResiduePolynomial p := c * b
  have hfac : F = φ * ψ := by
    dsimp [ψ]
    calc
      F = a * b := hab
      _ = (φ * c) * b := by rw [hac]
      _ = φ * (c * b) := by ring
  have hψnotunit : ¬ IsUnit ψ := by
    intro hu
    have hbunit : IsUnit b := isUnit_of_mul_isUnit_right (by simpa [ψ] using hu)
    exact hb hbunit
  have hφne : φ ≠ 0 := hφirr.ne_zero
  have hψne : ψ ≠ 0 := by
    intro hzero
    apply hFne
    rw [hfac, hzero]
    simp
  let d : ℕ := p - 1
  let n : ℕ := MvPolynomial.weightedTotalDegree polynomialWeights φ
  have hFdegree : MvPolynomial.weightedTotalDegree polynomialWeights F = d := by
    simpa [F, d] using weightedTotalDegree_Abar_sub_one (p := p)
  have hdegreeSum : n + MvPolynomial.weightedTotalDegree polynomialWeights ψ = d := by
    calc
      n + MvPolynomial.weightedTotalDegree polynomialWeights ψ =
          MvPolynomial.weightedTotalDegree polynomialWeights φ +
            MvPolynomial.weightedTotalDegree polynomialWeights ψ := rfl
      _ = MvPolynomial.weightedTotalDegree polynomialWeights (φ * ψ) :=
        (weightedTotalDegree_mul (p := p) φ ψ hφne hψne).symm
      _ = d := by rw [← hfac]; exact hFdegree
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hφhom0 : MvPolynomial.IsWeightedHomogeneous polynomialWeights φ 0 :=
      (MvPolynomial.isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero
        (w := polynomialWeights)).2 (by simpa [n] using hn0)
    exact hφirr.not_isUnit (isUnit_of_weightedHomogeneous_zero φ hφne hφhom0)
  have hψdegreepos : 0 < MvPolynomial.weightedTotalDegree polynomialWeights ψ := by
    by_contra hn
    have hn0 : MvPolynomial.weightedTotalDegree polynomialWeights ψ = 0 := by omega
    have hψhom0 : MvPolynomial.IsWeightedHomogeneous polynomialWeights ψ 0 :=
      (MvPolynomial.isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero
        (w := polynomialWeights)).2 hn0
    exact hψnotunit (isUnit_of_weightedHomogeneous_zero ψ hψne hψhom0)
  have hndlt : n < d := by omega

  have hφnonhom : ¬ ∃ j, MvPolynomial.IsWeightedHomogeneous polynomialWeights φ j := by
    rintro ⟨j, hj⟩
    have hjpos : 0 < j := by
      by_contra hj'
      have hj0 : j = 0 := by omega
      subst j
      exact hφirr.not_isUnit (isUnit_of_weightedHomogeneous_zero φ hφne hj)
    have hφcoeff0 : φ.coeff 0 = 0 := by
      by_contra hcoeff
      have hweight := hj hcoeff
      simp at hweight
      omega
    have hFcoeff0 : F.coeff 0 = -1 := by
      simp [F, hA0]
    have hcoeffFactor := congrArg (fun Q : ResiduePolynomial p => Q.coeff 0) hfac
    rw [hFcoeff0] at hcoeffFactor
    simp [MvPolynomial.coeff_mul, hφcoeff0] at hcoeffFactor

  have hlower : ∃ e < n,
      MvPolynomial.weightedHomogeneousComponent polynomialWeights e φ ≠ 0 := by
    by_contra h
    have hall : ∀ e, e < n →
        MvPolynomial.weightedHomogeneousComponent polynomialWeights e φ = 0 := by
      intro e he
      by_contra hne
      exact h ⟨e, he, hne⟩
    apply hφnonhom
    refine ⟨n, ?_⟩
    intro m hm
    have hle := MvPolynomial.le_weightedTotalDegree polynomialWeights
      (MvPolynomial.mem_support_iff.mpr hm)
    by_contra hweight
    have hlt : Finsupp.weight polynomialWeights m < n := by omega
    have hzero := hall (Finsupp.weight polynomialWeights m) hlt
    have hcoeff := congrArg (fun Q : ResiduePolynomial p => Q.coeff m) hzero
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hcoeff
    simp at hcoeff
    exact hm hcoeff
  obtain ⟨eLow, heLowlt, hLowComp⟩ := hlower
  have hφtopne := weightedComponent_top_ne_zero (p := p) φ hφne
  obtain ⟨eTop, heTopCoeff⟩ := MvPolynomial.exists_coeff_ne_zero hφtopne
  have heTopSupport : eTop ∈
      (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ).support :=
    MvPolynomial.mem_support_iff.mpr heTopCoeff
  rw [MvPolynomial.support_weightedHomogeneousComponent] at heTopSupport
  rcases Finset.mem_filter.mp heTopSupport with ⟨heTopPhi, heTopWeight⟩
  have heTopPhiCoeff : φ.coeff eTop ≠ 0 := MvPolynomial.mem_support_iff.mp heTopPhi
  obtain ⟨eLowMon, heLowCoeff⟩ := MvPolynomial.exists_coeff_ne_zero hLowComp
  have heLowSupport : eLowMon ∈
      (MvPolynomial.weightedHomogeneousComponent polynomialWeights eLow φ).support :=
    MvPolynomial.mem_support_iff.mpr heLowCoeff
  rw [MvPolynomial.support_weightedHomogeneousComponent] at heLowSupport
  rcases Finset.mem_filter.mp heLowSupport with ⟨heLowPhi, heLowWeight⟩
  have heLowPhiCoeff : φ.coeff eLowMon ≠ 0 := MvPolynomial.mem_support_iff.mp heLowPhi

  have hpPrime : p.Prime := (inferInstance : isLargePrime p).Prime
  obtain ⟨u, huCard⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (ZMod.isCyclic_units_prime hpPrime)
  have huOrder : orderOf u = p - 1 := by
    simpa [Nat.card_eq_fintype_card, ZMod.card_units, Nat.totient_prime hpPrime] using huCard
  have hzfull : (u : ZMod p) ^ d = 1 := by
    have hpow : u ^ orderOf u = 1 := pow_orderOf_eq_one u
    rw [huOrder] at hpow
    exact congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) (by simpa [d] using hpow)
  have hscaleA : scalePolynomial (p := p) (u : ZMod p) (Abar (p := p)) =
      Abar (p := p) := by
    rw [scalePolynomial_homogeneous (p := p) (u : ZMod p) _ d hA, hzfull]
    simp
  have hscaleF : (scalePolynomialEquiv (p := p) u) F = F := by
    change scalePolynomial (p := p) (u : ZMod p) F = F
    simp only [F, map_sub, map_one, hscaleA]

  let φ' : ResiduePolynomial p := (scalePolynomialEquiv (p := p) u) φ
  have hφ'irr : Irreducible φ' := by
    change Irreducible ((scalePolynomialEquiv (p := p) u) φ)
    exact (MulEquiv.irreducible_iff
      (f := scalePolynomialEquiv (p := p) u) (x := φ)).2 hφirr
  have hφ'ne : φ' ≠ 0 := hφ'irr.ne_zero
  have hφ'degree : MvPolynomial.weightedTotalDegree polynomialWeights φ' = n := by
    change MvPolynomial.weightedTotalDegree polynomialWeights
      (scalePolynomial (p := p) (u : ZMod p) φ) = n
    unfold MvPolynomial.weightedTotalDegree
    rw [scalePolynomial_support (p := p) u φ]
    rfl
  have hφ'top :
      MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ' =
        MvPolynomial.C ((u : ZMod p) ^ n) *
          MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ := by
    change MvPolynomial.weightedHomogeneousComponent polynomialWeights n
        (scalePolynomial (p := p) (u : ZMod p) φ) = _
    rw [weightedComponent_scalePolynomial]
    exact scalePolynomial_homogeneous (p := p) (u : ZMod p)
      (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ) n
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := polynomialWeights) n φ)

  have hnotAssoc : ¬ Associated φ φ' := by
    intro hassoc
    rcases hassoc with ⟨v, hv⟩
    obtain ⟨c₀, hc₀, hvC⟩ :=
      (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := (v : ResiduePolynomial p))).mp v.isUnit
    have hscaleEq : (scalePolynomialEquiv (p := p) u) φ =
        MvPolynomial.C c₀ * φ := by
      calc
        (scalePolynomialEquiv (p := p) u) φ = φ * (v : ResiduePolynomial p) := hv.symm
        _ = (v : ResiduePolynomial p) * φ := by rw [mul_comm]
        _ = MvPolynomial.C c₀ * φ := by rw [hvC]
    have htopCoeff := congrArg (fun Q : ResiduePolynomial p => Q.coeff eTop) hscaleEq
    change (scalePolynomial (p := p) (u : ZMod p) φ).coeff eTop = _ at htopCoeff
    rw [scalePolynomial_coeff, MvPolynomial.coeff_C_mul, heTopWeight] at htopCoeff
    have htopPower : (u : ZMod p) ^ n = c₀ :=
      mul_right_cancel₀ heTopPhiCoeff htopCoeff
    have hlowCoeff := congrArg (fun Q : ResiduePolynomial p => Q.coeff eLowMon) hscaleEq
    change (scalePolynomial (p := p) (u : ZMod p) φ).coeff eLowMon = _ at hlowCoeff
    rw [scalePolynomial_coeff, MvPolynomial.coeff_C_mul, heLowWeight] at hlowCoeff
    have hlowPower : (u : ZMod p) ^ eLow = c₀ :=
      mul_right_cancel₀ heLowPhiCoeff hlowCoeff
    have hpowEq : (u : ZMod p) ^ n = (u : ZMod p) ^ eLow :=
      htopPower.trans hlowPower.symm
    have hnat : eLow + (n - eLow) = n := by omega
    have hfactor : (u : ZMod p) ^ n =
        (u : ZMod p) ^ eLow * (u : ZMod p) ^ (n - eLow) := by
      conv_lhs => rw [← hnat]
      rw [pow_add]
    have hmul : (u : ZMod p) ^ eLow * (u : ZMod p) ^ (n - eLow) =
        (u : ZMod p) ^ eLow := by
      calc
        (u : ZMod p) ^ eLow * (u : ZMod p) ^ (n - eLow) =
            (u : ZMod p) ^ n := hfactor.symm
        _ = (u : ZMod p) ^ eLow := hpowEq
    have hpowOne : (u : ZMod p) ^ (n - eLow) = 1 :=
      mul_left_cancel₀ (a := (u : ZMod p) ^ eLow)
        (pow_ne_zero eLow (Units.ne_zero u)) (by simpa only [mul_one] using hmul)
    have hkpos : 0 < n - eLow := by omega
    have hklt : n - eLow < p - 1 := by
      exact lt_of_le_of_lt (Nat.sub_le _ _) (by simpa [d] using hndlt)
    exact primitiveUnit_pow_ne_one (p := p) u huOrder hkpos hklt hpowOne

  have hscaledDiv : φ' ∣ F := by
    have hmap := congrArg (scalePolynomialEquiv (p := p) u) hfac
    rw [map_mul, hscaleF] at hmap
    change F = φ' * (scalePolynomialEquiv (p := p) u) ψ at hmap
    exact ⟨(scalePolynomialEquiv (p := p) u) ψ, hmap⟩
  have hdivprod : φ' ∣ φ * ψ := by
    rw [← hfac]
    exact hscaledDiv
  have hprime' : Prime φ' := irreducible_iff_prime.mp hφ'irr
  rcases hprime'.dvd_mul.mp hdivprod with hdivφ | hdivψ
  · have hassoc := hφ'irr.associated_of_dvd hφirr hdivφ
    exact False.elim (hnotAssoc hassoc.symm)
  · rcases hdivψ with ⟨q, hψq⟩
    have hqne : q ≠ 0 := by
      intro hq
      apply hψne
      rw [hψq, hq]
      simp
    let r : ℕ := MvPolynomial.weightedTotalDegree polynomialWeights q
    have htrifac : F = (φ * φ') * q := by
      calc
        F = φ * ψ := hfac
        _ = φ * (φ' * q) := by rw [hψq]
        _ = (φ * φ') * q := by ring
    have hABdegree : MvPolynomial.weightedTotalDegree polynomialWeights (φ * φ') =
        n + n := by
      rw [weightedTotalDegree_mul (p := p) φ φ' hφne hφ'ne, hφ'degree]
    have htriDegree : d = (n + n) + r := by
      calc
        d = MvPolynomial.weightedTotalDegree polynomialWeights F := hFdegree.symm
        _ = MvPolynomial.weightedTotalDegree polynomialWeights ((φ * φ') * q) := by
          rw [htrifac]
        _ = MvPolynomial.weightedTotalDegree polynomialWeights (φ * φ') + r := by
          rw [weightedTotalDegree_mul (p := p) (φ * φ') q (mul_ne_zero hφne hφ'ne) hqne]
        _ = (n + n) + r := by rw [hABdegree]
    have htopAB :
        MvPolynomial.weightedHomogeneousComponent polynomialWeights (n + n) (φ * φ') =
          MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ *
            MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ' := by
      simpa [n, hφ'degree] using weightedComponent_mul_top (p := p) φ φ'
    have htopABQ :
        MvPolynomial.weightedHomogeneousComponent polynomialWeights ((n + n) + r)
            ((φ * φ') * q) =
          MvPolynomial.weightedHomogeneousComponent polynomialWeights (n + n) (φ * φ') *
            MvPolynomial.weightedHomogeneousComponent polynomialWeights r q := by
      simpa [r, hABdegree] using
        weightedComponent_mul_top (p := p) (φ * φ') q
    have htopTri :
        MvPolynomial.weightedHomogeneousComponent polynomialWeights d F =
          (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ *
            MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ') *
            MvPolynomial.weightedHomogeneousComponent polynomialWeights r q := by
      calc
        _ = MvPolynomial.weightedHomogeneousComponent polynomialWeights ((n + n) + r)
            ((φ * φ') * q) := by rw [htrifac, htriDegree]
        _ = MvPolynomial.weightedHomogeneousComponent polynomialWeights (n + n) (φ * φ') *
              MvPolynomial.weightedHomogeneousComponent polynomialWeights r q := htopABQ
        _ = _ := by rw [htopAB]
    have hAdiv :
        (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ) ^ 2 ∣
          Abar (p := p) := by
      refine ⟨MvPolynomial.C ((u : ZMod p) ^ n) *
        MvPolynomial.weightedHomogeneousComponent polynomialWeights r q, ?_⟩
      have htopA : Abar (p := p) =
          (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ) ^ 2 *
            (MvPolynomial.C ((u : ZMod p) ^ n) *
              MvPolynomial.weightedHomogeneousComponent polynomialWeights r q) := by
        calc
          Abar (p := p) = MvPolynomial.weightedHomogeneousComponent polynomialWeights d F :=
            hFtop.symm
          _ = (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ *
              MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ') *
              MvPolynomial.weightedHomogeneousComponent polynomialWeights r q := htopTri
          _ = _ := by rw [hφ'top]; ring
      simpa [pow_two] using htopA
    have htopHom := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := polynomialWeights) n φ
    have hsqA : ∀ x : ResiduePolynomial p,
        x * x ∣ Abar (p := p) → IsUnit x := lemma_1_40_squarefree (p := p)
    have htopUnit : IsUnit
        (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ) :=
      hsqA _ (by simpa [pow_two] using hAdiv)
    exfalso
    exact not_isUnit_of_weightedHomogeneous_pos
      (MvPolynomial.weightedHomogeneousComponent polynomialWeights n φ) hnpos htopHom htopUnit


theorem Prime_Abar_sub_one : Prime (Abar (p := p) - 1) :=
  irreducible_iff_prime.mp Irreducible_Abar_sub_one
