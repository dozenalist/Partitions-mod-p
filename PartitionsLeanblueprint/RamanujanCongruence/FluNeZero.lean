import PartitionsLeanblueprint.RamanujanCongruence.Partition
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Basic
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Operators
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.PowPrime



/-
This file proves `flu_eq_zero`
This proof is probably too long and could be shortened
by working with the power series instead of the coefficients
This file is sorry-free
-/



open ModularFormMod hiding coeff
open PowerSeries Finset Nat
open scoped IntegerModularForm


noncomputable section

set_option maxHeartbeats 0 in
private theorem coeff_mul_subst_UOp {R : Type} [CommRing R]
    (ℓ n : ℕ) (hℓ : ℓ ≠ 0) (f g : PowerSeries R) :
    coeff (ℓ * n) ((PowerSeries.subst (X ^ ℓ) f) * g) =
      coeff n (f * PowerSeries.UOp ℓ g) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  simp_rw [PowerSeries.coeff_subst_X_pow hℓ, PowerSeries.coeff_UOp]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  classical
  let s := (Finset.antidiagonal (ℓ * n)).filter (fun p => ℓ ∣ p.1)
  have hsum :
      (∑ p ∈ Finset.antidiagonal (ℓ * n),
        (if ℓ ∣ p.1 then coeff (p.1 / ℓ) f else 0) * coeff p.2 g) =
      ∑ p ∈ s, coeff (p.1 / ℓ) f * coeff p.2 g := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hd : ℓ ∣ p.1 <;> simp [s, hd]
  rw [hsum]
  apply Finset.sum_bij (fun p _ => (p.1 / ℓ, p.2 / ℓ))
  · intro p hp
    simp only [s, Finset.mem_filter] at hp
    rcases hp with ⟨hmem, hdvd⟩
    have hadd : p.1 + p.2 = ℓ * n := Finset.mem_antidiagonal.mp hmem
    have hdvd₂ : ℓ ∣ p.2 := by
      apply (Nat.dvd_add_iff_right hdvd).2
      rw [hadd]
      exact dvd_mul_right ℓ n
    have hmul : ℓ * (p.1 / ℓ + p.2 / ℓ) = ℓ * n := by
      rw [Nat.mul_add, Nat.mul_div_cancel' hdvd, Nat.mul_div_cancel' hdvd₂]
      exact hadd
    exact Finset.mem_antidiagonal.mpr <| Nat.mul_left_cancel (Nat.pos_of_ne_zero hℓ) hmul
  · intro p hp q hq heq
    simp only [s, Finset.mem_filter] at hp hq
    simp only [Prod.mk.injEq] at heq
    rcases hp with ⟨hpmem, hpdiv⟩
    rcases hq with ⟨hqmem, hqdiv⟩
    have hpadd : p.1 + p.2 = ℓ * n := Finset.mem_antidiagonal.mp hpmem
    have hqadd : q.1 + q.2 = ℓ * n := Finset.mem_antidiagonal.mp hqmem
    have hp2div : ℓ ∣ p.2 := (Nat.dvd_add_iff_right hpdiv).2 (by rw [hpadd]; exact dvd_mul_right ℓ n)
    have hq2div : ℓ ∣ q.2 := (Nat.dvd_add_iff_right hqdiv).2 (by rw [hqadd]; exact dvd_mul_right ℓ n)
    rcases heq with ⟨heq₁, heq₂⟩
    apply Prod.ext
    · calc
        p.1 = ℓ * (p.1 / ℓ) := (Nat.mul_div_cancel' hpdiv).symm
        _ = ℓ * (q.1 / ℓ) := congrArg (fun x => ℓ * x) heq₁
        _ = q.1 := Nat.mul_div_cancel' hqdiv
    · calc
        p.2 = ℓ * (p.2 / ℓ) := (Nat.mul_div_cancel' hp2div).symm
        _ = ℓ * (q.2 / ℓ) := congrArg (fun x => ℓ * x) heq₂
        _ = q.2 := Nat.mul_div_cancel' hq2div
  · intro p hp
    have hadd : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    refine ⟨(ℓ * p.1, ℓ * p.2), ?_, ?_⟩
    · simp only [s, Finset.mem_filter]
      constructor
      · apply Finset.mem_antidiagonal.mpr
        calc
          (ℓ * p.1) + (ℓ * p.2) = ℓ * (p.1 + p.2) := (Nat.mul_add ..).symm
          _ = ℓ * n := congrArg (fun x => ℓ * x) hadd
      · exact dvd_mul_right ℓ p.1
    · simp [Nat.mul_div_cancel_left, hℓ]
  · intro p hp
    simp only [s, Finset.mem_filter] at hp
    rcases hp with ⟨hmem, hdvd⟩
    have hadd : p.1 + p.2 = ℓ * n := Finset.mem_antidiagonal.mp hmem
    have hdvd₂ : ℓ ∣ p.2 := by
      apply (Nat.dvd_add_iff_right hdvd).2
      rw [hadd]
      exact dvd_mul_right ℓ n
    have hp1 : ℓ * (p.1 / ℓ) = p.1 := Nat.mul_div_cancel' hdvd
    have hp2 : ℓ * (p.2 / ℓ) = p.2 := Nat.mul_div_cancel' hdvd₂
    simp [hp1, hp2]

set_option maxHeartbeats 0 in
private theorem coeff_prod_range_pow_le_aux {R : Type} [CommRing R] [Nontrivial R]
    (r n m j : ℕ) (hnm : n ≤ m) (hmj : m ≤ j) :
    coeff (R := R) n (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ r) =
      coeff (R := R) n (∏ i ∈ range j, (1 - X ^ (i + 1)) ^ r) := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmj
  rw [Finset.prod_range_add]
  let p : PowerSeries R := ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ r
  let q : PowerSeries R := ∏ i ∈ range d, (1 - X ^ (m + i + 1)) ^ r
  have hq : q = ∏ ij ∈ range d ×ˢ range r, (1 - X ^ (m + ij.1 + 1)) := by
    dsimp [q]
    rw [Finset.prod_product]
    apply Finset.prod_congr rfl
    intro i hi
    simp
  change coeff n p = coeff n (p * q)
  rw [hq]
  symm
  apply PowerSeries.coeff_mul_prod_one_sub_of_lt_order
  intro ij hij
  simp only [Finset.mem_product, Finset.mem_range] at hij
  have hdeg : n < m + ij.1 + 1 := by omega
  rw [PowerSeries.order_X_pow]
  exact_mod_cast hdeg

set_option maxHeartbeats 0 in
private theorem coeff_prod_range_pow_le {R : Type} [CommRing R] [Nontrivial R]
    (r n m j : ℕ) (hnm : n ≤ m) (hnj : n ≤ j) :
    coeff (R := R) n (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ r) =
      coeff (R := R) n (∏ i ∈ range j, (1 - X ^ (i + 1)) ^ r) := by
  rcases le_total m j with hmj | hjm
  · exact coeff_prod_range_pow_le_aux r n m j hnm hmj
  · exact (coeff_prod_range_pow_le_aux r n j m hnj hjm).symm

theorem coeff_flu {ℓ} [hℓ : isLargePrime ℓ] (n : ℕ) :
   (fl ℓ).UOp.coeff n =
    coeff (R := ZMod ℓ) n
      ((∏ i ∈ range n, (1 - X ^ (i + 1)) ^ ℓ) *
        ∑ i ∈ range (n + 1),
          C (partition (ℓ * i - δ ℓ) : ZMod ℓ) * X ^ i) := by
  classical
  rw [ModularFormMod.coeff_def]
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    have := hℓ.AtLeastFive
    omega
  have hp : ℓ * n < ℓ * n + 1 := Nat.lt_succ_self _
  have hprodform : ∀ (M : ℕ),
      (X : (ZMod ℓ)⟦X⟧) ^ δ ℓ *
        ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2) =
      ((Polynomial.X ^ (δ ℓ) *
        ∏ i ∈ range M, (1 - Polynomial.X ^ (i + 1)) ^ (ℓ ^ 2) : Polynomial (ZMod ℓ)) : (ZMod ℓ)⟦X⟧) := by
    intro M
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, ← Polynomial.coe_prod]
    congr 2
    ext i
    simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X]
  set g : ℕ → Polynomial (ZMod ℓ) := fun k =>
    Polynomial.X ^ (δ ℓ) * ∏ i ∈ range k, (1 - Polynomial.X ^ (i + 1)) ^ (ℓ ^ 2) with hg
  obtain ⟨m, hsum⟩ := partitionProduct_mul_eq_natpart_sum (ℓ * n) g
  let M := max m (ℓ * n + 1)
  have hmM : m ≤ M := le_max_left _ _
  have hℓnM : ℓ * n < M := by
    dsimp [M]
    exact lt_of_lt_of_le hp (le_max_right _ _)
  have hnM : n ≤ M := by
    exact (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hℓ0)).trans hℓnM.le
  have hpoly :
      (X : (ZMod ℓ)⟦X⟧) ^ δ ℓ *
        ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2) = (g M : (ZMod ℓ)⟦X⟧) := by
    simpa only [hg] using hprodform M
  have hlarge : ℓ ^ 2 ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hℓ0)
  have hfactor :
      ∏ i ∈ range M, (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ^ (ℓ ^ 2 - 1) =
        (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
          (partitionProduct M : (ZMod ℓ)⟦X⟧) := by
    calc
      ∏ i ∈ range M, (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ^ (ℓ ^ 2 - 1) =
          ∏ i ∈ range M,
            ((1 - X ^ (i + 1)) ^ (ℓ ^ 2) * (1 - X ^ (i + 1))⁻¹) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hu : (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ^ (ℓ ^ 2 - 1) *
              (1 - X ^ (i + 1)) = (1 - X ^ (i + 1)) ^ (ℓ ^ 2) := by
          rw [← pow_succ, Nat.sub_add_cancel hlarge]
        have hconst : constantCoeff (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ≠ 0 := by
          simp [zero_ne_one]
        exact (PowerSeries.eq_mul_inv_iff_mul_eq hconst).mpr hu
      _ = (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
            (partitionProduct M : (ZMod ℓ)⟦X⟧) := by
        rw [prod_mul_distrib, partitionProduct]
  have hfrob (i : ℕ) :
      (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ^ (ℓ ^ 2) =
        (1 - (X : (ZMod ℓ)⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ := by
    calc
      (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ^ (ℓ ^ 2) =
          ((1 - X ^ (i + 1)) ^ ℓ) ^ ℓ := by
        rw [pow_two, pow_mul]
      _ = (1 - (X : (ZMod ℓ)⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ := by
        rw [sub_pow_expChar_of_commute ℓ, one_pow, ← pow_mul]
        rw [Nat.mul_comm]
        exact Commute.one_left _
  simp only [ModularFormMod.fourier_UOp, PowerSeries.coeff_UOp]
  change (fl ℓ).coeff (ℓ * n) = _
  rw [fl_eq_coeff_Product]
  have hscalar (i : ℕ) :
      natpart i • (X : (ZMod ℓ)⟦X⟧) ^ i =
        C (natpart i : ZMod ℓ) * (X : (ZMod ℓ)⟦X⟧) ^ i := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod ℓ)]
    exact PowerSeries.smul_eq_C_mul _ _
  have hsumscalar :
      (∑ i ∈ range M, C (natpart i : ZMod ℓ) * X ^ i) =
        (∑ i ∈ range M, natpart i • X ^ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (hscalar i).symm
  have hprodFrob :
      (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (i + 1)) ^ (ℓ ^ 2)) =
        (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (ℓ * (i + 1))) ^ ℓ) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hfrob i
  have hfrseries :
      (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (i + 1)) ^ (ℓ ^ 2)) *
          ((X : PowerSeries (ZMod ℓ)) ^ (δ ℓ) *
            ∑ i ∈ range M, C (natpart i : ZMod ℓ) * (X : PowerSeries (ZMod ℓ)) ^ i) =
        (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (ℓ * (i + 1))) ^ ℓ) *
          ((X : PowerSeries (ZMod ℓ)) ^ (δ ℓ) *
            ∑ i ∈ range M, natpart i • (X : PowerSeries (ZMod ℓ)) ^ i) := by
    calc
      _ = (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (i + 1)) ^ (ℓ ^ 2)) *
          ((X : PowerSeries (ZMod ℓ)) ^ (δ ℓ) *
            ∑ i ∈ range M, natpart i • (X : PowerSeries (ZMod ℓ)) ^ i) :=
          congrArg (fun s =>
            (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (i + 1)) ^ (ℓ ^ 2)) *
              ((X : PowerSeries (ZMod ℓ)) ^ (δ ℓ) * s)) hsumscalar
      _ = (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (ℓ * (i + 1))) ^ ℓ) *
          ((X : PowerSeries (ZMod ℓ)) ^ (δ ℓ) *
            ∑ i ∈ range M, natpart i • (X : PowerSeries (ZMod ℓ)) ^ i) :=
          congrArg (fun p => p *
            ((X : PowerSeries (ZMod ℓ)) ^ (δ ℓ) *
              ∑ i ∈ range M, natpart i • (X : PowerSeries (ZMod ℓ)) ^ i)) hprodFrob
  calc
    _ = coeff (R := ZMod ℓ) (ℓ * n) (flProduct ℓ M) := by
      exact flProduct_coeff_le (le_refl _) hℓnM.le
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        (X ^ (δ ℓ) * ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2 - 1)) := by
      rw [flProduct]
      congr! 4
      rw [twentyfour_mul_delta ℓ]
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((X ^ (δ ℓ) * ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
          (partitionProduct M : (ZMod ℓ)⟦X⟧)) := by
      apply congrArg (coeff (R := ZMod ℓ) (ℓ * n))
      rw [mul_assoc, hfactor]
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((g M : (ZMod ℓ)⟦X⟧) * (partitionProduct M : (ZMod ℓ)⟦X⟧)) := by
      rw [hpoly]
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((g M : (ZMod ℓ)⟦X⟧) *
          ∑ i ∈ range M, C (natpart i : ZMod ℓ) * X ^ i) := by
      rw [hsum M hmM]
      exact congrArg (fun s => coeff (R := ZMod ℓ) (ℓ * n) ((g M : (ZMod ℓ)⟦X⟧) * s))
        hsumscalar.symm
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((X ^ (δ ℓ) * ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
          ∑ i ∈ range M, C (natpart i : ZMod ℓ) * X ^ i) := by
      rw [← hpoly]
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
          (X ^ (δ ℓ) * ∑ i ∈ range M, C (natpart i : ZMod ℓ) * X ^ i)) := by
      apply congrArg (coeff (R := ZMod ℓ) (ℓ * n))
      ring
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((∏ i ∈ range M, (1 - X ^ (ℓ * (i + 1))) ^ ℓ) *
          (X ^ (δ ℓ) * ∑ i ∈ range M, natpart i • X ^ i)) := by
      exact congrArg (coeff (R := ZMod ℓ) (ℓ * n)) hfrseries
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((∏ i ∈ range M, (1 - X ^ (ℓ * (i + 1))) ^ ℓ) *
          (X ^ (δ ℓ) * ∑ i ∈ range M, (partition i) * (X : (ZMod ℓ)⟦X⟧) ^ i)) := by
      simp only [PowerSeries.coeff_mul]
      apply sum_congr rfl
      simp only [mem_antidiagonal, mul_eq_mul_left_iff, Prod.forall]
      intro a b addb
      by_cases ldiva : ℓ ∣ a
      · have ldivb : ℓ ∣ b := by
          suffices ℓ ∣ a + b from (Nat.dvd_add_iff_right ldiva).mpr this
          use n
        left
        apply sum_congr rfl
        simp only [mem_antidiagonal, mul_eq_mul_left_iff, Prod.forall]
        intro c d cadd
        by_cases ceq : c = δ ℓ
        · left
          have rw1 (x : ℕ) : (natpart x : (ZMod ℓ)⟦X⟧) = C (R := ZMod ℓ) (natpart x) := rfl
          have rw2 (x : ℕ) : (partition x : (ZMod ℓ)⟦X⟧) = C (R := ZMod ℓ) (partition x) := rfl
          have dlM : d < M := by
            calc
              d ≤ c + d := Nat.le_add_left d c
              _ ≤ ℓ * n := cadd ▸ addb ▸ Nat.le_add_left b a
              _ < M := hℓnM
          have nldivc : ¬ ℓ ∣ c := by
            rw [ceq]
            exact not_dvd_delta ℓ
          have nldivd : ¬ ℓ ∣ d := by
            contrapose! nldivc
            suffices ℓ ∣ c + d from (Nat.dvd_add_iff_left nldivc).mpr this
            rwa [cadd]
          have dn0 : d ≠ 0 := by
            contrapose! nldivd
            rw [nldivd]
            exact dvd_zero ℓ
          simp only [hscalar, rw2, coeff_sum_X_pow dlM,
            natpart_of_ne_zero dn0]
        · right
          rw [coeff_X_pow, if_neg ceq]
      · right
        exact coeff_zero_of_ndvd ldiva
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((∏ i ∈ range M, (1 - X ^ (ℓ * (i + 1))) ^ ℓ) *
          ∑ i ∈ range (M + δ ℓ), C (partition (i - δ ℓ) : ZMod ℓ) * X ^ i) := by
      simp_rw [ppart_eq, coeff_mul_shift_of_zero ppart ppart_zero]
      congr
      ext1 i
      rw [← ppart_eq]
      rfl
    _ = coeff (R := ZMod ℓ) n
        ((∏ i ∈ range M, (1 - X ^ (i + 1)) ^ ℓ) *
          PowerSeries.UOp ℓ (∑ i ∈ range (M + δ ℓ),
            C (partition (i - δ ℓ) : ZMod ℓ) * X ^ i)) := by
      have hsub :
          (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (ℓ * (i + 1))) ^ ℓ) =
            PowerSeries.subst ((X : PowerSeries (ZMod ℓ)) ^ ℓ)
              (∏ i ∈ range M, (1 - (X : PowerSeries (ZMod ℓ)) ^ (i + 1)) ^ ℓ) := by
        rw [← PowerSeries.coe_substAlgHom (HasSubst.X_pow hℓ0)]
        simp only [map_prod, map_pow, map_sub, map_one, PowerSeries.substAlgHom_X, pow_mul]
      rw [hsub]
      exact coeff_mul_subst_UOp ℓ n hℓ0 _ _
    _ = coeff (R := ZMod ℓ) n
        ((∏ i ∈ range n, (1 - X ^ (i + 1)) ^ ℓ) *
          ∑ i ∈ range (n + 1), C (partition (ℓ * i - δ ℓ) : ZMod ℓ) * X ^ i) := by
      rw [PowerSeries.coeff_mul]
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.mem_antidiagonal] at ha
      have hsumle : a.1 + a.2 ≤ n := le_of_eq ha
      have ha₁ : a.1 ≤ n := Nat.le_of_add_right_le hsumle
      have ha₂ : a.2 ≤ n := Nat.le_of_add_left_le hsumle
      rw [coeff_prod_range_pow_le ℓ a.1 n M ha₁ (le_trans ha₁ hnM)]
      rw [PowerSeries.coeff_UOp]
      have hshift : ℓ * a.2 < M + δ ℓ := by
        calc
          ℓ * a.2 ≤ ℓ * n := Nat.mul_le_mul_left ℓ ha₂
          _ < M := hℓnM
          _ ≤ M + δ ℓ := Nat.le_add_right _ _
      rw [PowerSeries.coeff_sum_X_pow hshift]
      rw [PowerSeries.coeff_sum_X_pow (Nat.lt_succ_of_le ha₂)]


theorem fourier_flu {ℓ} [hℓ : isLargePrime ℓ] :
  (fl ℓ).UOp.fourier =
    (.mk fun n => coeff n ((∏ i ∈ range n, (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ^ ℓ))) *
    .mk fun n => coeff n
        (∑ i ∈ range (n + 1),  C (partition (ℓ * i - δ ℓ) : ZMod ℓ) * X ^ i) := by
  ext n
  simp [-fourier_UOp, ← ModularFormMod.coeff_def, -ModularFormMod.coeff_UOp]
  rw [coeff_flu]
  simp [PowerSeries.coeff_mul]
  congr! 2 with y yin
  have : y.1 ≤ n := HasAntidiagonal.antidiagonal.fst_le yin

  exact coeff_prod_range_pow_le ℓ y.1 n y.1 this le_rfl
  conv =>
    lhs
    rhs
    intro z
    rw [show (partition (ℓ * z - δ ℓ) : PowerSeries (ZMod ℓ)) =
        C (R := ZMod ℓ) (partition (ℓ * z - δ ℓ)) from rfl]
    simp only [coeff_C, ← ite_and]
    rw [Finset.sum_ite_zero (antidiagonal y.2)
      (p := fun x => x.2 = z ∧ x.1 = 0)
      (by
        intro x hx y hy hxy hxy'
        apply Prod.ext
        · exact hxy.2.trans hxy'.2.symm
        · exact hxy.1.trans hxy'.1.symm)]
  simpa using by grind [HasAntidiagonal.antidiagonal.snd_le yin]




theorem flu_eq_zero_iff {ℓ} [hℓ : isLargePrime ℓ] :
    (fl ℓ).UOp = 0 ↔ ramanujan_congruence ℓ := by
  simp_rw [ramanujan_congruence, ramanujan_congruence', ← ZMod.natCast_eq_zero_iff]
  constructor <;> intro h
  · rw [fourier_eq_iff, fourier_flu, ModularFormMod.fourier_zero] at h
    simp at h
    rw [or_iff_not_imp_left] at h
    nth_rw 2 [PowerSeries.ext_iff] at h
    simp at h
    apply h <| exists_coeff_ne_zero_iff_ne_zero.mp ⟨0, by simp⟩
  · ext n
    simp_rw [coeff_flu, ModularFormMod.coeff_zero, delta, h]
    simp only [map_zero, MulZeroClass.zero_mul, sum_const_zero, MulZeroClass.mul_zero]


alias ⟨_, flu_eq_zero⟩ := flu_eq_zero_iff



-- theorem flu_eq_zero {ℓ} [hℓ : isLargePrime ℓ] :
--     ramanujan_congruence ℓ → (fl ℓ).UOp = 0 := fun h => ext fun n => by

--   simp only [ModularFormMod.coeff_UOp, fl_eq_coeff_Product, map_zero]

--   have lg5 : ℓ ≥ 5 := hℓ.AtLeastFive
--   have lsq : ℓ ^ 2 ≥ 25 := by
--     trans 5 * 5; rw [sq]; gcongr; rfl

--   set g : ℕ → Polynomial (ZMod ℓ) :=
--     fun n => Polynomial.X ^ (δ ℓ) * (∏ i ∈ range n, (1 - Polynomial.X ^ (i + 1)) ^ (ℓ ^ 2)) with geq

--   obtain ⟨ m, goeq ⟩ := partitionProduct_mul_eq_natpart_sum (ℓ * n) g

--   letI M := max m (ℓ * n + 1)
--   have mleM : m ≤ M := by simp only [M, le_sup_left]

--   have elnltM : ℓ * n < M := by simp only [← succ_le_iff, M, le_sup_right]

--   have g_coe_rw : (X : (ZMod ℓ)⟦X⟧) ^ δ ℓ * ∏ i ∈ range M,
--       (1 - (X : (ZMod ℓ) ⟦X⟧) ^ (i + 1)) ^ ℓ ^ 2 = ↑(g M) := by
--     simp only [geq, Polynomial.coe_mul, Polynomial.coe_pow,
--       Polynomial.coe_X, ← Polynomial.coe_prod, mul_eq_mul_left_iff,
--         pow_eq_zero_iff', X_ne_zero, ne_eq, false_and, or_false]
--     congr; ext1 i; simp only [Polynomial.coe_sub, Polynomial.coe_one,
--       Polynomial.coe_pow, Polynomial.coe_X]

--   calc

--   _ = coeff (R := ZMod ℓ) (ℓ * n) (flProduct ℓ M) := by
--     rw [flProduct_coeff_le elnltM.le <| le_refl _]


--   _ = (coeff (ℓ * n) )
--       (X ^ (δ ℓ) * ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2 - 1)) := by
--     rw [flProduct]; congr! 4; exact twentyfour_mul_delta ℓ

--   _ = (coeff (ℓ * n))
--       ( X ^ (δ ℓ) * (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
--       (partitionProduct M) ) := by
--     rw[mul_assoc]; congr
--     trans ∏ i ∈ range M, ( (↑1 - X ^ (i + 1)) ^ (ℓ ^ 2) * (↑1 - X ^ (i + 1))⁻¹ )
--     {
--       congr; ext1 i;

--       refine (PowerSeries.eq_mul_inv_iff_mul_eq ?_).mpr ?_
--       simp only [map_sub, constantCoeff_one, map_pow, constantCoeff_X]
--       rw [zero_pow <| succ_ne_zero i, sub_zero]; exact Ne.symm (zero_ne_one' (ZMod ℓ))
--       nth_rw 2 [← pow_one (1 - X ^ (i + 1))]; rw [mul_comm, pow_mul_pow_sub]
--       exact NeZero.one_le
--     }
--     exact prod_mul_distrib

--   _ = (coeff (R := ZMod ℓ) (ℓ * n))
--       ( (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
--       ( X ^ (δ ℓ) * ∑ i ∈ range M, (natpart i) * (X : (ZMod ℓ) ⟦X⟧) ^ i ) ) := by
--     rw [g_coe_rw, goeq M mleM, ← g_coe_rw]; ring_nf

--   _ = (coeff (R := ZMod ℓ) (ℓ * n))
--       ( (∏ i ∈ range M, ((↑1 - X ^ (ℓ * (i + 1))) ^ ℓ) ) *
--       (X ^ (δ ℓ) * ∑ i ∈ range M, (natpart i) * (X : (ZMod ℓ) ⟦X⟧) ^ i) ) := by
--     congr; ext1 i
--     trans ((1 - X ^ (i + 1)) ^ ℓ) ^ ℓ
--     rw[pow_two, pow_mul]
--     congr
--     rw [sub_pow_expChar_of_commute ℓ, one_pow, ← pow_mul, mul_comm]
--     exact Commute.one_left _


--   _ = (coeff (R := ZMod ℓ) (ℓ * n))
--       ( (∏ i ∈ range M, ((↑1 - X ^ (ℓ * (i + 1))) ^ ℓ) ) *
--       (X ^ (δ ℓ) * ∑ i ∈ range M, (partition i) * (X : (ZMod ℓ) ⟦X⟧) ^ i) ) := by
--     simp only [PowerSeries.coeff_mul]; apply sum_congr rfl
--     simp only [mem_antidiagonal, mul_eq_mul_left_iff, Prod.forall]
--     intro a b addb
--     by_cases ldiva : ℓ ∣ a
--     {
--       have ldivb : ℓ ∣ b := by
--         suffices ℓ ∣ a + b from (Nat.dvd_add_iff_right ldiva).mpr this
--         use n
--       left; apply sum_congr rfl
--       simp only [mem_antidiagonal, mul_eq_mul_left_iff, Prod.forall]
--       intro c d cadd
--       by_cases ceq : c = δ ℓ
--       {
--         left
--         have rw1 (x) : (natpart x : (ZMod ℓ)⟦X⟧) = C (R := ZMod ℓ) (natpart x) := rfl
--         have rw2 (x) : (partition x : (ZMod ℓ)⟦X⟧) = C (R := ZMod ℓ) (partition x) := rfl
--         have dlM : d < M := by calc
--           d ≤ c + d := Nat.le_add_left d c
--           _ ≤ ℓ * n := cadd ▸ addb ▸ (Nat.le_add_left b a)
--           _ < M := elnltM

--         have nldivc : ¬ ℓ ∣ c := by
--           rw[ceq]; exact not_dvd_delta ℓ
--         have nldivd : ¬  ℓ ∣ d := by
--           contrapose! nldivc
--           suffices ℓ ∣ c + d from (Nat.dvd_add_iff_left nldivc).mpr this
--           rwa[cadd]
--         have dn0 : ¬ d = 0 := by
--           contrapose! nldivd; rw[nldivd]; exact dvd_zero ℓ

--         simp only [rw1, rw2, coeff_sum_X_pow dlM, natpart_of_ne_zero dn0]
--       }

--       right; rw[coeff_X_pow, if_neg ceq]
--     }

--     right; exact coeff_zero_of_ndvd ldiva


--   _ = (coeff (R := ZMod ℓ) (ℓ * n))
--       ((∏ i ∈ range M, (1 - X ^ (ℓ * (i + 1))) ^ ℓ) *
--       ∑ i ∈ range (M + δ ℓ), C (partition (i - δ ℓ) : ZMod ℓ) * X ^ i) := by
--     simp_rw [ppart_eq, coeff_mul_shift_of_zero ppart ppart_zero]
--     congr; ext1 i; rw[← ppart_eq]; rfl

--   _ = 0 := by
--     obtain ⟨c, L, heq⟩ := prod_eq_sum (ZMod ℓ) ℓ M
--     simp_rw [heq, ← smul_eq_C_mul, apart_eq]

--     rw [mul_comm (∑ i ∈ range L, (c i) • X ^ (ℓ * i))]

--     set c' : ℕ → (ZMod ℓ) := fun i ↦ if i < L then c i else 0 with hc'
--     have c'rw : ∑ i ∈ range L,  (c i) • X (R := ZMod ℓ) ^ (ℓ * i) =
--         ∑ i ∈ range (L + (ℓ * n + 1)), (c' i) • X ^ (ℓ * i) := by
--       rw[sum_range_add, ← add_zero (∑ i ∈ range L, (c i) • X ^ (ℓ * i))]
--       congr 1; apply sum_congr rfl; intro i ilM; congr
--       rw[hc']; simp_all only [mem_range, if_pos]
--       symm; apply sum_eq_zero; intro i ilm
--       suffices c' (L + i) = 0 by simp only [this, zero_smul]
--       simp only [add_lt_iff_neg_left, not_lt_zero, reduceIte, c']

--     simp_rw [c'rw, smul_eq_C_mul]
--     rw [coeff_sum_squash]

--     simp only [← apart_eq]; apply sum_eq_zero
--     intro x hx
--     have : ↑(partition (ℓ * x.1 - δ ℓ)) = (0 : ZMod ℓ) :=
--       (ZMod.natCast_eq_zero_iff ..).mpr <| h x.1

--     rw [this, MulZeroClass.zero_mul]
--     exact Nat.lt_add_right (δ ℓ) elnltM
--     exact Nat.lt_add_left L <| Nat.le_refl _


-- end section
