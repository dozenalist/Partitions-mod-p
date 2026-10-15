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

/-- Shifting the partition series uses integer subtraction, so coefficients below
the shift vanish while the coefficient at the shift is the empty partition. -/
private theorem partition_sum_shift {R : Type} [CommRing R] (N d : ℕ) :
    (X : PowerSeries R) ^ d *
        ∑ i ∈ range N, C (partition (i : ℤ) : R) * X ^ i =
      ∑ i ∈ range (N + d), C (partition ((i : ℤ) - d) : R) * X ^ i := by
  rw [PowerSeries.coeff_mul_shift]
  trans ∑ i ∈ Ico d (N + d), C (partition ((i : ℤ) - d) : R) * X ^ i
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Int.ofNat_sub (Finset.mem_Ico.mp hi).1]
  · rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_left d N)]
    have hzero :
        ∑ i ∈ range d, C (partition ((i : ℤ) - d) : R) * (X : PowerSeries R) ^ i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : (i : ℤ) - d < 0 := by
        have := Finset.mem_range.mp hi
        omega
      simp [partition_of_neg hi']
    rw [hzero, sub_zero]

theorem coeff_flu {ℓ} [hℓ : isLargePrime ℓ] (n : ℕ) :
   (fl ℓ).UOp.coeff n =
    coeff (R := ZMod ℓ) n
      ((∏ i ∈ range n, (1 - X ^ (i + 1)) ^ ℓ) *
        ∑ i ∈ range (n + 1),
          C (partition ((ℓ : ℤ) * i - δ ℓ) : ZMod ℓ) * X ^ i) := by
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
          (X ^ (δ ℓ) * ∑ i ∈ range M,
            C (partition (i : ℤ) : ZMod ℓ) * X ^ i)) := by
      simp only [partition_ofNat, hscalar]
    _ = coeff (R := ZMod ℓ) (ℓ * n)
        ((∏ i ∈ range M, (1 - X ^ (ℓ * (i + 1))) ^ ℓ) *
          ∑ i ∈ range (M + δ ℓ), C (partition ((i : ℤ) - δ ℓ) : ZMod ℓ) * X ^ i) := by
      rw [partition_sum_shift]
    _ = coeff (R := ZMod ℓ) n
        ((∏ i ∈ range M, (1 - X ^ (i + 1)) ^ ℓ) *
          PowerSeries.UOp ℓ (∑ i ∈ range (M + δ ℓ),
            C (partition ((i : ℤ) - δ ℓ) : ZMod ℓ) * X ^ i)) := by
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
          ∑ i ∈ range (n + 1), C (partition ((ℓ : ℤ) * i - δ ℓ) : ZMod ℓ) * X ^ i) := by
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
      simp only [Nat.cast_mul]


theorem fourier_flu {ℓ} [hℓ : isLargePrime ℓ] :
  (fl ℓ).UOp.fourier =
    (.mk fun n => coeff n ((∏ i ∈ range n, (1 - (X : (ZMod ℓ)⟦X⟧) ^ (i + 1)) ^ ℓ))) *
    .mk fun n => coeff n
        (∑ i ∈ range (n + 1),  C (partition ((ℓ : ℤ) * i - δ ℓ) : ZMod ℓ) * X ^ i) := by
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
    rw [show (partition ((ℓ : ℤ) * z - δ ℓ) : PowerSeries (ZMod ℓ)) =
        C (R := ZMod ℓ) (partition ((ℓ : ℤ) * z - δ ℓ)) from rfl]
    simp only [coeff_C, ← ite_and]
    rw [Finset.sum_ite_zero (antidiagonal y.2)
      (p := fun x => x.2 = z ∧ x.1 = 0)
      (by
        intro x hx y hy hxy hxy'
        apply Prod.ext
        · exact hxy.2.trans hxy'.2.symm
        · exact hxy.1.trans hxy'.1.symm)]
  simpa using by grind [HasAntidiagonal.antidiagonal.snd_le yin]




private theorem ramanujan_congruence_iff_nat {ℓ} [hℓ : isLargePrime ℓ] :
    ramanujan_congruence ℓ ↔
      ∀ n : ℕ, ℓ ∣ partition ((ℓ : ℤ) * n - δ ℓ) := by
  constructor
  · intro h n
    exact h n
  · intro h n
    change ℓ ∣ partition ((ℓ : ℤ) * n - δ ℓ)
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      exact h n
    · have hℓpos : (0 : ℤ) < ℓ := by
        have := hℓ.AtLeastFive
        omega
      have harg : (ℓ : ℤ) * n - δ ℓ < 0 := by
        have hprod : (ℓ : ℤ) * n < 0 := mul_neg_of_pos_of_neg hℓpos (lt_of_not_ge hn)
        have hδ : (0 : ℤ) ≤ δ ℓ := by positivity
        omega
      simpa only [partition_of_neg harg] using (dvd_zero ℓ)

theorem flu_eq_zero_iff {ℓ} [hℓ : isLargePrime ℓ] :
    (fl ℓ).UOp = 0 ↔ ramanujan_congruence ℓ := by
  rw [ramanujan_congruence_iff_nat]
  simp_rw [← ZMod.natCast_eq_zero_iff]
  constructor <;> intro h
  · rw [fourier_eq_iff, fourier_flu, ModularFormMod.fourier_zero] at h
    simp at h
    rw [or_iff_not_imp_left] at h
    nth_rw 2 [PowerSeries.ext_iff] at h
    simp at h
    apply h <| exists_coeff_ne_zero_iff_ne_zero.mp ⟨0, by simp⟩
  · ext n
    simp_rw [coeff_flu, ModularFormMod.coeff_zero, h]
    simp only [map_zero, MulZeroClass.zero_mul, sum_const_zero, MulZeroClass.mul_zero]


alias ⟨_, flu_eq_zero⟩ := flu_eq_zero_iff
