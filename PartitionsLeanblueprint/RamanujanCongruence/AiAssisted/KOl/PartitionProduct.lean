import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.Statements
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.PowPrime

/-!
The generating-function passage from partition congruences to congruences
for powers of the discriminant, as in section 4 of Kiming--Olsson.
All products are finite: coefficient stabilization allows us to avoid
introducing an infinite-product topology.
-/

namespace KOl

open PowerSeries Finset
open scoped IntegerModularForm

noncomputable section

lemma delta_pow_coeff_product {ell : ℕ} [isLargePrime ell]
    (m n N : ℕ) (hn : n ≤ N) :
    ((ModularFormMod.Delta (ℓ := ell)).pow m).coeff n =
      ((DeltaProduct (α := ZMod ell) N) ^ m).coeff n := by
  simp only [ModularFormMod.coeff_def, ModularFormMod.fourier_pow, PowerSeries.coeff_pow]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro i hi
  have hxi : x i ≤ n := finsuppAntidiag.le_right hx hi
  change (ModularFormMod.Delta (ℓ := ell)).coeff (x i) = _
  rw [ModularFormMod.Delta_eq_coeff_Product]
  exact DeltaProduct_coeff_le (le_refl _) (hxi.trans hn)

lemma delta_product_pow_factor {ell m u N : ℕ} [isLargePrime ell]
    (hm : 24 * m + 1 = ell * u) :
    ((DeltaProduct (α := ZMod ell) N) ^ m) =
      ((∏ i ∈ range N, (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ^ u) ^ ell) *
        ((X : PowerSeries (ZMod ell)) ^ m * partitionProduct N) := by
  have hpow (i : ℕ) :
      (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ^ (24 * m) =
        (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ^ (ell * u) *
          (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1))⁻¹ := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
      constantCoeff (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ≠ 0)).2
    rw [← pow_succ, hm]
  rw [DeltaProduct, mul_pow, ← Finset.prod_pow]
  simp only [← pow_mul]
  have hprodFactor :
      (∏ i ∈ range N, (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ^ (24 * m)) =
        (∏ i ∈ range N, ((1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ^ (ell * u) *
          (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1))⁻¹)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hpow i
  rw [hprodFactor]
  rw [Finset.prod_mul_distrib, partitionProduct]
  have hprod :
      (∏ i ∈ range N, (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ^ (ell * u)) =
        (∏ i ∈ range N, (1 - (X : PowerSeries (ZMod ell)) ^ (i + 1)) ^ u) ^ ell := by
    rw [← Finset.prod_pow]
    simp_rw [← pow_mul, Nat.mul_comm u ell]
  rw [hprod]
  ring

lemma partition_progression_coeff_zero {ell a : ℕ} [isLargePrime ell]
    (ha : a < ell) (hcong : congruenceAt ell a)
    {n N : ℕ} (hn : n ≤ N) (hmod : n ≡ a [MOD ell]) :
    (partitionProduct N : PowerSeries (ZMod ell)).coeff n = 0 := by
  rw [← partitionProduct_eq_natpart hn]
  apply (ZMod.natCast_eq_zero_iff (natpart n) ell).2
  have hrem : n % ell = a := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha] using hmod
  have hnform : n = ell * (n / ell) + a := by
    have h := Nat.mod_add_div n ell
    omega
  have h := hcong (n / ell)
  have hcast : (ell : ℤ) * ((n / ell : ℕ) : ℤ) + a = (n : ℤ) := by
    exact_mod_cast hnform.symm
  rw [hcast, standardPartition_ofNat] at h
  exact h

/-- A partition congruence gives a discriminant congruence at the class
shifted by its leading exponent `m`. -/
lemma partition_congruence_delta_coeff_zero {ell m a : ℕ} [isLargePrime ell]
    (ha : a < ell) (hm : ell ∣ 24 * m + 1) (hcong : congruenceAt ell a)
    {n : ℕ} (hmod : n ≡ m + a [MOD ell]) :
    ((ModularFormMod.Delta (ℓ := ell)).pow m).coeff n = 0 := by
  obtain ⟨u, hu⟩ := hm
  rw [delta_pow_coeff_product m n n (le_refl _), delta_product_pow_factor hu,
    PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [PowerSeries.ZMod.coeff_pow_card]
  by_cases hdiv : ell ∣ ij.1
  · rw [ite_eq_left hdiv]
    have hmodj : ij.2 ≡ m + a [MOD ell] := by
      have hfirst : ij.1 ≡ 0 [MOD ell] := Nat.modEq_zero_iff_dvd.2 hdiv
      apply hfirst.add_left_cancel
      simpa only [hadd, zero_add] using hmod
    have hcoef :
        (((X : PowerSeries (ZMod ell)) ^ m) * partitionProduct n).coeff ij.2 = 0 := by
      rw [PowerSeries.coeff_X_pow_mul']
      split_ifs with hmj
      · apply partition_progression_coeff_zero ha hcong
        · have hjn : ij.2 ≤ n := by omega
          exact (Nat.sub_le _ _).trans hjn
        · simpa only [Nat.add_sub_cancel_left] using
            Nat.ModEq.sub_right hmj (Nat.le_add_right m a) hmodj
      · rfl
    rw [hcoef, mul_zero]
  · rw [ite_eq_right hdiv, zero_mul]

/-- The power-series version of Proposition 1, applied to the generating
function transformation for the ordinary partition function. -/
lemma partition_congruence_delta_identity {ell m a : ℕ} [isLargePrime ell]
    (ha : a < ell) (hm : ell ∣ 24 * m + 1) (hcong : congruenceAt ell a) :
    shiftedThetaIdentity ((ModularFormMod.Delta (ℓ := ell)).pow m)
      ((m + a) % ell) := by
  let F := (ModularFormMod.Delta (ℓ := ell)).pow m
  have hexp : ell - 1 ≠ 0 := by
    have hlarge := isLargePrime.AtLeastFive (ℓ := ell)
    omega
  change shiftedThetaSeries F ((m + a) % ell) = F.fourier
  apply PowerSeries.ext
  intro n
  simp only [shiftedThetaSeries, PowerSeries.coeff_mk]
  rw [← ModularFormMod.coeff_def]
  by_cases hx : (n : ZMod ell) - (((m + a) % ell : ℕ) : ZMod ell) = 0
  · have hn : n ≡ m + a [MOD ell] := by
      have hn' : n ≡ (m + a) % ell [MOD ell] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).1 (sub_eq_zero.1 hx)
      exact hn'.trans (Nat.mod_modEq _ _)
    have hcoeff : F.coeff n = 0 := partition_congruence_delta_coeff_zero ha hm hcong hn
    rw [hx, zero_pow hexp, hcoeff]
    simp
  · rw [ZMod.pow_card_sub_one_eq_one hx, one_mul]

/-- The exponent used in the passage from partitions to `Delta` can be
chosen between one and `ell - 1`. -/
lemma partition_delta_exponent {ell : ℕ} [isLargePrime ell] :
    ∃ m : ℕ, 0 < m ∧ m < ell ∧ ell ∣ 24 * m + 1 ∧
      ¬ (24 * m ≡ 1 [MOD ell]) ∧ ¬ (24 * m ≡ 3 [MOD ell]) := by
  let m := delta ell % ell
  have hlarge := isLargePrime.AtLeastFive (ℓ := ell)
  have hpos : 0 < ell := by omega
  have hmpos : 0 < m := by
    have hn := not_dvd_delta ell
    have : delta ell % ell ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hn
    exact Nat.pos_of_ne_zero this
  have hmlt : m < ell := Nat.mod_lt _ hpos
  have hclass : 24 * m ≡ ell - 1 [MOD ell] := by
    exact (Nat.mod_modEq (delta ell) ell).mul_left 24 |>.trans
      (twentyfour_mul_delta_modEq hlarge (inferInstance : isLargePrime ell).Prime)
  have hdiv : ell ∣ 24 * m + 1 := by
    apply Nat.modEq_zero_iff_dvd.1
    have heq : ell - 1 + 1 = ell := by omega
    exact (hclass.add_right 1).trans (by simp [heq, Nat.ModEq])
  refine ⟨m, hmpos, hmlt, hdiv, ?_, ?_⟩
  · intro h1
    have : ell - 1 ≡ 1 [MOD ell] := hclass.symm.trans h1
    have hsmall : ell - 1 < ell := by omega
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hsmall,
      Nat.mod_eq_of_lt (show 1 < ell by omega)] at this
    omega
  · intro h3
    have : ell - 1 ≡ 3 [MOD ell] := hclass.symm.trans h3
    have hsmall : ell - 1 < ell := by omega
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hsmall,
      Nat.mod_eq_of_lt (show 3 < ell by omega)] at this
    omega

/-- Theorem 1 of Kiming--Olsson for the ordinary partition function,
deduced from the theta-filtration obstruction of Theorem 3. -/
theorem kiming_olsson_theorem_one {ell a : ℕ}
    (hell_prime : Nat.Prime ell) (hell : 5 ≤ ell)
    (ha : a < ell) (hcong : congruenceAt ell a) :
    24 * a ≡ 1 [MOD ell] := by
  letI : isLargePrime ell := {Prime := hell_prime, AtLeastFive := hell}
  obtain ⟨m, hmpos, hmlt, hdiv, hm1, hm3⟩ := partition_delta_exponent (ell := ell)
  have hi := partition_congruence_delta_identity ha hdiv hcong
  have hlarge := isLargePrime.AtLeastFive (ℓ := ell)
  have hzero := (theorem_three hmpos hmlt
    (Nat.mod_lt _ (show 0 < ell by omega)) hm1 hm3 hi).1
  have hsum : m + a ≡ 0 [MOD ell] := by
    change (m + a) % ell = 0 % ell
    simpa using hzero
  have hsum24 : 24 * m + 24 * a ≡ 0 [MOD ell] := by
    simpa only [Nat.mul_add, Nat.mul_zero] using hsum.mul_left 24
  have hmclass : 24 * m + 1 ≡ 0 [MOD ell] := Nat.modEq_zero_iff_dvd.2 hdiv
  exact Nat.ModEq.add_left_cancel' (24 * m) (hsum24.trans hmclass.symm)

end

end KOl

