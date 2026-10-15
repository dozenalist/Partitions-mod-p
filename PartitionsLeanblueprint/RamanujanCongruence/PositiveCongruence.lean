import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.MaximalReduce
import PartitionsLeanblueprint.RamanujanCongruence.PrimaryLemmas
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.FiltrationPow


open ModularFormMod

instance : isLargePrime 5 where
  Prime := Nat.prime_five
  AtLeastFive := le_rfl

instance : isLargePrime 7 where
  Prime := Nat.prime_seven
  AtLeastFive := by decide

instance : isLargePrime 11 where
  Prime := Nat.prime_eleven
  AtLeastFive := by decide


theorem ramanujan_congruence_5 : ramanujan_congruence 5 := by
  rw [← flu_eq_zero_iff]
  apply sturm_bound 8
  · grw [Filt_UOp_bound, Filt_fl]; decide
  · rw [Filtration_zero]; decide
  · simpa using fl_lt_delta (by decide)


theorem ramanujan_congruence_7 : ramanujan_congruence 7 := by
  rw [← flu_eq_zero_iff]
  apply sturm_bound 11
  · grw [Filt_UOp_bound, Filt_fl]; decide
  · rw [Filtration_zero]; decide
  · simpa using fl_lt_delta (by decide)


theorem Filt_Theta_10_le : (Theta_pow 10 (fl 11)).Filtration ≤ 110 := by
  rcases Filt_Theta_pow_sub_one' (ℓ := 11) with heq | hdvd
  · rw [heq]; decide
  · obtain ⟨α, hα, hf⟩ := Filt_Theta_pow_congruence (fl 11) 10
    grind [Filt_fl]


theorem ramanujan_congruence_11 : ramanujan_congruence 11 := by
  rw [← flu_eq_zero_iff, ← pow_eq_zero_iff _ 11 (by decide), UOp_pow_l]
  apply sturm_bound 110
  · grw [Filtration_sub]
    simpa only [Nat.add_one_sub_one, Filtration_Mcast, sup_le_iff]
      using ⟨by rw [Filt_fl]; decide, Filt_Theta_10_le⟩
  · rw [Filtration_zero]; decide
  · simp only [Int.reduceToNat, Nat.reduceDiv, Nat.add_one_sub_one,
      Nat.cast_ofNat, map_sub, coeff_Mcast, coeff_zero]
    intro n nle
    rw [coeff_Theta_pow, nsmul_eq_mul, Nat.cast_pow, sub_eq_zero]
    interval_cases n <;> first
    | rw [fl_lt_delta (by decide), MulZeroClass.mul_zero]
    | rw [show (_ : ZMod 11) ^ 10 = 1 by decide, _root_.one_mul]


theorem ramanujan_congruence_5_verbose (n : ℤ) :
    partition (5 * n + 4) ≡ 0 [MOD 5] := by
  rw [Nat.modEq_zero_iff_dvd, show 5 * n + 4 = 5 * (n + 1) - 1 by ring]
  exact ramanujan_congruence_5 (n + 1)

theorem ramanujan_congruence_7_verbose (n : ℤ) :
    partition (7 * n + 5) ≡ 0 [MOD 7] := by
  rw [Nat.modEq_zero_iff_dvd, show 7 * n + 5 = 7 * (n + 1) - 2 by ring]
  exact ramanujan_congruence_7 (n + 1)

theorem ramanujan_congruence_11_verbose (n : ℤ) :
    partition (11 * n + 6) ≡ 0 [MOD 11] := by
  rw [Nat.modEq_zero_iff_dvd, show 11 * n + 6 = 11 * (n + 1) - 5 by ring]
  exact ramanujan_congruence_11 (n + 1)


#print axioms ramanujan_congruence_11_verbose
