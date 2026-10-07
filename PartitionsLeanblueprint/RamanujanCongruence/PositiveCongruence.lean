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
    simp only [Nat.add_one_sub_one, Filtration_Mcast, sup_le_iff]
    constructor
    · rw [Filt_fl]; decide
    · exact Filt_Theta_10_le
  · rw [Filtration_zero]; decide
  · simp only [Int.reduceToNat, Nat.reduceDiv, Nat.add_one_sub_one,
      Nat.cast_ofNat, map_sub, coeff_Mcast, coeff_zero]
    intro n nle
    rw [coeff_Theta_pow, nsmul_eq_mul, Nat.cast_pow, sub_eq_zero]
    interval_cases n
    all_goals
      try rw [fl_lt_delta (by decide)]
      try decide
    · rw [show 5 = δ 11 by rfl, fl_delta]
      decide
    · rw [show 6 = δ 11 + 1 by rfl, fl_delta_add_one]
      decide
    all_goals
      rw [show (_ : ZMod 11) ^ 10 = 1 by decide, _root_.one_mul]

#print axioms ramanujan_congruence_11
