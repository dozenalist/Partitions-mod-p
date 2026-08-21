import PartitionsLeanblueprint.RamanujanCongruence.DescentArgument
import Mathlib.NumberTheory.LegendreSymbol.Basic

open ModularFormMod hiding mul_one one_mul


private lemma Oddl (ℓ) [isLargePrime ℓ] : Odd ℓ :=
  let t : ℓ ≥ 5 := Fact.out
  Nat.Prime.odd_of_ne_two Fact.out (by linarith)

lemma Theta_l_add_three_div_two_fl_delta_add_one {ℓ : ℕ} [isLargePrime ℓ] :
    (Θ^[(ℓ + 3)/2] (fl ℓ)).coeff (δ ℓ + 1) = (δ ℓ + 1) ^ ((ℓ + 3) / 2) := by
  rw[coeff_Theta_pow, fl_delta_add_one, nsmul_one]; norm_cast


-- section private_lemmas

-- variable {ℓ : ℕ}

-- instance institobvious : NeZero (6 * δ ℓ + 2) := ⟨by norm_num⟩

-- @[norm_cast] lemma l_add_three [ℓ.AtLeastTwo] : (ℓ + 3 : ℕ) = (4 : ZMod (ℓ - 1)) := by
--   trans ℓ + 3; norm_cast
--   trans (0 + 1 : ℕ) + 3; congr 1; simp
--   norm_num



-- private lemma mod_caster [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 13)] :
--     ((2 * (6 * δ ℓ + 2) : ℕ) : ZMod (ℓ - 1)) = 12 * ↑(δ ℓ) + ↑((ℓ + 3) / 2) * 2 := by
--   conv => rhs; rhs; norm_cast; rw [Nat.div_mul_cancel (by have := Nat.odd_iff.mp Oddl; omega)]
--   rw [l_add_three, mul_add, ← mul_assoc]; norm_num

-- open ModularForm in
-- lemma dim_six_delta_add_two : dim (6 * δ ℓ + 2) = δ ℓ + 1 := by
--   simp [dim, if_neg, Nat.add_div]
--   rw [Nat.ModEq]; omega



-- open ModularForm in
-- private lemma delta_lt_dim : δ ℓ < dim (6 * δ ℓ + 2) := dim_six_delta_add_two ▸ lt_add_one (δ ℓ)


-- open ModularForm in
-- private lemma mod_mod_six : (6 * δ ℓ + 2) %% 6 = 2 := by
--   rw [mod_without_two, if_neg]
--   rw [Nat.add_mod, add_zero]
--   trans (0 + 2) % 6; congr
--   rw [← Nat.dvd_iff_mod_eq_zero]
--   apply Nat.dvd_mul_right_of_dvd <| by norm_num
--   rfl

--   suffices t : 6 * δ ℓ + 2 ≡ 0 + 2 [MOD 6] from fun h =>
--     have := h.symm.trans t
--     by rw [Nat.ModEq] at this; omega

--   gcongr
--   apply Nat.modEq_zero_iff_dvd.mpr
--   apply Nat.dvd_mul_right_of_dvd <| by norm_num



-- open ModularForm in
-- private lemma Gmk_set_mk_delta : Gmk_set_mk (6 * δ ℓ + 2) (δ ℓ) = (1, 0, δ ℓ) := by
--   simp [Gmk_set_mk, mod_mod_six, Gmk_dim_one, Gmk_twelve_mk]
--   exact Nat.sub_eq_zero_of_le <| le_of_eq <| Nat.div_eq_of_eq_mul_right zero_lt_two <| by ring

-- end private_lemmas

-- set_option push_neg.use_distrib true in open IntegerModularForm in

-- theorem G_delta_add_one : G (h := ⟨by omega⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩ (δ ℓ + 1) = (241 : ZMod ℓ) := by
--   rw [G_def, Icast_apply, mul_apply]
--   simp; rw [Gmk_set_mk_delta]; dsimp
--   rw [Ipow_one, Ipow_zero, mul_Iconst, one_smul]
--   simp only [Icast_apply]; norm_cast
--   calc

--     _ = (∑ x ∈ antidiagonal (δ ℓ + 1) \ {(0, δ ℓ + 1), (1, δ ℓ)}, (Eis 2) x.1 * (Delta**δ ℓ) x.2
--         + (Eis 2 0 * (Delta**δ ℓ) (δ ℓ + 1) + Eis 2 1 * (Delta**δ ℓ) (δ ℓ)) : ZMod ℓ) := by
--       norm_cast; congr
--       rw [sum_sdiff_eq_sub, sum_pair, sub_add_cancel]
--       exact not_eq_of_beq_eq_false rfl
--       intro x; simp only [mem_insert, mem_singleton, mem_antidiagonal];
--       intro h; rcases h with h | h <;> simp only [h, zero_add, add_comm]

--     _ = 0 + 241 := by
--       congr; trans ↑(0 : ℤ); congr; apply sum_eq_zero fun x xin => ?_
--       simp only [mem_sdiff, mem_antidiagonal, mem_insert, mem_singleton, not_or] at xin

--       have : x.2 ≠ δ ℓ ∧ x.2 ≠ δ ℓ + 1 := by
--         contrapose! xin
--         rw [or_iff_not_imp_left]
--         push_neg; intro h'
--         rcases xin with h | h
--         right; ext <;> omega
--         left; ext <;> omega

--       have : x.2 < δ ℓ := by omega

--       rw [leading_Ipow_zeros Delta_zero this, mul_zero]
--       exact Lean.Grind.Ring.intCast_zero

--       rw [Eis_ne_one_zero, Int.cast_one, one_mul, Eis_two_one,
--         ord_Ipow_ord' _ _ (δ ℓ), ord_Delta, Delta_one, one_pow, Int.cast_one, mul_one]

--       rw [← IntegerModularForm.fl, ← ModularFormMod.fl_apply, fl_delta_add_one]; norm_num

--       rw [ord_Delta, mul_one]
--       exact Nat.add_one_add_one_ne_one

--     _ = 241 := zero_add 241





-- theorem Theta_l_add_three_div_two (flu : fl ℓ |𝓤 = 0) :
--   Mcast mod_caster.symm (Θ^[(ℓ + 3)/2] (fl ℓ)) = (Reduce ℓ ((δ ℓ ^ ((ℓ + 3) / 2))
--     • IntegerModularForm.G (h := ⟨by decide⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩)) := by

--   set fell := (Mcast (by rw[mod_caster.symm]; norm_cast) (Θ^[(ℓ + 3) / 2] (fl ℓ)) : ModularFormMod ℓ (2 * (6 * δ ℓ + 2 : ℕ))) with fellquall

--   have fellply : ∀ n, (Θ^[(ℓ + 3) / 2] (fl ℓ)) n = fell n := fun n => by rw [fellquall, Mcast_apply]

--   have fellell : ∀ n < δ ℓ, fell n = 0 := fun n nlt => by
--     simp only [fellquall, Mcast_apply, Theta_pow_apply, fl_lt_delta nlt, mul_zero]

--   have : NeZero fell := by
--     rw [fellquall, Mcast_NeZero]
--     infer_instance


--   have haw : hasWeight fell (2 * (6 * δ ℓ + 2)) := by
--     have := Weight_of_Filt (Filt_Theta_l_add_three_div_two flu)
--     rw [mul_add, ← mul_assoc]; norm_num; rwa [twelve_delta, fellquall, Weight_Mcast]

--   obtain ⟨b', hb, hj, aeq, ordb⟩ := exists_maximal_Reduce fell fellell haw

--   ext n; simp only [fellply, aeq, Mcast_apply, Reduce_apply]

--   {
--     trans ((b' (δ ℓ) • IntegerModularForm.G (h := ⟨by decide⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩ n : ℤ) : ZMod ℓ)

--     nth_rw 1 [IntegerModularForm.eq_G_of_ord_max b' (hk := ⟨by omega⟩)]
--     simp only [dim_six_delta_add_two, Nat.add_sub_cancel]; congr
--     rw [dim_six_delta_add_two, Nat.add_sub_cancel]
--     rcases ordb.eq_or_gt with ordb | ordb
--     exact ordb
--     suffices b' = 0 from absurd this hb.out
--     apply IntegerModularForm.zero_of_leading_zeros
--     rw [dim_six_delta_add_two]
--     intro n nlt
--     apply IntegerModularForm.lt_ord_apply; omega


--     trans ((((δ ℓ) ^ ((ℓ + 3) / 2) : ℤ) • IntegerModularForm.G (h := ⟨by decide⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩ n : ℤ) : ZMod ℓ)
--     simp only [IntegerModularForm.zsmul_apply, smul_eq_mul, Int.cast_mul]
--     push_cast; congr 2; trans fell (δ ℓ)
--     simp only [aeq, Mcast_apply, Reduce_apply]
--     rw [fellquall, Mcast_apply, Theta_pow_apply, fl_delta, mul_one]

--     norm_cast
--   }






lemma Theta_l_add_three_div_two_eq_241 {ℓ : ℕ} (flu : fl ℓ |𝓤 = 0) :
    (Θ^[(ℓ + 3)/2] (fl ℓ)).coeff (δ ℓ + 1) = 241 * (δ ℓ) ^ ((ℓ + 3) / 2) := by
  sorry
  -- have t := ModularFormMod.ext_iff <| Theta_l_add_three_div_two flu
  -- specialize t (δ ℓ + 1); simp_all [mul_comm, G_delta_add_one]





private lemma pow_congr_reduce_of_dvd {a c n : ℤ} {b : ℕ} (an0 : a ≠ 0) (adiv : a ∣ (n^2 - 1))
    ( h : ((n^2 - 1)/a + 1) ^ b ≡ c * ((n^2 - 1)/a) ^ b [ZMOD n] ) :
      (-a + 1) ^ (b) ≡ c [ZMOD n] := by

  obtain ⟨k, hk⟩ := adiv
  rw[hk, Int.mul_ediv_cancel_left _ an0] at h
  have h1 : a * k ≡ -1 [ZMOD n] := by
    trans n ^ 2 - 1; rw[hk]
    trans 0 ^ 2 - 1; gcongr
    exact Final.Hidden.Int.modEq_self; rfl

  have h2 : a * (k + 1) ≡ a - 1 [ZMOD n] := calc
      a * (k + 1) = a * k + a := by ring
      _ ≡ -1 + a [ZMOD n] := by gcongr
      _ = a - 1 := by ring

  have h3 : (a - 1) ^ b ≡ c * (a * k) ^ b [ZMOD n] := calc
      _ ≡ (a * (k + 1)) ^ b [ZMOD n] := by gcongr
      _ = a ^ b * (k + 1) ^ b := by rw [mul_pow]
      _ ≡ c * (a ^ b * k ^ b) [ZMOD n] := by
        rw[← mul_assoc, mul_comm c, mul_assoc]; gcongr
      _ = c * (a * k) ^ b := by rw[mul_pow]

  calc
    (-a + 1) ^ b = (-(a - 1)) ^ b := by ring
    _ = (-1) ^ b * (a - 1) ^ b := by rw [← mul_pow]; ring
    _ ≡ (-1) ^ b * (c * (a * k) ^ b) [ZMOD n] := by gcongr
    _ ≡ c * ((-1)^b * (-1)^b) [ZMOD n] := by
      rw[mul_comm, mul_assoc]; gcongr
    _ = c * 1 := by congr; exact pow_mul_pow_eq_one b rfl
    _ = c := mul_one c



lemma flu_ne_zero {ℓ} [isLargerPrime ℓ] (flu : fl ℓ |𝓤 = 0) : False := by

  have equel : (δ ℓ + 1) ^ ((ℓ + 3) / 2) ≡ 241 * (δ ℓ) ^ ((ℓ + 3) / 2) [ZMOD ℓ] := by
    suffices (δ ℓ + 1) ^ ((ℓ + 3) / 2) = (241 * (δ ℓ) ^ ((ℓ + 3) / 2) : ZMod ℓ) by
      rw[← ZMod.intCast_eq_intCast_iff]; exact_mod_cast this
    rw[← Theta_l_add_three_div_two_fl_delta_add_one, ← Theta_l_add_three_div_two_eq_241 flu]

  have nequal : (δ ℓ + 1) ^ ((ℓ + 3) / 2) ≡ 241 * (δ ℓ) ^ ((ℓ + 3) / 2) [MOD ℓ] := by
    rw[← Int.natCast_modEq_iff]; exact_mod_cast equel

  have delcast : (δ ℓ : ℤ) = (ℓ ^ 2 - 1) / 24 := by
    unfold delta; trans ((ℓ ^ 2 - 1) : ℕ) / 24; rfl
    congr; trans ((ℓ ^ 2) : ℕ) - 1
    exact Int.natCast_pred_of_pos (Nat.pos_of_neZero (ℓ ^ 2))
    rfl

  have deldiv : (24 : ℤ) ∣ (ℓ ^ 2 - 1) := by
    trans ↑(24 : ℕ); exact Int.dvd_of_emod_eq_zero rfl
    trans ↑((ℓ^2 - 1) : ℕ)
    rw[Int.natCast_dvd_natCast]
    exact delta_integer ℓ
    apply dvd_of_eq; rw[Int.natCast_pred_of_pos (Nat.pos_of_neZero (ℓ ^ 2))]; rfl

  have inter : (-23) ^ ((ℓ + 3)/2) ≡ 241 [ZMOD ℓ] := by
    apply pow_congr_reduce_of_dvd (OfNat.zero_ne_ofNat 24).symm deldiv
    rwa[← delcast]

  have binder : (-23) ^ 2 * (-23) ^ ((ℓ - 1)/2) ≡ 241 [ZMOD ℓ] := calc

    (-23) ^ 2 * (-23) ^ ((ℓ - 1)/2) = (-23) ^ (4/2 + (ℓ - 1)/2) := by
      rw[pow_add]

    _ = (-23) ^ ((4 + ℓ - 1)/2) := by
      congr; symm; rw[Nat.add_sub_assoc]; apply Nat.add_div_of_dvd_right
      use 2; exact NeZero.one_le

    _ = (-23) ^ ((ℓ + 3)/2) := by
      congr 2; symm; apply Nat.eq_sub_of_add_eq'
      rw[add_comm ℓ, ← add_assoc]

    _ ≡ 241 [ZMOD ℓ] := inter

  by_cases l23 : ℓ = 23
  {
    simp_all only
    contrapose! inter
    norm_num
    decide
  }
  have ln0 : (-23 : ZMod ℓ) ≠ 0 := by
    contrapose! l23; rw [neg_eq_zero] at l23
    have : (23 : ℕ) = (0 : ZMod ℓ) := by
      rw[← l23]; rfl

    rw [ZMod.natCast_eq_zero_iff] at this
    rwa[← Nat.prime_dvd_prime_iff_eq]
    exact Fact.out
    exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl


  have lrw : (ℓ - 1)/ 2 = ℓ / 2 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_one.mpr (@NeZero.one_le ℓ _)
    rw[hk, add_tsub_cancel_right]; refine Eq.symm (Nat.succ_div_of_not_dvd ?_)
    have : Odd ℓ := Oddl ℓ
    have : ¬ Odd k := by
      rw[hk] at this
      exact Nat.odd_add_one.mp this
    contrapose! this; refine Nat.odd_iff.mpr ?_
    refine Nat.two_dvd_ne_zero.mp ?_
    omega


  have rcases : ((-23 : ZMod ℓ)) ^ ((ℓ - 1)/2) = 1 ∨ (-23 : ZMod ℓ) ^ ((ℓ - 1)/2) = -1 := by
    simp only [lrw]
    apply ZMod.pow_div_two_eq_neg_one_or_one
    exact ln0


  have bindf : (-23 : ZMod ℓ) ^ 2 * (-23 : ZMod ℓ) ^ ((ℓ - 1) / 2) = 241 := by
    calc
       (-23 : ZMod ℓ) ^ 2 * (-23 : ZMod ℓ) ^ ((ℓ - 1) / 2) =
          ↑ ((-23 : ℤ) ^ 2 * (-23 : ℤ) ^ ((ℓ - 1) / 2)) := by zify

      _ = ↑(241 : ℤ) := by
        rwa[ZMod.intCast_eq_intCast_iff]

      _ = 241 := Int.cast_ofNat 241

  have lprime : Nat.Prime ℓ := Fact.out
  have lg13 : ℓ ≥ 13 := Fact.out

  rcases rcases with rcases | rcases

  simp only [even_two, Even.neg_pow, rcases, mul_one] at bindf

  have : ((23 ^ 2: ℕ) : ZMod ℓ) = ((241 : ℕ) : ZMod ℓ) := by
    norm_cast at *

  simp only [ZMod.natCast_eq_natCast_iff, Nat.reducePow, Nat.modEq_iff_dvd] at this
  simp only [Nat.cast_ofNat, Int.reduceSub, dvd_neg] at this
  have : ℓ ∣ 288 := by zify; exact this
  have rw288 : 288 = 2 ^ 5 * 3 ^ 2 := rfl


  have ldiv : ℓ ∣ 2 ^ 5 ∨ ℓ ∣ 3 ^ 2 := by
    rw[rw288] at this
    exact (Nat.Prime.dvd_mul lprime).mp this

  rcases ldiv with lp | lp
  <;> apply Nat.Prime.dvd_of_dvd_pow lprime at lp <;>
  apply Nat.le_of_dvd at lp <;> omega


  simp only [even_two, Even.neg_pow, rcases, mul_neg, mul_one] at bindf

  have : (-(23 ^ 2: ℕ) : ZMod ℓ) = ((241 : ℕ) : ZMod ℓ) := mod_cast bindf

  simp only [Nat.reducePow, Nat.cast_ofNat] at this
  have : ((-529 : ℤ) : ZMod ℓ) = ((241 : ℤ) : ZMod ℓ) := mod_cast this
  simp only [ZMod.intCast_eq_intCast_iff,
    Int.modEq_iff_dvd, Int.sub_neg, Int.reduceAdd] at this

  have : ℓ ∣ 770 := by zify; exact this
  have rw770 : 770 = 2 * 5 * 7 * 11 := rfl


  have ldiv : ℓ ∣ 2 ∨ ℓ ∣ 5 ∨ ℓ ∣ 7 ∨ ℓ ∣ 11 := by
    simpa only [rw770, Nat.Prime.dvd_mul lprime, or_assoc]

  rcases ldiv with lp | lp | lp | lp
  <;> apply Nat.le_of_dvd at lp <;> omega



theorem MainResult (ℓ : ℕ) [isLargerPrime ℓ] : ¬ ramanujan_congruence ℓ :=
  (flu_ne_zero <| flu_eq_zero ·)
