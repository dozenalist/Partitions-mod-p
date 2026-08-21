import PartitionsLeanblueprint.RamanujanCongruence.PreliminaryResults


open ModularFormMod

noncomputable section

variable {ℓ : ℕ} {k j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k)

lemma Filt_Delta : (Δ : ModularFormMod ℓ 12).Filtration = 12 := sorry

lemma twelve_delta_cast [isLargePrime ℓ] : ((ℓ^2 - 1)/2 : ℕ) = ((ℓ : ℤ)^2 - 1)/2 := by
  rw [Int.natCast_ediv, Nat.cast_ofNat, Int.natCast_pred_of_pos <| pow_two_pos_of_ne_zero NeZero.out, Nat.cast_pow]

lemma Filt_fl [isLargePrime ℓ] : (fl ℓ).Filtration = (ℓ^2 - 1)/2 := by
  rw[fl_eq_Delta_pow, Filtration_pow, Filt_Delta, mul_comm]
  norm_cast; rw [twelve_delta, twelve_delta_cast]
  rfl



theorem NeZero.of_coeff_ne_zero {k} {f : ModularFormMod ℓ k} (h : ∃ n, f.coeff n ≠ 0) : NeZero f where
  out := by contrapose! h; simp only [h, coeff_zero, implies_true]

theorem NeZero.coeff_ne_zero {k} {f : ModularFormMod ℓ k} [h : NeZero f] :
    ∃ n, f.coeff n ≠ 0 := have h := h.out; by contrapose! h; exact ext h

instance NeZero_Theta_fl [isLargePrime ℓ] : NeZero (fl ℓ).Theta :=
  NeZero.of_coeff_ne_zero ⟨δ ℓ, by simpa [ZMod.natCast_eq_zero_iff] using not_dvd_delta ℓ⟩

instance NeZero_Theta_pow_fl (m) [isLargePrime ℓ] : NeZero ((fl ℓ).Theta_pow m) :=
  NeZero.of_coeff_ne_zero ⟨δ ℓ, by simp [ZMod.natCast_eq_zero_iff, not_dvd_delta]⟩



--Lemma 2.1

-- (pt 1)
theorem Filt_Theta_bound : f.Theta.Filtration ≤ f.Filtration + (ℓ + 1) := sorry

-- (pt 2)
theorem Filt_Theta_iff :
    f.Theta.Filtration = f.Filtration + (ℓ + 1) ↔ ¬ ↑ℓ ∣ f.Filtration := sorry




lemma Filt_Theta_bound' {m j : ℕ} (h : m = j + 1) :
    (f.Theta_pow m).Filtration ≤ (f.Theta_pow j).Filtration + (ℓ + 1) := by
  subst h
  simpa only [Theta_pow_succ, Filtration_Mcast] using Filt_Theta_bound <| f.Theta_pow j


lemma Filt_Theta_iff' {m j : ℕ} (h : m = j + 1) :
    (f.Theta_pow m).Filtration = (f.Theta_pow j).Filtration + (ℓ + 1) ↔
      ¬ ↑ℓ ∣ (f.Theta_pow j).Filtration := by
  subst h
  simpa only [Theta_pow_succ, Filtration_Mcast] using Filt_Theta_iff <| f.Theta_pow j


lemma Filt_Theta_congruence [NeZero f.Theta] [NeZero ℓ] :
    f.Theta.Filtration = f.Filtration + (ℓ + (1 : ZMod (ℓ - 1))) := by
  simp only [Filtration_congruence, ← one_add_one_eq_two, ZMod.pred_eq_one]



lemma Filt_Theta_congruence_of_dvd [hℓ : ℓ.AtLeastTwo] [hfT : NeZero f.Theta] (ldiv : ↑ℓ ∣ f.Filtration) :
    ∃ α > 0, f.Theta.Filtration = f.Filtration + (ℓ + 1) - α * (ℓ - 1) := by

  have : NeZero (ℓ - 1) := ⟨have := hℓ.prop; by omega⟩

  have bound := lt_of_le_of_ne (Filt_Theta_bound f) fun h => (Filt_Theta_iff f).1 h ldiv

  have := by simpa only [← AddCommGroup.modEq_iff_intModEq, AddCommGroup.modEq_iff_eq_add_zsmul, smul_eq_mul]
    using ZMod.intCast_eq_intCast_iff ..|>.1 <| by exact_mod_cast (Filt_Theta_congruence f).symm

  norm_cast at bound
  obtain ⟨α, hα⟩ := this
  rw [hα, add_lt_iff_neg_left] at bound
  have := this.out.pos

  use -α, by
    simp only [Int.neg_pos]
    zify at this
    exact Int.neg_of_mul_neg_left bound this

  rw [hα, neg_mul, sub_neg_eq_add, Nat.cast_pred <| NeZero.pos ℓ]; rfl




lemma Filt_Theta_congruence_of_dvd' {m j : ℕ} [ℓ.AtLeastTwo] [hfT : NeZero (f.Theta_pow m)]
  (ldiv: ↑ℓ ∣ (f.Theta_pow j).Filtration) (h : m = j + 1) :
    ∃ α > 0, (f.Theta_pow m).Filtration = (f.Theta_pow j).Filtration + (ℓ + 1) - α * (ℓ - 1) := by
  subst h
  simp_all only [Theta_pow_succ, Filtration_Mcast]
  exact Filt_Theta_congruence_of_dvd _ ldiv (hfT := NeZero.Mcast _ hfT)



-- Lemma 3.2
theorem le_Filt_Theta_fl [isLargePrime ℓ] : ∀ m, (fl ℓ).Filtration ≤ ((fl ℓ).Theta_pow m).Filtration := by
  sorry
  -- intro m
  -- have eq2 : 12 * δ ℓ = 2 * (6 * δ ℓ) := by rw [← mul_assoc]; rfl
  -- rw [Filt_fl, ← twelve_delta]
  -- by_contra! filt_lt
  -- rw [Filt_lt_iff] at filt_lt
  -- obtain ⟨k, klt, haw⟩ := filt_lt

  -- have fn0 : NeZero (Θ^[m] (fl ℓ)) := inferInstance

  -- obtain ⟨d, hd⟩ := haw
  -- have dn0 : NeZero d := by
  --   obtain ⟨a,b⟩ := @val_of_NeZero _ _ _ _ fn0
  --   refine IntegerModularForm.Exists_ne_zero ⟨a, ?_⟩
  --   contrapose! b
  --   rw [hd]; trans ↑(d a); rfl
  --   rw [b, Int.cast_zero]

  -- obtain ⟨h, dr⟩ := Reduce_of_reduce hd

  -- obtain ⟨j, jcon⟩ := IntegerModularForm.exists_two_mul_weight d
  -- subst jcon

  -- set f := (Mcast (by rw [← h]; norm_cast) (Θ^[m] (fl ℓ)) : ModularFormMod ℓ (2 * j)) with feq

  -- have : NeZero f := by rw [Mcast_NeZero]; infer_instance

  -- have hf : ∀ n < δ ℓ, f n = 0 := fun n nlt => by
  --   simp only [feq, Mcast_apply, Theta_pow_apply, fl_lt_delta nlt, mul_zero]

  -- obtain ⟨b', hb, hj, aeq, ordb⟩ := exists_maximal_Reduce f hf ⟨d, fun n => by rw [← hd, feq, Mcast_apply]⟩

  -- suffices b' = 0 from absurd this hb.out

  -- apply IntegerModularForm.zero_of_leading_zeros

  -- suffices ModularForm.dim j ≤ δ ℓ from fun n nlt => by
  --   rw [IntegerModularForm.lt_ord_apply]
  --   omega

  -- apply (IntegerModularForm.dim_le j).trans
  -- omega




-- Lemma 3.3

-- (pt 1) stated here as an implication, instead of an or statement
-- theorem Filt_Theta_pow_l_sub_one [Fact (ℓ ≥ 5)] :
--     ¬ ℓ ∣ 𝔀 (Θ^[ℓ - 1] (fl ℓ)) → 𝔀 (Θ^[ℓ - 1] (fl ℓ)) = (ℓ^2 - 1)/2 := by
--   sorry
--   intro h

--   have Filt_eq : 𝔀 (Θ (fl ℓ)) = (ℓ^2 - 1) / 2 + ℓ + 1 := by
--     rw [← Filt_fl]; apply Filt_Theta_iff.2; rw [Filt_fl]; exact not_dvd_filt

--   rw [Filt_eq_of_Mod_eq Theta_pow_l_eq_Theta.symm, Filt_eq_of_Mod_eq Theta_pow_pred] at Filt_eq

--   have : 𝔀 (Θ (Theta_pow (ℓ - 1) (fl ℓ))) - (ℓ + 1) = 𝔀 (Theta_pow (ℓ - 1) (fl ℓ)) :=
--     (Nat.eq_sub_of_add_eq (add_assoc _ _ 1 ▸ (Filt_Theta_iff.2 h).symm)).symm

--   exact this ▸ Nat.sub_eq_of_eq_add Filt_eq


-- -- (pt 2)
-- theorem Filt_U_pos [Fact (ℓ ≥ 5)] : ℓ ∣ 𝔀 (Θ^[ℓ - 1] (fl ℓ)) → 𝔀 (fl ℓ |𝓤) > 0 := by

--   intro h; by_contra! filto; rw[nonpos_iff_eq_zero] at filto
--   have folly : 𝔀 (fl ℓ |𝓤 ** ℓ) = 0 := by rw[Filtration_Log, filto, mul_zero]
--   obtain ⟨c,hc⟩ := const_of_Filt_zero filto
--   have fconn : (fl ℓ |𝓤) ** ℓ == (const c) ** ℓ := by
--     intro n; rw[Mpow_apply, Mpow_apply]; congr
--     ext x; congr; ext y; rw[hc (x y)]
--   have (c) : ∃ d : ZMod ℓ, (const c) ** ℓ == const d := ⟨c^ℓ, const_pow c ℓ⟩

--   obtain ⟨d,hd⟩ := this c

--   have Thecon : ((fl ℓ) -l Θ^[ℓ - 1] (fl ℓ)) (by simp only [CharP.cast_eq_zero, zero_mul,
--     add_zero]) == const d := calc
--       _ == (fl ℓ |𝓤)**ℓ := (U_pow_l_eq_self_sub_Theta_pow_l_sub_one (fl ℓ)).symm
--       _ == const c**ℓ := fconn
--       _ == const d := hd

--   have zepo : ∀ n, ((fl ℓ) -l Θ^[ℓ - 1] (fl ℓ))
--       (by simp only [CharP.cast_eq_zero, zero_mul, add_zero]) n = 0

--     | 0 => by rw [sub_congr_left_apply, Theta_pow_apply, fl_zero, mul_zero, sub_zero]

--     | _ + 1 => Thecon _ ▸ rfl

--   have feq : fl ℓ == Θ^[ℓ - 1] (fl ℓ) := by
--     simpa only [sub_congr_left_apply, sub_eq_zero] using zepo

--   apply Filt_eq_of_Mod_eq at feq
--   have wrong : ℓ ∣ 𝔀 (fl ℓ) := feq ▸ h
--   have right := @not_dvd_filt ℓ _ _
--   rw[Filt_fl] at wrong
--   exact right wrong


-- (3.5)
-- theorem Lemma_stitch [Fact (ℓ ≥ 5)] : 𝔀 (fl ℓ |𝓤) = 0 → 𝔀 (Θ^[ℓ - 1] (fl ℓ)) = (ℓ^2 - 1)/2 := fun h =>
--   have h' : ¬ 𝔀 (fl ℓ |𝓤) > 0 := Eq.not_gt h
--   have : ¬ ℓ ∣ 𝔀 (Θ^[ℓ - 1] (fl ℓ)) := by contrapose! h'; exact Filt_U_pos h'
--   Filt_Theta_pow_l_sub_one this


theorem Filtration_Theta_pow_sub_one [isLargePrime ℓ] (flu : (fl ℓ).UOp = 0) : ((fl ℓ).Theta_pow (ℓ - 1)).Filtration = (ℓ^2 - 1)/2 := by
  rw [← Filt_fl]; apply Filtration_ext
  intro n; symm; rw [← sub_eq_zero]
  have this := (ModularFormMod.ext_iff.1 <| UOp_pow_l (fl ℓ)) n
  simp only [map_sub, coeff_Mcast] at this
  rw [← this, flu, zero_pow, coeff_zero]
