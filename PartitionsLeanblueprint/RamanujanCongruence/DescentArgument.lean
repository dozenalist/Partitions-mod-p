import PartitionsLeanblueprint.RamanujanCongruence.PrimaryLemmas

/- This file proves from after Lemma 3.3 (line 3.5) to line 3.8
It proves that 𝔀 (Θ^[(ℓ + 3)/2] (f ℓ)) = (ℓ^2 - 1)/2 + 4.
From here on, information about a basis will be needed -/

open ModularFormMod hiding mul_one one_mul zero_mul mul_zero

variable {ℓ : ℕ} [isLargePrime ℓ]


private lemma Oddl (ℓ) [isLargePrime ℓ] : Odd ℓ :=
  let t : ℓ ≥ 5 := Fact.out
  Nat.Prime.odd_of_ne_two Fact.out (by linarith)

/-- Θ sends modular forms mod ℓ of weight k to weight k + 2 by
(Θ a) n = n * a n -/
notation "Θ" => Theta

/-- The U operator sends modular forms mod ℓ of weight k to weight k by
(a |𝓤) n = a (ℓ * n) -/
postfix:90 "|𝓤" => UOp


/-- The Θ function, applied repeatedly -/
notation "Θ^["n"]" => Theta_pow n

notation "𝔀" => Filtration


-- (3.6)
theorem Filt_Theta_l_sub_two (flu : fl ℓ |𝓤 = 0) : ↑ℓ ∣ 𝔀 (Θ^[ℓ - 2] (fl ℓ)) := by

  have filt_fl : 𝔀 (fl ℓ |𝓤) = 0 := flu ▸ Filtration_zero
  have sub_one : 𝔀 (Θ^[ℓ - 1] (fl ℓ)) = (ℓ^2 - 1) / 2 := Filtration_Theta_pow_sub_one flu
  by_contra! ndvd
  have lg5 : ℓ ≥ 5 := Fact.out
  have lrw : ℓ - 1 = (ℓ - 2) + 1 := by
    refine (Nat.sub_eq_iff_eq_add ?_).mp rfl; refine (Nat.le_sub_one_iff_lt ?_).mpr ?_ <;> linarith
  have : 𝔀 (fl ℓ) = 𝔀 (Θ^[ℓ - 2] (fl ℓ)) + (ℓ + 1) := by
    trans 𝔀 (Θ^[ℓ - 1] (fl ℓ)); rw [Filt_fl, sub_one]
    rwa [Filt_Theta_iff' (fl ℓ) lrw]
  have : 𝔀 (fl ℓ) ≤ 𝔀 (Θ^[ℓ - 2] (fl ℓ)) := le_Filt_Theta_fl (ℓ - 2)
  linarith


lemma ndvd_of_lel_sub_one_div_two {m} (mmle : m ≤ (ℓ - 1)/2) :
    ¬ℓ ∣ (ℓ ^ 2 - 1) / 2 + m * (ℓ + 1) := by
  suffices ¬ (ℓ ^ 2 - 1) / 2 + m * (ℓ + 1) ≡ 0 [MOD ℓ] by
    contrapose! this; exact (Dvd.dvd.zero_modEq_nat this).symm

  have rarw : (ℓ ^ 2 - 1) / 2 + m * (ℓ + 1) ≡ (ℓ ^ 2 - 1) / 2 + m [MOD ℓ] := by
    rw[mul_add, mul_one]; apply Nat.ModEq.add_left
    suffices m * ℓ ≡ 0 [MOD ℓ] by
      trans 0 + m; gcongr; rw[zero_add]
    exact Nat.modEq_zero_iff_dvd.mpr ⟨m, mul_comm ..⟩

  have mm : (ℓ ^ 2 - 1) / 2 + m = (ℓ ^ 2 + 2*m - 1) / 2 := by
    trans (ℓ ^ 2 - 1) / 2 + 2 * m / 2
    congr; exact Nat.eq_div_of_mul_eq_right two_ne_zero rfl
    trans ((ℓ ^ 2 - 1) + 2 * m) / 2
    exact Eq.symm (Nat.add_div_of_dvd_left ⟨m,rfl⟩)
    congr; refine Eq.symm (Nat.sub_add_comm NeZero.one_le)

  have ll : (ℓ ^ 2 - ℓ) / 2 + ℓ = (ℓ^2 + ℓ) / 2 := by
    trans (ℓ ^ 2 - ℓ) / 2 + 2*ℓ / 2
    congr; exact Nat.eq_div_of_mul_eq_right two_ne_zero rfl
    trans ((ℓ ^ 2 - ℓ) + 2 * ℓ) / 2
    exact Eq.symm (Nat.add_div_of_dvd_left ⟨ℓ,rfl⟩)
    congr 1; rw[two_mul]; rw[← Nat.sub_add_comm]; omega
    exact Nat.le_pow zero_lt_two

  intro h
  have : (ℓ ^ 2 - 1) / 2 + m ≡ 0 [MOD ℓ] := rarw.symm.trans h
  apply Nat.modEq_zero_iff_dvd.mp at this
  contrapose! this
  refine (Nat.not_dvd_iff_lt_mul_succ ((ℓ ^ 2 - 1) / 2 + m) (Nat.pos_of_neZero ℓ)).mpr ?_
  use (ℓ - 1) / 2; constructor; calc
    _ = (ℓ ^ 2 - ℓ) / 2 := by
      rw[pow_two]; trans (ℓ * (ℓ - 1)) / 2
      refine Eq.symm (Nat.mul_div_assoc ℓ ?_)
      obtain ⟨k,hk⟩ := Oddl ℓ
      rw [hk, Nat.add_sub_cancel_right]; exact Nat.dvd_mul_right 2 k
      congr; exact Nat.mul_sub_one ℓ ℓ
    _ < _ := by
      rw[mm]; refine Nat.div_lt_div_of_lt_of_dvd ?_ ?_
      suffices 2 ∣ (ℓ^2 - 1) by omega
      have : Odd (ℓ^2) := Odd.pow <| Oddl ℓ
      obtain ⟨k,hk⟩ := this
      rw[hk]; rw [Nat.add_sub_cancel_right]; exact Nat.dvd_mul_right 2 k
      have lg5 : ℓ ≥ 5 := Fact.out
      refine Nat.sub_lt_right_of_lt_add (Nat.le_pow zero_lt_two) ?_
      omega

  rw[mul_add, mul_one]

  have rlw : ℓ * ((ℓ - 1) / 2) = (ℓ ^ 2 - ℓ) / 2 := by
    rw[pow_two]; trans (ℓ * (ℓ - 1)) / 2
    refine Eq.symm (Nat.mul_div_assoc ℓ ?_)
    obtain ⟨k,hk⟩ := Oddl ℓ
    rw [hk, Nat.add_sub_cancel_right]; exact Nat.dvd_mul_right 2 k
    congr; exact Nat.mul_sub_one ℓ ℓ

  rw[rlw, mm, ll]; refine Nat.div_lt_div_of_lt_of_dvd ?_ ?_
  obtain ⟨k, hk⟩ := Oddl ℓ; rw[hk]
  use 2 * k * k + 3 * k + 1; ring
  refine Nat.sub_one_lt_of_le ?_ ?_
  apply add_pos_of_pos_of_nonneg
  exact Nat.pos_of_neZero (ℓ ^ 2)
  exact Nat.zero_le (2 * m)
  apply add_le_add_right
  omega


lemma Filt_Theta_lel_add_one_div_two {m} (mle : m ≤ (ℓ + 1)/2) :
    𝔀 (Θ^[m] (fl ℓ)) = (ℓ^2 - 1)/2 + m * (ℓ + 1) := by
  induction m with

  | zero => simp only [Theta_pow_zero, Filtration_Mcast,
    Filt_fl, Nat.cast_zero, zero_mul, add_zero]

  | succ m ih =>
    specialize ih (Nat.le_of_succ_le mle)
    have mmle : m ≤ (ℓ - 1) / 2 := by
      trans (ℓ + 1) / 2 - 1 <;> omega

    rw [Theta_pow_succ, Filtration_Mcast, Nat.cast_add, add_mul, ← add_assoc, ← ih,
      Nat.cast_one, one_mul, Filt_Theta_iff, ih]

    have := ndvd_of_lel_sub_one_div_two mmle
    zify at this
    simpa only [Int.natCast_pred_of_pos <| pow_two_pos_of_ne_zero NeZero.out, Nat.cast_pow]



theorem Filt_Theta_l_add_one_div_two : ↑ℓ ∣ 𝔀 (Θ^[(ℓ + 1)/2] (fl ℓ)) := by

  use ℓ + 1
  obtain ⟨k, hk⟩ := Oddl ℓ

  rw [Filt_Theta_lel_add_one_div_two <| le_refl _]; push_cast
  rw [mul_comm, ← Int.mul_ediv_assoc, hk] <;> lia


-- (3.7)
lemma exists_Filt_Theta_l_add_three_div_two :
    ∃ α > 0, 𝔀 (Θ^[(ℓ + 3)/2] (fl ℓ)) = (ℓ^2 - 1)/2 + (ℓ + 3)/2 * (ℓ + 1) - α * (ℓ - 1) := by

  have leq : (ℓ + 3)/2 = (ℓ + 1)/2 + 1 :=
    Nat.div_eq_sub_div zero_lt_two (by linarith)

  have := Filt_Theta_congruence_of_dvd' (ℓ := ℓ) _ Filt_Theta_l_add_one_div_two rfl
  sorry

  -- rw[leq, add_mul, one_mul, ← add_assoc, ← add_assoc,
  --   ← Filt_Theta_lel_add_one_div_two (le_refl _)]





-- Start of page 494

/- Note : α and j are defined differently from the paper.
There is no requirement for them to be ≥ 1, they are both just natural numbers
α here is α + 1, and j here is j + 1 in the paper. -/

variable {ℓ : ℕ} [hℓ : isLargerPrime ℓ]

lemma alpha_bound_ex {α : ℤ}
  (h : 𝔀 (Θ^[(ℓ + 3)/2] (fl ℓ)) = (ℓ^2 - 1)/2 + (ℓ + 3)/2 * (ℓ + 1) - α * (ℓ - 1)) :
    α ≤ (ℓ + 5) / 2 := by


  have bound := le_Filt_Theta_fl (ℓ := ℓ) ((ℓ + 3) / 2)

  contrapose! bound

  rw [h, Filt_fl]
  clear h
  have : Odd (ℓ : ℤ) := by grind [Oddl ℓ]
  obtain ⟨k, hk⟩ := this
  have klarge : k ≥ 6 := by grind [hℓ.AtLeastThirteen]
  rw [hk, add_assoc] at ⊢ bound
  change (2 * k + 2 * 3) / 2 < α at bound
  rw [← mul_add, mul_comm, Int.mul_ediv_cancel _ two_ne_zero] at bound
  ring_nf
  calc

    _ =  k * (((2 + k) * 2) / 2) * 2 - k * α * 2 +
      (k * 2 + k ^ 2 * 2) * 2 / 2 + (2 + k) * 2 / 2 * 2 := by ring_nf

    _ = 4 + k * 8 - k * α * 2 + k ^ 2 * 4 := by simp; ring_nf
    _ ≤ 4 + k * 8 - k * (k + 4) * 2 + k ^ 2 * 4 := by gcongr; omega
    _ < (k * 2 + k ^ 2 * 2) * 2 / 2 := by simp; ring_nf; lia
    _ = _ := by ring_nf



  -- have aleb : (ℓ^2 - 1)/2 + (ℓ + 3)/2 * (ℓ + 1) - (α + 1) * (ℓ - 1) ≥ (ℓ^2 - 1)/2 := by
  --   rw[← h, ← Filt_fl]; exact le_Filt_Theta_fl _

  -- have : (ℓ + 3)/2 * (ℓ + 1) ≥ (α + 1) * (ℓ - 1) := by
  --   suffices (ℓ ^ 2 - 1) / 2 + (ℓ + 3) / 2 * (ℓ + 1) ≥ (ℓ ^ 2 - 1) / 2 + (α + 1) * (ℓ - 1) from
  --     Nat.add_le_add_iff_left.mp this
  --   have : (ℓ ^ 2 - 1) / 2 + (ℓ + 3) / 2 * (ℓ + 1) - (α + 1) * (ℓ - 1) + (α + 1) * (ℓ - 1) ≥
  --       (ℓ ^ 2 - 1) / 2 + (α + 1) * (ℓ - 1) := by
  --     exact Nat.add_le_add_right aleb ((α + 1) * (ℓ - 1))

  --   trans (ℓ ^ 2 - 1) / 2 + (ℓ + 3) / 2 * (ℓ + 1) - (α + 1) * (ℓ - 1) + (α + 1) * (ℓ - 1)
  --   apply le_of_eq; apply Nat.sub_add_cancel
  --   {
  --     apply le_of_lt; by_contra! theweeds
  --     have : (ℓ ^ 2 - 1) / 2 + (ℓ + 3) / 2 * (ℓ + 1) - (α + 1) * (ℓ - 1) = 0 :=
  --       Nat.sub_eq_zero_of_le theweeds
  --     rw[this] at h
  --     have bound : 𝔀 (Θ^[(ℓ + 3) / 2] (fl ℓ)) > 0 := calc
  --       _ ≥ 𝔀 (fl ℓ) := le_Filt_Theta_fl _
  --       _ = (ℓ^2 - 1)/2 := Filt_fl
  --       _ ≥ (ℓ^2 - 1)/24 :=
  --         Nat.div_le_div_left Nat.AtLeastTwo.prop zero_lt_two
  --       _ > 0 := delta_pos
  --     omega
  --   }
  --   exact Nat.add_le_add_iff_right.mpr aleb

  -- by_contra! alarge
  -- have a1large : α + 1 > (ℓ + 5)/2 := calc
  --   _ > (ℓ + 3)/2 + 1 := Nat.add_lt_add_right alarge 1
  --   _ = (ℓ + 5)/2 := by
  --     rw [← Nat.add_div_right (ℓ + 3) (Nat.le.step Nat.le.refl)]

  -- have lg5 : ℓ ≥ 13 := Fact.out

  -- have l1g0 : ℓ - 1 > 0 := by omega

  -- have lrw : (ℓ + 7)/2 = (ℓ + 5)/2 + 1 := calc
  --   _ = (ℓ + 5 + 2)/2 := rfl
  --   _ = (ℓ + 5)/2 + 2/2 := Nat.add_div_right (ℓ + 5) zero_lt_two


  -- have gge : (ℓ + 3)/2 * (ℓ + 1) ≥ (ℓ + 7)/2 * (ℓ - 1) := calc
  --   _ ≥ (α + 1) * (ℓ - 1) := this
  --   _ ≥ (ℓ + 7)/2 * (ℓ - 1) := by
  --     apply Nat.mul_le_mul_right
  --     apply Nat.le_of_lt_add_one at a1large
  --     rw[lrw]; apply Nat.add_le_add_right a1large


  -- have rw1 : (ℓ + 3)/2 * (ℓ + 1) = (ℓ + 3) * (ℓ + 1) / 2 := by
  --   apply Nat.div_mul_right_comm
  --   obtain ⟨k,hk⟩ := Oddl
  --   use k + 2; rw[hk]; ring

  -- have rw2 : (ℓ + 7)/2 * (ℓ - 1) = (ℓ + 7) * (ℓ - 1) / 2 := by
  --   apply Nat.div_mul_right_comm
  --   obtain ⟨k,hk⟩ := Oddl
  --   use k + 4; rw[hk]; ring

  -- rw[rw1,rw2] at gge

  -- have rw3 : (ℓ + 3) * (ℓ + 1) = ℓ^2 + (4*ℓ + 3) := by group

  -- have rw4 : (ℓ + 7) * (ℓ - 1) = ℓ^2 + 6*ℓ - 7 := by
  --   trans (ℓ + 7) * ℓ - (ℓ + 7)
  --   exact Nat.mul_sub_one (ℓ + 7) ℓ
  --   rw[add_mul, pow_two]
  --   trans ℓ * ℓ + (7 * ℓ - ℓ) - 7
  --   omega
  --   omega

  -- have rw5 : ℓ^2 + 6*ℓ - 7 = ℓ^2 + (6*ℓ - 7) :=
  --   Nat.add_sub_assoc (by omega) (ℓ ^ 2)


  -- have glgl : (ℓ + 3) * (ℓ + 1) / 2 < (ℓ + 7) * (ℓ - 1) / 2 := by
  --   rw[Nat.div_lt_div_right two_ne_zero]
  --   rw[rw3,rw4,rw5]; apply add_lt_add_left
  --   calc
  --     _ < 4 * ℓ + ℓ := add_lt_add_left (Nat.lt_of_add_left_lt lg5) (4*ℓ)
  --     _ = 5 * ℓ := (Nat.succ_mul 4 ℓ).symm
  --     _ ≤ 6 * ℓ - ℓ := by
  --       apply le_of_eq; exact Eq.symm (Nat.sub_eq_of_eq_add (Nat.succ_mul 5 ℓ))
  --     _ ≤ _ := by apply Nat.sub_le_sub_left (by omega)

  --   apply Nat.dvd_mul_left_of_dvd
  --   obtain ⟨k,hk⟩ := Oddl
  --   use k + 1; rw[hk]; ring
  --   suffices 2 ∣ (ℓ - 1) by omega
  --   obtain ⟨k,hk⟩ := Oddl
  --   use k; rw [hk, add_tsub_cancel_right]

  -- exact (lt_iff_not_ge.1 glgl) gge


namespace Final.Hidden -- α, j should not show up outside this file

noncomputable def alpha (ℓ) [isLargePrime ℓ] : ℤ :=
  Exists.choose <| exists_Filt_Theta_l_add_three_div_two (ℓ := ℓ)

local notation "α" => alpha


lemma alpha_bound : α ℓ ≤ (ℓ + 5) / 2 :=
  alpha_bound_ex exists_Filt_Theta_l_add_three_div_two.choose_spec.2

lemma alpha_pos : α ℓ > 0 := exists_Filt_Theta_l_add_three_div_two.choose_spec.1



lemma l_div_Filt_Theta_add (flu : fl ℓ |𝓤 = 0) : ↑ℓ ∣ 𝔀 (Θ^[(ℓ+3)/2 + (ℓ - 7)/2] (fl ℓ)) := by
  have : (ℓ + 3) / 2 + (ℓ - 7) / 2 = ℓ - 2 := by
    trans ((ℓ + 3) + (ℓ - 7)) / 2
    refine Eq.symm (Nat.add_div_of_dvd_right ?_)
    obtain ⟨k,hk⟩ := Oddl ℓ
    use k + 2; rw[hk]; ring
    have : ℓ + 3 + (ℓ - 7) = 2*ℓ - 4 := by
      have : ℓ ≥ 13 := Fact.out
      omega
    rw[this]
    trans 2 * (ℓ - 2) / 2
    congr; omega
    exact Nat.mul_div_right (ℓ - 2) zero_lt_two

  rw [Filtration_Theta_cast _ this]
  exact Filt_Theta_l_sub_two flu


noncomputable def j (ℓ) [isLargerPrime ℓ] [Fact (fl ℓ |𝓤 = 0)] :=
  Nat.find ( ⟨(ℓ - 7)/2, l_div_Filt_Theta_add Fact.out⟩ : ∃ j, ↑ℓ ∣ 𝔀 (Θ^[(ℓ+3)/2 + j] (fl ℓ)) )

lemma j_bound (ℓ) [isLargerPrime ℓ] [Fact (fl ℓ |𝓤 = 0)] : j ℓ ≤ (ℓ - 7)/2 := by
  rw [j, Nat.find_le_iff]
  use (ℓ - 7)/2, le_refl _
  exact l_div_Filt_Theta_add Fact.out

lemma j_spec (ℓ) [isLargerPrime ℓ] [Fact (fl ℓ |𝓤 = 0)] : ↑ℓ ∣ 𝔀 (Θ^[(ℓ+3)/2 + j ℓ] (fl ℓ)) :=
  Nat.find_spec (⟨(ℓ - 7)/2, l_div_Filt_Theta_add Fact.out⟩ : ∃ j, ↑ℓ ∣ 𝔀 (Θ^[(ℓ+3)/2 + j] (fl ℓ)))



section omission_inequalities

omit [isLargerPrime ℓ]


@[simp] lemma Int.modEq_self  {n : ℤ} : n ≡ 0 [ZMOD n] := by
  rw [Int.modEq_zero_iff_dvd]

lemma Int.modEq_of_Eq {a b n : ℤ} : a = b → a ≡ b [ZMOD n] := by
  intro h; rw[h]


lemma l_death_ineq [isLargePrime ℓ] :
    (ℓ + 5) / 2 * (ℓ - 1) ≤ (ℓ + 3) / 2 * (ℓ + 1) :=
  calc

  _ = (ℓ + 5) * (ℓ - 1) / 2 := by
    refine Nat.div_mul_right_comm ?_ (ℓ - 1)
    obtain ⟨k,hk⟩ := Oddl ℓ
    rw[hk]; use k + 3; ring

  _ ≤ (ℓ ^ 2 + 4 * ℓ)/2 := by
    apply Nat.div_le_div_right;
    have rw1 : (ℓ + 5) * (ℓ - 1) = (ℓ + 5) * ℓ - (ℓ + 5) := by
      exact Nat.mul_sub_one (ℓ + 5) ℓ

    have rw2 : (ℓ + 5) * ℓ - (ℓ + 5) = ℓ * ℓ + 5 * ℓ - ℓ - 5 := by
      rw[add_mul]; rfl

    have rw3 : ℓ * ℓ + 5 * ℓ - ℓ - 5 = ℓ * ℓ + (5* ℓ - ℓ) - 5 := by
      lia

    have rw4 : ℓ * ℓ + (5* ℓ - ℓ) - 5 = ℓ ^ 2 + 4 * ℓ - 5 := by
      rw[pow_two]; congr; omega

    rw [rw1,rw2,rw3,rw4]
    omega

  _ ≤ (ℓ + 3) * (ℓ + 1) / 2 := by
    apply Nat.div_le_div_right; ring_nf; omega

  _ = _ := by
    refine Nat.mul_div_right_comm ?_ (ℓ + 1)
    obtain ⟨k,hk⟩ := Oddl ℓ
    rw[hk]; use k + 2; ring


lemma l_second_death : (ℓ + 5) * (ℓ - 1) ≤ (ℓ + 3) * (ℓ + 1) := calc

  _ ≤ ℓ ^ 2 + 4 * ℓ := by

    have rw1 : (ℓ + 5) * (ℓ - 1) = (ℓ + 5) * ℓ - (ℓ + 5) := by
      exact Nat.mul_sub_one (ℓ + 5) ℓ

    have rw2 : (ℓ + 5) * ℓ - (ℓ + 5) = ℓ * ℓ + 5 * ℓ - ℓ - 5 := by
      rw[add_mul]; rfl

    have rw3 : ℓ * ℓ + 5 * ℓ - ℓ - 5 = ℓ * ℓ + (5* ℓ - ℓ) - 5 := by
      lia

    have rw4 : ℓ * ℓ + (5* ℓ - ℓ) - 5 = ℓ ^ 2 + 4 * ℓ - 5 := by
      rw[pow_two]; congr; omega

    rw [rw1,rw2,rw3,rw4]
    omega

  _ ≤ (ℓ + 3) * (ℓ + 1)  := by
      ring_nf; omega


end omission_inequalities


-- lemma m_death_ineq (m : ℕ) : α ℓ * (ℓ - 1) ≤ (ℓ ^ 2 - 1) / 2 + ((ℓ + 3) / 2 + m) * (ℓ + 1) := by

--   have lg : ℓ ≥ 13 := Fact.out
--   trans ((ℓ + 3)/2 + 1) * (ℓ - 1)
--   gcongr
--   lia


--   apply add_le_add_right alpha_bound
--   trans ((ℓ + 3) / 2) * (ℓ + 1); calc

--     ((ℓ + 3) / 2 + 1) * (ℓ - 1) = ((ℓ + 5) / 2) * (ℓ - 1) := by
--       congr; exact Eq.symm (Nat.div_eq_sub_div zero_lt_two (Nat.le_add_left 2 (ℓ + 3)))

--     _ ≤ _ := l_death_ineq


--   trans 0 + ((ℓ + 3)/2 + 0) * (ℓ + 1)
--   simp only [add_zero, zero_add, le_refl]
--   apply add_le_add; exact Nat.zero_le ((ℓ ^ 2 - 1) / 2)
--   apply Nat.mul_le_mul_right
--   apply Nat.add_le_add_left (Nat.zero_le m)


lemma Filt_Theta_lej [Fact (fl ℓ |𝓤 = 0)] {m} (mle : m ≤ j ℓ) :
    𝔀 (Θ^[(ℓ + 3)/2 + m] (fl ℓ)) = (ℓ^2 - 1)/2 + ((ℓ + 3)/2 + m) * (ℓ + 1) - α ℓ * (ℓ - 1) := by

  induction m with

  | zero => rw [add_zero, Nat.cast_zero, add_zero, exists_Filt_Theta_l_add_three_div_two.choose_spec.2]; rfl

  | succ m ih =>
    specialize ih (Nat.le_of_succ_le mle)
    have mlt : m < j ℓ := trans (lt_add_one m) mle

    have nmdiv : ¬ ↑ℓ ∣ 𝔀 (Θ^[(ℓ + 3) / 2 + m] (fl ℓ)) := by
      apply Nat.find_min at mlt; exact mlt

    have lrw : (ℓ + 3) / 2 + (m + 1) = (ℓ + 3) / 2 + m + 1 := (add_assoc ..).symm

    rw [(Filt_Theta_iff' _ lrw).2 nmdiv, ih]
    lia




lemma ldiv_j_add_a [Fact (fl ℓ |𝓤 = 0)] : ↑ℓ ∣ (j ℓ + 1) + α ℓ := by
  sorry

  -- have Oddel : Odd (ℓ : ℤ) := by grind [Oddl ℓ]

  -- obtain ⟨c, hc⟩ := Oddel

  -- -- have divl : 2 ∣ ℓ + 1 := by
  -- --   use c + 1; rw[hc]; ring


  -- suffices (j ℓ + 1) + α ℓ ≡ 0 [ZMOD ℓ] by
  --   rwa [← Int.modEq_zero_iff_dvd]


  -- calc

  --   _ ≡ 0 + (j ℓ + 1) * (ℓ + 1) - α ℓ * (ℓ - 1) [ZMOD ℓ] := by


  --     rw[zero_add, sub_eq_add_neg]; gcongr
  --     trans (j ℓ + 1) * (0 + 1); rw[zero_add, mul_one]
  --     gcongr; exact Int.modEq_self.symm
  --     trans 0 + -α ℓ * -1
  --     simp only [Int.reduceNeg, mul_neg, mul_one, neg_neg, zero_add, Int.ModEq.refl]
  --     simp only [mul_sub, Int.reduceNeg, mul_neg, mul_one, neg_neg, zero_add, neg_sub]
  --     nth_rw 1 [← add_zero (α ℓ), sub_eq_add_neg]
  --     gcongr; trans - α ℓ * 0
  --     rw[mul_zero]; trans -α ℓ * ℓ
  --     gcongr; exact Int.modEq_self.symm; simp

  --   _ ≡ (ℓ^2 - 1)/2 + ((ℓ + 1)/2 + (j ℓ + 1)) * (ℓ + 1) - α ℓ * (ℓ - 1) [ZMOD ℓ] := by


  --     nth_rw 3 [add_mul]; rw[← add_assoc]; gcongr; symm
  --     trans (l ^ 2 - 1) / 2 + (l + 1) * (l + 1) / 2
  --     congr; refine Eq.symm (Int.mul_ediv_assoc' (l + 1) divl)

  --     trans ((l ^ 2 - 1) + (l + 1) * (l + 1)) / 2
  --     apply Int.modEq_of_Eq
  --     refine Eq.symm (Int.add_ediv_of_dvd_right ?_)
  --     exact Dvd.dvd.mul_right divl (l + 1)


  --     ring_nf; trans l * 2 / 2 + l ^ 2 * 2 / 2
  --     apply Int.modEq_of_Eq; apply Int.add_ediv_of_dvd_right
  --     exact Int.dvd_mul_left ..
  --     trans l + l^2; congr <;>
  --     refine Int.mul_ediv_cancel _ two_ne_zero

  --     trans 0 + 0 ^ 2; gcongr <;> exact Int.modEq_self
  --     rfl

  --   _ = 𝔀 (Θ^[(ℓ + 3)/2 + j ℓ] (fl ℓ)) := by
  --   {
  --     symm

  --     have : 𝔀 (Θ^[(ℓ + 3)/2 + j] (fl ℓ)) =
  --         (ℓ ^ 2 - 1) / 2 + ((ℓ + 3) / 2 + j) * (ℓ + 1) - (α + 1) * (ℓ - 1) :=
  --       Filt_Theta_lej (le_refl j)

  --     rw[this]; unfold l k a;
  --     trans ↑(((ℓ ^ 2 - 1) / 2 : ℕ) + (((ℓ + 3) / 2 + j) : ℕ) * ((ℓ + 1) : ℕ)) - ↑((α + 1) * (ℓ - 1))
  --     refine Int.ofNat_sub ?_; exact m_death_ineq j

  --     trans ↑((ℓ ^ 2 - 1) / 2 : ℕ) + ↑(((ℓ + 3) / 2 + j) : ℕ) * ↑((ℓ + 1) : ℕ) - ↑(α + 1) * ↑(ℓ - 1)
  --     rfl

  --     trans  ↑((ℓ ^ 2 - 1) / 2 : ℕ) + (↑(((ℓ + 3) / 2 + j) : ℕ) * ↑((ℓ + 1) : ℕ) - ↑(α + 1) * ↑(ℓ - 1))
  --     apply Int.add_sub_assoc

  --     trans (↑((ℓ ^ 2 - 1): ℕ)) / 2 + (↑(((ℓ + 3) / 2 + j) : ℕ) * ↑((ℓ + 1) : ℕ) - ↑(α + 1) * ↑(ℓ - 1))
  --     rfl

  --     trans (↑ℓ ^ 2 - 1) / 2 + (↑(((ℓ + 3) / 2 + j) : ℕ) * ↑((ℓ + 1) : ℕ) - ↑(α + 1) * ↑(ℓ - 1))
  --     have : ↑((ℓ ^ 2 - 1): ℕ) = ((ℓ ^ 2) : ℕ) - (1 : ℤ) := by
  --       refine Int.natCast_pred_of_pos ?_; exact Nat.pos_of_neZero (ℓ ^ 2)
  --     rw[this]; rfl

  --     have rw1 : ↑(((ℓ + 3) / 2 + j) : ℕ) = ((↑ℓ + 3) / 2 + ↑j : ℤ) := rfl
  --     have rw2 : ↑((ℓ + 1) : ℕ) = (↑ℓ + 1 : ℤ) := rfl
  --     have rw3 : ↑((α + 1) : ℕ) = (↑α + 1 : ℤ) := rfl
  --     have rw4 : ↑(ℓ - 1) = (↑ℓ - 1 : ℤ) := by
  --       apply Int.natCast_pred_of_pos (Nat.pos_of_neZero ℓ)
  --     have rw5 : ((↑ℓ + 1) / 2 + (↑j + 1 : ℤ)) = (↑ℓ + 3) / 2 + ↑j := by
  --       trans (↑ℓ + 1) / 2 + 2/2 + ↑j
  --       ring; congr; trans (↑ℓ + 1 + 2) / 2
  --       refine Eq.symm (Int.add_ediv_of_dvd_left ?_)
  --       exact divl; congr 1

  --     rw[rw1,rw2,rw3,rw4,rw5, Int.add_sub_assoc]
  --   }


  --   _ ≡ 0 [ZMOD ℓ] := by
  --     rw[Int.modEq_zero_iff_dvd]

  --     exact Nat.find_spec



lemma alpha_equal [Fact (fl ℓ |𝓤 = 0)] : α ℓ = (ℓ + 5) / 2 := by

  have lel : α ℓ + (j ℓ + 1) ≥ ℓ := by
    apply Int.le_of_dvd
    apply Int.add_pos_of_pos_of_nonneg alpha_pos <| Nat.cast_nonneg _
    rw [add_comm]; exact ldiv_j_add_a


  have lg : ℓ ≥ 13 := Fact.out

  apply le_antisymm alpha_bound

  contrapose! lel;

  calc
    α ℓ + (j ℓ + 1) < (ℓ + 5) / 2 + ((ℓ - 7) / 2 + 1) :=
      add_lt_add_of_lt_of_le lel <| by
        have := j_bound ℓ
        gcongr
        zify at this
        rw [Int.natCast_sub <| by omega] at this
        exact this
    _ = ℓ := by
      obtain ⟨k, hk⟩ := show Odd (ℓ : ℤ) by grind [Oddl ℓ]
      rw [hk]
      lia


end Final.Hidden

open Final.Hidden

-- (3.8)
theorem Filt_Theta_l_add_three_div_two (flu : fl ℓ |𝓤 = 0) :
    𝔀 (Θ^[(ℓ + 3)/2] (fl ℓ)) = (ℓ^2 - 1)/2 + 4 := by

  have flufact : Fact (fl ℓ |𝓤 = 0) := ⟨flu⟩

  rw[exists_Filt_Theta_l_add_three_div_two.choose_spec.2, ← alpha, alpha_equal]
  rw [add_sub_assoc]
  congr

  obtain ⟨k, hk⟩ := show Odd (ℓ : ℤ) by grind [Oddl ℓ]

  rw [hk]
  ring_nf

  trans k * ((2 + k) * 2 / 2) * 2 - k * ((3 + k) * 2 / 2) * 2 + (2 + k) * 2 / 2 * 2
  congr <;> ring
  simp; ring
