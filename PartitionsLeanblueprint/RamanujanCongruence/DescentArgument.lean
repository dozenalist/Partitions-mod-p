import PartitionsLeanblueprint.RamanujanCongruence.PrimaryLemmas

/- This file proves from after Lemma 3.3 (line 3.5) to line 3.8
It proves that `𝔀 (Θ^[(ℓ + 3)/2] (f ℓ)) = (ℓ^2 - 1)/2 + 4`.
From here on, information about a basis will be needed
This file is sorry-free
 -/

open ModularFormMod hiding mul_one one_mul zero_mul mul_zero

variable {ℓ : ℕ} [hℓ : isLargePrime ℓ]


private lemma Oddl (ℓ) [isLargePrime ℓ] : Odd ℓ :=
  let t : ℓ ≥ 5 := Fact.out
  Nat.Prime.odd_of_ne_two Fact.out (by linarith)

private lemma ZMod.two_ne_zero : (2 : ZMod ℓ) ≠ 0 := fun h => by
  rw [← Nat.cast_two, ZMod.natCast_eq_zero_iff] at h
  apply Nat.le_of_dvd two_pos at h
  grind [hℓ.AtLeastFive]



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
  obtain ⟨a, apos, h⟩ := this
  use a, apos, by
    rw [leq, h, Filt_Theta_lel_add_one_div_two (le_refl _)]
    rw [add_assoc, add_sub_assoc, add_sub_assoc, add_sub_assoc, add_sub_assoc, add_right_inj]
    norm_cast
    rw [leq, add_mul]
    grind





-- Start of page 494

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



private noncomputable def alpha (ℓ) [isLargePrime ℓ] : ℤ :=
  Exists.choose <| exists_Filt_Theta_l_add_three_div_two (ℓ := ℓ)

local notation "α" => alpha


private lemma alpha_bound : α ℓ ≤ (ℓ + 5) / 2 :=
  alpha_bound_ex exists_Filt_Theta_l_add_three_div_two.choose_spec.2

private lemma alpha_pos : α ℓ > 0 := exists_Filt_Theta_l_add_three_div_two.choose_spec.1



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


private noncomputable def j (ℓ) [isLargerPrime ℓ] [Fact (fl ℓ |𝓤 = 0)] :=
  Nat.find ( ⟨(ℓ - 7)/2, l_div_Filt_Theta_add Fact.out⟩ : ∃ j, ↑ℓ ∣ 𝔀 (Θ^[(ℓ+3)/2 + j] (fl ℓ)) )

private lemma j_bound (ℓ) [isLargerPrime ℓ] [Fact (fl ℓ |𝓤 = 0)] : j ℓ ≤ (ℓ - 7)/2 := by
  rw [j, Nat.find_le_iff]
  use (ℓ - 7)/2, le_refl _
  exact l_div_Filt_Theta_add Fact.out

private lemma j_spec (ℓ) [isLargerPrime ℓ] [Fact (fl ℓ |𝓤 = 0)] : ↑ℓ ∣ 𝔀 (Θ^[(ℓ+3)/2 + j ℓ] (fl ℓ)) :=
  Nat.find_spec (⟨(ℓ - 7)/2, l_div_Filt_Theta_add Fact.out⟩ : ∃ j, ↑ℓ ∣ 𝔀 (Θ^[(ℓ+3)/2 + j] (fl ℓ)))



private lemma Filt_Theta_lej [Fact (fl ℓ |𝓤 = 0)] {m} (mle : m ≤ j ℓ) :
    𝔀 (Θ^[(ℓ + 3)/2 + m] (fl ℓ)) = (ℓ^2 - 1)/2 + ((ℓ + 3)/2 + m) * (ℓ + 1) - α ℓ * (ℓ - 1) := by

  induction m with

  | zero => rw [add_zero, Nat.cast_zero, add_zero, exists_Filt_Theta_l_add_three_div_two.choose_spec.2]; rfl

  | succ m ih =>
    have mlt : m < j ℓ := trans (lt_add_one m) mle
    have nmdiv : ¬ ↑ℓ ∣ 𝔀 (Θ^[(ℓ + 3) / 2 + m] (fl ℓ)) := Nat.find_min _ mlt
    have lrw : (ℓ + 3) / 2 + (m + 1) = (ℓ + 3) / 2 + m + 1 := add_assoc ..|>.symm

    rw [(Filt_Theta_iff' _ lrw).2 nmdiv, ih (Nat.le_of_succ_le mle)]
    lia




private lemma ldiv_j_add_a [Fact (fl ℓ |𝓤 = 0)] : ↑ℓ ∣ (j ℓ + 1) + α ℓ := by
  rw [← Int.modEq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
  simp
  trans ↑ (𝔀 (Θ^[(ℓ + 3)/2 + j ℓ] (fl ℓ)))
  {
    simp [Filt_Theta_lej <| le_refl _, sub_eq_add_neg, add_comm, add_assoc]

    rw [← Int.cast_add, ← Int.add_ediv_of_dvd_left <| by grind [Oddl ℓ]]
    trans ((ℓ : ZMod ℓ) + 3 + (-1 + (ℓ : ZMod ℓ) ^ 2)) / 2
    simp
    norm_num
    refine Eq.symm (EuclideanDomain.div_self ZMod.two_ne_zero)
    norm_cast
    refine Eq.symm (eq_div_of_mul_eq ZMod.two_ne_zero ?_)
    rw [← Int.cast_two (R := ZMod ℓ), ← Int.cast_mul]
    congr
    rw [mul_comm, ← Int.mul_ediv_assoc, mul_comm, Int.mul_ediv_cancel _ two_ne_zero]
    obtain ⟨k, rfl⟩ := Oddl ℓ
    grind
  }
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact j_spec ℓ



private lemma alpha_equal [Fact (fl ℓ |𝓤 = 0)] : α ℓ = (ℓ + 5) / 2 := by

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




-- (3.8)
theorem Filt_Theta_l_add_three_div_two (flu : fl ℓ |𝓤 = 0) :
    𝔀 (Θ^[(ℓ + 3)/2] (fl ℓ)) = (ℓ^2 - 1)/2 + 4 := by

  have flufact : Fact (fl ℓ |𝓤 = 0) := ⟨flu⟩

  rw [exists_Filt_Theta_l_add_three_div_two.choose_spec.2, ← alpha, alpha_equal, add_sub_assoc]
  congr

  obtain ⟨k, hk⟩ := show Odd (ℓ : ℤ) by grind [Oddl ℓ]

  rw [hk]
  ring_nf

  trans k * ((2 + k) * 2 / 2) * 2 - k * ((3 + k) * 2 / 2) * 2 + (2 + k) * 2 / 2 * 2
  congr <;> ring
  simp; ring
