import PartitionsLeanblueprint.PrimaryLemmas



/- The goal of this file is to prove from Lemma 3.3 to the end of the paper -/

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 5)]

lemma Filt_Theta_l_sub_two (flu : f ℓ |𝓤 = 0) : ℓ ∣ 𝔀 (Θ^[ℓ - 2] (f ℓ)) := by

  have filt_fl : 𝔀 (f ℓ |𝓤) = 0 := flu ▸ Filt_zero
  have sub_one : 𝔀 (Θ^[ℓ - 1] (f ℓ)) = (ℓ^2 - 1) / 2 := Lemma_stitch filt_fl
  by_contra! ndvd
  have lg5 : ℓ ≥ 5 := Fact.out
  have lrw : ℓ - 1 = (ℓ - 2) + 1 := by
    refine (Nat.sub_eq_iff_eq_add ?_).mp rfl; refine (Nat.le_sub_one_iff_lt ?_).mpr ?_ <;> linarith
  have trw: Θ^[ℓ - 1] (f ℓ) == Θ^[(ℓ - 2) + 1] (f ℓ) := Theta_pow_cast lrw
  have : 𝔀 (f ℓ) = 𝔀 (Θ^[ℓ - 2] (f ℓ)) + ℓ + 1 := by
    trans 𝔀 (Θ^[ℓ - 1] (f ℓ)); rw [Filt_fl, (Lemma_stitch filt_fl)]
    rw [Filt_eq_of_Mod_eq trw, Filt_eq_of_Mod_eq Theta_pow_succ, Filt_Theta_iff.2 ndvd]
  have := @le_Filt_Theta_fl ℓ _ _ (ℓ - 2)
  linarith


lemma Filt_Theta_lel_add_one_div_two {m} (flu : f ℓ |𝓤 = 0) (mle : m ≤ (ℓ + 1)/2) :
    𝔀 (Θ^[m] (f ℓ)) = (ℓ^2 - 1)/2 + m * (ℓ + 1) := by
  induction m with

  | zero => simp only [Theta_pow_zero', Filt_cast, Filt_fl, zero_mul, add_zero]

  | succ m ih =>
    specialize ih (by linarith)
    rw [Theta_pow_succ', Filt_cast, Nat.succ_mul, ← add_assoc, ← ih, ← add_assoc]
    apply Filt_Theta_iff.2; rw[ih]; intro h
    sorry


    --refine (Nat.not_dvd_iff_lt_mul_succ ((ℓ ^ 2 - 1) / 2 + m * (ℓ + 1)) (Nat.pos_of_neZero ℓ)).mpr ?_

instance Oddl : Odd ℓ :=
  let t : ℓ ≥ 5 := Fact.out
  Nat.Prime.odd_of_ne_two Fact.out (by linarith)


lemma Filt_Theta_l_add_one_div_two (flu : f ℓ |𝓤 = 0) : ℓ ∣ 𝔀 (Θ^[(ℓ + 1)/2] (f ℓ)) := by
  have Oddl : Odd ℓ := Oddl

  use ℓ + 1; calc
  _ = (ℓ^2 - 1)/2 + (ℓ + 1)/2 * (ℓ + 1) := Filt_Theta_lel_add_one_div_two flu (le_refl _)
  _ = ((ℓ^2 - 1)) / 2 + (ℓ^2 + 2*ℓ + 1) / 2 := by
    congr; trans ((ℓ + 1) * (ℓ + 1)) / 2
    refine Nat.div_mul_right_comm ?_ (ℓ + 1)
    obtain ⟨k,rfl⟩ := Oddl
    exact ⟨k + 1, by group⟩
    congr; group

  _ = ((ℓ^2 - 1) + (ℓ^2 + 2*ℓ + 1)) / 2 := by
    refine Eq.symm (Nat.add_div_of_dvd_right ?_)
    have Oddl2 : Odd (ℓ^2) := Odd.pow Oddl
    obtain ⟨k,hk⟩ := Oddl2
    exact ⟨k, by rw[hk, Nat.add_sub_cancel_right]⟩

  _ = 2 * (ℓ * (ℓ + 1)) / 2 := by
    congr; group; rw[mul_two (ℓ^2), add_comm, add_assoc, ← add_assoc, ← add_assoc]
    have : ℓ ^ 2 - 1 + 1 = ℓ^2 := Nat.sub_add_cancel NeZero.one_le
    rw[this]; ring
  _ = _ :=  Nat.mul_div_right (ℓ * (ℓ + 1)) zero_lt_two
