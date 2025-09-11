import PartitionsLeanBlueprint.PreliminaryResults

/- This file defines Δ and fℓ. It states lemmas 2.1 and 3.2,
and proves lemma 3.3 assuming them. This is currently where the main
body of the paper lives. -/

noncomputable section

open Modulo2 Finset.Nat

variable {ℓ n : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

def δ (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24
-- δℓ ?

-- The series expansion of ∏ n, (1-q^n)
def Etaish : (n : ℕ) → ZMod ℓ
  | 0 => 0
  | n + 1 =>
    if h : (∃ m : ℤ, n + 1 = m * (3*m - 1) / 2)
      then
        let m := Classical.choose h
        (-1) ^ m
      else 0


def Delta : ModularFormMod ℓ 12 where

  sequence n := match n with
    | 0 => 0
    | n + 1 => (ZModpow Etaish 24) n

  modular := sorry

notation "Δ" => Delta



def f (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)] : ModularFormMod ℓ (12 * δ ℓ) := Δ ** δ ℓ
-- or fℓ : ModularFormMod ℓ (((ℓ^2 - 1)/2) : ℕ) := Mcongr (Δ ** δ ℓ) (by sorry)


instance : NeZero (f ℓ) where
  out := sorry


lemma not_dvd_filt : ¬ ℓ ∣ (ℓ ^ 2 - 1) / 2 := by
    intro h
    by_cases l2 : ℓ = 2
    simp only [l2, Nat.reducePow, Nat.add_one_sub_one, Nat.reduceDiv, Nat.dvd_one,
      OfNat.ofNat_ne_one] at h

    have : Odd ℓ := Nat.Prime.odd_of_ne_two Fact.out l2;
    have h_div_full : ℓ ∣ (ℓ ^ 2 - 1) / 2 * 2 := by
      exact Nat.dvd_mul_right_of_dvd h 2

    have : ℓ ∣ (ℓ ^ 2 - 1) := by
      trans (ℓ ^ 2 - 1) / 2 * 2
      exact Nat.dvd_mul_right_of_dvd h 2
      apply dvd_of_eq

      apply Nat.div_two_mul_two_of_even
      apply Nat.Odd.sub_odd (Odd.pow this)
      exact Nat.odd_iff.mpr rfl

    have don : ℓ ^ 2 - 1 = (ℓ + 1) * (ℓ - 1) := by
        trans ℓ * ℓ - 1
        rw[pow_two]
        exact mul_self_tsub_one ℓ

    rw[don] at this
    have bla : ℓ ∣ (ℓ + 1) ∨ ℓ ∣ (ℓ - 1) := (Nat.Prime.dvd_mul Fact.out).mp this
    have lg2 : ℓ ≥ 2 := Nat.Prime.two_le Fact.out
    rcases bla with h|h
    contrapose! h
    refine (Nat.not_dvd_iff_lt_mul_succ (ℓ + 1) ?_).mpr ?_
    exact Nat.pos_of_neZero ℓ
    use 1; constructor <;> linarith
    contrapose! h
    refine Nat.not_dvd_of_pos_of_lt ?_ ?_
    exact Nat.zero_lt_sub_of_lt lg2
    exact Nat.sub_one_lt_of_lt lg2


@[simp] lemma fl_zero [Fact (ℓ ≥ 5)]: f ℓ 0 = 0 := by
  simp[f, δ, pow_apply, antidiagonalTuple_zero_right]; constructor; rfl
  have lg5 : ℓ ≥ 5 := Fact.out
  have fivesq : 5 * 5 = 25 := rfl
  have lsq : ℓ ^ 2 ≥ 25 := by
    rw[pow_two, ← fivesq]; exact mul_le_mul lg5 lg5 (Nat.zero_le 5) (Nat.zero_le ℓ)
  exact Nat.le_sub_one_of_lt lsq



lemma Filt_fl : 𝔀 (f ℓ) = (ℓ^2 - 1)/2  := sorry



--Lemma 2.1

-- (1)
theorem Filt_Theta_bound (a : ModularFormMod ℓ k) : 𝔀 (Θ a) ≤ 𝔀 a + ℓ + 1 := sorry

-- (2)
theorem Filt_Theta_iff {a : ModularFormMod ℓ k} :
  𝔀 (Θ a) = 𝔀 a + ℓ + 1 ↔ ¬ ℓ ∣ 𝔀 a := sorry



-- Lemma 3.2
theorem le_Filt_Theta_fl : ∀ m, 𝔀 (f ℓ) ≤ 𝔀 (Θ^[m] (f ℓ)) := sorry



-- Lemma 3.3

-- (1) stated here as an implication, instead of an or statement
theorem Filt_Theta_pow_l_sub_one : ¬ ℓ ∣ 𝔀 (Θ^[ℓ - 1] (f ℓ)) → 𝔀 (Θ^[ℓ - 1] (f ℓ)) = (ℓ^2 - 1)/2 := by
  intro h

  have Filt_eq : 𝔀 (Θ (f ℓ)) = (ℓ^2 - 1) / 2 + ℓ + 1 := by
    rw[← Filt_fl]; apply Filt_Theta_iff.2; rw[Filt_fl]
    exact not_dvd_filt

  rw [Filt_eq_of_Mod_eq Theta_pow_ℓ_eq_Theta.symm, Filt_eq_of_Mod_eq Theta_pow_pred] at Filt_eq

  have :  𝔀 (Θ (Theta_pow (ℓ - 1) (f ℓ))) - (ℓ + 1) = 𝔀 (Theta_pow (ℓ - 1) (f ℓ)) := by
    refine Eq.symm (Nat.eq_sub_of_add_eq ?_); rw[← add_assoc]; symm
    apply Filt_Theta_iff.2 h

  rw [← this]
  exact Nat.sub_eq_of_eq_add Filt_eq


-- (2) We now need that ℓ ≥ 5, here to guarantee that δ ℓ ≥ 1
theorem Filt_U_pos [Fact (ℓ ≥ 5)] : ℓ ∣ 𝔀 (Θ^[ℓ - 1] (f ℓ)) → 𝔀 (f ℓ |𝓤) > 0 := by

  intro h; by_contra! filto; rw[nonpos_iff_eq_zero] at filto
  have folly : 𝔀 (f ℓ |𝓤 ** ℓ) = 0 := by rw[Filtration_Log, filto, mul_zero]
  obtain ⟨c,hc⟩ := const_of_Filt_zero filto
  have fconn : (f ℓ |𝓤) ** ℓ == (const c) ** ℓ := by
    intro n; rw[pow_apply, pow_apply]; congr
    ext x; congr; ext y; rw[hc (x y)]
  have (c) : ∃ d : ZMod ℓ, (const c) ** ℓ == const d := by
    use c ^ ℓ; exact const_pow c ℓ

  obtain ⟨d,hd⟩ := this c

  have Thecon : ((f ℓ) -l Θ^[ℓ - 1] (f ℓ)) (by simp) == const d := by
    calc
      _ == (f ℓ |𝓤)**ℓ := U_pow_l_eq_self_sub_Theta_pow_l_sub_one.symm
      _ == const c**ℓ := fconn
      _ == const d := hd

  have zepo : ∀ n, ((f ℓ) -l Θ^[ℓ - 1] (f ℓ))
      (by simp only [CharP.cast_eq_zero, zero_mul, add_zero]) n = 0 := by
    intro n; match n with

    | 0 =>
      simp only [sub_congr_left_apply, Theta_Pow_apply, Nat.cast_zero, ZMod.pow_card_sub_one,
          ne_eq, not_true_eq_false, reduceIte, zero_mul, sub_zero, fl_zero]

    | n + 1 => rw[Thecon (n + 1)]; rfl

  have feq : f ℓ == Θ^[ℓ - 1] (f ℓ) := by
    intro n; specialize zepo n
    simp only [sub_congr_left_apply, sub_eq_zero] at zepo
    exact zepo

  apply Filt_eq_of_Mod_eq at feq
  have wrong : ℓ ∣ 𝔀 (f ℓ) := by rw[feq]; exact h
  let right := @not_dvd_filt ℓ _ _
  rw[Filt_fl] at wrong
  exact right wrong


theorem Lemma_stitch [Fact (ℓ ≥ 5)] : 𝔀 (f ℓ |𝓤) = 0 → 𝔀 (Θ^[ℓ - 1] (f ℓ)) = (ℓ^2 - 1)/2 := by
  intro h
  have h' : ¬ 𝔀 (f ℓ |𝓤) > 0 := Eq.not_gt h
  have : ¬ ℓ ∣ 𝔀 (Θ^[ℓ - 1] (f ℓ)) := by contrapose! h'; exact Filt_U_pos h'
  exact Filt_Theta_pow_l_sub_one this
