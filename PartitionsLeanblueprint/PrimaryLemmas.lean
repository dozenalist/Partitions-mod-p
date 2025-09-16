import PartitionsLeanBlueprint.PreliminaryResults

/- This file defines Δ and fℓ. It states lemmas 2.1 and 3.2,
and proves lemma 3.3 assuming them. This is currently where the main
body of the paper lives. -/

noncomputable section

open Modulo2 Finset.Nat Finset

variable {ℓ n : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

def δ (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24
-- δℓ ?

-- The series expansion of ∏ n, (1-q^n)
def Etaish (n : ℕ) : ZMod ℓ :=

    if h : (∃ m : ℤ, n = m * (3*m - 1) / 2)
      then
        let m := Classical.choose h
        (-1) ^ m
      else 0


def Delta : ModularFormMod ℓ 12 where

  sequence
    | 0 => 0
    | n + 1 => (ZModpow Etaish 24) n

  modular := sorry


notation "Δ" => Delta


def f (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)] : ModularFormMod ℓ (12 * δ ℓ) := Δ ** δ ℓ
-- or fℓ : ModularFormMod ℓ (((ℓ^2 - 1)/2) : ℕ) := Mcongr (Δ ** δ ℓ) (by sorry)

@[simp] lemma Del_one : Δ 1 = (1 : ZMod ℓ) := by
  trans (ZModpow Etaish 24) 0; rfl
  rw[ZModpow_apply, antidiagonalTuple_zero_right]
  simp only [sum_singleton, Pi.zero_apply, prod_const, card_univ, Fintype.card_fin]
  suffices Etaish 0 = (1 : ZMod ℓ) by rw[this, one_pow]
  rw[Etaish]
  have h : ∃ m : ℤ, 0 = m * (3 * m - 1) / 2 := ⟨0, by ring⟩
  trans let m := Classical.choose h; (-1) ^ m
  simp_all only [CharP.cast_eq_zero, ↓reduceDIte]
  simp only


  have m0 (m : ℤ) : 0 = m * (3 * m - 1) / 2 → m = 0 := by
    intro hm
    rcases lt_trichotomy m 0 with ml0 | m0 | mg0
    contrapose! hm; apply ne_of_lt
    suffices m * (3 * m - 1) ≥ 2 by omega
    have ml : m ≤ -1 := by omega
    have mml : (3 * m - 1) < -2 := by omega
    have : (2 : ℤ) = -1 * -2 := rfl
    rw[this]
    suffices (3 * m - 1) ≤ -2 by
      refine Int.mul_le_mul_of_le_of_le_of_nonpos_of_nonpos ml this ?_ (le_of_lt ml0)
      exact Int.neg_ofNat_le_ofNat 2 0
    omega
    exact m0
    contrapose! hm; apply ne_of_lt
    suffices m * (3 * m - 1) ≥ 2 by omega
    have ml : m ≥ 1 := by omega
    have : (2 : ℤ) = 1 * 2 := rfl
    rw[this]; refine mul_le_mul ml ?_ zero_le_two (le_of_lt ml)
    omega


  trans (-1) ^ (0 : ℤ)
  congr; exact m0 (Classical.choose h) (Classical.choose_spec h)
  rfl


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
    exact Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_sub_of_lt lg2) (Nat.sub_one_lt_of_lt lg2)


lemma fl_lt_delta {n : ℕ} (nlt : n < (ℓ^2 - 1)/24) : f ℓ n = 0 :=
  leading_pow_zeros rfl nlt

@[simp] lemma fl_zero [Fact (ℓ ≥ 5)]: f ℓ 0 = 0 :=

  let lg5 : ℓ ≥ 5 := Fact.out
  let fivesq : 5 * 5 = 25 := rfl
  let lsq : ℓ ^ 2 ≥ 25 :=
    fivesq ▸ pow_two ℓ ▸ mul_le_mul lg5 lg5 (Nat.zero_le 5) (Nat.zero_le ℓ)

  fl_lt_delta ((Nat.one_le_div_iff (Nat.zero_lt_succ 23)).mpr (Nat.le_sub_one_of_lt lsq))


@[simp] lemma fl_delta : f ℓ (δ ℓ) = 1 := by
  simp only [δ, f, pow_apply]
  calc
    _ = ∑ x ∈ antidiagonalTuple ((ℓ ^ 2 - 1) / 24) ((ℓ ^ 2 - 1) / 24) \ {fun _ ↦ 1}, ∏ y, Δ (x y) +
    ∑ x ∈ {fun _ ↦ 1}, ∏ y, Δ (x y) := by
      apply Eq.symm (sum_sdiff _); intro x hx
      apply mem_antidiagonalTuple.2
      rw [mem_singleton] at hx
      rw[hx]; dsimp only
      rw[sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

    _ = (0 : ZMod ℓ) + 1 := by
      congr
      {
        apply sum_eq_zero; intro x hx
        apply prod_eq_zero_iff.2
        simp only [mem_sdiff, mem_singleton] at hx
        obtain ⟨hx, xn1⟩ := hx
        rw[mem_antidiagonalTuple] at hx
        apply le_of_eq at hx; contrapose! hx

        calc
          (ℓ ^ 2 - 1) / 24 = ∑ i : Fin ((ℓ ^ 2 - 1) / 24), 1 := by
            rw[sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
          _ < ∑ i, x i := by
            have xn0 : ∀ i, x i ≥ 1 := by
              simp_rw[Nat.one_le_iff_ne_zero]
              intro i; contrapose! hx
              use i, mem_univ i; rw[hx]; rfl
            have : ∃ j, x j ≠ 1 := by
              contrapose! xn1; ext j; exact xn1 j
            obtain ⟨j, jn1⟩ := this
            have jg2 : x j ≥ 2 := by
              apply (Nat.two_le_iff (x j)).2
              exact ⟨Nat.one_le_iff_ne_zero.1 (xn0 j), jn1⟩
            calc
            _ = ∑ i ∈ univ \ {j}, 1 + 1 :=
              sum_eq_sum_diff_singleton_add (mem_univ j) _

            _ < ∑ i ∈ univ \ {j}, x i + x j := by
              apply add_lt_add_of_le_of_lt
              exact sum_le_sum (λ i hi ↦ xn0 i)
              exact jg2
            _ = _ := (sum_eq_sum_diff_singleton_add (mem_univ j) _).symm
      }
      simp only [sum_singleton, prod_const, card_univ, Fintype.card_fin]
      rw[Del_one]; exact one_pow _

    0 + 1 = 1 := zero_add 1


instance fl_ne_zero : NeZero (f ℓ) where
  out := λ f0 ↦
    let h := @fl_delta ℓ _ _
    let g := DFunLike.ext_iff.1 f0 (δ ℓ)
    one_ne_zero (h.symm.trans g)


lemma delta_integer [Fact (ℓ ≥ 5)]: 24 ∣ ℓ ^ 2 - 1 := by

  have lg5 : ℓ ≥ 5 := Fact.out
  have fivesq : 5 * 5 = 25 := rfl
  have lsq : ℓ ^ 2 ≥ 25 :=
    fivesq ▸ pow_two ℓ ▸ mul_le_mul lg5 lg5 (Nat.zero_le 5) (Nat.zero_le ℓ)
  have lprime : Nat.Prime ℓ := Fact.out
  have don : ℓ ^ 2 - 1 = (ℓ + 1) * (ℓ - 1) := by
    trans ℓ * ℓ - 1
    rw[pow_two]
    exact mul_self_tsub_one ℓ


  suffices h : 3 ∣ ℓ ^ 2 - 1 ∧ 8 ∣ ℓ ^ 2 - 1 by
    have : 24 = 3 * 8 := rfl
    rw[this]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h.1 h.2
  constructor

  have h : 3 ∣ ℓ ∨ 3 ∣ (ℓ - 1) ∨ 3 ∣ (ℓ + 1) := by omega
  rcases h with h | h | h
  exfalso
  simp_all only [ge_iff_le, Nat.reduceMul]
  have l3 : ℓ = 3 := by
    obtain ⟨k,rfl⟩ := h
    rcases lprime.2 rfl with h' | h'
    simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
    simp_all only [isUnit_iff_eq_one, mul_one]
  linarith
  rw[don]; exact Nat.dvd_mul_left_of_dvd h (ℓ + 1)
  rw[don]; exact Nat.dvd_mul_right_of_dvd h (ℓ - 1)

  have h : 8 ∣ ℓ ∨ 8 ∣ (ℓ - 1) ∨ 8 ∣ (ℓ - 2) ∨ 8 ∣ (ℓ - 3) ∨
    8 ∣ (ℓ - 4) ∨ 8 ∣ (ℓ - 5) ∨ 8 ∣ (ℓ + 2) ∨ 8 ∣ (ℓ + 1) := by omega

  rcases h with h | h | h | h | h | h | h | h

  {
    exfalso
    have l8 : ℓ = 8 := by
      obtain ⟨k,rfl⟩ := h
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    rw[l8] at lprime
    contrapose! lprime
    decide
  }
  { rw[don]; exact Nat.dvd_mul_left_of_dvd h (ℓ + 1) }
  {
    exfalso
    have d2l : 2 ∣ ℓ := by omega
    have l3 : ℓ = 2 := by
      obtain ⟨k,rfl⟩ := d2l
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    linarith
  }
  {
    suffices ℓ ^ 2 ≡ 1 [MOD 8] from
      (Nat.modEq_iff_dvd' (Nat.one_le_of_lt lsq)).mp (id (Nat.ModEq.symm this))
    trans 3 * 3
    rw[pow_two]; refine Nat.ModEq.symm (Nat.ModEq.mul ?_ ?_) <;>
    rwa[Nat.modEq_iff_dvd']
    exact le_of_add_le_right lg5
    exact le_of_add_le_right lg5
    rfl
  }
  {
    exfalso
    have d2l : 2 ∣ ℓ := by omega
    have l3 : ℓ = 2 := by
      obtain ⟨k,rfl⟩ := d2l
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    linarith
  }
  {
    suffices ℓ ^ 2 ≡ 1 [MOD 8] from
      (Nat.modEq_iff_dvd' (Nat.one_le_of_lt lsq)).mp (id (Nat.ModEq.symm this))
    trans 5 * 5
    rw[pow_two]; refine Nat.ModEq.symm (Nat.ModEq.mul ?_ ?_) <;>
    rwa[Nat.modEq_iff_dvd']
    exact lg5
    exact lg5
    rfl
  }
  {
    exfalso
    have d2l : 2 ∣ ℓ := by omega
    have l3 : ℓ = 2 := by
      obtain ⟨k,rfl⟩ := d2l
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    linarith
  }
  {rw[don]; exact Nat.dvd_mul_right_of_dvd h (ℓ - 1)}


lemma Filt_Del : 𝔀 (Δ : ModularFormMod ℓ 12) = 12 := sorry


lemma Filt_fl [Fact (ℓ ≥ 5)]: 𝔀 (f ℓ) = (ℓ^2 - 1)/2  := by
  rw[f, Filtration_Log]
  suffices h : 𝔀 Δ = 12 by
    rw[h, δ]; refine Eq.symm (Nat.div_eq_of_eq_mul_left zero_lt_two ?_)
    symm; calc
      _ = (ℓ ^ 2 - 1) / 24 * 24 := by ring
      _ = _ := Nat.div_mul_cancel delta_integer
  exact Filt_Del



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
theorem Filt_Theta_pow_l_sub_one [Fact (ℓ ≥ 5)] :
    ¬ ℓ ∣ 𝔀 (Θ^[ℓ - 1] (f ℓ)) → 𝔀 (Θ^[ℓ - 1] (f ℓ)) = (ℓ^2 - 1)/2 := by
  intro h

  have Filt_eq : 𝔀 (Θ (f ℓ)) = (ℓ^2 - 1) / 2 + ℓ + 1 := by
    rw [← Filt_fl]; apply Filt_Theta_iff.2; rw [Filt_fl]; exact not_dvd_filt

  rw [Filt_eq_of_Mod_eq Theta_pow_ℓ_eq_Theta.symm, Filt_eq_of_Mod_eq Theta_pow_pred] at Filt_eq

  have : 𝔀 (Θ (Theta_pow (ℓ - 1) (f ℓ))) - (ℓ + 1) = 𝔀 (Theta_pow (ℓ - 1) (f ℓ)) :=
    Eq.symm (Nat.eq_sub_of_add_eq (add_assoc _ _ 1 ▸ (Filt_Theta_iff.2 h).symm))


  exact this ▸ Nat.sub_eq_of_eq_add Filt_eq -- rw[← this]; exact Nat.sub_eq_of_eq_add Filt_eq also works


-- (2)
theorem Filt_U_pos [Fact (ℓ ≥ 5)] : ℓ ∣ 𝔀 (Θ^[ℓ - 1] (f ℓ)) → 𝔀 (f ℓ |𝓤) > 0 := by

  intro h; by_contra! filto; rw[nonpos_iff_eq_zero] at filto
  have folly : 𝔀 (f ℓ |𝓤 ** ℓ) = 0 := by rw[Filtration_Log, filto, mul_zero]
  obtain ⟨c,hc⟩ := const_of_Filt_zero filto
  have fconn : (f ℓ |𝓤) ** ℓ == (const c) ** ℓ := by
    intro n; rw[pow_apply, pow_apply]; congr
    ext x; congr; ext y; rw[hc (x y)]
  have (c) : ∃ d : ZMod ℓ, (const c) ** ℓ == const d := ⟨c^ℓ, const_pow c ℓ⟩

  obtain ⟨d,hd⟩ := this c

  have Thecon : ((f ℓ) -l Θ^[ℓ - 1] (f ℓ)) (by simp only [CharP.cast_eq_zero, zero_mul,
    add_zero]) == const d := by
    calc
      _ == (f ℓ |𝓤)**ℓ := U_pow_l_eq_self_sub_Theta_pow_l_sub_one.symm
      _ == const c**ℓ := fconn
      _ == const d := hd

  have zepo : ∀ n, ((f ℓ) -l Θ^[ℓ - 1] (f ℓ))
      (by simp only [CharP.cast_eq_zero, zero_mul, add_zero]) n = 0

    | 0 => by rw [sub_congr_left_apply, Theta_Pow_apply, Nat.cast_zero,
        ZMod.pow_card_sub_one, fl_zero, mul_zero, sub_zero]

    | _ + 1 => Thecon _ ▸ rfl

  have feq : f ℓ == Θ^[ℓ - 1] (f ℓ) := by
    intro n; specialize zepo n
    rw [sub_congr_left_apply, sub_eq_zero] at zepo
    exact zepo

  apply Filt_eq_of_Mod_eq at feq
  have wrong : ℓ ∣ 𝔀 (f ℓ) := feq ▸ h
  let right := @not_dvd_filt ℓ _ _
  rw[Filt_fl] at wrong
  exact right wrong


theorem Lemma_stitch [Fact (ℓ ≥ 5)] : 𝔀 (f ℓ |𝓤) = 0 → 𝔀 (Θ^[ℓ - 1] (f ℓ)) = (ℓ^2 - 1)/2 := by
  intro h
  have h' : ¬ 𝔀 (f ℓ |𝓤) > 0 := Eq.not_gt h
  have : ¬ ℓ ∣ 𝔀 (Θ^[ℓ - 1] (f ℓ)) := by contrapose! h'; exact Filt_U_pos h'
  exact Filt_Theta_pow_l_sub_one this
