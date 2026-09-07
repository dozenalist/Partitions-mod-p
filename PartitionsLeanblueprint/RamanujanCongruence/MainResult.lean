import PartitionsLeanblueprint.RamanujanCongruence.DescentArgument
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-
This file proves the main result of the paper, that there does not exists
a ramanujan congruence for large primes ℓ
-/

private lemma Oddl (ℓ) [isLargePrime ℓ] : Odd ℓ :=
  let t : ℓ ≥ 5 := Fact.out
  Nat.Prime.odd_of_ne_two Fact.out (by linarith)


open ModularFormMod in
lemma Theta_l_add_three_div_two_fl_delta_add_one {ℓ : ℕ} [isLargePrime ℓ] :
    (Θ^[(ℓ + 3)/2] (fl ℓ)).coeff (δ ℓ + 1) = (δ ℓ + 1) ^ ((ℓ + 3) / 2) := by
  rw [coeff_Theta_pow, fl_delta_add_one, nsmul_one]; norm_cast


open IntegerModularForm

variable {ℓ : ℕ}


private lemma dim_twelve_delta_add_four : dim (12 * δ ℓ + 4) = δ ℓ + 1 := by
  rw [dim]
  aesop
  norm_cast
  norm_cast
  grind
  grind
  grind

private lemma delta_lt_dim : δ ℓ < dim (12 * δ ℓ + 4) := by
  rw [dim_twelve_delta_add_four]; exact lt_add_one (δ ℓ)


private lemma power_eq_zero : ((12 * ↑(δ ℓ) + 4 - (12 * ↑(δ ℓ) + 4 %% 12)).toNat / 4 - 3 * δ ℓ) = 0 := by
  grind


variable {k} (f : IntegerModularForm k)

@[simp] lemma Icast_fun {k j} (h : k = j) (f : (k : ℤ) → IntegerModularForm k) : Icast h (f k) = f j := by
  subst h
  rfl

@[simp] lemma Icast_pow {m n} (h : m = n) : (f.pow n).Icast (by rw [h]) = f.pow m := by
  subst h; rfl

-- @[simp] lemma Icast_G {m n : Fin (dim k)} (h : m = n) : G n = G m := by
--   rw [h]



@[simp] theorem mod_without_two_four : (4 %% 12) = 4 := rfl


theorem G_delta_add_one [isLargePrime ℓ] : (G ⟨δ ℓ, delta_lt_dim⟩).coeff (δ ℓ + 1) = 241 - ℓ ^ 2 := by
  simp [G]

  set k := 12 * δ ℓ + 4 %% 12 with keq
  have h4 : (12 * δ ℓ + 4 %% 12) = 4 := by simp only [mod_without_two_two_mul_add]; rfl
  have h4' : (12 * ↑(δ ℓ) + 4 - (12 * ↑(δ ℓ) + 4 %% 12)) = 12 * δ ℓ := by
    simp only [mod_without_two_two_mul_add, add_sub_assoc, add_eq_left]; rfl

  conv => rw [coeff_mul]; lhs; rhs; intro p; rw [← coeff_Icast (h := h4), Icast_fun]
  simp [← coeff_mul, G_dim_one]
  rw [← zero_add (δ ℓ + 1), ← add_assoc, coeff_mul_ord_add_one]
  simp [Eis_four_one]

  rw [G_twelve_ord_G_twelve]
  rw [G_twelve, G_twelve']
  simp
  rw [add_comm (δ ℓ)]
  rw [← Icast_pow _ power_eq_zero]
  simp_rw [coeff_mul, pow_zero, coeff_Icast, ← coeff_mul, const_mul, coeff_Icast, one_smul]
  rw [add_comm 1, ← fl, fl_delta_add_one]
  ring

  rw [ord_Eis_four, CharP.cast_eq_zero]
  exact ord_G_twelve _ _


open ModularFormMod


theorem Theta_l_add_three_div_two [isLargerPrime ℓ] (flu : fl ℓ |𝓤 = 0) (n) :
  (Θ^[(ℓ + 3)/2] (fl ℓ)).coeff n = (Reduce ℓ ((δ ℓ ^ ((ℓ + 3) / 2))
    • IntegerModularForm.G ⟨δ ℓ, delta_lt_dim⟩)).coeff n := by

  set fell := (Θ^[(ℓ + 3) / 2] (fl ℓ)) with fellquall


  have fellell : ∀ n < δ ℓ, fell.coeff n = 0 := fun n nlt => by
    simp only [fellquall, coeff_Theta_pow, ModularFormMod.fl_lt_delta nlt, smul_zero]


  have haw : fell.hasWeight (12 * δ ℓ + 4) := by
    norm_cast
    simp_rw [twelve_delta, Nat.cast_add, twelve_delta_cast, Nat.cast_ofNat,
      ← Filt_Theta_l_add_three_div_two flu]
    exact Filtration_spec _

  obtain ⟨b', hj, aeq, ordb⟩ := exists_maximal_Reduce fell fellell haw

  rw [aeq, eq_G_of_ord_max _ b']
  simp_rw [dim_twelve_delta_add_four]
  simp
  left

  rw [← coeff_Reduce, ← coeff_Mcast (h := hj), ← aeq, fellquall]
  simp only [coeff_Theta_pow, ModularFormMod.fl_delta,
     nsmul_eq_mul, Nat.cast_pow, _root_.mul_one]

  simpa [dim_twelve_delta_add_four]

  rw [dim_twelve_delta_add_four]
  use 0, Nat.zero_lt_succ (δ ℓ)





lemma Theta_l_add_three_div_two_eq_241 [isLargerPrime ℓ] (flu : fl ℓ |𝓤 = 0) :
    (Θ^[(ℓ + 3)/2] (fl ℓ)).coeff (δ ℓ + 1) = 241 * (δ ℓ) ^ ((ℓ + 3) / 2) := by
  simp [Theta_l_add_three_div_two flu, G_delta_add_one, mul_comm]



private lemma pow_congr_reduce_of_dvd {a c n : ℤ} {b : ℕ} (an0 : a ≠ 0) (adiv : a ∣ (n^2 - 1))
    ( h : ((n^2 - 1)/a + 1) ^ b ≡ c * ((n^2 - 1)/a) ^ b [ZMOD n] ) :
      (-a + 1) ^ (b) ≡ c [ZMOD n] := by

  obtain ⟨k, hk⟩ := adiv
  rw[hk, Int.mul_ediv_cancel_left _ an0] at h
  have h1 : a * k ≡ -1 [ZMOD n] := by
    trans n ^ 2 - 1; rw[hk]
    trans 0 ^ 2 - 1; gcongr
    exact Int.modulus_modEq_zero
    rfl


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

      _ = ↑(241 : ℤ) := by rwa[ZMod.intCast_eq_intCast_iff]

      _ = 241 := Int.cast_ofNat 241

  have lprime : Nat.Prime ℓ := Fact.out
  have lg13 : ℓ ≥ 13 := Fact.out

  rcases rcases with rcases | rcases

  simp only [even_two, Even.neg_pow, rcases, _root_.mul_one] at bindf

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


  simp only [even_two, Even.neg_pow, rcases, mul_neg, _root_.mul_one] at bindf

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
