import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Basic
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.ThetaOperator.KummerCongruence

open IntegerModularForm ModularFormMod
open ArithmeticFunction.sigma

noncomputable section

namespace ThetaOperator

open KummerCongruence

variable {ℓ : ℕ}

/-!
The integral Eisenstein series used in the proof of Corollary 1.37.

`IntegerModularForm.Eis` already contains the integral normalisation of the
level-one Eisenstein series.  This abbreviation records the particular
weight `ℓ + 1` used in the reduction argument.
-/

def eisLPlusOne (ℓ : ℕ) : IntegerModularForm (ℓ + 1) :=
  IntegerModularForm.Eis (ℓ + 1)

theorem eisLPlusOne_eq_Eis : eisLPlusOne ℓ = IntegerModularForm.Eis (ℓ + 1) := rfl

/-!
The residue-class weight of `E_{ℓ+1}` is the same as the weight `2` of the
weight-two Eisenstein series modulo `ℓ`.
-/

theorem eisLPlusOne_weight (hℓ : ℓ ≠ 0) :
    ((ℓ + 1 : ℤ) : ZMod (ℓ - 1)) = (2 : ZMod (ℓ - 1)) := by
  have hℓ : (ℓ : ZMod (ℓ - 1)) = 1 := by
    rcases Nat.exists_eq_add_one.2 <| Nat.pos_of_ne_zero hℓ with ⟨n, rfl⟩
    simp only [Nat.cast_add, CharP.cast_eq_zero, Nat.cast_one, zero_add]
  push_cast
  rw [hℓ]
  norm_num

/-!
The integral model `Eis (ℓ + 1)` need not have constant coefficient `1`: its
integral normalization clears the denominator of `2(ℓ+1)/B_(ℓ+1)`.  We first
reduce it modulo `ℓ`, then normalize by the inverse of its constant
coefficient.  This is the form whose first coefficient is `1`.
-/

variable [isLargePrime ℓ]

def eisLPlusOneConstant : ZMod ℓ :=
  (eisLPlusOne ℓ).coeff 0

def E₂ : ModularFormMod ℓ (2 : ZMod (ℓ - 1)) :=
  (eisLPlusOneConstant (ℓ := ℓ))⁻¹ •
    ((eisLPlusOne ℓ).Reduce ℓ).Mcast (eisLPlusOne_weight (NeZero.ne ℓ))

private lemma residue_normalizedBernoulli_two {p : ℕ} [isLargePrime p] :
    residue p (normalizedBernoulli 2) = (12 : ZMod p)⁻¹ := by
  norm_num [residue, normalizedBernoulli, bernoulli_two]

private lemma residue_normalizedBernoulli_two_ne_zero {p : ℕ} [isLargePrime p] :
    residue p (normalizedBernoulli 2) ≠ 0 := by
  rw [residue_normalizedBernoulli_two]
  apply inv_ne_zero
  intro h
  have hd : p ∣ 12 := (ZMod.natCast_eq_zero_iff 12 p).mp h
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  rcases (inferInstance : isLargePrime p).Prime.dvd_mul.mp
      (by simpa using hd : p ∣ 3 * 4) with h3 | h4
  · exact (by omega : ¬ p ≤ 3) (Nat.le_of_dvd (by norm_num) h3)
  · exact (by omega : ¬ p ≤ 4) (Nat.le_of_dvd (by norm_num) h4)

private lemma hmod_special {p : ℕ} [isLargePrime p] :
    Nat.ModEq (p - 1) (p + 1) 2 := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  rw [Nat.modEq_iff_dvd]
  refine ⟨-1, ?_⟩
  push_cast
  rw [Nat.cast_sub (by omega)]
  ring

private lemma hkp_special {p : ℕ} [isLargePrime p] : ¬ (p - 1) ∣ p + 1 := by
  intro h
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have h2 : p - 1 ∣ 2 := by
    apply (Nat.dvd_add_iff_left (k := p - 1) (m := 2) (n := p - 1)
      (dvd_refl (p - 1))).mpr
    convert h using 1; omega
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2
  omega

private lemma hkp'_special {p : ℕ} [isLargePrime p] : ¬ (p - 1) ∣ 2 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  omega

private lemma kummer_special {p : ℕ} [isLargePrime p] :
    PIntegral p (normalizedBernoulli (p + 1)) ∧
      PIntegral p (normalizedBernoulli 2) ∧
      residue p (normalizedBernoulli (p + 1)) = residue p (normalizedBernoulli 2) := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hpPrime : p.Prime := (inferInstance : isLargePrime p).Prime
  have normalized_integral (N : ℕ) (hN : 0 < N) (hpN : ¬ p ∣ N)
      (hB : ¬ p ∣ (bernoulli N).den) : PIntegral p (normalizedBernoulli N) := by
    apply (pIntegral_iff (normalizedBernoulli N)).2
    intro hden
    have hdenMul : (normalizedBernoulli N).den ∣ (bernoulli N).den * N := by
      have hmul := Rat.mul_den_dvd (bernoulli N) ((N : ℚ)⁻¹)
      have hinv : ((N : ℚ)⁻¹).den = N :=
        Rat.den_inv_of_ne_zero (by exact_mod_cast (Nat.ne_of_gt hN))
      simpa [normalizedBernoulli, div_eq_mul_inv, hinv] using hmul
    have hprod : p ∣ (bernoulli N).den * N := Nat.dvd_trans hden hdenMul
    rcases hpPrime.dvd_mul.mp hprod with hBden | hNdiv
    · exact hB hBden
    · exact hpN hNdiv
  have hpNotDvdOne : ¬ p ∣ 1 := by
    intro h
    have : p ≤ 1 := Nat.le_of_dvd (by norm_num) h
    omega
  have hpNotDvdPPlusOne : ¬ p ∣ p + 1 := by
    intro h
    have hdivOne : p ∣ 1 := by
      apply (Nat.dvd_add_iff_left (k := p) (m := 1) (n := p) (dvd_refl p)).mpr
      simpa [Nat.add_comm] using h
    exact hpNotDvdOne hdivOne
  have hpNotDvdTwo : ¬ p ∣ 2 := by
    intro h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
    omega
  have hBden1 : ¬ p ∣ (bernoulli (p + 1)).den := by
    intro h
    exact hkp_special (p := p)
      (Bernoulli.sub_one_dvd_of_dvd_den_bernoulli hpPrime h)
  have hBden2 : ¬ p ∣ (bernoulli 2).den := by
    intro h
    exact hkp'_special (p := p)
      (Bernoulli.sub_one_dvd_of_dvd_den_bernoulli hpPrime h)
  have hpk : PIntegral p (normalizedBernoulli (p + 1)) :=
    normalized_integral (p + 1) (by omega) hpNotDvdPPlusOne hBden1
  have hpk' : PIntegral p (normalizedBernoulli 2) :=
    normalized_integral 2 (by norm_num) hpNotDvdTwo hBden2
  refine ⟨hpk, hpk', ?_⟩
  have hmcast : (p + 1 : ZMod p) = 1 := by simp
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro htwo0
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo0
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hK := Bernoulli.kummer_congr (p := p) (m := p + 1) (n := 2)
    (hmod_special (p := p)) (hkp_special (p := p)) (by omega) (by norm_num)
  have cast_normalized (N : ℕ) (hN : 0 < N)
      (hNint : PIntegral p (normalizedBernoulli N)) :
      (bernoulli N : ZMod p) = (N : ZMod p) * (normalizedBernoulli N : ZMod p) := by
    have hNrat : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hrepr : bernoulli N = (N : ℚ) * normalizedBernoulli N := by
      unfold normalizedBernoulli
      field_simp [hNrat]
    have hden : ((normalizedBernoulli N).den : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (pIntegral_iff (normalizedBernoulli N)).mp hNint
    have hnatden : (((N : ℚ).den : ZMod p)) ≠ 0 := by simp
    rw [hrepr, Rat.cast_mul_of_ne_zero hnatden hden]
    norm_cast
  have hcast1 := cast_normalized (p + 1) (by omega) hpk
  have hcast2 := cast_normalized 2 (by norm_num) hpk'
  rw [hcast1, hcast2] at hK
  simp only [Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add] at hK
  have hK' : (2 : ZMod p) * (normalizedBernoulli (p + 1) : ZMod p) =
      2 * (normalizedBernoulli 2 : ZMod p) := by simpa using hK
  have hnormalized : (normalizedBernoulli (p + 1) : ZMod p) =
      (normalizedBernoulli 2 : ZMod p) := mul_left_cancel₀ htwo hK'
  have residue_eq_cast (x : ℚ) : residue p x = (x : ZMod p) := by
    simp [residue, Rat.cast_def, div_eq_mul_inv]
  rw [residue_eq_cast, residue_eq_cast]
  exact hnormalized

private lemma ratio_den_dvd_num {p : ℕ} [isLargePrime p] :
    (2 * (p + 1 : ℚ) / bernoulli (p + 1)).den ∣
      (normalizedBernoulli (p + 1)).num.natAbs := by
  have hx : normalizedBernoulli (p + 1) ≠ 0 := by
    intro h
    have hres := (kummer_special (p := p)).2.2
    have hne := residue_normalizedBernoulli_two_ne_zero (p := p)
    apply hne
    rw [← hres]
    simp [h, residue]
  have hmul := Rat.mul_den_dvd (2 : ℚ) (normalizedBernoulli (p + 1))⁻¹
  have hratio : (2 * (p + 1 : ℚ) / bernoulli (p + 1)) =
      2 * (normalizedBernoulli (p + 1))⁻¹ := by
    unfold normalizedBernoulli
    push_cast
    field_simp
  rw [hratio]
  simpa [Rat.den_inv_of_ne_zero hx] using hmul

private lemma coeff_zero_ratio {p : ℕ} [isLargePrime p] :
    (eisLPlusOne p).coeff 0 =
      ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).den : ℤ) := by
  have hp5 := (inferInstance : isLargePrime p).AtLeastFive
  have hodd : Odd p := (Nat.Prime.odd_iff (inferInstance : isLargePrime p).Prime).mpr (by omega)
  have hevenNat : Even (p + 1) := hodd.add_one
  have heven : Even (p + 1 : ℤ) := by exact_mod_cast hevenNat
  rw [eisLPlusOne, IntegerModularForm.coeff_Eis (k := (p + 1 : ℤ)) (by omega) heven]
  norm_num

/-!
Kummer's congruence, applied to `B_(ℓ+1)/(ℓ+1)` and `B₂/2`, gives the
nonvanishing of the constant coefficient modulo `ℓ`.  The arithmetic bridge
from the rational residue to the numerator/denominator representation used by
`IntegerModularForm.Eis` is isolated here.
-/

theorem eisLPlusOneConstant_ne_zero :
    eisLPlusOneConstant (ℓ := ℓ) ≠ 0 := by
  rw [eisLPlusOneConstant, coeff_zero_ratio]
  intro h
  have hdivz : (ℓ : ℤ) ∣
      ((2 * (ℓ + 1 : ℚ) / bernoulli (ℓ + 1)).den : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hnat : ℓ ∣ (2 * (ℓ + 1 : ℚ) / bernoulli (ℓ + 1)).den := by
    exact_mod_cast hdivz
  have hnum := (kummer_special (p := ℓ)).1
  have hxden : ¬ ℓ ∣ (normalizedBernoulli (ℓ + 1)).den :=
    (pIntegral_iff _).mp hnum
  have hxres : residue ℓ (normalizedBernoulli (ℓ + 1)) ≠ 0 := by
    rw [(kummer_special (p := ℓ)).2.2]
    exact residue_normalizedBernoulli_two_ne_zero
  have hxnum : (normalizedBernoulli (ℓ + 1)).num.natAbs |> fun n => ¬ ℓ ∣ n := by
    intro hdiv
    apply hxres
    simp only [residue]
    have hzero : ((normalizedBernoulli (ℓ + 1)).num : ZMod ℓ) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr hdiv)
    simp [hzero]
  exact hxnum (Nat.dvd_trans hnat (ratio_den_dvd_num (p := ℓ)))

private lemma ratio_num_mul_num {p : ℕ} [isLargePrime p] :
    ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).num : ZMod p) *
        ((normalizedBernoulli (p + 1)).num : ZMod p) =
      2 * ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).den : ZMod p) *
        ((normalizedBernoulli (p + 1)).den : ZMod p) := by
  let q : ℚ := 2 * (p + 1 : ℚ) / bernoulli (p + 1)
  let x : ℚ := normalizedBernoulli (p + 1)
  have hx : x ≠ 0 := by
    intro h
    have hresne : residue p (normalizedBernoulli (p + 1)) ≠ 0 := by
      rw [(kummer_special (p := p)).2.2]
      exact residue_normalizedBernoulli_two_ne_zero
    apply hresne
    simp [x, h, residue]
  have hB : bernoulli (p + 1) ≠ 0 := by
    intro h
    apply hx
    simp [x, normalizedBernoulli, h]
  have hqx : q * x = 2 := by
    dsimp [q, x, normalizedBernoulli]
    push_cast
    field_simp [hB]
  have hrat : (q.num : ℚ) / q.den * ((x.num : ℚ) / x.den) = 2 := by
    rw [Rat.num_div_den, Rat.num_div_den]
    exact hqx
  have hrat' := hrat
  field_simp at hrat'
  have hrat_int : q.num * (x.num : ℤ) =
      (q.den : ℤ) * (x.den : ℤ) * 2 := by
    exact_mod_cast hrat'
  have hcross_qx : (q.num : ZMod p) * (x.num : ZMod p) =
      2 * (q.den : ZMod p) * (x.den : ZMod p) := by
    have hrat_zmod := congrArg (fun z : ℤ => (z : ZMod p)) hrat_int
    simpa [Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat,
      mul_assoc, mul_comm, mul_left_comm] using hrat_zmod
  simpa [q, x, mul_assoc, mul_comm, mul_left_comm] using hcross_qx

private lemma ratio_num_mod {p : ℕ} [isLargePrime p] :
    (eisLPlusOneConstant (ℓ := p))⁻¹ *
        ((2 * (p + 1 : ℚ) / bernoulli (p + 1)).num : ZMod p) = 24 := by
  let q : ℚ := 2 * (p + 1 : ℚ) / bernoulli (p + 1)
  let x : ℚ := normalizedBernoulli (p + 1)
  have hK := kummer_special (p := p)
  have hxden : (x.den : ZMod p) ≠ 0 := by
    intro hzero
    apply (pIntegral_iff x).mp (by simpa [x] using hK.1)
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hxres : (x.num : ZMod p) * (x.den : ZMod p)⁻¹ = (12 : ZMod p)⁻¹ := by
    simpa [x, residue] using (hK.2.2.trans (residue_normalizedBernoulli_two (p := p)))
  have hxnum : (x.num : ZMod p) ≠ 0 := by
    intro h
    have hresne : (x.num : ZMod p) * (x.den : ZMod p)⁻¹ ≠ 0 := by
      have hresne' : residue p (normalizedBernoulli (p + 1)) ≠ 0 := by
        rw [hK.2.2]
        exact residue_normalizedBernoulli_two_ne_zero
      simpa [x, residue] using hresne'
    simp [h] at hresne
  have h12 : (12 : ZMod p) ≠ 0 := by
    intro h
    exact residue_normalizedBernoulli_two_ne_zero (p := p) (by
      rw [residue_normalizedBernoulli_two, h, inv_zero])
  have hxrel : (x.num : ZMod p) = (12 : ZMod p)⁻¹ * (x.den : ZMod p) := by
    calc
      (x.num : ZMod p) = ((x.num : ZMod p) * (x.den : ZMod p)⁻¹) *
          (x.den : ZMod p) := by field_simp
      _ = (12 : ZMod p)⁻¹ * (x.den : ZMod p) := by rw [hxres]
  have hcross := ratio_num_mul_num (p := p)
  have hcross' : (q.num : ZMod p) * ((12 : ZMod p)⁻¹ * (x.den : ZMod p)) =
      2 * (q.den : ZMod p) * (x.den : ZMod p) := by
    simpa [q, x, hxrel] using hcross
  have hqrel : (q.num : ZMod p) * (12 : ZMod p)⁻¹ =
      2 * (q.den : ZMod p) := by
    apply (mul_right_cancel₀ hxden)
    simpa [mul_assoc] using hcross'
  have hqrel' : (q.num : ZMod p) = 24 * (q.den : ZMod p) := by
    calc
      (q.num : ZMod p) = ((q.num : ZMod p) * (12 : ZMod p)⁻¹) * (12 : ZMod p) := by
        field_simp
      _ = (2 * (q.den : ZMod p)) * (12 : ZMod p) := by rw [hqrel]
      _ = 24 * (q.den : ZMod p) := by ring
  rw [eisLPlusOneConstant, coeff_zero_ratio]
  have hfinal : (q.den : ZMod p)⁻¹ * (q.num : ZMod p) = 24 := by
    rw [hqrel']
    have hqden : (q.den : ZMod p) ≠ 0 := by
      simpa [eisLPlusOneConstant, coeff_zero_ratio, q] using
        (eisLPlusOneConstant_ne_zero (ℓ := p))
    field_simp [hqden]
  simpa [q] using hfinal

private lemma sigma_prime_mod {p : ℕ} [isLargePrime p] (n : ℕ) :
    (σ p n : ZMod p) = σ 1 n := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  simp only [Nat.cast_sum, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [ZMod.pow_card]
  simp

theorem coeff_E₂_zero : (E₂ (ℓ := ℓ)).coeff 0 = 1 := by
  rw [E₂, ModularFormMod.coeff_def, ModularFormMod.fourier_smul,
    PowerSeries.coeff_smul, ModularFormMod.fourier_Mcast,
    IntegerModularForm.fourier_Reduce]
  change (eisLPlusOneConstant (ℓ := ℓ))⁻¹ *
    ((eisLPlusOne ℓ).reduce ℓ).coeff 0 = 1
  rw [IntegerModularForm.reduce_apply]
  change (eisLPlusOneConstant (ℓ := ℓ))⁻¹ *
    eisLPlusOneConstant (ℓ := ℓ) = 1
  exact inv_mul_cancel₀ (eisLPlusOneConstant_ne_zero (ℓ := ℓ))

/-!
The coefficient computation is the explicit q-expansion part of Corollary
1.36.  For `n > 0`, the coefficient of `Eis (ℓ+1)` is
`-(2(ℓ+1)/B_(ℓ+1)).num * σ ℓ n`; Kummer changes the normalized scalar to
`24` modulo `ℓ`, and Fermat changes `σ ℓ n` to `σ 1 n`.
-/

theorem coeff_E₂ (n : ℕ) :
    (E₂ (ℓ := ℓ)).coeff n = if n = 0 then (1 : ZMod ℓ) else
      -24 * σ 1 n := by
  by_cases hn : n = 0
  · simp [hn, coeff_E₂_zero]
  · rw [ite_eq_right hn]
    rw [E₂, ModularFormMod.coeff_def, ModularFormMod.fourier_smul,
      PowerSeries.coeff_smul, ModularFormMod.fourier_Mcast,
      IntegerModularForm.fourier_Reduce]
    change (eisLPlusOneConstant (ℓ := ℓ))⁻¹ *
      ((eisLPlusOne ℓ).reduce ℓ).coeff n = -24 * σ 1 n
    rw [IntegerModularForm.reduce_apply]
    have hℓ5 := (inferInstance : isLargePrime ℓ).AtLeastFive
    have hodd : Odd ℓ := (Nat.Prime.odd_iff (inferInstance : isLargePrime ℓ).Prime).mpr
      (by omega)
    have hevenNat : Even (ℓ + 1) := hodd.add_one
    have heven : Even (ℓ + 1 : ℤ) := by exact_mod_cast hevenNat
    rw [show eisLPlusOne ℓ = IntegerModularForm.Eis (ℓ + 1) by rfl]
    rw [IntegerModularForm.coeff_Eis (k := (ℓ + 1 : ℤ)) (by omega) heven]
    simp only [ite_eq_right hn, Int.cast_neg, Int.cast_mul]
    norm_num
    calc
      (eisLPlusOneConstant (ℓ := ℓ))⁻¹ *
          (((2 * (ℓ + 1 : ℚ) / bernoulli (ℓ + 1)).num : ZMod ℓ) * σ ℓ n) =
        ((eisLPlusOneConstant (ℓ := ℓ))⁻¹ *
          ((2 * (ℓ + 1 : ℚ) / bernoulli (ℓ + 1)).num : ZMod ℓ)) * σ ℓ n := by
            ring
      _ = 24 * σ ℓ n := by rw [ratio_num_mod]
      _ = 24 * σ 1 n := by rw [sigma_prime_mod]

theorem eisLPlusOne_reduce :
    ((eisLPlusOne ℓ).Reduce ℓ).Mcast (eisLPlusOne_weight (NeZero.ne ℓ)) =
      eisLPlusOneConstant (ℓ := ℓ) • E₂ (ℓ := ℓ) := by
  rw [E₂, smul_smul]
  simp only [mul_inv_cancel₀ (eisLPlusOneConstant_ne_zero (ℓ := ℓ)), one_smul]

theorem eisLPlusOne_reduce_fourier :
    (E₂ (ℓ := ℓ)).fourier =
      (eisLPlusOneConstant (ℓ := ℓ))⁻¹ • (eisLPlusOne ℓ).reduce ℓ := by
  rfl

end ThetaOperator
