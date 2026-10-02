import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.ProductDefs
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.LdvdBernoulliNum
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.DeltaCarrierEq
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Tactic.ModCases
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Algebra.Polynomial.SumIteratedDerivative


/-
This file defines Delta, fl, and the Eisenstein series
This file is sorry-free
-/

open PowerSeries Finset

namespace IntegerModularForm

noncomputable section Delta_fl_Defs




/-- The integer modular form of weight 12. Defined by the coefficients of the `DeltaProduct` -/
def Delta : IntegerModularForm 12 where
  fourier := .mk fun m => (DeltaProduct m).coeff m
  carrier := CuspForm.discriminant
  carrier_eq := Delta_carrier_eq


@[inherit_doc] scoped notation "Δ" => Delta


/-- The integer modular form. Equal to `Δ ^ (δ ℓ)` -/
def fl (ℓ : ℕ) : IntegerModularForm (δ ℓ * 12) := Delta.pow (δ ℓ)



lemma coeff_Delta (n : ℕ) : (Δ).coeff n = (DeltaProduct n).coeff n := by
  simp only [coeff, Delta, coeff_mk]

alias Delta_eq_coeff_Product := coeff_Delta


lemma coeff_fl {ℓ : ℕ} (n : ℕ) : (fl ℓ).coeff n = (flProduct ℓ n).coeff n := by
  simp_rw [fl, flProduct_eq_DeltaProduct_pow, coeff_pow, Pi.pow_apply,
      DeltaProduct, PowerSeries.coeff_pow, ← DeltaProduct_apply]
  congr! with x xin y yin
  rw [← DeltaProduct_coeff_le (le_refl _) <| finsuppAntidiag.le_right xin yin]
  exact coeff_Delta (x y)

alias fl_eq_coeff_Product := coeff_fl


variable {α : Type*}

theorem DeltaProduct_eventually_sum [CommRing α] :
    (DeltaProduct ·) ⟶ (∑ i ∈ range ·, Delta.coeff i • (X : α⟦X⟧) ^ i) := by

  intro n
  simp_rw [coeff_Delta]
  use n + 1; intro k kle j jg
  have : j > k := Nat.lt_of_le_of_lt kle jg
  trans (PowerSeries.coeff (R := α) k) (∑ x ∈ range j, C ((PowerSeries.coeff (R := α) x) (DeltaProduct x)) * X ^ x)
  set f : ℕ → α := fun n ↦ (PowerSeries.coeff (R := α) n) (DeltaProduct n) with feq
  rw [coeff_sum_X_pow (a := f) this, feq]; symm

  exact DeltaProduct_coeff_le k.le_refl this.le
  congr! 2 with x -; rw [map_coeff_DeltaProduct, zsmul_eq_mul, Int.cast_coeff_DeltaProduct]



theorem flProduct_eventually_sum [CommRing α] (ℓ) :
    (flProduct ℓ ·) ⟶ (∑ i ∈ range ·, (fl ℓ).coeff i • (X : α⟦X⟧) ^ i) := by

  rw [flProduct_eq_DeltaProduct_pow, fl]; symm; calc

    _ ⟶ (fun x ↦ ∑ i ∈ range x, (Delta.coeff i) • (X : α ⟦X⟧) ^ i) ^ (δ ℓ) := by

      intro k; use k + 1; intro n nlek M Mgk
      dsimp
      simp_rw [coeff_pow]

      have rw1 (x) : (((∑ l ∈ (range (δ ℓ)).finsuppAntidiag x, ∏ i ∈ range (δ ℓ), IntegerModularForm.coeff (l i) Δ) : ℤ) : α ⟦X⟧) =
        C (R := α) (∑ l ∈ (range (δ ℓ)).finsuppAntidiag x, ∏ i ∈ range (δ ℓ), IntegerModularForm.coeff (l i) Δ) := by
          simp only [map_sum, map_prod, map_intCast, Int.cast_sum, Int.cast_prod]

      have rw2 (i) : (Delta.coeff i : α ⟦X⟧) = C (R := α) (IntegerModularForm.Delta.coeff i) := by
        simp only [map_intCast]

      have nlM : n < M := by omega
      simp_rw [zsmul_eq_mul, rw1, coeff_sum_X_pow nlM, PowerSeries.coeff_pow]

      apply sum_congr rfl; intro y yin
      apply prod_congr rfl; intro i ilt
      have ylen : y i ≤ n := by calc
        _ = ∑ j ∈ {i}, y j := rfl
        _ ≤ ∑ j ∈ range (δ ℓ), y j :=
          sum_le_sum_of_subset <| singleton_subset_iff.mpr ilt
        _ = n := by rw [mem_finsuppAntidiag] at yin; exact yin.1

      simp only [rw2, coeff_sum_X_pow (ylen |> Trans.trans <| nlM)]

    _ ⟶ (DeltaProduct ·) ^ δ ℓ := by
      gcongr; exact DeltaProduct_eventually_sum.symm


@[simp] lemma Delta_zero : (Δ).coeff 0 = 0 := by simp [coeff_Delta, DeltaProduct]

@[simp] lemma Delta_one : (Δ).coeff 1 = 1 := by simp [coeff_Delta, DeltaProduct]

@[simp] lemma Delta_two : (Δ).coeff 2 = -24 := by
  simp only [coeff_Delta, DeltaProduct, prod_range, Fin.prod_univ_two, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, _root_.pow_one, Nat.mod_succ, Nat.reduceAdd,
    coeff_succ_X_mul, Int.reduceNeg]
  ring_nf
  simpa only [map_add, map_sub, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte, PowerSeries.coeff_one_mul,
    coeff_one_X, _root_.one_mul, constantCoeff_X, MulZeroClass.mul_zero, add_zero, zero_sub,
    coeff_X_pow_mul', Nat.not_ofNat_le_one, sub_zero, coeff_X_pow, OfNat.one_ne_ofNat,
    Int.reduceNeg, neg_inj, Nat.cast_ofNat] using (map_natCast _ _ : constantCoeff 24 = (24 : ℤ))

@[simp] lemma Delta_three : (Δ).coeff 3 = 252 := by
  simp only [coeff_Delta, DeltaProduct, prod_range, Fin.prod_univ_three, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, _root_.pow_one, Nat.one_mod, Nat.reduceAdd,
    Nat.mod_succ, coeff_succ_X_mul]
  ring_nf
  simp only [map_add, map_sub, PowerSeries.coeff_one, OfNat.ofNat_ne_zero, ↓reduceIte, zero_sub,
    coeff_X_pow_mul', Std.le_refl, tsub_self, coeff_zero_eq_constantCoeff, Nat.reduceLeDiff,
    sub_zero, add_zero, coeff_X_pow, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  rw [← _root_.pow_one X, coeff_X_pow_mul']
  simp only [Nat.one_le_ofNat, ↓reduceIte, Nat.reduceSub]
  show -(C 24).coeff 1 + _ = 252
  rw [coeff_succ_C, neg_zero, zero_add]
  rfl


lemma fl_lt_delta {ℓ n} (nlt : n < δ ℓ) : (fl ℓ).coeff n = 0 :=
  leading_pow_zeros Delta_zero nlt

@[simp] lemma fl_delta {ℓ} : (fl ℓ).coeff (δ ℓ) = 1 := by
   rw [fl, coeff_pow_of_leading_zero Delta_zero (δ ℓ), Delta_one, one_pow]


@[simp] lemma fl_delta_add_one {ℓ} [isLargePrime ℓ] : (fl ℓ).coeff (δ ℓ + 1) = 1 - ℓ ^ 2 := by
  rw [fl, coeff_succ_pow_of_leading_zero Delta_zero (δ ℓ), Delta_two, Delta_one]
  simp only [Int.reduceNeg, Int.nsmul_eq_mul, mul_neg, one_pow, _root_.mul_one]
  norm_cast
  rw [mul_comm, twentyfour_mul_delta,
    Int.natCast_pred_of_pos <| pow_two_pos_of_ne_zero NeZero.out, Nat.cast_pow, neg_sub]
  norm_cast


end Delta_fl_Defs

noncomputable section Eisenstein_defs

open ModularForm PowerSeries ArithmeticFunction.sigma UpperHalfPlane MatrixGroups



def EisNat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : IntegerModularForm k where
  fourier := .mk fun m => if m = 0 then (2 * k / bernoulli k).den else -(2 * k / bernoulli k).num * (σ (k - 1) m)
  carrier := (2 * k / bernoulli k).den • E hk
  carrier_eq := PowerSeries.ext fun m => by
    rw [qexp_eq', FunLike.coe_smul]
    rw [show (2 * ↑k / bernoulli k).den • ⇑ (E hk) = ((2 * ↑k / bernoulli k).den : ℂ) • ⇑(E hk) by norm_cast]
    rw [ModularForm.qExpansion_smul zero_lt_one (by simp), map_smul, EisensteinSeries.E_qExpansion_coeff hk hk2]
    simp
    split_ifs
    · norm_cast
    · norm_cast
      rw [← mul_assoc, Rat.den_mul_eq_num]
      norm_cast



def EisInt {k : ℤ} (hk : 3 ≤ k) (hk2 : Even k) : IntegerModularForm k :=
  Icast (Int.toNat_of_nonneg (by lia)) <| EisNat (show 3 ≤ k.toNat from
    (Int.le_toNat (by lia)).mpr hk)
    ((Int.even_coe_nat k.toNat).mp <| by rwa [Int.toNat_of_nonneg (by lia)])

def Eis (k : ℤ) : IntegerModularForm k :=
  if hk : 3 ≤ k then if hk2 : Even k then EisInt hk hk2 else 0 else 0

theorem coeff_EisNat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n) :
  (EisNat hk hk2).coeff n = if n = 0 then ((2 * k / bernoulli k).den : ℤ) else
    -(2 * k / bernoulli k).num * (σ (k - 1) n) := by
  rw [EisNat, ← coeff_def, coeff_mk]


lemma coeff_eq_EisNat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n) :
    (EisNat hk hk2).coeff n = (2 * k / bernoulli k).den • (qExpansion 1 (E hk)).coeff n := by
  rw [← qexp_eq', ← coeff_def, ← eq_intCast (f := Int.castRingHom ℂ), ← coeff_map, ← carrier_eq]
  simp only [EisNat, neg_mul, map_nsmul]


lemma coeff_eq_EisInt {k : ℤ} (hk : 3 ≤ k) (hk2 : Even k) (n) :
    (EisInt hk hk2).coeff n = (2 * k / bernoulli k.toNat).den • (qExpansion 1 (E (show 3 ≤ k.toNat by grind))).coeff n := by
  lift k to ℕ using by lia
  simp only [EisInt, Int.toNat_natCast, coeff_Icast, coeff_eq_EisNat, Int.cast_natCast]


lemma coeff_eq_Eis {k : ℤ} (hk : 3 ≤ k) (n) :
    (Eis k).coeff n = (2 * k / bernoulli k.toNat).den • (qExpansion 1 (E (show 3 ≤ k.toNat by grind))).coeff n := by
  rw [Eis]
  split_ifs with hk2
  · rw [coeff_eq_EisInt]
  · have kodd := Int.not_even_iff_odd.1 hk2
    lift k to ℕ using by lia
    simp [ModularForm.levelOne_odd_weight_eq_zero kodd <| E _, qExpansion_zero]


lemma coeff_Eis {k} (hk : 3 ≤ k) (hk2 : Even k) (n) :
    (Eis k).coeff n = if n = 0 then ((2 * k / bernoulli k.toNat).den : ℤ) else -(2 * k / bernoulli k.toNat).num * (σ (k.toNat - 1) n) := by
  lift k to ℕ using by lia
  simp [Eis, EisInt, dite_eq_left hk, dite_eq_left hk2, coeff_EisNat]


theorem coeff_Eis_four (n) : (Eis 4).coeff n = if n = 0 then 1 else 240 * σ 3 n := by
  rw [coeff_Eis (by decide) (by decide)]
  split_ifs
  simp only [Int.cast_ofNat, bernoulli, Int.reduceToNat, bernoulli'_four, Nat.cast_one,
    Nat.cast_eq_one]
  decide +kernel
  simp only [Int.cast_ofNat, bernoulli, Int.reduceToNat, bernoulli'_four, Nat.add_one_sub_one,
    neg_mul, Nat.cast_mul, Nat.cast_ofNat]
  norm_num

theorem coeff_Eis_six (n) : (Eis 6).coeff n = if n = 0 then 1 else - (504 * σ 5 n : ℤ) := by
  rw [coeff_Eis (by decide) (by decide)];
  split_ifs
  simp only [Int.cast_ofNat, bernoulli, Int.reduceToNat, Nat.cast_eq_one]
  decide +kernel
  simp only [Int.cast_ofNat, bernoulli, Int.reduceToNat, Nat.add_one_sub_one, neg_mul, neg_inj,
    mul_eq_mul_right_iff, Int.natCast_eq_zero, ArithmeticFunction.sigma_eq_zero]
  norm_num
  left
  decide +kernel


lemma Eis_le_two {k} (hk : k ≤ 2) : Eis k = 0 := dite_eq_right <| by lia

lemma Eis_Odd {k} (hk : Odd k) : Eis k = 0 := by
  simpa only [Eis, dite_eq_right_iff] using fun _ hk2 => (Int.not_odd_iff_even.2 hk2) hk |>.elim

lemma Eis_zero {k} (hk : 3 ≤ k) (hk2 : Even k) : (Eis k).coeff 0 = (2 * k / bernoulli k.toNat).den := by
  rw [coeff_Eis hk hk2, ite_eq_left rfl]

@[simp] theorem Eis_four_zero : (Eis 4).coeff 0 = 1 := by
  rw [coeff_Eis_four, ite_eq_left rfl]; rfl

@[simp] theorem Eis_six_zero : (Eis 6).coeff 0 = 1 := by
  rw [coeff_Eis_six, ite_eq_left rfl]

@[simp] theorem Eis_four_one : (Eis 4).coeff 1 = 240 := by
  rw [coeff_Eis_four]
  decide

end Eisenstein_defs



noncomputable section Eis_sub_one

variable (ℓ : ℕ)

def reduce {k : ℤ} (ℓ : ℕ) : IntegerModularForm k →ₗ[ℤ] PowerSeries (ZMod ℓ) where
  toFun f := map (Int.castRingHom (ZMod ℓ)) f.fourier
  map_add' := by simp
  map_smul' := by simp


@[simp] theorem reduce_apply {k} (ℓ) (f : IntegerModularForm k) (n) :
    (reduce ℓ f).coeff n = f.coeff n := rfl

@[simp]
theorem reduce_mul {k j : ℤ} (ℓ : ℕ) (f : IntegerModularForm k) (g : IntegerModularForm j) :
    (f.mul g).reduce ℓ = f.reduce ℓ * g.reduce ℓ := by
  simp only [reduce, LinearMap.coe_mk, AddHom.coe_mk, fourier_mul, map_mul]

@[simp]
theorem reduce_pow {k} (ℓ : ℕ) (f : IntegerModularForm k) (m : ℕ) :
    (f.pow m).reduce ℓ = f.reduce ℓ ^ m := by
  simp only [reduce, LinearMap.coe_mk, AddHom.coe_mk, fourier_pow, map_pow]


theorem nldvd_bernoulli_den (ℓ) [hℓ : isLargePrime ℓ] : ¬ ℓ ∣ (2 * (ℓ - 1) / bernoulli (ℓ - 1)).den := by
  suffices ℓ ∣ (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)).num.natAbs by
    by_contra h
    let b := (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1))
    have : ¬ b.num.natAbs.Coprime b.den := by
      apply Nat.not_coprime_of_dvd_of_dvd (show 1 < ℓ by grind [hℓ.AtLeastFive])
      exact this
      unfold b
      rwa [Nat.cast_pred <| by grind [hℓ.AtLeastFive]]
    exact this b.reduced

  rw [← Int.natCast_dvd, ← Int.modEq_zero_iff_dvd]
  exact ldvd_bernoulli_num ℓ hℓ.Prime hℓ.AtLeastFive



theorem bernoulli_den_exists_inv (ℓ) [h : isLargePrime ℓ] : ∃ j : ℕ, j * (2 * (ℓ - 1) / bernoulli (ℓ - 1)).den ≡ 1 [MOD ℓ] := by

  have hcoprime : Nat.Coprime ℓ (2 * (ℓ - 1) / bernoulli (ℓ - 1)).den :=
    h.Prime.coprime_iff_not_dvd.mpr <| nldvd_bernoulli_den ℓ

  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcoprime.symm h.Prime.one_lt
  use j, by rwa [mul_comm, Nat.ModEq, Nat.one_mod_eq_one.mpr h.Prime.ne_one]



def bernoulli_den_inv (ℓ : ℕ) [h : isLargePrime ℓ] : ℕ := (bernoulli_den_exists_inv ℓ).choose

theorem bernoulli_den_inv_spec (ℓ) [h : isLargePrime ℓ] : bernoulli_den_inv ℓ * (2 * (ℓ - 1) / bernoulli (ℓ - 1)).den ≡ 1 [MOD ℓ] :=
  (bernoulli_den_exists_inv ℓ).choose_spec


variable [hℓ : isLargePrime ℓ]
open ArithmeticFunction.sigma

abbrev El := bernoulli_den_inv ℓ • EisNat (show 3 ≤ ℓ - 1 by grind [hℓ.AtLeastFive]) (by
    suffices Odd ℓ by grind [hℓ.AtLeastFive]
    exact Nat.Prime.odd_iff hℓ.Prime|>.mpr <| show 3 ≤ 5 by norm_num |>.trans hℓ.AtLeastFive)

theorem El_zero : (El ℓ).coeff 0 ≡ 1 [ZMOD ℓ] := by
  rw [IntegerModularForm.coeff_smuln, coeff_EisNat, ite_eq_left rfl]
  simp only [Int.nsmul_eq_mul]
  have := bernoulli_den_inv_spec ℓ
  rw [Nat.cast_pred (by grind [hℓ.AtLeastFive])]
  norm_cast at *

theorem coeff_El (n) : (El ℓ).coeff n = if n = 0 then (bernoulli_den_inv ℓ * (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)).den : ℤ)
    else bernoulli_den_inv ℓ * -(2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)).num * σ (ℓ - 2) n := by
  rw [El, coeff_smuln, coeff_EisNat]
  split_ifs
  rfl
  rw [nsmul_eq_mul, mul_assoc]
  congr 2


theorem coeff_succ_El (n) : (El ℓ).coeff (n + 1) ≡ 0 [ZMOD ℓ] := by
  rw [coeff_El, ite_eq_right n.succ_ne_zero]

  suffices h : (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)).num ≡ 0 [ZMOD ℓ] by
    grw [h]
    simp only [neg_zero, MulZeroClass.mul_zero, MulZeroClass.zero_mul, Int.ModEq.refl]

  exact ldvd_bernoulli_num ℓ hℓ.Prime hℓ.AtLeastFive


theorem reduce_El : (El ℓ).reduce ℓ = 1 :=
  PowerSeries.ext fun
    | 0 => by
      rw [reduce_apply, PowerSeries.coeff_one, ite_eq_left rfl, ← Int.cast_one, ZMod.intCast_eq_intCast_iff]
      exact El_zero ℓ
    | n + 1 => by
      rw [reduce_apply, PowerSeries.coeff_one, ite_eq_right n.succ_ne_zero, ← Int.cast_zero, ZMod.intCast_eq_intCast_iff]
      exact coeff_succ_El ℓ n


theorem reduce_El_pow (m) : ((El ℓ).pow m).reduce ℓ = 1 := by
  rw [reduce_pow, reduce_El, one_pow]


@[simp] theorem reduce_two_Eis_four : (Eis 4).reduce 2 = 1 :=
  PowerSeries.ext fun
  | 0 => by
    simp [reduce_apply, coeff_Eis_four]
  | n + 1 => by
    simp [coeff_Eis_four]
    left
    decide

@[simp] theorem reduce_three_Eis_four : (Eis 4).reduce 3 = 1 :=
  PowerSeries.ext fun
  | 0 => by
    simp [reduce_apply, coeff_Eis_four]
  | n + 1 => by
    simp [coeff_Eis_four]
    left
    decide


@[simp] theorem reduce_two_Eis_four_pow (m) : ((Eis 4).pow m).reduce 2 = 1 := by
    rw [reduce_pow, reduce_two_Eis_four, one_pow]

@[simp] theorem reduce_three_Eis_four_pow (m) : ((Eis 4).pow m).reduce 3 = 1 := by
    rw [reduce_pow, reduce_three_Eis_four, one_pow]

end Eis_sub_one
