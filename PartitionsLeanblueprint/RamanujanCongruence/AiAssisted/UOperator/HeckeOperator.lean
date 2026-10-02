/-
# Hecke operators on level-one modular forms

We specialize the `Gamma1` Hecke operators from `LeanModularForms` to level
one.  Since `Gamma1 1 = SL(2, ℤ)`, its image in `GL(2, ℝ)` is `𝒮ℒ`, so the
operator acts directly on `ModularForm 𝒮ℒ k`.
-/

import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Defs
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.FourierHecke

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm UpperHalfPlane

namespace HeckeOperator

private theorem gamma1_one : Gamma1 1 = ⊤ := by
  ext A
  simp [Gamma1_mem]

private theorem gamma1_one_map : (Gamma1 1).map (mapGL ℝ) = 𝒮ℒ := by
  rw [gamma1_one]
  exact (MonoidHom.range_eq_map (mapGL ℝ)).symm

/-!
The level-one operator is the `T_n` from LeanModularForms, transported from
`ModularForm ((Gamma1 1).map (mapGL ℝ)) k` to the definitionally intended
level-one space `ModularForm 𝒮ℒ k`.
-/
private noncomputable def levelOneEquiv {k : ℤ} :
    ModularForm ((Gamma1 1).map (mapGL ℝ)) k ≃ₗ[ℂ] ModularForm 𝒮ℒ k :=
  { toFun := fun f => f.copy (f : UpperHalfPlane → ℂ) rfl gamma1_one_map.symm
    invFun := fun f => f.copy (f : UpperHalfPlane → ℂ) rfl gamma1_one_map
    left_inv := by intro f; apply ModularForm.ext; intro z; rfl
    right_inv := by intro f; apply ModularForm.ext; intro z; rfl
    map_add' := by intro f g; apply ModularForm.ext; intro z; rfl
    map_smul' := by intro c f; apply ModularForm.ext; intro z; rfl }

private theorem qExpansion_levelOneEquiv {k : ℤ}
    (f : ModularForm ((Gamma1 1).map (mapGL ℝ)) k) :
    UpperHalfPlane.qExpansion 1 (levelOneEquiv f) =
      UpperHalfPlane.qExpansion 1 f := by
  rfl

private theorem qExpansion_levelOneEquiv_symm {k : ℤ}
    (f : ModularForm 𝒮ℒ k) :
    UpperHalfPlane.qExpansion 1 (levelOneEquiv.symm f) =
      UpperHalfPlane.qExpansion 1 f := by
  rfl

noncomputable def T {k : ℤ} (n : ℕ) [NeZero n] :
    Module.End ℂ (ModularForm 𝒮ℒ k) :=
  (levelOneEquiv (k := k)).conj (HeckeRing.GL2.heckeT_n (N := 1) k n)

private theorem mem_trivial_char {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    (levelOneEquiv (k := k)).symm f ∈
      HeckeRing.GL2.modFormCharSpace (N := 1) k
      (1 : (ZMod 1)ˣ →* ℂˣ) := by
  rw [HeckeRing.GL2.mem_modFormCharSpace_iff]
  intro d
  have hd : d = 1 := by
    ext
    simp
  subst hd
  simp [HeckeRing.GL2.diamondOpHom_apply]

/-!
The period-one q-expansion coefficient formula.  At level one the character
factor is trivial, so the general divisor-sum formula becomes

`a_m(T_n f) = ∑ d ∣ gcd(m,n), d^(k-1) a_(mn/d²)(f)`.
-/
theorem coeff_T {k : ℤ} (n : ℕ) [NeZero n]
    (f : ModularForm 𝒮ℒ k) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 (T n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : ℂ) ^ (k - 1) *
          (UpperHalfPlane.qExpansion 1 f).coeff (m * n / (d * d)) := by
  rw [T, LinearEquiv.conj_apply_apply, qExpansion_levelOneEquiv]
  rw [HeckeRing.GL2.fourierCoeff_heckeT_n_period_one (N := 1) k n
    (by simp) (1 : (ZMod 1)ˣ →* ℂˣ) (mem_trivial_char f) m]
  rw [qExpansion_levelOneEquiv_symm]
  simp

/-- For prime `p`, the divisor sum has only the terms `1` and, when `p ∣ m`, `p`.
This formula also holds for the constant coefficient `m = 0`. -/
theorem coeff_T_prime {k : ℤ} (p : ℕ) (hp : p.Prime)
    (f : ModularForm 𝒮ℒ k) (m : ℕ) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (UpperHalfPlane.qExpansion 1 (T p f)).coeff m =
      (UpperHalfPlane.qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (p : ℂ) ^ (k - 1) *
          (UpperHalfPlane.qExpansion 1 f).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [coeff_T]
  by_cases hdvd : p ∣ m
  · rw [Nat.gcd_eq_right hdvd, hp.divisors, Finset.sum_pair hp.one_lt.ne]
    simp only [Nat.cast_one, _root_.one_zpow, one_mul, Nat.div_one,
      Nat.mul_div_mul_right m p hp.pos, ite_eq_left hdvd]
    rw [Nat.mul_comm m p]
  · have hgcd : Nat.gcd m p = 1 :=
      (hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right m p)).resolve_right fun h ↦
        hdvd (h ▸ Nat.gcd_dvd_left m p)
    rw [hgcd, Nat.divisors_one, Finset.sum_singleton]
    simp [hdvd, Nat.mul_comm m p]

end HeckeOperator

namespace IntegerModularForm

private theorem qExpansion_carrier_coeff {k : ℤ}
    (f : IntegerModularForm k) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 f.carrier).coeff m = (f.coeff m : ℂ) := by
  rw [← ModularForm.qexp_eq', f.carrier_eq]
  rfl

/-- The integral divisor-sum coefficients of the Hecke operator. -/
noncomputable def heckeCoeff {k : ℤ} (n : ℕ) (f : IntegerModularForm k) (m : ℕ) : ℤ :=
  ∑ d ∈ (Nat.gcd m n).divisors,
    (d : ℤ) ^ Int.toNat (k - 1) * f.coeff (m * n / (d * d))

private noncomputable def TApply {k : ℤ} (n : ℕ) [NeZero n]
    (hk : 1 ≤ k) (f : IntegerModularForm k) : IntegerModularForm k where
  fourier := PowerSeries.mk (heckeCoeff n f)
  carrier := HeckeOperator.T n f.carrier
  carrier_eq := by
    rw [ModularForm.qexp_eq']
    apply PowerSeries.ext
    intro m
    rw [HeckeOperator.coeff_T, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    simp only [heckeCoeff, eq_intCast, Int.cast_sum, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro d hd
    rw [qExpansion_carrier_coeff, ← _root_.zpow_natCast,
      Int.toNat_of_nonneg (sub_nonneg.mpr hk)]

/-- The Hecke operator `T_n` on integral modular forms of positive weight.
The weight hypothesis is needed for this normalization to preserve integrality:
at weight zero, `T_p 1 = (1 + 1 / p) • 1` for prime `p`. -/
noncomputable def T {k : ℤ} (n : ℕ) [NeZero n] (hk : 1 ≤ k) :
    Module.End ℤ (IntegerModularForm k) where
  toFun := TApply n hk
  map_add' f g := by
    apply carrier_inj
    change HeckeOperator.T n (f.carrier + g.carrier) =
      HeckeOperator.T n f.carrier + HeckeOperator.T n g.carrier
    exact (HeckeOperator.T n).map_add _ _
  map_smul' c f := by
    apply carrier_inj
    change HeckeOperator.T n (c • f.carrier) = c • HeckeOperator.T n f.carrier
    exact ((HeckeOperator.T n).restrictScalars ℤ).map_smul c f.carrier

@[simp]
theorem carrier_T {k : ℤ} (n : ℕ) [NeZero n] (hk : 1 ≤ k)
    (f : IntegerModularForm k) :
    (T n hk f).carrier = HeckeOperator.T n f.carrier := rfl

@[simp]
theorem fourier_T {k : ℤ} (n : ℕ) [NeZero n] (hk : 1 ≤ k)
    (f : IntegerModularForm k) :
    (T n hk f).fourier = PowerSeries.mk (heckeCoeff n f) := rfl

@[simp]
theorem coeff_T {k : ℤ} (n : ℕ) [NeZero n] (hk : 1 ≤ k)
    (f : IntegerModularForm k) (m : ℕ) :
    (T n hk f).coeff m = heckeCoeff n f m := by
  change (PowerSeries.mk (heckeCoeff n f)).coeff m = heckeCoeff n f m
  rw [PowerSeries.coeff_mk]

theorem coeff_T_expanded {k : ℤ} (n : ℕ) [NeZero n] (hk : 1 ≤ k)
    (f : IntegerModularForm k) (m : ℕ) :
    (T n hk f).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : ℤ) ^ Int.toNat (k - 1) * f.coeff (m * n / (d * d)) :=
  coeff_T n hk f m

/-- The two-term coefficient formula for a prime Hecke operator on integral
modular forms, including the constant coefficient `m = 0`. -/
theorem coeff_T_prime {k : ℤ} (p : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (f : IntegerModularForm k) (m : ℕ) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (T p hk f).coeff m = f.coeff (p * m) +
      if p ∣ m then (p : ℤ) ^ Int.toNat (k - 1) * f.coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [coeff_T_expanded]
  by_cases hdvd : p ∣ m
  · rw [Nat.gcd_eq_right hdvd, hp.divisors, Finset.sum_pair hp.one_lt.ne]
    simp only [Nat.cast_one, _root_.one_pow, _root_.one_mul, Nat.div_one,
      Nat.mul_div_mul_right m p hp.pos, ite_eq_left hdvd]
    rw [Nat.mul_comm m p]
  · have hgcd : Nat.gcd m p = 1 :=
      (hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right m p)).resolve_right fun h ↦
        hdvd (h ▸ Nat.gcd_dvd_left m p)
    rw [hgcd, Nat.divisors_one, Finset.sum_singleton]
    simp [hdvd, Nat.mul_comm m p]

end IntegerModularForm
