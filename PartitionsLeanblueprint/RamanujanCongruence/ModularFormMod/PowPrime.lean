import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Defs
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic



open PowerSeries

theorem FiniteField.PowerSeries_expand_card {K : Type*} [Fintype K] [Field K] (f : K⟦X⟧) :
    expand (Fintype.card K) NeZero.out f = f ^ (Fintype.card K) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  simp_rw [hn, ← MvPowerSeries.map_iterateFrobenius_expand p NeZero.out, iterateFrobenius_eq_pow,
    FiniteField.frobenius_pow hn, RingHom.one_def, MvPowerSeries.map_id]
  rfl


namespace PowerSeries.ZMod

variable (p : ℕ) [Fact (Nat.Prime p)]

instance : CharP ((ZMod p) ⟦X⟧) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).mpr <|
    show C _ = 0 by rw [CharP.cast_eq_zero, map_zero]

theorem expand_card (f : PowerSeries (ZMod p)) :
    f.expand p NeZero.out = f ^ p := by
  simpa only [ZMod.card p] using FiniteField.PowerSeries_expand_card f


theorem coeff_pow_card  (f : PowerSeries (ZMod p)) (n) :
    (f ^ p).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  rw [← expand_card, coeff_expand]

end PowerSeries.ZMod

namespace ModularFormMod

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {k j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k)


theorem coeff_pow_Prime (n) : (f.pow ℓ).coeff n = if ℓ ∣ n then f.coeff (n / ℓ) else 0 := by
  simp only [coeff_def, fourier_pow, ZMod.coeff_pow_card]

@[simp] theorem coeff_pow_Prime_of_dvd (n) : (f.pow ℓ).coeff (ℓ * n) = f.coeff n := by
  rw [coeff_pow_Prime, if_pos ⟨n, rfl⟩, ← Nat.eq_div_of_mul_eq_right NeZero.out rfl]

theorem coeff_pow_Prime_of_not_dvd {n} (h : ¬ ℓ ∣ n) : (f.pow ℓ).coeff n = 0 :=
  coeff_pow_Prime f n ▸ if_neg h
