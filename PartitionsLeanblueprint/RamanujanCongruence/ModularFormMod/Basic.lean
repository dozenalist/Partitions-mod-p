import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Defs
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basic


open ModularFormMod IntegerModularForm BigOperators

namespace ModularFormMod

variable {ℓ : ℕ} {k : ZMod (ℓ - 1)}

noncomputable def Delta : ModularFormMod ℓ 12 :=
  Mcast (Int.cast_ofNat _) <| (Δ).Reduce ℓ

scoped notation (priority := high) "Δ" => Delta


noncomputable def fl (ℓ) : ModularFormMod ℓ (δ ℓ * 12) :=
  Mcast (by rw [Int.cast_mul, Int.cast_natCast, Int.cast_ofNat])
    <| (IntegerModularForm.fl ℓ).Reduce ℓ

theorem coeff_Delta (n) : ((Δ).coeff n : ZMod ℓ) = IntegerModularForm.Delta.coeff n := rfl

theorem coeff_fl (n) : (fl ℓ).coeff n = (IntegerModularForm.fl ℓ).coeff n := rfl

theorem fl_eq_Delta_pow : fl ℓ = Delta.pow (δ ℓ) := ext fun _ => by
  simp only [coeff_fl, Delta, pow_Mcast, Reduce_pow, coeff_Mcast, coeff_Reduce]
  rfl

theorem Delta_eq_coeff_Product (n : ℕ) :
    (Δ).coeff n = (DeltaProduct (α := ZMod ℓ) n).coeff n := by
  simp only [coeff_Delta, IntegerModularForm.coeff_Delta, Int.cast_coeff_DeltaProduct]

theorem fl_eq_coeff_Product (n : ℕ) : (fl ℓ).coeff n = (flProduct ℓ n).coeff n := by
  simp only [coeff_fl, IntegerModularForm.coeff_fl, Int.cast_coeff_flProduct]



@[simp] theorem Delta_zero : (Δ).coeff 0 = (0 : ZMod ℓ) := by
  rw [coeff_Delta, IntegerModularForm.Delta_zero, Int.cast_zero]

@[simp] theorem Delta_one : (Δ).coeff 1 = (1 : ZMod ℓ) := by
  rw [coeff_Delta, IntegerModularForm.Delta_one, Int.cast_one]

@[simp] theorem Delta_two : (Δ).coeff 2 = (-24 : ZMod ℓ) := by
  rw [coeff_Delta, IntegerModularForm.Delta_two]; norm_cast

@[simp] theorem Delta_three : (Δ).coeff 3 = (252 : ZMod ℓ) := by
  rw [coeff_Delta, IntegerModularForm.Delta_three]; norm_cast

theorem fl_lt_delta {n : ℕ} (nlt : n < δ ℓ) : (fl ℓ).coeff n = 0 := by
  rw [coeff_fl, IntegerModularForm.fl_lt_delta nlt, Int.cast_zero]

@[simp] theorem fl_delta : (fl ℓ).coeff (δ ℓ) = 1 := by
  rw [coeff_fl, IntegerModularForm.fl_delta, Int.cast_one]

@[simp] theorem fl_delta_add_one [isLargePrime ℓ] : (fl ℓ).coeff (δ ℓ + 1) = 1 := by
  simp [coeff_fl]
