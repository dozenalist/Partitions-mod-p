import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.Defs
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basic

/-!
# Basic p-integral modular forms

This file transports the integral discriminant and Eisenstein series to the
localization of `ℤ` at `(p)`. Their Fourier coefficients are viewed in that
localization through its canonical map from `ℤ`.
-/

open PowerSeries ModularForm UpperHalfPlane MatrixGroups

namespace PIntegralModularForm

variable {p : ℕ} [Fact p.Prime]

noncomputable section

/-- Regard an integer modular form as a modular form with p-integral
Fourier coefficients. -/
def ofInteger {k : ℤ} (f : IntegerModularForm k) : PIntegralModularForm p k where
  fourier := PowerSeries.map (algebraMap ℤ (CoeffRing p)) f.fourier
  carrier := f.carrier
  carrier_eq := by
    apply PowerSeries.ext
    intro n
    rw [← ModularForm.qexp_eq' f.carrier, f.carrier_eq,
      PowerSeries.coeff_map, PowerSeries.coeff_map]
    simp [toComplex]

@[simp]
theorem coeff_ofInteger {k : ℤ} (f : IntegerModularForm k) (n : ℕ) :
    (ofInteger (p := p) f).coeff n = algebraMap ℤ (CoeffRing p) (f.coeff n) := by
  simp [ofInteger, coeff, PowerSeries.coeff_map]

/-- The p-integral discriminant form of weight 12. -/
def Delta : PIntegralModularForm p 12 := ofInteger (p := p) IntegerModularForm.Delta

@[simp]
theorem coeff_Delta (n : ℕ) :
    (Delta (p := p)).coeff n = algebraMap ℤ (CoeffRing p) (IntegerModularForm.Delta.coeff n) := by
  simp [Delta]

@[simp]
theorem Delta_zero : (Delta (p := p)).coeff 0 = 0 := by
  simp [IntegerModularForm.Delta_zero]

@[simp]
theorem Delta_one : (Delta (p := p)).coeff 1 = 1 := by
  simp [IntegerModularForm.Delta_one]

@[simp]
theorem Delta_two : (Delta (p := p)).coeff 2 = -24 := by
  simp [IntegerModularForm.Delta_two]

@[simp]
theorem Delta_three : (Delta (p := p)).coeff 3 = 252 := by
  simp [IntegerModularForm.Delta_three]

/-- The p-integral lift of the (integrally scaled) Eisenstein series of
weight `k`. For weights whose Bernoulli denominator is a p-adic unit, this
can be rescaled to the usual normalized Eisenstein series. -/
def Eis (k : ℤ) : PIntegralModularForm p k :=
  ofInteger (p := p) (IntegerModularForm.Eis k)

@[simp]
theorem coeff_Eis {k : ℤ} (hk : 3 ≤ k) (hk2 : Even k) (n : ℕ) :
    (Eis (p := p) k).coeff n =
      algebraMap ℤ (CoeffRing p)
        (if n = 0 then ((2 * k / bernoulli k.toNat).den : ℤ)
         else -(2 * k / bernoulli k.toNat).num * ArithmeticFunction.sigma (k.toNat - 1) n) := by
  rw [Eis, coeff_ofInteger]
  rw [IntegerModularForm.coeff_Eis hk hk2]

end
end PIntegralModularForm
