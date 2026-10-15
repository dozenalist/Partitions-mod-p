import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.Statements
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.ThetaBinomial

/-!
The Laurent-series step in Proposition 3, expressed using ordinary power
series.  The paper writes `q⁻ᵃ f` and applies `Theta^(ell-1)`; after
multiplication by `qᵃ`, its coefficient at `qⁿ` is exactly the shifted theta
coefficient used in `shiftedThetaSeries`.
-/

namespace KOl

open scoped IntegerModularForm

variable {ell : ℕ} [isLargePrime ell]

noncomputable def thetaBinomialSeries {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (a : ℕ) : PowerSeries (ZMod ell) :=
  PowerSeries.mk fun n =>
    ∑ i ∈ Finset.range ell,
      (Nat.choose (ell - 1) i : ZMod ell) *
        (f.Theta_pow i).coeff n * (-(a : ZMod ell)) ^ (ell - 1 - i)

lemma shiftedThetaSeries_eq_thetaBinomial {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (a : ℕ) :
    shiftedThetaSeries f a = thetaBinomialSeries f a := by
  apply PowerSeries.ext
  intro n
  simp only [shiftedThetaSeries, thetaBinomialSeries, PowerSeries.coeff_mk]
  have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
  have hrange : ell = ell - 1 + 1 := by omega
  have hrangeFin : Finset.range ell = Finset.range (ell - 1 + 1) := by
    exact congrArg Finset.range hrange
  rw [hrangeFin]
  exact theta_binomial_coeff_theta f a n (ell - 1)

end KOl
