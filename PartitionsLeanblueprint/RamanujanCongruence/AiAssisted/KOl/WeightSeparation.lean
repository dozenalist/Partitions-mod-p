import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.ThetaBinomial
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.MaximalReduce

/-!
Weight-space separation and the prime-characteristic form of the theta
binomial expansion.  These lemmas are deliberately coefficientwise: the
Kiming--Olsson proof repeatedly compares forms which have the same Fourier
series but different weights.
-/

namespace KOl

open scoped IntegerModularForm

variable {ell : ℕ} [isLargePrime ell]

lemma weight_eq_of_coeff_eq {k j : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (g : ModularFormMod ell j)
    [NeZero f] (hcoeff : ∀ n : ℕ, f.coeff n = g.coeff n) :
    k = j := by
  apply ModularFormMod.Weight_eq_of_reduce_eq f g
  exact PowerSeries.ext hcoeff

lemma eq_zero_of_coeff_eq_of_weight_ne {k j : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (g : ModularFormMod ell j)
    (hweight : k ≠ j) (hcoeff : ∀ n : ℕ, f.coeff n = g.coeff n) :
    f = 0 ∧ g = 0 := by
  apply ModularFormMod.eq_zero_of_Weight_ne f g
  · exact PowerSeries.ext hcoeff
  · exact hweight

lemma prime_theta_binomial_coeff {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (a n : ℕ) :
    (((n : ZMod ell) - a) ^ (ell - 1)) * f.coeff n =
      ∑ i ∈ Finset.range ell,
        (-1 : ZMod ell) ^ i *
          (f.Theta_pow i).coeff n * (-(a : ZMod ell)) ^ (ell - 1 - i) := by
  rw [theta_binomial_coeff_theta]
  have hrange : ell - 1 + 1 = ell := by
    have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
    omega
  rw [hrange]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < ell := by
    simpa only [Finset.mem_range] using hi
  rw [choose_pred_eq_neg_pow i hil]

end KOl
