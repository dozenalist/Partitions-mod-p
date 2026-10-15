import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Operators
import Mathlib.Data.Nat.Choose.Dvd

/-!
Background identities for the theta-binomial part of the Kiming--Olsson
argument.  These are kept independent of the KOl statement file so that the
formalization can be developed without introducing circular imports.
-/

namespace KOl

open scoped IntegerModularForm

variable {ell : ℕ} [isLargePrime ell] {k}

/-- Interior binomial coefficients in the row `ell - 1` alternate modulo
`ell`.  The proof is Pascal induction, using that `ell` divides every
interior coefficient in the row `ell`. -/
lemma choose_pred_eq_neg_pow (i : ℕ) (hi : i < ell) :
    (Nat.choose (ell - 1) i : ZMod ell) = (-1 : ZMod ell) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hi0 : i + 1 ≠ 0 := by omega
      have hdiv : ell ∣ Nat.choose ell (i + 1) := by
        exact Nat.Prime.dvd_choose_self (Fact.out : Nat.Prime ell) hi0 hi
      have hzero : (Nat.choose ell (i + 1) : ZMod ell) = 0 :=
        (ZMod.natCast_eq_zero_iff _ ell).2 hdiv
      have hpascal : Nat.choose ell (i + 1) =
          Nat.choose (ell - 1) (i + 1) + Nat.choose (ell - 1) i := by
        simpa [Nat.add_comm, Nat.sub_add_cancel (by omega : 1 ≤ ell)] using
          (Nat.choose_succ_succ (ell - 1) i)
      rw [hpascal] at hzero
      have hrec : (Nat.choose (ell - 1) (i + 1) : ZMod ell) =
          -(Nat.choose (ell - 1) i : ZMod ell) := by
        rw [Nat.cast_add] at hzero
        exact eq_neg_of_add_eq_zero_left hzero
      rw [hrec, ih (by omega), pow_succ]
      ring

/-- The coefficientwise binomial expansion used after clearing the negative
power of `q`.  The statement is deliberately coefficientwise: the project
represents modular forms by ordinary power series, while the paper uses a
Laurent-series notation. -/
lemma theta_binomial_coeff (f : ModularFormMod ell k) (a n m : ℕ) :
    (((n : ZMod ell) - a) ^ m) * f.coeff n =
      ∑ i ∈ Finset.range (m + 1),
        (Nat.choose m i : ZMod ell) *
          ((n : ZMod ell) ^ i * (-(a : ZMod ell)) ^ (m - i)) * f.coeff n := by
  rw [sub_pow]
  simp only [Finset.sum_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i ≤ m := by
    simp only [Finset.mem_range] at hi
    omega
  have hsign : (-1 : ZMod ell) ^ i * (-1 : ZMod ell) ^ m =
      (-1 : ZMod ell) ^ (m - i) := by
    calc
      (-1 : ZMod ell) ^ i * (-1 : ZMod ell) ^ m =
          (-1 : ZMod ell) ^ (i + m) := by rw [pow_add]
      _ = (-1 : ZMod ell) ^ ((m - i) + i + i) := by congr 1 <;> omega
      _ = (-1 : ZMod ell) ^ (m - i) *
          ((-1 : ZMod ell) ^ i * (-1 : ZMod ell) ^ i) := by
            rw [pow_add, pow_add]
            ring
      _ = (-1 : ZMod ell) ^ (m - i) := by
        have htwo : (-1 : ZMod ell) ^ (i + i) = 1 := by
          rw [show i + i = 2 * i by omega, pow_mul]
          norm_num
        rw [← pow_add, htwo, mul_one]
  rw [show (-a : ZMod ell) = (-1 : ZMod ell) * a by ring, mul_pow]
  rw [pow_add, hsign]
  ring

/-- The same identity with the coefficient of `Theta_pow i` exposed. -/
lemma theta_binomial_coeff_theta (f : ModularFormMod ell k) (a n m : ℕ) :
    (((n : ZMod ell) - a) ^ m) * f.coeff n =
      ∑ i ∈ Finset.range (m + 1),
        (Nat.choose m i : ZMod ell) *
          (f.Theta_pow i).coeff n * (-(a : ZMod ell)) ^ (m - i) := by
  rw [theta_binomial_coeff]
  simp only [ModularFormMod.coeff_Theta_pow, Nat.cast_pow, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end KOl
