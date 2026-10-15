import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.Statements

/-!
Elementary coefficient bridges for the K--O partition notation.  The main
theorems use divisibility in `ℕ`, whereas modular-form arguments use the
coefficient map into `ZMod ell`; these lemmas isolate that conversion.
-/

namespace KOl

open scoped IntegerModularForm

variable {ell a : ℕ}

lemma congruenceAt_iff_zmod (ha : a < ell) :
    congruenceAt ell a ↔
      ∀ n : ℕ, (partition (ell * (n : ℤ) + a) : ZMod ell) = 0 := by
  constructor
  · intro h n
    exact (ZMod.natCast_eq_zero_iff (partition (ell * (n : ℤ) + a)) ell).2
      (h n)
  · intro h n
    apply (ZMod.natCast_eq_zero_iff (partition (ell * (n : ℤ) + a)) ell).1
    exact h n

lemma congruenceAt_zero_false {ell : ℕ} (hell : 1 < ell) :
    ¬ congruenceAt ell 0 := by
  intro h
  have h0 := h 0
  have : ell = 1 := by simpa using h0
  omega

lemma congruenceAt_pos_of_congruenceAt {ell a : ℕ}
    (hell : 1 < ell) (h : congruenceAt ell a) (ha : a < ell) : 0 < a := by
  by_contra ha0
  have : a = 0 := Nat.eq_zero_of_not_pos ha0
  subst a
  exact congruenceAt_zero_false hell h

end KOl
