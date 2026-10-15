import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
The natural partition count used by the public integer partition function
and its generating-function lemmas.
-/

/-- The number of partitions of a natural number, including the empty partition. -/
def natpart (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

@[simp] lemma natpart_zero : natpart 0 = 1 := by
  unfold natpart
  rw [Fintype.card_unique]

