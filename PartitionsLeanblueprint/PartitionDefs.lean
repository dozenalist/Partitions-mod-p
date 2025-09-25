import Mathlib.Data.Multiset.Basic
import Mathlib.Combinatorics.Enumerative.Partition
import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.PrimaryLemmas


/- The goal of this file is to define the partition function and ramanujan congruences,
and to ultimately prove that if there exists a ramanujan congruence mod ℓ then fℓ|𝓤 = 0 -/

open Nat

def partition (n : ℕ) : ℕ :=
  Fintype.card (Partition n)


def ramanujan_congruence' (ℓ β : ℕ) : Prop :=
  ∀ n, ℓ ∣ partition (ℓ*n - β)


lemma ramanujan_congruence_unique (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    ∃ β, ramanujan_congruence' ℓ β → ramanujan_congruence' ℓ (δ ℓ) := by
  sorry

abbrev ramanujan_congruence ℓ := ramanujan_congruence' ℓ (δ ℓ)


variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]


theorem TheBigOne [Fact (ℓ ≥ 13)] : ¬ ramanujan_congruence ℓ := sorry


theorem fl_U_zero : ramanujan_congruence ℓ → f ℓ |𝓤 = 0 := sorry
