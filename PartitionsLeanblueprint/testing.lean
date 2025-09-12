import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ModularForms.Basic


-- variable {k : ℕ}
structure testb (k:ℕ) where
  a : ℕ

def add {k:ℕ} (x y : testb k) : testb k :=
  { a := x.a + y.a }

instance {k : ℕ} : Add (testb k) where
  add a b := add a b

variable {k1 : ℕ} {k2 : ℕ}
variable {a : testb (k1+k2)} {b : testb (k2+k1)}



open MatrixGroups

variable {Γ : Subgroup SL(2, ℤ)}
variable {a : ModularForm Γ 2} {b : ModularForm Γ (2 + 0)}

structure Multivector (α : Type*) (n : ℕ) where

  toMultiset : Multiset α

  card_toMultiset : toMultiset.card = n


lemma condor {p q : Prop} (h : p → q) : ¬ q → ¬ p := λ a a_1 ↦ a (h a_1)
