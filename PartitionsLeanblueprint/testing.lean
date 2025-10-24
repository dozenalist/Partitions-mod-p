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


inductive exis {α : Type} (p : α → Prop) where

  | intro (w : α) (hw : p w)






local notation "["a"]" => Function.const _ a

def gg : ℕ → Prop := [2 = 3]

open Function

def swip {α β χ} (f : α → β) (g : β → χ) (a : α) := g (f a)

infixl : 100 "<<|" => swip

def swap_comp {α β χ} (f : α → β) (g : β → χ) := g ∘ f

infixl : 100 "⊚" => swap_comp


lemma condo {p q : Prop} : (p → q) → ¬ q → ¬ p :=
  (· ⊚ · <| ·)

#check flip
#check ModularForm
