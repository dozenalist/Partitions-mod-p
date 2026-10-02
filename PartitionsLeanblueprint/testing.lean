import Mathlib







#check riemannZeta

variable (p) [Fact (Nat.Prime p)]

#synth ExpChar (PowerSeries (ZMod p))



local notation "["a"]" => Function.const _ a

def gg : ℕ → Prop := [2 = 3]

open Function

def swip {α β χ} (f : α → β) (g : β → χ) (a : α) := g (f a)

infixl : 100 "<<|" => swip

def swap_comp {α β χ} (f : α → β) (g : β → χ) := g ∘ f

infixl : 100 "⊚" => swap_comp


lemma condo {p q : Prop} : (p → q) → ¬ q → ¬ p :=
  (· ⊚ · <| ·)



infixl:15 " › " => Trans.trans

lemma transin {a b c d e f : ℕ} (h1 : a ≤ b) (h2 : b < c)
    (h3 : c ≤ d) (h4 : d ≤ e) (h5 : e < f) : a < f :=
  h1 › h2 › h3 › h4 › h5

lemma bla (n) : n ≡ 3 [MOD 3] := by
  mod_cases n % 3 <;> sorry

theorem wrong (α : Prop) : α := sorry



-- theorem SignClass.eq_one_or_neg_one (a : SignClass) : a = ⟦1⟧ ∨ a = ⟦-1⟧ := by
  -- obtain ⟨k, rfl⟩ := Quotient.exists_rep a
  -- rcases lt_trichotomy (k : ℝ) 0 with h | h | h
  -- · right
  --   apply Quotient.sound
  --   change k * -1 > (0 : ℝ)
  --   linarith
  -- · exact k.ne_zero h |>.elim
  -- · left 
  --   apply Quotient.sound
  --   change k * 1 > (0 : ℝ)
  --   linarith
