import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def convergesTo (a : ℕ → ℝ) (L : ℝ) :=
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

def converges (a : ℕ → ℝ) :=
    ∃ L : ℝ, convergesTo a L

section theorems

variable {a b : ℕ → ℝ}
variable {L K c : ℝ}

theorem convergesTo_scalar_mul (h: convergesTo a L) :
convergesTo (fun n ↦ c * a n) (c * L) := by
    intro ε εpos
    by_cases hc : c = 0
    use 0; intro n hn; rw[hc]; simp; exact εpos
    obtain ⟨N, hN⟩ := h (ε / |c|) (by apply div_pos εpos (abs_pos.2 hc))
    use N; intro n hn; dsimp
    calc
        |c * a n - c * L| = |c| * |a n - L| := by rw[← mul_sub, abs_mul]
        _ < |c| * (ε / |c|) :=
            mul_lt_mul' (le_refl _) (hN n hn) (by apply abs_nonneg) (abs_pos.2 hc)
        _ = ε := by field_simp


theorem convergesTo_add (ha : convergesTo a L) (hb : convergesTo b K) :
convergesTo (fun n ↦ a n + b n) (L + K) := by
    intro ε ε_pos
    dsimp
    obtain ⟨N1, hN1⟩ := ha (ε / 2) (div_pos ε_pos zero_lt_two)
    obtain ⟨N2, hN2⟩ := hb (ε / 2) (div_pos ε_pos zero_lt_two)
    use (max N1 N2)
    intro n hn
    have hn1 : n ≥ N1 := le_of_max_le_left hn
    have hn2 : n ≥ N2 := le_of_max_le_right hn
    calc
    |a n + b n - (L + K)| = |(a n - L) + (b n - K)| := by
        ring_nf
    |(a n - L) + (b n - K)| ≤ |a n - L| + |b n - K| := by
        apply abs_add
    |a n - L| + |b n - K| < ε / 2 + ε / 2 :=
        add_lt_add (hN1 n hn1) (hN2 n hn2)
    ε / 2 + ε / 2 = ε := by
        ring



#check le_max_of_le_left
