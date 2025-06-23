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
    sorry



#check le_max_of_le_left
