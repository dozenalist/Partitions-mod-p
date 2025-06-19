import Mathlib.Data.Real.Basic


def convergesTo (a : ℕ → ℝ) (L : ℝ) :=
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

def converges (a : ℕ → ℝ) :=
    ∃ L : ℝ, convergesTo a L
