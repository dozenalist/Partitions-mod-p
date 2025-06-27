import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def convergesTo (a : ℕ → ℝ) (L : ℝ) :=
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

def converges (a : ℕ → ℝ) :=
    ∃ L : ℝ, convergesTo a L

def Icc (a : ℝ) (b : ℝ) : Set ℝ :=
    { x | a ≤ x ∧ x ≤ b }


def upper_bound (S : Set ℝ) (M : ℝ) :=
    ∀ x ∈ S, x ≤ M

def bounded_above (S : Set ℝ) :=
    ∃ M : ℝ, upper_bound S M

def sup (S : Set ℝ) (y : ℝ) :=
  upper_bound S y ∧ ( ∀ (z : ℝ), upper_bound S z → y ≤ z )



def continuous (f : ℝ → ℝ) :=
    ∀ x ε, ε > 0 → ∃ δ > 0, ∀ y, |x - y| < δ → |f x - f y| < ε

def continuous' (f : ℝ → ℝ) :=
    ∀ (x : ℝ) (a : ℕ → ℝ), convergesTo a x → convergesTo (fun n ↦ f (a n)) (f x)


section theorems

variable {a b : ℕ → ℝ}
variable {L K c : ℝ}

theorem convergesTo_scalar_mul (h: convergesTo a L) :
convergesTo (fun n ↦ c * a n) (c * L) := by
    intro ε εpos
    rcases eq_or_ne c 0 with hc | hc
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


lemma convergesTo_nonneg (ha : convergesTo a L) (h : ∃ (N : ℕ), ∀ n ≥ N, a n ≥ 0) : L ≥ 0 := by
    sorry


theorem le_convergesTo_of_le (ha : convergesTo a L) (hb : convergesTo b K) (h : ∃ (N : ℕ), ∀ n ≥ N, a n ≤ b n) : L ≤ K := by
    sorry


theorem exists_sup_of_bounded_above (S : Set ℝ) (h : bounded_above S) :
    ∃ y : ℝ, sup S y := sorry





theorem intermediate_value {f : ℝ → ℝ} {a b y: ℝ} (h : continuous f ) (hy : y ∈ Icc (f a) (f b)) (alb : a < b) :
∃ c ∈ Icc a b, f c = y := by
    sorry
