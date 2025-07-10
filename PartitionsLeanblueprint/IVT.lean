import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option push_neg.use_distrib true

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

theorem convergesTo_add' (ha : convergesTo a L) (hb : convergesTo b K) :
convergesTo (λ n => a n + b n) (L + K) :=
    λ ε εpos =>
    let ⟨N1, hN1⟩ := ha (ε / 2) (div_pos εpos zero_lt_two)
    let ⟨N2, hN2⟩ := hb (ε / 2) (div_pos εpos zero_lt_two)
    ⟨ max N1 N2, λ n hn => calc
        _ = |(a n - L) + (b n - K)| := congr_arg abs (add_sub_add_comm (a n) (b n) L K)
        _ ≤ |a n - L| + |b n - K| := abs_add _ _
        _ < ε / 2 + ε / 2 :=
            add_lt_add (hN1 n (le_of_max_le_left hn)) (hN2 n (le_of_max_le_right hn))
        _ = ε := add_halves ε ⟩

#print convergesTo_add'  -- look at that small proof term


lemma convergesTo_nonneg (ha : convergesTo a L) (h : ∃ (N : ℕ), ∀ n ≥ N, a n ≥ 0) : L ≥ 0 := by
    unfold convergesTo at ha
    contrapose! ha
    use abs L
    constructor
    apply abs_pos_of_neg ha
    intro N1
    obtain ⟨N2, hN2⟩ := h
    use (max N1 N2)
    constructor
    apply le_max_left
    have h1 : a (max N1 N2) ≥ 0 := by
        apply hN2
        apply le_max_right
    nth_rewrite 2 [abs_eq_self.2]
    rw [abs_eq_neg_self.2]
    linarith
    exact le_of_lt ha
    linarith


theorem le_convergesTo_of_le (ha : convergesTo a L) (hb : convergesTo b K) (h : ∃ (N : ℕ), ∀ n ≥ N, a n ≤ b n) : L ≤ K := by
    let c n := b n + -1 * a n
    have hc : ∃ (N : ℕ), ∀ n ≥ N, c n ≥ 0:= by
        obtain ⟨N1, hN1⟩ := h
        use N1
        intro n hn
        simp [c]
        apply hN1
        exact hn
    suffices K - L ≥ 0 by linarith
    have c_limit : convergesTo c (K - L) := by
        apply convergesTo_add
        exact hb
        conv => rhs ; rw [neg_eq_neg_one_mul]
        apply convergesTo_scalar_mul
        exact ha
    apply convergesTo_nonneg c_limit hc




theorem exists_sup_of_bounded_above (S : Set ℝ) (h : bounded_above S) (nempty : ∃ x, x ∈ S) :
    ∃ y : ℝ, sup S y := sorry





theorem intermediate_value {f : ℝ → ℝ} {a b y: ℝ} (h : continuous f ) (hy : y ∈ Icc (f a) (f b)) (alb : a < b) :
∃ c ∈ Icc a b, f c = y := by
    have aa : a ∈ Icc a b := ⟨le_refl a, le_of_lt alb⟩
    have bb : b ∈ Icc a b := ⟨le_of_lt alb, le_refl b⟩

    -- Proving c ∈ Icc a b
    set K : Set ℝ := {x : ℝ | x ∈ Icc a b ∧ f x ≤ y} with hK
    have buK : bounded_above K := by use b; intro x xinK; exact xinK.1.2
    have nemptyK : ∃ x, x ∈ K := ⟨a, aa, hy.1⟩
    obtain ⟨c, hc⟩ := exists_sup_of_bounded_above K buK nemptyK
    have c_in_ab : c ∈ Icc a b := by
        constructor; apply hc.1; exact ⟨aa, hy.1⟩
        apply hc.2; intro z hz; exact hz.1.2
    use c; constructor; exact c_in_ab

    apply eq_of_le_of_le

    -- f c ≤ y
    by_contra! yltfc
    obtain ⟨δ, δpos, hδ⟩ := h c (f c - y) (by linarith)

    have aux : ∀ x ∈ K, x ≤ c - δ := by
        intro x xinK
        have : x ≤ c := hc.1 x xinK
        contrapose! xinK
        specialize hδ x (by apply abs_lt.2; constructor <;> linarith)
        have yltfx : y < f x := by
            apply abs_lt.1 at hδ; linarith
        contrapose! yltfx; exact yltfx.2

    specialize hδ (c - δ / 2) (by simp; apply abs_lt.2; constructor <;> linarith)

    have upper_bound_K : upper_bound K (c - δ / 2) := by
        intro x hx; specialize aux x hx; linarith
    have c_le_c_minus_delta : c ≤ c - δ / 2 := by apply hc.2; exact upper_bound_K
    linarith

    -- f c ≥ y
    contrapose! hc; unfold sup upper_bound; push_neg; left
    obtain ⟨δ, δpos, hδ⟩ := h c (y - f c) (by linarith)


    by_cases h' : c + δ / 2 ≤ b
    specialize hδ (c + δ / 2) (by simp; apply abs_lt.2; constructor <;> linarith)
    use (c + δ / 2); constructor
    constructor; constructor; linarith [c_in_ab.1]
    exact h'
    apply abs_lt.1 at hδ; linarith
    linarith

    push_neg at h'
    use b; constructor
    specialize hδ b (by apply abs_lt.2; constructor <;> linarith[c_in_ab.2])
    constructor; exact bb; apply abs_lt.1 at hδ; linarith
    apply lt_of_le_of_ne c_in_ab.2
    by_contra! ceqb
    have : f c = f b := by congr
    linarith [hy.2]

    -- not a great proof, could probably be made a lot cleaner
    -- didn't end up using the order limit theorem
    -- In fact, this proof uses no information about sequences at all


end theorems
