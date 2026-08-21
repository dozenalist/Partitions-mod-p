import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order


open PowerSeries Finset.HasAntidiagonal Finset Nat

namespace PowerSeries

variable {α : Type*}

lemma coeff_X_mul [Semiring α] (f : α ⟦X⟧) {n : ℕ} (npos : n > 0) :
    (coeff n) (X * f) = coeff (n - 1) f := by
  rw [coeff_mul]; trans ∑ p ∈ antidiagonal n, (coeff p.1) (X ^ 1) * (coeff p.2) f
  rw [pow_one]
  simp_rw [coeff_X_pow]; simp only [ite_mul, one_mul, zero_mul, sum_ite]
  simp only [sum_const_zero, add_zero]
  trans ∑ x ∈ {(1, n - 1)}, (coeff x.2) f
  congr; ext x; simp only [mem_filter, mem_antidiagonal, mem_singleton]
  constructor; rintro ⟨xsum, x1⟩; ext <;> dsimp
  exact x1; omega
  intro hx; simp_all only [gt_iff_lt, and_true]; exact add_sub_of_le npos
  rw [sum_singleton]

lemma coeff_sum_X_pow [Semiring α] {n N : ℕ} {a : ℕ → α} (h : n < N) :
    coeff n (∑ i ∈ range N, C (a i) * (X : α⟦X⟧) ^ i ) = a n := by
  simpa [map_sum, coeff_X_pow] using fun nle => (not_lt_of_ge nle h).elim


lemma coeff_sum_X_pow_mul [Semiring α] {n N ℓ : ℕ} [NeZero ℓ] {a : ℕ → α} (h : n < N) :
    (coeff n) (∑ i ∈ range N, C (a i) * X ^ (ℓ * i)) = if ℓ ∣ n then a (n / ℓ) else 0 := by

  simp [map_sum, coeff_X_pow]
  have ln0 : ℓ ≠ 0 := Ne.symm (NeZero.ne' ℓ)
  split_ifs with ldiv; obtain ⟨k, rfl⟩ := ldiv
  simp only [mul_eq_mul_left_iff, sum_ite]
  trans a k + 0; congr
  trans ∑ x ∈ {k}, a x
  congr; ext x; constructor <;> simp only [mem_filter, mem_range, mem_singleton, and_imp]
  intro xlN keqx
  simp_all only [or_false, ne_eq]
  intro xeqk; constructor
  have : x ≤ ℓ * x := Nat.le_mul_of_pos_left x <| pos_of_neZero ℓ
  exact trans this <| xeqk ▸ h
  left; exact xeqk.symm
  rw [sum_singleton]
  rw [sum_const_zero]
  rw [add_zero]; congr; exact Nat.eq_div_of_mul_eq_right ln0 rfl
  apply sum_eq_zero; intro x xlN
  rw [dvd_def] at ldiv; push Not at ldiv
  exact if_neg (ldiv x)

lemma coeff_int_cast [Ring α] (f : α ⟦X⟧) (n : ℕ) (k : ℤ) : (coeff n) ((k : α⟦X⟧) * f) = k * (coeff n) f := by
  trans (coeff n) (k • f); congr; exact (zsmul_eq_mul f k).symm
  trans k • (coeff n) f; rfl
  exact zsmul_eq_mul ((coeff n) f) k

lemma coeff_sum_squash [Semiring α] {j ℓ N M : ℕ} [NeZero ℓ] {a b : ℕ → α} (jlN : ℓ * j < N) (jlM : ℓ * j < M) :
  coeff (ℓ * j) ( (∑ i ∈ range N, (PowerSeries.C (a i)) * (X : α⟦X⟧) ^ i)
    * (∑ i ∈ range M, (PowerSeries.C (b i)) * (X : α⟦X⟧) ^ (ℓ * i)) )
      = ∑ ⟨x,y⟩ ∈ antidiagonal j, a (ℓ * x) * b y := by

  simp only [coeff_mul]

  have ln0 : ℓ ≠ 0 := Ne.symm (NeZero.ne' ℓ)

  have plN {p} (hp : p ∈ antidiagonal (ℓ * j)) : p.1 < N :=
    lt_of_le_of_lt (antidiagonal.fst_le hp) jlN

  have plM {p} (hp : p ∈ antidiagonal (ℓ * j)) : p.2 < M :=
    lt_of_le_of_lt (antidiagonal.snd_le hp) jlM

  calc
    _ = ∑ p ∈ antidiagonal (ℓ * j), a (p.1) * (if ℓ ∣ p.2 then b (p.2 / ℓ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp; congr
      rw [coeff_sum_X_pow (plN hp)]
      rw [coeff_sum_X_pow_mul (plM hp)]

    _ = ∑ p ∈ antidiagonal (ℓ * j) with ℓ ∣ p.2, a (p.1) * b (p.2 / ℓ) := by
      simp_rw [mul_ite, sum_ite, mul_zero, sum_const_zero, add_zero]

    _ = _ := by
      symm; apply Finset.sum_bij (fun x _ ↦ (ℓ * x.1, ℓ * x.2))
      intro p hp
      simp only [mem_filter, mem_antidiagonal, dvd_mul_right, and_true]
      trans ℓ * (p.1 + p.2); ring
      congr; exact mem_antidiagonal.mp hp
      intro p hp q hq heq
      ext; simp only [Prod.mk.injEq, mul_eq_mul_left_iff] at heq
      simp_all only [ne_eq, or_false]
      simp only [Prod.mk.injEq, mul_eq_mul_left_iff] at heq
      simp_all only [ne_eq, or_false]
      intro p hp
      simp only [mem_filter, mem_antidiagonal] at hp
      obtain ⟨psum, ldiv⟩ := hp
      have : ℓ ∣ p.1 := by rw [Nat.dvd_add_iff_left ldiv]; use j

      obtain ⟨ ⟨k, hk⟩, ⟨c, hc⟩ ⟩ := (⟨ldiv, this⟩ : And ..) -- lol
      use (c, k), by
        simp only [mem_antidiagonal]
        suffices ℓ * (c + k) = ℓ * j from (Nat.mul_right_inj ln0).mp this
        rwa [mul_add, ← hk, ← hc]
      ext <;> dsimp <;> symm <;> assumption
      intro p hp; congr; dsimp
      exact Nat.eq_div_of_mul_eq_right ln0 rfl


lemma coeff_mul_shift [CommSemiring α] {m N : ℕ} (f : ℕ → α ⟦X⟧) :
    X ^ m * ∑ i ∈ range N, f i * X ^ i = ∑ i ∈ Ico m (N + m), f (i - m) * X ^ i := by

  simp_rw [mul_sum, ← mul_assoc, mul_comm, mul_assoc, ← pow_add]
  apply sum_bij (fun i _ ↦ i + m)
  simp only [mem_range, mem_Ico, le_add_iff_nonneg_left, zero_le, true_and]
  intro a alN; exact Nat.add_lt_add_right alN _
  intro a alN b blN; exact (Nat.add_right_cancel ·)
  simp_all only [mem_Ico, mem_range]
  intro b bin
  use b - m, by omega
  exact Nat.sub_add_cancel bin.1
  simp only [mem_range]; intro a alN
  congr! 2; exact Nat.eq_sub_of_add_eq rfl
  ac_rfl


lemma coeff_mul_shift_of_zero [CommRing α] {m N : ℕ} (f : ℕ → α ⟦X⟧) (f0 : f 0 = 0) :
    X ^ m * ∑ i ∈ range N, f i * X ^ i = ∑ i ∈ range (N + m), f (i - m) * X ^ i := calc

  _ = ∑ i ∈ Ico m (N + m), f (i - m) * X ^ i := coeff_mul_shift f

  _ = (∑ i ∈ range (N + m), f (i - m) * X ^ i) - ∑ i ∈ range m, f (i - m) * X ^ i :=
    sum_Ico_eq_sub _ <| Nat.le_add_left m N

  _ = _ := by
    nth_rw 2 [← sub_zero (∑ i ∈ range (N + m), f (i - m) * X ^ i)]
    congr; apply sum_eq_zero; intro x xlm; trans 0 * X ^ x
    congr; rw[← f0]; apply congrArg; refine Nat.sub_eq_zero_of_le ?_
    exact le_of_lt <| List.mem_range.mp xlm
    rw[zero_mul]


@[norm_cast] lemma _root_.Polynomial.coe_prod [CommSemiring α] (m : ℕ) (f : ℕ → Polynomial α) :
    ∏ i ∈ range m, (f i : α ⟦X⟧) = ((∏ i ∈ range m, f i : Polynomial α) : α ⟦X⟧) := by
  induction m with
  | zero => simp only [range_zero, prod_empty, Polynomial.coe_one]
  | succ m ih => simp only [prod_range_succ, ih, Polynomial.coe_mul]


lemma coeff_zero_of_ndvd [CommRing α] {ℓ M k : ℕ} (ndvd : ¬ ℓ ∣ k) :
    coeff k (∏ i ∈ range M, (1 - (X : α ⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ) = 0 := by

  rw [coeff_prod]
  apply sum_eq_zero; intro x xin

  have exa : ∃ a ∈ range M, ¬ ℓ ∣ x a := by
    contrapose! xin
    simp only [mem_finsuppAntidiag, not_and_or]
    left; contrapose! ndvd; calc
    _ ∣ ∑ a ∈ range M, x a := by
      apply dvd_sum; exact xin
    _ = k := ndvd ▸ rfl

  obtain ⟨a, alt, nad⟩ := exa
  rw [prod_eq_zero]
  use alt
  rw[coeff_pow]
  apply sum_eq_zero; intro y yin

  have exb : ∃ a ∈ range ℓ, ¬ ℓ ∣ y a := by
    contrapose! yin
    simp only [mem_finsuppAntidiag, not_and_or]
    left; contrapose! nad; calc
    _ ∣ ∑ a ∈ range ℓ, y a := by
      apply dvd_sum; exact yin
    _ = x a := nad ▸ rfl

  obtain ⟨b, blt, nbd⟩ := exb

  rw [prod_eq_zero]
  use blt

  simp only [map_sub, coeff_one]
  split_ifs with yb0
  simp_all only [dvd_zero, not_true_eq_false]
  simp only [zero_sub, neg_eq_zero]
  rw [coeff_X_pow]; apply if_neg
  rw [dvd_def] at nbd; push Not at nbd
  exact nbd (a + 1)



lemma coeff_sum_eventually_zero [Semiring α] (m : ℕ) (f : ℕ → Polynomial α) :
    ∃ N : ℕ, ∀ n ≥ N, PowerSeries.coeff (R := α) n (∑ i ∈ range m, f i) = 0 := by
  simp only [ge_iff_le, map_sum, Polynomial.coeff_coe]
  set M := sup (range m) (Polynomial.natDegree ∘ f) with Meq
  use M + 1; intro n Mle
  apply sum_eq_zero; intro x xlm
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_; calc
    _ ≤ M := by
      have : (f x).natDegree = (Polynomial.natDegree ∘ f) x := rfl
      rw[Meq, this]; exact le_sup xlm
    _ < n := Mle

#check Eq.subst
lemma coeff_prod_eventually_zero [CommSemiring α] (m : ℕ) (f : ℕ → Polynomial α) :
    ∃ N, ∀ n ≥ N, coeff (R := α) n (∏ i ∈ range m, f i) = 0 := by
  simp only [ge_iff_le]
  set M := ∑ i ∈ range m, (f i).natDegree with Meq
  use M + 1; intro n Mle;
  trans coeff n (∏ i ∈ range m, f i : Polynomial α); congr
  apply Polynomial.coe_prod
  simp only [Polynomial.coeff_coe]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt; calc
    _ ≤ M := by rw[Meq]; exact Polynomial.natDegree_prod_le (range m) f
    _ < n := Mle


lemma prod_eq_sum (α) [CommRing α] (ℓ K : ℕ) [NeZero ℓ] : ∃ c : ℕ → α, ∃ M,
    (∏ i ∈ range K, (1 - (X : α ⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ) = ∑ i ∈ range M, C (c i) * X ^ (ℓ * i) := by

  have ln0 : ℓ ≠ 0 := Ne.symm (NeZero.ne' ℓ)

  set f : ℕ → Polynomial α := fun i ↦ (1 - (Polynomial.X) ^ (ℓ * (i+1))) ^ ℓ with feq

  obtain ⟨M, hM⟩ := coeff_prod_eventually_zero K f

  use fun i ↦ coeff (ℓ * i) (∏ i ∈ range K, (1 - (X : α ⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ), M
  ext i; simp only [map_sum, coeff_C_mul, coeff_X_pow]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases ldi : ℓ ∣ i
  obtain ⟨k, rfl⟩ := ldi
  simp_all only [mul_eq_mul_left_iff, or_false, sum_ite_eq, mem_range, left_eq_ite_iff, not_lt]
  intro lek

  trans (coeff (ℓ * k)) (∏ i ∈ range K, f i)
  simp only [feq, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
  have : ℓ * k ≥ M := by
    trans k; exact Nat.le_mul_of_pos_left k <| zero_lt_of_ne_zero ln0
    exact lek
  rw[feq]; dsimp; exact hM _ this

  trans 0; exact coeff_zero_of_ndvd ldi
  symm; apply sum_eq_zero; intro x xle
  apply if_neg; rw[dvd_def] at ldi; push Not at ldi
  exact ldi x


end PowerSeries
