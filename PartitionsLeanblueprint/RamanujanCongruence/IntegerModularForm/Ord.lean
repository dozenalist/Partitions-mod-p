import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basic

/- This file defines ord, the order of vanishing of an Integer Modular Form,
as the order of its fourier expansion, and proves some basic facts about it.
This file is sorry-free. -/

noncomputable section ord
namespace IntegerModularForm

open PowerSeries

variable {k j : ℤ} (f : IntegerModularForm k) (g : IntegerModularForm j)


abbrev ord {k} (f : IntegerModularForm k) : ℕ∞ := f.fourier.order

@[simp] theorem ord_zero : ord (0 : IntegerModularForm k) = ⊤ := order_zero

@[simp] theorem ord_one : ord (1 : IntegerModularForm 0) = 0 := order_one

@[simp] theorem ord_mul : ord (f.mul g) = ord f + ord g := order_mul _ _

@[simp] theorem ord_pow (m) : ord (f.pow m) = m • ord f := order_pow _ _

theorem le_ord_smul (c : ℤ) : ord f ≤ ord (c • f) := le_order_smul

theorem coeff_lt_ord (f : IntegerModularForm k) {m : ℕ} (hm : m < ord f) : f.coeff m = 0 :=
  coeff_of_lt_order m hm

@[simp] theorem ord_eq_zero : ord f = 0 ↔ f.coeff 0 ≠ 0 := by
  simp [ord, ← coeff_def]
  contrapose!
  exact order_ne_zero_iff_constCoeff_eq_zero


theorem ord_eq_ord (h : ∀ n, f.coeff n = 0 ↔ g.coeff n = 0) : ord f = ord g := by

  by_cases h0 : f.fourier = 0
  ·
    have hg0 : g.fourier = 0 := by
      ext n
      simp
      rw [← h n, ← coeff_def, h0, map_zero]
    simp only [ord, h0, hg0]
  ·
    have hg0 : g.fourier ≠ 0 := by
      intro hg
      apply h0
      ext n
      simp
      rw [h n, ← coeff_def, hg, map_zero]

    simp only [ord, order, dif_neg h0, dif_neg hg0]
    congr
    exact funext (propext <| h · |>.not)



@[simp] theorem ord_smul (c : ℤ) [NeZero c] : ord (c • f) = ord f :=
  ord_eq_ord _ _ fun n => by
    simpa only [coeff_smulz, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
      using (NeZero.out · |>.elim)

@[simp] theorem ord_Delta : ord Δ = 1 := by
  rw [← Nat.cast_one, order_eq_nat]
  simp only [coeff_def, Delta_one, ne_eq, one_ne_zero, not_false_eq_true, Order.lt_one_iff,
    forall_eq, Delta_zero, and_self]

theorem ord_Eis (hk : 3 ≤ k) (hk2 : Even k) : ord (Eis k) = 0 := by
  rw [← Nat.cast_zero, order_eq_nat]
  simp only [coeff_def, Eis_zero hk hk2, ne_eq, one_ne_zero, not_false_eq_true, not_lt_zero,
    IsEmpty.forall_iff, implies_true, and_self]

@[simp] theorem ord_Eis_four : ord (Eis 4) = 0 :=
  ord_Eis (by decide) (by decide)

@[simp] theorem ord_Eis_six : ord (Eis 6) = 0 :=
  ord_Eis (by decide) (by decide)

@[simp] theorem ord_Icast (h : k = j) : ord (Icast h f) = ord f := rfl


open Finset in
theorem coeff_mul_ord (n m : ℕ) (hn : ord f = n) (hm : ord g = m) :
    (f.mul g).coeff (n + m) = f.coeff n * g.coeff m := by
  rw [coeff_mul]
  calc

  _ = ∑ x ∈ antidiagonal (n + m) \ {(n, m)},
    f.coeff (x.1) * g.coeff (x.2) + f.coeff n * g.coeff m := by simp

  _ = 0 + f.coeff n * g.coeff m := by
    congr; apply Finset.sum_eq_zero fun x hx => ?_
    simp only [mem_sdiff, mem_antidiagonal, mem_singleton] at hx
    obtain ⟨xsum, xne⟩ := hx
    have : x.1 ≠ n ∨ x.2 ≠ m := by contrapose! xne; exact Prod.ext_iff.mpr xne
    have : x.1 < n ∨ x.2 < m := by omega
    rcases this with h | h
    · have : x.1 < f.ord := by rw [hn]; norm_cast
      rw [← coeff_def, coeff_of_lt_order _ this, MulZeroClass.zero_mul]
    · have : x.2 < g.ord := by rw [hm]; norm_cast
      rw [← coeff_def x.2, coeff_of_lt_order _ this, MulZeroClass.mul_zero]

  _ = _ := zero_add _


-- clean up the grinds
theorem coeff_mul_ord_add_one {n m : ℕ} (hn : ord f = n) (hm : ord g = m) :
    (f.mul g).coeff (n + m + 1) = f.coeff (n + 1) * g.coeff m + g.coeff (m + 1) * f.coeff n := by
  set f' := PowerSeries.mk fun i => f.coeff (n + i) with f'eq
  set g' := PowerSeries.mk fun i => g.coeff (m + i) with g'eq
  simp only [PowerSeries.ext_iff, coeff_mk] at *
  nth_rw 3 [← add_zero n]
  nth_rw 2 [← add_zero m]
  simp only [← f'eq, ← g'eq]
  simp [← PowerSeries.coeff_one_mul, ← coeff_def]
  trans ((PowerSeries.mk fun i ↦ coeff (n + i) f) * (PowerSeries.mk fun i ↦ coeff (m + i) g)).coeff 1
  simp [PowerSeries.coeff_mul]
  trans ∑ p ∈ (Finset.antidiagonal (n + m + 1)).filter fun p => (p.1 ≥ n ∧ p.2 ≥ m), coeff p.1 f * coeff p.2 g
  apply Eq.symm <| Finset.sum_filter_of_ne fun x xin => by

    contrapose!
    intro a
    have : x.1 < n ∨ x.2 < m := by grind
    rcases this with h | h
    rw [coeff_lt_ord f, MulZeroClass.zero_mul]
    rw [hn]; norm_cast
    rw [coeff_lt_ord g, MulZeroClass.mul_zero]
    rw [hm]; norm_cast



  apply Finset.sum_bij fun a _ => (a.1 - n, a.2 - m)

  simp; grind
  simp; grind
  simp; intro a b h
  use a + n, b + m; grind
  simp; intro a b h na mb
  grind

  grind
