import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.BasicOperators
import PartitionsLeanblueprint.PowFacts

/- This file defines Delta and fl as integer modular forms in terms of their generating functions.
It defines the modular forms mod ℓ as their reductions mod ℓ,
and it proves some basic facts about these functions. -/



noncomputable section



open PowerSeries Finset ModularForm


variable {α : Type*} [CommRing α]


def delta (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24


def DeltaProduct (m : ℕ) : α ⟦X⟧ :=
  (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24


def flProduct (ℓ : ℕ) (m : ℕ) : α ⟦X⟧ :=
  (X : α⟦X⟧) ^ (delta ℓ) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ (24 * delta ℓ)


lemma DeltaProduct_apply (m : ℕ) :
  DeltaProduct m = (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24 := rfl

lemma flProduct_apply (ℓ : ℕ) (m : ℕ) :
  flProduct ℓ m = (X : α⟦X⟧) ^ (delta ℓ) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ (24 * delta ℓ) := rfl



lemma flProduct_eq_DeltaProduct_pow (ℓ : ℕ) : (flProduct ℓ : ℕ → α ⟦X⟧) = DeltaProduct ^ (delta ℓ) := by
  ext n : 1; simp_rw [flProduct, Pi.pow_apply, DeltaProduct, pow_mul, mul_pow, prod_pow]


@[simp] lemma map_DeltaProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (n : ℕ) :
    map g (DeltaProduct (α := R) n) = DeltaProduct (α := S) n := by
  simp only [DeltaProduct, map_mul, map_X, map_prod, map_pow, map_sub, map_one]

@[simp] lemma map_coeff_DeltaProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (k j : ℕ) :
    g ((coeff R k) (DeltaProduct j)) = (coeff S k) (DeltaProduct j) := by
  trans (coeff S k) (map g (DeltaProduct j)); rfl; rw [map_DeltaProduct]

@[simp, norm_cast] lemma Int.cast_coeff_DeltaProduct {S : Type*} [CommRing S] (k j : ℕ) :
    ((↑) : ℤ → S) ((coeff ℤ k) (DeltaProduct j)) = (coeff S k) (DeltaProduct j) := by
  trans (Int.castRingHom S) ((coeff ℤ k) (DeltaProduct j)); rfl; rw [map_coeff_DeltaProduct]


@[simp] lemma map_flProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (ℓ n : ℕ) :
    map g (flProduct (α := R) ℓ n) = flProduct (α := S) ℓ n := by
  simp only [flProduct_eq_DeltaProduct_pow, map_DeltaProduct, Pi.pow_apply, map_pow]

@[simp] lemma map_coeff_flProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (ℓ k j : ℕ) :
    g ((coeff R k) (flProduct ℓ j)) = (coeff S k) (flProduct ℓ j) := by
  trans (coeff S k) (map g (flProduct ℓ j)); rfl; rw [map_flProduct]

@[simp, norm_cast] lemma Int.cast_coeff_flProduct {S : Type*} [CommRing S] (ℓ k j : ℕ) :
    ((↑) : ℤ → S) ((coeff ℤ k) (flProduct ℓ j)) = (coeff S k) (flProduct ℓ j) := by
  trans (Int.castRingHom S) ((coeff ℤ k) (flProduct ℓ j)); rfl; rw [map_coeff_flProduct]


section Delta_coeff_le
omit [CommRing α]

open Finset.Nat Finset Nat


lemma coeff_X_mul [Semiring α] (f : α ⟦X⟧) {n : ℕ} (npos : n > 0) :
    (coeff α n) (X * f) = coeff α (n - 1) f := by
  rw [coeff_mul]; trans  ∑ p ∈ antidiagonal n, (coeff α p.1) (X ^ 1) * (coeff α p.2) f
  rw [pow_one]
  simp_rw [coeff_X_pow]; simp only [ite_mul, one_mul, zero_mul, sum_ite]
  simp only [sum_const_zero, add_zero]
  trans ∑ x ∈ {(1, n - 1)}, (coeff α x.2) f
  congr; ext x; simp only [mem_filter, mem_antidiagonal, mem_singleton]
  constructor; rintro ⟨xsum, x1⟩; ext <;> dsimp
  exact x1; omega
  intro hx; simp_all only [gt_iff_lt, and_true]; exact add_sub_of_le npos
  rw [sum_singleton]


lemma DeltaProduct_coeff_le [CommRing α] {n m j : ℕ} (nlm : n ≤ m) (mlj : m ≤ j) :
    (coeff α n) (DeltaProduct m) = (coeff α n) (DeltaProduct j) := by

  by_cases n0 : n = 0
  simp [DeltaProduct, n0]

  have npos : n > 0 := zero_lt_of_ne_zero n0
  simp only [DeltaProduct, coeff_X_mul _ npos];
  set k := n - 1 with keq; symm; calc
    _ = (coeff α k) ((∏ i ∈ Ico 0 m, (1 - X ^ (i + 1)) ^ 24) *
        (∏ i ∈ Ico m j, (1 - X ^ (i + 1)) ^ 24)) := by
      rw [prod_Ico_consecutive, Ico_zero_eq_range]
      exact Nat.zero_le m; exact mlj
    _ = _ := by
      rw [Ico_zero_eq_range, coeff_mul]

      have coeff_eq_ite {k : ℕ} (klt : k < m) :
          (coeff α k) (∏ i ∈ Ico m j, (1 - X ^ (i + 1)) ^ 24) = if k = 0 then 1 else 0 := by
        split_ifs with k0
        rw [k0]; simp

        rw [coeff_prod]; apply sum_eq_zero;
        intro x xin; rw [mem_finsuppAntidiag] at xin

        have exy : ∃ y ∈ Ico m j, x y ≠ 0 ∧ x y < m := by
          contrapose! xin

          intro sum_eq
          contrapose! sum_eq
          have fozer {k} (hk : x k ≠ 0) : k ∈ Ico m j := by
            have : k ∈ x.support := Finsupp.mem_support_iff.mpr hk
            exact sum_eq this

          by_cases ex : ∃ y, x y ≠ 0
          obtain ⟨y, yn0⟩ := ex
          have : y ≥ m := List.left_le_of_mem_range' (fozer yn0)
          apply Nat.ne_of_gt; calc
            _ < m := klt
            _ ≤ x y := xin y (fozer yn0) yn0
            _ ≤ _ := CanonicallyOrderedAddCommMonoid.single_le_sum (fozer yn0)


          push_neg at ex
          suffices (Ico m j).sum ⇑x = 0 by symm; rwa[this]
          exact sum_eq_zero (λ y _ ↦ ex y)

        obtain ⟨y, yin, xyn0, xylm⟩ := exy
        rw [prod_eq_zero]; use yin
        rw [coeff_pow]
        set f : ℕ → α := fun n ↦ (coeff α n) (1 - X ^ (y + 1)) with hf
        trans ∑ l ∈ (range 24).finsuppAntidiag (x y), ∏ i ∈ range 24, f (l i); rfl
        rw [finsuppAntidiag_to_antidiagonalTuple 24 (x y) f]
        rw [hf]; dsimp; apply sum_eq_zero; intro z zin
        rw [Nat.mem_antidiagonalTuple] at zin

        have exb : ∃ b, z b > 0 := by
          contrapose! zin
          have : ∑ i, z i = 0 := sum_eq_zero λ x _ ↦ eq_zero_of_le_zero (zin x)
          symm; rwa [this]
        obtain ⟨b, bn0⟩ := exb

        rw [prod_eq_zero]
        use mem_univ b
        have ble : z b < y := by

          have : z b ≤ ∑ i, z i := le_sum_fintype
          have : m ≤ y := by rw [mem_Ico] at yin; exact yin.1
          omega

        simp only [map_sub, coeff_one]; rw [if_neg (Nat.ne_of_gt bn0)]
        simp only [zero_sub, neg_eq_zero, coeff_pow]

        set f : ℕ → α := fun n ↦ (coeff α n) (X) with hf
        trans ∑ l ∈ (range (y + 1)).finsuppAntidiag (z b), ∏ i ∈ range (y + 1), f (l i); rfl
        rw [finsuppAntidiag_to_antidiagonalTuple _ _ f, hf]


        apply sum_eq_zero; intro x xsum
        have exc : ∃ c : Fin (y + 1), x c < 1 := by
          contrapose! xsum; rw[Nat.mem_antidiagonalTuple]
          push_neg; apply Nat.ne_of_gt;
          have : ∑ i : Fin (y + 1), 1 ≤ ∑ i, x i := sum_le_sum λ i _ ↦ xsum i
          simp only [sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
          omega

        obtain ⟨c, c0⟩ := exc; rw [lt_one_iff] at c0
        dsimp; rw [prod_eq_zero]
        use mem_univ c; rw[c0, coeff_zero_X]


      calc
        _ = ∑ p ∈ antidiagonal k, (coeff α p.1) (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24) *
            if p.2 = 0 then 1 else 0 := by
          congr! with p pin;

          have plt : p.2 < m := by
            have : p.2 ≤ k := antidiagonal.snd_le pin
            omega
          rw [coeff_eq_ite plt]
        _ =  ∑ x ∈ {(k,0)}, (coeff α x.1) (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24) := by
          simp only [mul_ite, mul_one, mul_zero, sum_ite, sum_const_zero, add_zero]
          congr with x; simp only [mem_filter, mem_antidiagonal, mem_singleton]
          simp_all only [gt_iff_lt, k]
          obtain ⟨fst, snd⟩ := x
          simp_all only [Prod.mk.injEq, and_congr_left_iff, add_zero, implies_true]

        _ = _ := by simp only [sum_singleton]

end Delta_coeff_le


namespace Integer

-- open either the Integer or Modulo namespace to use δ
scoped notation "δ" => delta


def Delta : IntegerModularForm 12 where

  sequence n := coeff ℤ n (DeltaProduct n)
  summable := sorry
  modular := sorry

/-- The integer modular form. Equal to Δ ^ (δ ℓ) -/
def fl (ℓ : ℕ) : IntegerModularForm (12 * δ ℓ) := Delta ** δ ℓ

/-- The integer modular form of weight 12. Defined by the coefficients of the DeltaProduct -/
scoped notation "Δ" => Delta


lemma Delta_apply (n : ℕ) : Δ n = coeff ℤ n (DeltaProduct n) := rfl

alias Delta_eq_coeff_Product := Delta_apply


lemma fl_apply {ℓ : ℕ} (n : ℕ) : fl ℓ n = coeff ℤ n (flProduct ℓ n) := by
  simp_rw [fl, flProduct_eq_DeltaProduct_pow, Ipow_apply, Pi.pow_apply,
      DeltaProduct, coeff_pow, ← DeltaProduct_apply]

  set f : ℕ → ℤ := fun m ↦ (coeff ℤ m) (DeltaProduct n) with hf
  trans ∑ x ∈ Nat.antidiagonalTuple (δ ℓ) n, ∏ y, f (x y)
  simp only [hf]; congr! with x xin y -
  exact DeltaProduct_coeff_le (le_refl _) <| le_antidiag_right xin y

  simp_rw [← finsuppAntidiag_to_antidiagonalTuple (δ ℓ) n f, hf]

alias fl_eq_coeff_Product := fl_apply



@[simp] lemma Delta_zero : Δ 0 = 0 := by
  rw [Delta_apply, coeff_zero_eq_constantCoeff, DeltaProduct,
    range_zero, prod_empty, mul_one, constantCoeff_X]

@[simp] lemma Delta_one : Δ 1 = 1 := by simp [Delta_apply, DeltaProduct]


open Finset.Nat


private lemma prod_q_image (q : Fin 24 → ℕ := fun x ↦ if x = 0 then 1 else 0)
  (qeq : q = fun x ↦ if x = 0 then 1 else 0) (q_zero : q 0 = 1)
      (q_ne_zero : ∀ {n : Fin 24}, n ≠ 0 → q n = 0) :
    ∏ m ∈ image q univ, (#{n | q n = m}).factorial = Nat.factorial 23 := by
  have : image q univ = {0, 1} := by
    ext a; rw[mem_insert, mem_singleton]; constructor <;> intro ha
    rw[mem_image] at ha
    obtain ⟨k,_,hk⟩ := ha
    by_cases k0 : k = 0
    right; rw[k0] at hk
    rwa [← hk]
    left; rw[← hk]
    exact q_ne_zero k0

    rw [mem_image]
    rcases ha with a0 | a1
    use 1; refine ⟨mem_univ _, ?_⟩
    rw [a0]; apply q_ne_zero; exact Ne.symm Fin.zero_ne_one
    use 0; exact ⟨mem_univ _, a1 ▸ q_zero⟩

  rw [this, prod_pair]; trans Nat.factorial 23 * 1
  congr; rw [qeq];
  simp only [Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false]
  simp_all only [Fin.isValue, ↓reduceIte, ne_eq, implies_true]
  rfl
  simp only [qeq, Fin.isValue, ite_eq_left_iff, zero_ne_one,
    imp_false, Decidable.not_not, Nat.factorial_eq_one]
  apply le_of_eq;
  simp_all only [Fin.isValue, ↓reduceIte, ne_eq, implies_true]
  rfl

  rfl
  exact Nat.zero_ne_one



@[simp] lemma Delta_two : Δ 2 = -24 := by

  rw [Delta_apply, DeltaProduct, coeff_succ_X_mul]; calc

    _ = (coeff ℤ 1) (∏ i ∈ insert 0 {1}, (1 - X ^ (i + 1)) ^ 24) := rfl

    _ = (coeff ℤ 1) (((1 - X - X ^ 2 + X ^ 3)) ^ 24) := by
      rw [prod_insert (by simp only [mem_singleton, zero_ne_one, not_false_eq_true])]
      rw [prod_singleton, zero_add, pow_one, ← mul_pow]; congr! 2; ring

    _ = ∑ x ∈ antidiagonalTuple 24 1, ∏ y,
        (coeff ℤ (x y)) (1 - X - X ^ 2 + X ^ 3) := by
      let f := (λ m ↦ (coeff ℤ m) (1 - X - X ^ 2 + X ^ 3))
      rw [coeff_pow, finsuppAntidiag_to_antidiagonalTuple 24 1 f]

    _ = -24 := by

      set q : (Fin 24) → ℕ := (if · = 0 then 1 else 0) with qeq

      have q_zero : q 0 = 1 := rfl
      have q_ne_zero {n} (h : n ≠ 0) : q n = 0 := if_neg h

      have Qadd : q ∈ antidiagonalTuple 24 1 := by
        rw [mem_antidiagonalTuple]
        calc
          ∑ i, q i = ∑ i ∈ univ \ { (0 : Fin 24) }, q i + ∑ i ∈ { (0 : Fin 24) }, q i := by
            symm; apply sum_sdiff; exact subset_univ {0}
          _ = 0 + 1 := by
            simp_all only [Fin.isValue, ↓reduceIte, ne_eq, implies_true, sum_ite_eq',
              mem_sdiff, mem_univ, mem_singleton, not_true_eq_false, and_false, zero_add, q]

      have unique_x {x} (xin : x ∈ antidiagonalTuple 24 1) : ∃! y, x y = 1 := by
        rw [mem_antidiagonalTuple] at xin
        unfold ExistsUnique; dsimp
        have ex1 : ∃ y, x y = 1 := by
          contrapose! xin
          by_cases h : ∀ y, x y = 0
          have : ∑ i, x i = 0 := sum_eq_zero λ y _ ↦ h y
          rw [this]; exact Nat.one_ne_zero.symm
          push_neg at h; obtain ⟨k, hk⟩ := h
          apply ne_of_gt
          have : 1 < x k := by specialize xin k; omega
          apply lt_of_lt_of_le this
          exact le_sum_fintype

        obtain ⟨y, yeq1⟩ := ex1
        use y, yeq1
        contrapose! xin; obtain ⟨z, zeq1, zny⟩ := xin
        have t1 : ∑ y ∈ {y, z}, x y + ∑ y ∈ univ \ {y, z}, x y = ∑ y, x y := by
          rw [add_comm, sum_sdiff]; exact subset_univ _
        have t2: 1 < x y + x z := by omega
        have t3: x y + x z = ∑ y ∈ {y, z}, x y := by
            rw[sum_pair]; symm; exact zny
        have t4 : ∑ y ∈ {y, z}, x y ≤ ∑ y ∈ {y, z}, x y + ∑ y ∈ univ \ {y, z}, x y :=
            Nat.le_add_right ..
        omega


      have equiv_q {x} (xin : x ∈ antidiagonalTuple 24 1) : perm_equiv x q := by
        {
          obtain ⟨k, hk, h⟩ := unique_x xin
          dsimp at h
          use Equiv.swap k 0
          ext i; dsimp;
          by_cases ik : i = k
          trans 1; rwa[ik]
          rw[ik]; trans q 0; rfl
          rw [Equiv.swap_apply_left]

          trans 0
          rw [mem_antidiagonalTuple] at xin; apply le_of_eq at xin
          contrapose! xin; rw[← Nat.pos_iff_ne_zero] at xin; calc
            1 < x k + x i := by omega
            x k + x i = ∑ y ∈ {k, i}, x y := by
              rw[sum_pair]; symm; exact ik
            ∑ y ∈ {k, i}, x y ≤ ∑ y ∈ {k, i}, x y + ∑ y ∈ univ \ {k, i}, x y :=
              Nat.le_add_right ..
            ∑ y ∈ {k, i}, x y + ∑ y ∈ univ \ {k, i}, x y = ∑ y, x y := by
              rw [add_comm, sum_sdiff]; exact subset_univ _

          by_cases i0 : i = 0
          trans q k;
          have : ¬ k = 0 := calc
            _ ≠ i := by symm; rwa[ne_eq]
            _ = 0 := i0
          symm; exact q_ne_zero this
          simp only [i0, Fin.isValue, Equiv.swap_apply_right]
          trans q i; symm; exact q_ne_zero i0
          symm; congr; exact Equiv.swap_apply_of_ne_of_ne ik i0
        }

      have eq_orbit : antidiagonalTuple 24 1 = orbit_finset q := by
        ext x; rw [orbit_equiv]; constructor <;> intro h
        exact (equiv_q h).symm
        rw [mem_antidiagonalTuple]; trans ∑ i, q i
        rw [sum_eq_of_perm_equiv h]; rwa [← mem_antidiagonalTuple]


      calc
        _ =  ∑ x ∈ antidiagonalTuple 24 1, ∏ y, (coeff ℤ (q y)) (1 - X - X ^ 2 + X ^ 3) := by
          congr! 1 with x xin
          set f : ℕ → ℤ := fun n ↦ (coeff ℤ n) (1 - X - X ^ 2 + X ^ 3)
          rw [prod_eq_of_perm_equiv (a := f) (equiv_q xin)]

        _ = ∑ x ∈ antidiagonalTuple 24 1, -1 := by
          apply sum_congr rfl; intro x xin
          calc
            _ = (coeff ℤ (q 0)) (1 - X - X ^ 2 + X ^ 3) *
                ∏ y ∈ univ \ {0}, (coeff ℤ (q y)) (1 - X - X ^ 2 + X ^ 3) := by
              rw[mul_comm]; apply prod_eq_prod_diff_singleton_mul (mem_univ _)

            _ = - 1 * ∏ y ∈ (@univ (Fin 24) _) \ {0}, 1 := by
              congr! with y yin
              simp only [q_zero, map_add, map_sub, coeff_one, one_ne_zero,
                  ↓reduceIte, coeff_one_X, zero_sub, coeff_X_pow,
                  OfNat.one_ne_ofNat, ↓reduceIte, sub_zero, add_zero]
              have ny0 : y ≠ 0 := by
                simp_all only [ne_eq, implies_true, mem_sdiff,
                  mem_univ, mem_singleton, true_and, not_false_eq_true]
              rw [q_ne_zero ny0]; simp



        _ = #(orbit_finset q) * -1 := by
          simp only [sum_neg_distrib, sum_const, nsmul_eq_mul, mul_one, mul_neg, eq_orbit]

        _ = ↑(24 : ℕ) * -1 := by
          clear! eq_orbit equiv_q unique_x Qadd
          rw [orbit_card]; congr
          suffices h : ∏ m ∈ image q univ, (#{n | q n = m}).factorial = (23).factorial by
            rw [h, Nat.div_eq_iff_eq_mul_left]; rw[Nat.factorial_succ]
            exact Nat.factorial_pos 23
            rw[Nat.factorial_succ 23]; exact Nat.dvd_mul_left _ _
          rw[prod_q_image]
          rfl; simp only [Fin.isValue, ↓reduceIte]
          intro n nn0
          exact if_neg nn0


        _ = -24 := by norm_num


lemma fl_lt_delta {ℓ n : ℕ} (nlt : n < δ ℓ) : fl ℓ n = 0 :=
  leading_Ipow_zeros Delta_zero nlt



@[simp] lemma fl_delta {ℓ : ℕ} : fl ℓ (δ ℓ) = 1 := by
  simp only [delta, fl, Ipow_apply]
  calc
    _ = ∑ x ∈ antidiagonalTuple ((ℓ ^ 2 - 1) / 24) ((ℓ ^ 2 - 1) / 24) \ {fun _ ↦ 1}, ∏ y, Δ (x y) +
    ∑ x ∈ {fun _ ↦ 1}, ∏ y, Δ (x y) := by
      apply Eq.symm (sum_sdiff _); intro x hx
      apply mem_antidiagonalTuple.2
      rw [mem_singleton] at hx
      rw[hx]; dsimp only
      rw[sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

    _ = 0 + 1 := by
      congr
      {
        apply sum_eq_zero; intro x hx
        apply prod_eq_zero_iff.2
        simp only [mem_sdiff, mem_singleton] at hx
        obtain ⟨hx, xn1⟩ := hx
        rw[mem_antidiagonalTuple] at hx
        apply le_of_eq at hx; contrapose! hx

        calc
          (ℓ ^ 2 - 1) / 24 = ∑ i : Fin ((ℓ ^ 2 - 1) / 24), 1 := by
            rw[sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
          _ < ∑ i, x i := by
            have xn0 : ∀ i, x i ≥ 1 := by
              simp_rw[Nat.one_le_iff_ne_zero]
              intro i; contrapose! hx
              use i, mem_univ i; rw[hx]; exact Delta_zero
            have : ∃ j, x j ≠ 1 := by
              contrapose! xn1; ext j; exact xn1 j
            obtain ⟨j, jn1⟩ := this
            have jg2 : x j ≥ 2 := by
              apply (Nat.two_le_iff (x j)).2
              exact ⟨Nat.one_le_iff_ne_zero.1 (xn0 j), jn1⟩
            calc
            _ = ∑ i ∈ univ \ {j}, 1 + 1 :=
              sum_eq_sum_diff_singleton_add (mem_univ j) _

            _ < ∑ i ∈ univ \ {j}, x i + x j := by
              apply add_lt_add_of_le_of_lt
              exact sum_le_sum (λ i hi ↦ xn0 i)
              exact jg2
            _ = _ := (sum_eq_sum_diff_singleton_add (mem_univ j) _).symm
      }
      simp only [sum_singleton, prod_const, card_univ, Fintype.card_fin]
      rw[Delta_one]; exact one_pow _



end Integer


namespace Modulo

scoped notation (priority := high) "δ" => delta


variable {ℓ k j : ℕ} [NeZero ℓ]

lemma Reduce_congr  {f g : IntegerModularForm k} (h : f = g) : Reduce f ℓ = Reduce g ℓ :=
  h ▸ rfl


@[simp] lemma Reduce_add (f g : IntegerModularForm k) : Reduce (f + g) ℓ = Reduce f ℓ + Reduce g ℓ := by
  ext n; simp only [Reduce_apply, Integer.add_apply, Int.cast_add, add_apply]

@[simp] lemma Reduce_mul (f : IntegerModularForm k) (g : IntegerModularForm j) :
    Reduce (f * g) ℓ = Mcongr (by norm_cast) (Reduce f ℓ * Reduce g ℓ) := by
  ext n; simp only [Reduce_apply, Integer.mul_apply, Int.cast_sum, Int.cast_mul, cast_eval, mul_apply]



lemma Reduce_cast_swap (a : IntegerModularForm k) (h : k = j) :
    Reduce (Integer.Icongr h a) ℓ = Mcongr (by rw [h]) (Reduce a ℓ) := by
  ext n; simp only [Reduce_apply, Integer.cast_eval, cast_eval]

lemma Reduce_pow (g : IntegerModularForm k) (j : ℕ) :
    Reduce (Integer.Ipow g j) ℓ = Mcongr (by norm_cast) ((Reduce g ℓ) ** j) := by

  induction' j with j ih
  ext n
  cases n <;> simp
  ext n
  simp only [cast_eval, Integer.cast_eval, Integer.Ipow_succ, Mpow_succ, Reduce_cast_swap,
      cast_eval, Reduce_mul, ih, mul_apply, Integer.mul_apply, Reduce_apply, cast_eval]


@[simp] lemma Reduce_pow_apply (g : IntegerModularForm k) (j n : ℕ) :
    Reduce (Integer.Ipow g j) ℓ n = ((Reduce g ℓ) ** j) n := by
  rw [Reduce_pow, cast_eval]




def Delta : ModularFormMod ℓ 12 := Reduce Integer.Delta ℓ


-- maybe change the weight to drop the Mcongr? but then we lose fl_eq_Delta
/-- The modular form mod ℓ. Equal to Δ ^ (δ ℓ) -/
def fl (ℓ : ℕ) [NeZero ℓ] : ModularFormMod ℓ (12 * δ ℓ) := Mcongr (by norm_cast) (Reduce (Integer.fl ℓ) ℓ)


-- when both Modulo and Integer are opened, Δ refers to Modulo.Delta
/- if you open Integer, then Modulo, you can use Delta to refer to Integer.Delta
and Δ for Modulo.Delta, so that's cool I guess -/
/-- The modular form mod ℓ of weight 12. The reduction of Integer.Delta -/
scoped notation (priority := high) "Δ" => Delta


theorem fl_eq_Delta : fl ℓ = Δ ** δ ℓ := by
  ext n; rw [fl, Delta, Integer.fl, cast_eval, Reduce_pow_apply]


theorem Delta_apply (n : ℕ) : Δ n = (Integer.Delta n : ZMod ℓ) := by
  rw [Delta, Reduce_apply]

theorem Delta_eq_coeff_Product (n : ℕ) : Δ n = coeff (ZMod ℓ) n (DeltaProduct n) := by
  rw [Delta_apply, Integer.Delta_apply]; norm_cast


theorem fl_apply (n : ℕ) : fl ℓ n = (Integer.fl ℓ n : ZMod ℓ) := by
  rw [fl, cast_eval, Reduce_apply]

theorem fl_eq_coeff_Product (n : ℕ) : fl ℓ n = coeff (ZMod ℓ) n (flProduct ℓ n) := by
  rw [fl_apply, Integer.fl_apply]; norm_cast


lemma Delta_zero : Δ 0 = (0 : ZMod ℓ) := by
  rw[Delta, Reduce_apply, Integer.Delta_zero]; norm_cast

lemma Delta_one : Δ 1 = (1 : ZMod ℓ) := by
  rw[Delta, Reduce_apply, Integer.Delta_one]; norm_cast

lemma Delta_two : Δ 2 = (-24 : ZMod ℓ) := by
  rw[Delta, Reduce_apply, Integer.Delta_two]; norm_cast


lemma fl_lt_delta {n : ℕ} (nlt : n < δ ℓ) : fl ℓ n = 0 := by
  rw [fl_eq_Delta, leading_Mpow_zeros Delta_zero nlt]

@[simp] lemma fl_delta : fl ℓ (δ ℓ) = 1 := by
  rw [fl_apply, Integer.fl_delta, Int.cast_one]


end Modulo


end section
