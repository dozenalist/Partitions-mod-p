import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.BasicOperators
import PartitionsLeanblueprint.PowFacts

/- The Goal of this file is to define E₄ and E₆, and to prove that
the space of Modular Forms Mod ℓ of weight 12ℓ + k' has a ZMod ℓ basis of the form
(E₄^a * E₆^b) * { (E₄^3)^ℓ , (E₄^3)^(ℓ - 1) * Δ , ... , (E₄^3) * Δ^(ℓ - 1) , Δ^ℓ } -/
-- this is worded poorly. sorry



noncomputable section



open PowerSeries Finset ModularForm

-- def δ (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24
-- -- δℓ ?

-- -- The series expansion of ∏ n, (1-q^n)
-- def Etaish (n : ℕ) : ZMod ℓ :=

--     if h : (∃ m : ℤ, n = m * (3*m - 1) / 2)
--       then
--         let m := Classical.choose h
--         (-1) ^ m
--       else 0


-- def Delta : ModularFormMod ℓ 12 where

--   sequence
--     | 0 => 0
--     | n + 1 => (Sequencepow Etaish 24) n

--   modular := sorry


-- notation "Δ" => Delta


-- def f (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)] : ModularFormMod ℓ (12 * δ ℓ) := Δ ** δ ℓ
-- -- or fℓ : ModularFormMod ℓ (((ℓ^2 - 1)/2) : ℕ) := Mcongr (Δ ** δ ℓ) (by sorry)

variable {α : Type*} [CommRing α]

def DeltaProduct (m : ℕ) : α ⟦X⟧ :=
  (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24


def delta (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24

@[simp] lemma DeltaProduct_apply (n : ℕ) :
  DeltaProduct n = (X : α⟦X⟧) * ∏ i ∈ range n, (1 - X ^ (i + 1)) ^ 24 := rfl


@[simp] lemma DeltaProduct_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (n : ℕ) :
    map g (DeltaProduct (α := R) n) = DeltaProduct (α := S) n := by
  simp only [DeltaProduct_apply, map_mul, map_X, map_prod, map_pow, map_sub, map_one]

@[simp] lemma DeltaProduct_coeff_cast {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (k j : ℕ) :
    g ((coeff R k) (DeltaProduct j)) = (coeff S k) (DeltaProduct j) := by
  trans (coeff S k) (map g (DeltaProduct j : R⟦X⟧))
  rfl; rw [DeltaProduct_map]


namespace Integer

scoped notation "δ" => delta


def Delta : IntegerModularForm 12 where

  sequence n := coeff ℤ n (DeltaProduct n)
  summable := sorry
  modular := sorry


def fl (ℓ : ℕ) : IntegerModularForm (12 * δ ℓ) := Delta ** δ ℓ


scoped notation "Δ" => Delta


lemma Delta_apply (n : ℕ) : Δ n = coeff ℤ n (DeltaProduct n) := rfl

lemma fl_apply {ℓ : ℕ} (n : ℕ) : fl ℓ n = (Δ ** (δ ℓ)) n := rfl



lemma Delta_zero : Δ 0 = 0 := by
  rw [Delta_apply, coeff_zero_eq_constantCoeff, DeltaProduct,
    range_zero, prod_empty, mul_one, constantCoeff_X]

lemma Delta_one : Δ 1 = 1 := by
  simp [Delta_apply]


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



lemma Delta_two : Δ 2 = -24 := by

  rw [Delta_apply, DeltaProduct_apply, coeff_succ_X_mul]; calc

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

@[simp] lemma Reduce_pow (g : IntegerModularForm k) (j : ℕ) :
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
def fl (ℓ : ℕ) [NeZero ℓ] : ModularFormMod ℓ (12 * δ ℓ) := Mcongr (by norm_cast) (Reduce (Integer.fl ℓ) ℓ)


-- when both Modulo and Integer are opened, Δ refers to Modulo.Delta
/- if you open Integer, then Modulo, you can use Delta to refer to Integer.Delta
and Δ for Modulo.Delta, so that's cool I guess -/
scoped notation (priority := high) "Δ" => Delta


theorem fl_eq_Delta : fl ℓ = Δ ** δ ℓ := by
  ext n; rw [fl, Delta, Integer.fl, cast_eval, Reduce_pow_apply]


theorem Delta_apply (n : ℕ) : Δ n = coeff (ZMod ℓ) n (DeltaProduct n) := by
  rw [Delta, Reduce_apply, Integer.Delta_apply]
  exact DeltaProduct_coeff_cast (Int.castRingHom (ZMod ℓ)) n n



lemma Delta_zero : Δ 0 = (0 : ZMod ℓ) := by
  rw[Delta, Reduce_apply, Integer.Delta_zero]; norm_cast

lemma Delta_one : Δ 1 = (1 : ZMod ℓ) := by
  rw[Delta, Reduce_apply, Integer.Delta_one]; norm_cast

lemma Delta_two : Δ 2 = (-24 : ZMod ℓ) := by
  rw[Delta, Reduce_apply, Integer.Delta_two]; norm_cast



end Modulo


end section
