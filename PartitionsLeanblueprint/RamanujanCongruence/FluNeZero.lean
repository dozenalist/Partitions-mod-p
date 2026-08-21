import PartitionsLeanblueprint.RamanujanCongruence.Partition
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Basic
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Operators
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.PowPrime







open ModularFormMod hiding coeff
open PowerSeries Finset Nat
open scoped IntegerModularForm


noncomputable section

theorem flu_eq_zero {ℓ} [hℓ : isLargePrime ℓ] :
    ramanujan_congruence ℓ → (fl ℓ).UOp = 0 := fun h => ext fun n => by

  simp only [ModularFormMod.coeff_UOp, fl_eq_coeff_Product, map_zero]

  have lg5 : ℓ ≥ 5 := hℓ.AtLeastFive
  have lsq : ℓ ^ 2 ≥ 25 := by
    trans 5 * 5; rw [sq]; gcongr; rfl

  set g : ℕ → Polynomial (ZMod ℓ) :=
    fun n => Polynomial.X ^ (δ ℓ) * (∏ i ∈ range n, (1 - Polynomial.X ^ (i + 1)) ^ (ℓ ^ 2)) with geq

  obtain ⟨ m, goeq ⟩ := partitionProduct_mul_eq_natpart_sum (ℓ * n) g

  letI M := max m (ℓ * n + 1)
  have mleM : m ≤ M := by simp only [M, le_sup_left]

  have elnltM : ℓ * n < M := by simp only [← succ_le_iff, M, le_sup_right]

  have g_coe_rw : (X : (ZMod ℓ)⟦X⟧) ^ δ ℓ * ∏ i ∈ range M,
      (1 - (X : (ZMod ℓ) ⟦X⟧) ^ (i + 1)) ^ ℓ ^ 2 = ↑(g M) := by
    simp only [geq, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, ← Polynomial.coe_prod, mul_eq_mul_left_iff,
        pow_eq_zero_iff', X_ne_zero, ne_eq, false_and, or_false]
    congr; ext1 i; simp only [Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_pow, Polynomial.coe_X]

  calc

  _ = coeff (R := ZMod ℓ) (ℓ * n) (flProduct ℓ M) := by
    rw [flProduct_coeff_le elnltM.le <| le_refl _]


  _ = (coeff (ℓ * n) )
      (X ^ (δ ℓ) * ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2 - 1)) := by
    rw [flProduct]; congr! 4; exact twentyfour_mul_delta ℓ

  _ = (coeff (ℓ * n))
      ( X ^ (δ ℓ) * (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
      (partitionProduct M) ) := by
    rw[mul_assoc]; congr
    trans ∏ i ∈ range M, ( (↑1 - X ^ (i + 1)) ^ (ℓ ^ 2) * (↑1 - X ^ (i + 1))⁻¹ )
    {
      congr; ext1 i;

      refine (PowerSeries.eq_mul_inv_iff_mul_eq ?_).mpr ?_
      simp only [map_sub, constantCoeff_one, map_pow, constantCoeff_X]
      rw [zero_pow <| succ_ne_zero i, sub_zero]; exact Ne.symm (zero_ne_one' (ZMod ℓ))
      nth_rw 2 [← pow_one (1 - X ^ (i + 1))]; rw [mul_comm, pow_mul_pow_sub]
      exact NeZero.one_le
    }
    exact prod_mul_distrib

  _ = (coeff (R := ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
      ( X ^ (δ ℓ) * ∑ i ∈ range M, (natpart i) * (X : (ZMod ℓ) ⟦X⟧) ^ i ) ) := by
    rw [g_coe_rw, goeq M mleM, ← g_coe_rw]; ring_nf

  _ = (coeff (R := ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range M, ((↑1 - X ^ (ℓ * (i + 1))) ^ ℓ) ) *
      (X ^ (δ ℓ) * ∑ i ∈ range M, (natpart i) * (X : (ZMod ℓ) ⟦X⟧) ^ i) ) := by
    congr; ext1 i
    trans ((1 - X ^ (i + 1)) ^ ℓ) ^ ℓ
    rw[pow_two, pow_mul]
    congr
    rw [sub_pow_expChar_of_commute ℓ, one_pow, ← pow_mul, mul_comm]
    exact Commute.one_left _


  _ = (coeff (R := ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range M, ((↑1 - X ^ (ℓ * (i + 1))) ^ ℓ) ) *
      (X ^ (δ ℓ) * ∑ i ∈ range M, (partition i) * (X : (ZMod ℓ) ⟦X⟧) ^ i) ) := by
    simp only [PowerSeries.coeff_mul]; apply sum_congr rfl
    simp only [mem_antidiagonal, mul_eq_mul_left_iff, Prod.forall]
    intro a b addb
    by_cases ldiva : ℓ ∣ a
    {
      have ldivb : ℓ ∣ b := by
        suffices ℓ ∣ a + b from (Nat.dvd_add_iff_right ldiva).mpr this
        use n
      left; apply sum_congr rfl
      simp only [mem_antidiagonal, mul_eq_mul_left_iff, Prod.forall]
      intro c d cadd
      by_cases ceq : c = δ ℓ
      {
        left
        have rw1 (x) : (natpart x : (ZMod ℓ)⟦X⟧) = C (R := ZMod ℓ) (natpart x) := rfl
        have rw2 (x) : (partition x : (ZMod ℓ)⟦X⟧) = C (R := ZMod ℓ) (partition x) := rfl
        have dlM : d < M := by calc
          d ≤ c + d := Nat.le_add_left d c
          _ ≤ ℓ * n := cadd ▸ addb ▸ (Nat.le_add_left b a)
          _ < M := elnltM

        have nldivc : ¬ ℓ ∣ c := by
          rw[ceq]; exact not_dvd_delta ℓ
        have nldivd : ¬  ℓ ∣ d := by
          contrapose! nldivc
          suffices ℓ ∣ c + d from (Nat.dvd_add_iff_left nldivc).mpr this
          rwa[cadd]
        have dn0 : ¬ d = 0 := by
          contrapose! nldivd; rw[nldivd]; exact dvd_zero ℓ

        simp only [rw1, rw2, coeff_sum_X_pow dlM, natpart_of_ne_zero dn0]
      }

      right; rw[coeff_X_pow, if_neg ceq]
    }

    right; exact coeff_zero_of_ndvd ldiva


  _ = (coeff (R := ZMod ℓ) (ℓ * n))
      ((∏ i ∈ range M, (1 - X ^ (ℓ * (i + 1))) ^ ℓ) *
      ∑ i ∈ range (M + δ ℓ), C (partition (i - δ ℓ) : ZMod ℓ) * X ^ i) := by
    simp_rw [ppart_eq, coeff_mul_shift_of_zero ppart ppart_zero]
    congr; ext1 i; rw[← ppart_eq]; rfl

  _ = 0 := by
    obtain ⟨c, L, heq⟩ := prod_eq_sum (ZMod ℓ) ℓ M
    simp_rw [heq, ← smul_eq_C_mul, apart_eq]

    rw [mul_comm (∑ i ∈ range L, (c i) • X ^ (ℓ * i))]

    set c' : ℕ → (ZMod ℓ) := fun i ↦ if i < L then c i else 0 with hc'
    have c'rw : ∑ i ∈ range L,  (c i) • X (R := ZMod ℓ) ^ (ℓ * i) =
        ∑ i ∈ range (L + (ℓ * n + 1)), (c' i) • X ^ (ℓ * i) := by
      rw[sum_range_add, ← add_zero (∑ i ∈ range L, (c i) • X ^ (ℓ * i))]
      congr 1; apply sum_congr rfl; intro i ilM; congr
      rw[hc']; simp_all only [mem_range, if_pos]
      symm; apply sum_eq_zero; intro i ilm
      suffices c' (L + i) = 0 by simp only [this, zero_smul]
      simp only [add_lt_iff_neg_left, not_lt_zero, reduceIte, c']

    simp_rw [c'rw, smul_eq_C_mul]
    rw [coeff_sum_squash]

    simp only [← apart_eq]; apply sum_eq_zero
    intro x hx
    have : ↑(partition (ℓ * x.1 - δ ℓ)) = (0 : ZMod ℓ) :=
      (ZMod.natCast_eq_zero_iff ..).mpr <| h x.1

    rw [this, MulZeroClass.zero_mul]
    exact Nat.lt_add_right (δ ℓ) elnltM
    exact Nat.lt_add_left L <| Nat.le_refl _


end section
