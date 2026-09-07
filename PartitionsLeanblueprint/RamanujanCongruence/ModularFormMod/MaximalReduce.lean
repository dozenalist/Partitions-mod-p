import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basis
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Operators



/-
This file proves `exists_maximal_Reduce`
This file has 1 sorry
· `Reduce_of_reduce` (it is maybe unnecessary to assume this)
-/

namespace ModularFormMod

open IntegerModularForm

variable {ℓ : ℕ} [isLargePrime ℓ] {k : ZMod (ℓ - 1)}


theorem Reduce_of_reduce {m} {f : ModularFormMod ℓ k} [hf : NeZero f]
  {b : IntegerModularForm m} (hab : b.reduce ℓ = f.fourier) :
    ∃ h, f = Mcast h (Reduce ℓ b) := by sorry

theorem Filtration_congruence (f : ModularFormMod ℓ k) [NeZero f] : f.Filtration = k :=
  Reduce_of_reduce f.Filtration_choose_spec.symm |>.1


-- we can assume that the function that reduces to a ModularFormMod ℓ has the maximum ord possible
theorem exists_maximal_Reduce {j p} (f : ModularFormMod ℓ k)
  [hf : NeZero f] (hk : ∀ n < p, f.coeff n = 0) (haw : hasWeight j f) :
    ∃ b : IntegerModularForm j, ∃ hj : j = k,
      f = Mcast hj (Reduce ℓ b) ∧ ord b ≥ p := by

  obtain ⟨c, ceq⟩ := haw

  obtain ⟨hj, aeqcr⟩ := Reduce_of_reduce ceq


  obtain ⟨l, leq⟩ := exists_G_combo c

  have aeqc : ∀ n, f.coeff n = ↑(c.coeff n) := by
    simpa [PowerSeries.ext_iff, reduce, eq_comm, coeff_def] using ceq

  set b := ∑ c, (if ↑ℓ ∣ l c then 0 else l c) • IntegerModularForm.G c with beq

  have feqb : f = Mcast hj ((Reduce ℓ) b) := by
    ext n; simp [beq, aeqc, leq]
    simp only [← Int.coe_castRingHom, ← coeffLinearMap_apply, map_sum, map_smul]
    simp
    congr! with x -
    split_ifs with hdvd
    simp only [ZMod.intCast_zmod_eq_zero_iff_dvd _ _ |>.2 hdvd, MulZeroClass.zero_mul,
      IntegerModularForm.coeff_zero, Int.cast_zero]
    simp only [coeff_smulz, Int.zsmul_eq_mul, Int.cast_mul]

  use b, hj, feqb

  {
    apply PowerSeries.le_order
    intro i ilp
    norm_cast at ilp
    rw [IntegerModularForm.coeff_def, ← coeffLinearMap_apply, beq]
    simp [-coeffLinearMap_apply]
    simp

    apply Fintype.sum_eq_zero
    rintro ⟨x,xlt⟩
    split_ifs with hdvd
    · rw [IntegerModularForm.coeff_zero]

    simp only [coeff_smulz, Int.zsmul_eq_mul, mul_eq_zero]

    by_cases xlek : x < p
    {
      left
      induction x using Nat.strong_induction_on with

      | h x ih =>
        suffices l ⟨x,xlt⟩ = f.coeff x by
          rw [hk x xlek, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
          exact (hdvd this).elim

        simp_rw [aeqc, leq, ← coeffLinearMap_apply, map_sum, map_zsmul]
        simp



        trans (l ⟨x, xlt⟩ : ZMod ℓ) • ↑((IntegerModularForm.G ⟨x,xlt⟩).coeff ↑(⟨x,xlt⟩ : Fin (dim j)))
        rw [G_ord_G, Int.cast_one, smul_eq_mul, _root_.mul_one]

        simp; symm; apply Fintype.sum_eq_single
        rintro ⟨m, mlt⟩ mnx
        simp only [ne_eq, Fin.mk.injEq] at mnx
        rcases Nat.lt_or_lt_of_ne mnx with mlx | mgx
        suffices l ⟨m,mlt⟩ = (0 : ZMod ℓ) by rw [this, MulZeroClass.zero_mul]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        by_contra dvdm
        specialize ih m mlx mlt dvdm (by omega)
        exact ih ▸ dvdm <| Int.dvd_zero ↑ℓ

        rw [coeff_lt_ord, Int.cast_zero, MulZeroClass.mul_zero]
        rw [ord_G]; norm_cast
    }
    {
    right
    apply coeff_lt_ord
    simp only [ord_G]; norm_cast
    omega
    }

  }


theorem le_Filtration {p} (f : ModularFormMod ℓ k) [fn0 : NeZero f] (hk : ∀ n < p, f.coeff n = 0) :
    12 * p ≤ f.Filtration := by

  have fn0 := fn0.out

  have (j : ℤ) := exists_maximal_Reduce (j := j) f hk

  apply le_csInf (nonempty_hasWeight_set f) fun j jin => by

    obtain ⟨b, hb, hfb, hord⟩ := exists_maximal_Reduce f hk jin

    have bn0 : b ≠ 0 := by
      contrapose! fn0
      exact fourier_inj <| by rw [hfb, fn0, map_zero]; rfl

    contrapose! bn0

    apply coeff_trunc_injective <| funext fun ⟨n,nlt⟩ => by

      simp
      have : dim j ≤ p := by grind [dim]
      rw [coeff_lt_ord]
      have : n < p := by grind
      have : n < (p : ℕ∞) := by norm_cast
      grind







end ModularFormMod
