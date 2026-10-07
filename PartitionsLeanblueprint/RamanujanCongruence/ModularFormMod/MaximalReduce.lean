import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basis
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Operators
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.Reduce_of_reduce



/-
This file proves `exists_maximal_Reduce`
This file is sorry-free
-/

namespace ModularFormMod

open IntegerModularForm

variable {ℓ : ℕ} [hℓ : isLargePrime ℓ] {k j : ZMod (ℓ - 1)}


theorem Reduce_of_reduce {m} {f : ModularFormMod ℓ k} [hf : NeZero f]
  {b : IntegerModularForm m} (hab : b.reduce ℓ = f.fourier) :
    ∃ h, f = Mcast h (Reduce ℓ b) :=
  PIntegralModularForm.SwD.Reduce_of_reduce hab

-- nice proof
theorem Filtration_congruence (f : ModularFormMod ℓ k) [NeZero f] : f.Filtration = k :=
  Reduce_of_reduce f.Filtration_choose_spec.symm |>.1

theorem Weight_eq_of_reduce_eq (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j)
    [hf: NeZero f] (h : f.fourier = g.fourier) : k = j := by
  obtain ⟨a, ha, -, -⟩ := f.Exists_reduce
  obtain ⟨b, hb, g', hg'⟩ := g.Exists_reduce
  have := h ▸ hg'
  rwa [← Reduce_of_reduce this |>.1]

theorem eq_zero_of_Weight_ne (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j)
    (h : f.fourier = g.fourier) (hne : k ≠ j) : f = 0 ∧ g = 0 := by
  contrapose! +distrib hne
  obtain fn0 | gn0 := hne
  · exact @Weight_eq_of_reduce_eq _ _ k j f g ⟨fn0⟩ h
  · exact @Weight_eq_of_reduce_eq _ _ j k g f ⟨gn0⟩ h.symm |>.symm


theorem exists_Reduce (f : ModularFormMod ℓ k) : ∃ j : ℤ, ∃ hj : j = k,
    ∃ g : IntegerModularForm j, f = Mcast hj (g.Reduce ℓ) := by
  by_cases f0 : f = 0
  · use k.cast, by simp, 0, by simp [f0]
  obtain ⟨j, hj, g, hg⟩ := f.Exists_reduce
  obtain ⟨hj', h⟩ := Reduce_of_reduce hg (hf := ⟨f0⟩)
  use j, hj, g, h

open PIntegralModularForm in
theorem exists_Reduce_PIntegralModularForm (f : ModularFormMod ℓ k) :
  ∃ j : ℤ, ∃ hj : j = k,
    ∃ g : PIntegralModularForm ℓ j, f = g.Reduce.Mcast hj := by
  obtain ⟨j, hj, g, hg⟩ := f.exists_Reduce
  use j, hj, ofInteger g, by rw [Reduce_ofInteger, hg]




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


theorem exists_maximal_Reduce' {p} (f : ModularFormMod ℓ k)
  [hf : NeZero f] (hk : ∀ n < p, f.coeff n = 0) :
    ∃ b : IntegerModularForm f.Filtration, ∃ _hb : NeZero b,
      f = Mcast f.Filtration_congruence (Reduce ℓ b) ∧ ord b ≥ p := by
  obtain ⟨b, hb, feq, bord⟩ := f.exists_maximal_Reduce hk f.Filtration_spec
  use b, ⟨fun b0 => by
    simp only [b0, map_zero, Mcast_zero] at feq;
    exact hf.out.elim feq⟩



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


theorem Filtration_nonneg (f : ModularFormMod ℓ k) : 0 ≤ f.Filtration := by
  by_cases f0 : f = 0
  · rw [f0, Filtration_zero]
  · trans 12 * (0 : ℕ) ; rfl
    exact le_Filtration (fn0 := ⟨f0⟩) _ fun n nlt => n.not_lt_zero.elim nlt


theorem Filtration_add (f g : ModularFormMod ℓ k) :
    Filtration (f + g) ≤ max f.Filtration g.Filtration := by

  wlog hf : f.Filtration ≤ g.Filtration
  · simpa only [add_comm, max_comm] using this g f (by lia)

  by_cases! h : f = 0 ∨ g = 0 ∨ f + g = 0
  · rcases h with h | h | h <;> simp [h, Filtration_nonneg]

  have : NeZero (f + g) := ⟨h.2.2⟩
  have : NeZero f := ⟨h.1⟩
  have : NeZero g := ⟨h.2.1⟩

  apply Filtration_le
  simp_all
  have h'filt := f.Filtration_congruence.trans g.Filtration_congruence.symm
  have : ∃ m : ℕ, g.Filtration = f.Filtration + m * (ℓ - 1 : ℕ) := by
      have := ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _ |>.1 h'filt
      obtain ⟨m, hm⟩ := this
      lift m to ℕ using by
        have lpos : (ℓ - 1 : ℕ) > (0 : ℤ) := by grind [hℓ.AtLeastFive]
        have : (ℓ - 1 : ℕ) * m ≥ 0 := by grind
        exact Int.nonneg_of_mul_nonneg_right this lpos
      use m, by grind

  obtain ⟨m, hm⟩ := this
  use g.Filtration_choose + (f.Filtration_choose.mul ((El ℓ).pow m)).Icast hm.symm
  rw [map_add, reduce_Icast, reduce_mul, reduce_El_pow, _root_.mul_one,
    ← f.Filtration_choose_spec, ← g.Filtration_choose_spec, fourier_add, add_comm]


theorem Filtration_sub (f g : ModularFormMod ℓ k) :
    Filtration (f - g) ≤ max f.Filtration g.Filtration := by
  rw [sub_eq_add_neg, ← Filtration_neg g]
  exact Filtration_add _ _


theorem Filtration_mul (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j) :
    (f.mul g).Filtration ≤ f.Filtration + g.Filtration := by
  by_cases! h : f = 0 ∨ g = 0 ∨ f.mul g = 0
  · have fn := f.Filtration_nonneg
    have gn := g.Filtration_nonneg
    rcases h with h | h | h <;>
    simp [h, Filtration_nonneg]
    grind

  exact Filtration_le (fn0 := ⟨h.2.2⟩) ⟨f.Filtration_choose.mul g.Filtration_choose,
    by simp only [reduce_mul, ← Filtration_choose_spec, fourier_mul]⟩


-- sturm bound mod ℓ
theorem sturm_bound {f g : ModularFormMod ℓ k} (m : ℤ) (hf : f.Filtration ≤ m)
    (hg : g.Filtration ≤ m) (h : ∀ n ≤ m.toNat / 12, f.coeff n = g.coeff n) : f = g := by

  rw [← sub_eq_zero]
  simp_rw [← sub_eq_zero (a := coeff _ f), ← map_sub] at h
  by_contra hne
  have : NeZero (f - g) := ⟨hne⟩
  obtain ⟨F,Fn0,b,c⟩ := exists_maximal_Reduce' (f - g) (hf := ⟨hne⟩) fun n nlt => h n <| n.lt_succ_iff.mp nlt
  have filtsub : (f - g).Filtration ≤ max f.Filtration g.Filtration := by
    rw [sub_eq_add_neg]
    apply (Filtration_add _ _).trans
    rw [Filtration_neg]
  have : (f - g).Filtration ≤ m := by
    trans m
    apply filtsub.trans
    simpa using ⟨hf, hg⟩
    rfl

  have : dim (f - g).Filtration ≤ m.toNat / 12 + 1 := by
    apply (dim_le_div_twelve _).trans
    have : m ≥ 0 := (Filtration_nonneg _).trans this
    grind

  apply Fn0.out.elim
  apply IntegerModularForm.coeff_trunc_injective <| funext fun ⟨n, nlt⟩ => by
    simp
    apply coeff_lt_ord
    calc
    _ < ((m.toNat / 12 + 1 : ℕ) : ℕ∞) := by norm_cast; grind
    _ ≤ F.ord := c



end ModularFormMod
