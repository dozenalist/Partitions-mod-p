import PartitionsLeanblueprint.RamanujanCongruence.PreliminaryResults
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.MaximalReduce


/-
This file proves the lemmas in the first section of the paper
It shortcuts lemma 3.3, because we don't need it (see `Filtration_Theta_pow_sub_one`)
This file has 2 sorries (both lemma 2.1)
· `Filt_Theta_bound : f.Theta.Filtration ≤ f.Filtration + (ℓ + 1)`
· `Filt_Theta_iff : f.Theta.Filtration = f.Filtration + (ℓ + 1) ↔ ¬ ↑ℓ ∣ f.Filtration`
-/

open ModularFormMod

noncomputable section




theorem ZMod.one_ne_zero' {ℓ : ℕ} [h : ℓ.AtLeastTwo] : (1 : ZMod ℓ) ≠ 0 := by
  haveI : Fact (1 < ℓ) := ⟨h.prop⟩
  exact one_ne_zero

variable {ℓ : ℕ} [isLargePrime ℓ] {k j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k)

theorem NeZero.of_coeff_ne_zero {k} {f : ModularFormMod ℓ k} (h : ∃ n, f.coeff n ≠ 0) : NeZero f where
  out := by contrapose! h; simp only [h, coeff_zero, implies_true]

theorem NeZero.coeff_ne_zero {k} {f : ModularFormMod ℓ k} [h : NeZero f] :
    ∃ n, f.coeff n ≠ 0 := have h := h.out; by contrapose! h; exact ext h

instance NeZero_Delta [ℓ.AtLeastTwo] : NeZero (Δ : ModularFormMod ℓ 12) :=
  NeZero.of_coeff_ne_zero ⟨1, by rw [Delta_one]; exact ZMod.one_ne_zero' ⟩


instance NeZero_Theta_fl : NeZero (fl ℓ).Theta :=
  NeZero.of_coeff_ne_zero ⟨δ ℓ, by simpa [ZMod.natCast_eq_zero_iff] using not_dvd_delta ℓ⟩

instance NeZero_Theta_pow_fl (m) : NeZero ((fl ℓ).Theta_pow m) :=
  NeZero.of_coeff_ne_zero ⟨δ ℓ, by simp [ZMod.natCast_eq_zero_iff, not_dvd_delta]⟩

instance NeZero_Mcast (h : k = j) [hf : NeZero f] : NeZero (f.Mcast h) := by
    obtain ⟨n, hn⟩ := hf.coeff_ne_zero
    exact NeZero.of_coeff_ne_zero ⟨n, by simpa⟩



lemma Filt_Delta [ℓ.AtLeastTwo] : (Δ : ModularFormMod ℓ 12).Filtration = 12 :=
  le_antisymm
    (Filtration_le ⟨IntegerModularForm.Delta, by ext n; simp only [IntegerModularForm.reduce_coeff,
      Delta, fourier_Mcast, IntegerModularForm.fourier_Reduce] ⟩)
    (le_Filtration (p := 1) Δ fun n nlt => by simp_all only [Order.lt_one_iff, Delta_zero])


lemma twelve_delta_cast : ((ℓ^2 - 1)/2 : ℕ) = ((ℓ : ℤ)^2 - 1)/2 := by
  rw [Int.natCast_ediv, Nat.cast_ofNat, Int.natCast_pred_of_pos <| pow_two_pos_of_ne_zero NeZero.out, Nat.cast_pow]


-- lemma Filt_fl' [isLargePrime ℓ] : (fl ℓ).Filtration = (ℓ^2 - 1)/2 := by
--   rw[fl_eq_Delta_pow, Filtration_pow, Filt_Delta, mul_comm]
--   norm_cast; rw [twelve_delta, twelve_delta_cast]
--   rfl

lemma Filt_fl : (fl ℓ).Filtration = (ℓ^2 - 1)/2 :=
  have h1 : (12 : ℤ) * δ ℓ = (ℓ^2 - 1)/2 := by
    rw [show (12 : ℤ) = (12 : ℕ) from rfl, ← Nat.cast_mul, twelve_delta, twelve_delta_cast]
  have h2 : δ ℓ * (12 : ℤ) = (ℓ^2 - 1)/2 := by rwa [mul_comm]
  le_antisymm
    (Filtration_le ⟨(IntegerModularForm.fl ℓ).Icast h2,
        by rw [fl, fourier_Mcast, IntegerModularForm.fourier_Reduce]; rfl⟩)
    (h1 ▸ le_Filtration (p := (δ ℓ)) (fl ℓ) fun n => fl_lt_delta)


--Lemma 2.1

-- (pt 1)
theorem Filt_Theta_bound : f.Theta.Filtration ≤ f.Filtration + (ℓ + 1) := sorry

-- (pt 2)
theorem Filt_Theta_iff :
    f.Theta.Filtration = f.Filtration + (ℓ + 1) ↔ ¬ ↑ℓ ∣ f.Filtration := sorry




lemma Filt_Theta_bound' {m j : ℕ} (h : m = j + 1) :
    (f.Theta_pow m).Filtration ≤ (f.Theta_pow j).Filtration + (ℓ + 1) := by
  subst h
  simpa only [Theta_pow_succ, Filtration_Mcast] using Filt_Theta_bound <| f.Theta_pow j


lemma Filt_Theta_iff' {m j : ℕ} (h : m = j + 1) :
    (f.Theta_pow m).Filtration = (f.Theta_pow j).Filtration + (ℓ + 1) ↔
      ¬ ↑ℓ ∣ (f.Theta_pow j).Filtration := by
  subst h
  simpa only [Theta_pow_succ, Filtration_Mcast] using Filt_Theta_iff <| f.Theta_pow j


lemma Filt_Theta_congruence [NeZero f.Theta] [NeZero ℓ] :
    f.Theta.Filtration = f.Filtration + (ℓ + (1 : ZMod (ℓ - 1))) := by
  simp only [Filtration_congruence, ← one_add_one_eq_two, ZMod.pred_eq_one]



lemma Filt_Theta_congruence_of_dvd [hℓ : ℓ.AtLeastTwo] [hfT : NeZero f.Theta] (ldiv : ↑ℓ ∣ f.Filtration) :
    ∃ α > 0, f.Theta.Filtration = f.Filtration + (ℓ + 1) - α * (ℓ - 1) := by

  have : NeZero (ℓ - 1) := ⟨have := hℓ.prop; by omega⟩

  have bound := lt_of_le_of_ne (Filt_Theta_bound f) fun h => (Filt_Theta_iff f).1 h ldiv

  have := by simpa only [← AddCommGroup.modEq_iff_intModEq, AddCommGroup.modEq_iff_eq_add_zsmul, smul_eq_mul]
    using ZMod.intCast_eq_intCast_iff ..|>.1 <| mod_cast (Filt_Theta_congruence f).symm

  norm_cast at bound
  obtain ⟨α, hα⟩ := this
  rw [hα, add_lt_iff_neg_left] at bound
  have := this.out.pos

  use -α, by
    simp only [Int.neg_pos]
    zify at this
    exact Int.neg_of_mul_neg_left bound this

  rw [hα, neg_mul, sub_neg_eq_add, Nat.cast_pred <| NeZero.pos ℓ]; rfl




lemma Filt_Theta_congruence_of_dvd' {m j : ℕ} [hfT : NeZero (f.Theta_pow m)]
  (ldiv: ↑ℓ ∣ (f.Theta_pow j).Filtration) (h : m = j + 1) :
    ∃ α > 0, (f.Theta_pow m).Filtration = (f.Theta_pow j).Filtration + (ℓ + 1) - α * (ℓ - 1) := by
  subst h
  simp_all only [Theta_pow_succ, Filtration_Mcast]
  exact Filt_Theta_congruence_of_dvd _ ldiv (hfT := NeZero.Mcast _ hfT)



-- Lemma 3.2
-- This proof is currently bad
theorem le_Filt_Theta_fl (m) : (fl ℓ).Filtration ≤ ((fl ℓ).Theta_pow m).Filtration := by

  have eq2 : 12 * δ ℓ = 2 * (6 * δ ℓ) := by rw [← mul_assoc]; rfl

  rw [Filt_fl, ← twelve_delta_cast]
  by_contra! filt_lt
  rw [Filtration] at filt_lt
  apply exists_lt_of_csInf_lt <| exists_hasWeight _ at filt_lt
  obtain ⟨j, ⟨d,hd⟩, jlt⟩ := filt_lt

  obtain ⟨h, dr⟩ := Reduce_of_reduce hd



  set f := (Mcast h.symm ((fl ℓ).Theta_pow m) : ModularFormMod ℓ j) with feq


  have hf : ∀ n < δ ℓ, f.coeff n = 0 := fun n nlt => by
    simp only [feq, coeff_Mcast, coeff_Theta_pow, fl_lt_delta nlt, smul_zero]

  obtain ⟨b', jeq, hj, hbord⟩ := exists_maximal_Reduce (j := j) f hf (by
    use d; rw [feq]
    rw [hd, fourier_Mcast])


  suffices b' = 0 by
    subst this
    simp at hj
    rw [feq] at hj
    exact absurd hj NeZero.out


  apply IntegerModularForm.coeff_trunc_injective
  ext ⟨x, xlt⟩
  simp
  rw [IntegerModularForm.coeff_lt_ord]
  have : dim j ≤ δ ℓ := by

    rw [dim]
    simp_all only [Int.natCast_ediv, Nat.cast_ofNat, fourier_Mcast, IntegerModularForm.fourier_Reduce, coeff_Mcast,
      IntegerModularForm.coeff_Reduce, ge_iff_le, f]
    split
    next h_1 =>
      split
      next h_2 =>
        split
        next h_3 =>
          zify; simp
          rw [delta]
          grind

        next h_3 =>
          simp_all only [Order.add_one_le_iff]
          zify
          simp
          simp_all only [sup_of_le_left]
          refine (Int.ediv_lt_iff_lt_mul (by decide)).mpr ?_
          rw [mul_comm]
          norm_cast; rw [twelve_delta]
          simpa only [Int.natCast_ediv, Nat.cast_ofNat]



      next h_2 => simp_all only [Int.not_even_iff_odd, zero_le]
    next h_1 => simp_all only [not_le, zero_le]



  refine lt_of_lt_of_le ?_ hbord
  norm_cast
  lia



theorem Filtration_Theta_pow_sub_one (flu : (fl ℓ).UOp = 0) :
    ((fl ℓ).Theta_pow (ℓ - 1)).Filtration = (ℓ^2 - 1)/2 := by
  rw [← Filt_fl]; exact .symm <| Filtration_ext fun _ =>
  have := by simpa only [map_sub, coeff_Mcast] using ModularFormMod.ext_iff.1 <| UOp_pow_l (fl ℓ)
  by rw [← sub_eq_zero, ← this, flu, ModularFormMod.zero_pow, coeff_zero]
