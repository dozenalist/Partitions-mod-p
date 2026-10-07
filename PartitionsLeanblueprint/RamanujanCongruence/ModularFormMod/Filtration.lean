import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Basic



variable {ℓ : ℕ} [hℓ : isLargePrime ℓ] {k j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j)


@[simp] theorem _root_.ZMod.pred_eq_one [NeZero ℓ] : (ℓ : ZMod (ℓ - 1)) = 1 := by
  rcases Nat.exists_eq_add_one.2 <| Nat.pos_of_neZero ℓ with ⟨n, rfl⟩
  simp only [Nat.cast_add, CharP.cast_eq_zero, Nat.cast_one, zero_add]

open IntegerModularForm
namespace ModularFormMod



def hasWeight (j : ℤ) (f : ModularFormMod ℓ k) : Prop :=
  f.fourier ∈ Set.range (@reduce j ℓ)

theorem hasWeight.exists_reduce {j : ℤ} (h : f.hasWeight j) :
    ∃ g : IntegerModularForm j, f.fourier = g.reduce ℓ := by
  obtain ⟨h, hh⟩ := by simpa only [hasWeight, Set.mem_range] using h
  exact ⟨h, hh.symm⟩

theorem hasWeight.exists {j : ℤ} (h : f.hasWeight j) :
    ∃ g : ModularFormMod ℓ j, ∀ n, f.coeff n = g.coeff n := by
  obtain ⟨h, hh⟩ := h.exists_reduce
  use h.Reduce ℓ, fun n => by simp only [coeff_def, hh, fourier_Reduce]

@[simp] theorem hasWeight_Mcast {m} (h : k = j) : (f.Mcast h).hasWeight m ↔ f.hasWeight m := Iff.rfl

theorem exists_hasWeight : {j : ℤ | f.hasWeight j}.Nonempty := by
  obtain ⟨i, hi, h⟩ := by simpa [ZMod.reduce_set] using f.modular
  use i
  simpa only [hasWeight, Set.mem_range, Set.mem_ofPred_eq]

theorem exists_hasWeight_ge (j : ℤ) : ∃ i ≥ j, ↑i = k ∧ f.hasWeight i := by
  obtain ⟨m, hm, g, hg⟩ := f.Exists_reduce
  use m + ((j.toNat + m.natAbs) * (ℓ - 1 : ℕ)), by calc
    _ = m + |m| * (ℓ - 1) + max j 0 * (ℓ - 1) := by
      rw [Nat.cast_pred (by grind [hℓ.AtLeastFive])]
      simp only [Int.ofNat_toNat, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq]
      ring
    _ ≥ m + |m| * 1 + j * 1 := by
      gcongr
      grind [hℓ.AtLeastFive]
      exact Int.le_max_left j 0
      grind [hℓ.AtLeastFive]
    _ ≥ j := by simp only [_root_.mul_one, ge_iff_le, le_add_iff_nonneg_left, add_abs_nonneg]

  use by simpa, g.mul ((El ℓ).pow (j.toNat + m.natAbs))
  rwa [reduce_mul, reduce_El_pow, MulOneClass.mul_one]

theorem hasWeight_mul {m n} {f : ModularFormMod ℓ k} {g : ModularFormMod ℓ j}
  (hf : f.hasWeight m) (hg : g.hasWeight n) :
    (f.mul g).hasWeight (m + n) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  use f'.mul g', by rw [reduce_mul, fourier_mul, hf', hg']


noncomputable def Filtration (f : ModularFormMod ℓ k) : ℤ :=
  sInf {j : ℤ | f.hasWeight j}


theorem nonempty_hasWeight_set : {j : ℤ | f.hasWeight j}.Nonempty := by
  obtain ⟨j, -, h⟩ := by simpa [ZMod.reduce_set] using f.modular
  exact ⟨j, by simpa⟩

theorem BddBelow_hasWeight_set [fn0 : NeZero f] : BddBelow {j : ℤ | f.hasWeight j} := by
  use 0
  simp [mem_lowerBounds, hasWeight]
  intro j g hf
  have g0 : g ≠ 0 := by
    have := fn0.out; contrapose! this; rw [this, map_zero] at hf
    exact fourier_inj <| fourier_zero (ℓ := ℓ) ▸ hf.symm

  contrapose! g0
  apply carrier_inj

  ext x
  rw [ModularFormClass.levelOne_neg_weight_eq_zero g0]
  rfl

theorem Filtration_spec (f : ModularFormMod ℓ k) :
    f.hasWeight f.Filtration := by
  by_cases fn0 : f = 0
  · use 0, by rw [fn0, fourier_zero, map_zero]
  · exact Int.csInf_mem (nonempty_hasWeight_set f) (BddBelow_hasWeight_set f (fn0 := ⟨fn0⟩))


theorem Filtration_le {j} {f : ModularFormMod ℓ k} [fn0 : NeZero f] (hf : hasWeight j f) : f.Filtration ≤ j :=
  csInf_le (BddBelow_hasWeight_set f) hf


noncomputable def Filtration_choose (f : ModularFormMod ℓ k) :
  IntegerModularForm f.Filtration := f.Filtration_spec.choose

theorem Filtration_choose_spec (f : ModularFormMod ℓ k) :
  f.fourier = reduce ℓ f.Filtration_choose := f.Filtration_spec.choose_spec.symm

theorem coeff_eq_Filtration_choose (f : ModularFormMod ℓ k) (n : ℕ) :
    f.coeff n = f.Filtration_choose.coeff n := by
  rw [coeff_def, Filtration_choose_spec, reduce_coeff]

@[simp] theorem Filtration_zero : Filtration (0 : ModularFormMod ℓ k) = 0 :=
  Int.csInf_of_not_bddBelow <| not_bddBelow_iff.2 fun j =>
    ⟨j - 1, ⟨0, map_zero _⟩, sub_lt_self j zero_lt_one⟩

@[simp] theorem Filtration_Mcast (h : k = j) : (f.Mcast h).Filtration = f.Filtration := rfl



theorem Filtration_le_Nat {j : ℕ} {f : ModularFormMod ℓ k} (hf : hasWeight j f) : f.Filtration ≤ j := by
  by_cases f0 : f = 0
  · rw [f0, Filtration_zero]; exact Int.natCast_nonneg j
  · exact Filtration_le hf (fn0 := ⟨f0⟩)

theorem Filtration_ext {f : ModularFormMod ℓ k} {g : ModularFormMod ℓ j}
    (h : ∀ n, f.coeff n = g.coeff n) : f.Filtration = g.Filtration := by
  simpa only [Filtration, hasWeight] using
    congrArg (fun f => (sInf {j : ℤ | f ∈ Set.range ⇑(@reduce j ℓ)})) <| PowerSeries.ext_iff.2 h


theorem Filtration_ext' {f : ModularFormMod ℓ k} {g : ModularFormMod ℓ j}
    (h : ∀ m, f.hasWeight m ↔ g.hasWeight m) : f.Filtration = g.Filtration := by
  simpa only [Filtration] using congrArg _ <| Set.ext (by exact h ·)


@[simp] theorem Filtration_neg : (-f).Filtration = f.Filtration :=
  Filtration_ext' fun _ =>
    ⟨fun ⟨f', h⟩ => ⟨-f', by simp [h]⟩, fun ⟨f', h⟩ => ⟨-f', by simp [h]⟩⟩




theorem NeZero.Mcast {h : k = j} (i : NeZero (f.Mcast h)) : NeZero f where
  out := have := i.out; by contrapose! this; simp only [this, Mcast_zero]



end ModularFormMod
