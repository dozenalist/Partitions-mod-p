import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Defs

open MatrixGroups PowerSeries Finset UpperHalfPlane ModularForm
open IntegerModularForm ModularFormMod

noncomputable section




section IntegerModularForm.Basic


/-- The power series generating function for `Δ`. Can be instantiated over any commutative ring -/

def DeltaProduct' {α : Type} [CommRing α] (m : ℕ) : α ⟦X⟧ :=
  X * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24


def IntegerModularForm.Delta' : IntegerModularForm 12 where
  fourier := .mk fun m => (DeltaProduct' m).coeff m
  carrier := CuspForm.discriminant
  carrier_eq := sorry




end IntegerModularForm.Basic


section ModularFormMod.MaximalReduce

variable {ℓ : ℕ} [isLargePrime ℓ] {k : ZMod (ℓ - 1)}

theorem Reduce_of_reduce {m} {f : ModularFormMod ℓ k} [hf : NeZero f]
  {b : IntegerModularForm m} (hab : b.reduce ℓ = f.fourier) :
    ∃ h, f = Mcast h (Reduce ℓ b) := by sorry

end ModularFormMod.MaximalReduce


section Filtration.Defs

namespace ModularFormMod

variable {ℓ : ℕ} [isLargePrime ℓ] {k j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k)

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


theorem Filtration_ext {f : ModularFormMod ℓ k} {g : ModularFormMod ℓ j}
    (h : ∀ n, f.coeff n = g.coeff n) : f.Filtration = g.Filtration := by
  simpa only [Filtration, hasWeight] using
    congrArg (fun f => (sInf {j : ℤ | f ∈ Set.range ⇑(@reduce j ℓ)})) <| PowerSeries.ext_iff.2 h

end ModularFormMod
end Filtration.Defs

section ModularFormMod.Operators
variable {α} [CommRing α]

namespace PowerSeries


noncomputable def Theta : PowerSeries α →ₗ[α] PowerSeries α :=
  (LinearMap.mulLeft α X).comp (derivative α).toLinearMap


theorem Theta_apply (f : PowerSeries α) : Theta f = X * derivative α f := rfl

@[simp] theorem coeff_Theta (f : PowerSeries α) : ∀ n, (Theta f).coeff n = n • f.coeff n
  | 0 => by simp [Theta]
  | n + 1 => by simp [Theta, coeff_derivative, mul_comm]


instance (f : PowerSeries α) [h : NeZero f.Theta] : NeZero f where
  out := have := h.out; by contrapose! this; simp only [this, map_zero]


end PowerSeries

namespace ModularFormMod
open PowerSeries
variable {ℓ : ℕ} [isLargePrime ℓ] {k : ZMod (ℓ - 1)}

-- should be a nicer way to do this? don't want to make api
noncomputable def Theta : ModularFormMod ℓ k →ₗ[ZMod ℓ] ModularFormMod ℓ (k + 2) where
  toFun f := {
    fourier := f.fourier.Theta
    modular := sorry }

  map_add' _ _ := fourier_inj <| by simp only [fourier_add, map_add]

  map_smul' _ _ := fourier_inj <| by simp only [fourier_smul, map_smul, RingHom.id_apply]
end ModularFormMod

namespace PowerSeries

noncomputable def UOp (ℓ : ℕ) : PowerSeries α →ₗ[α] PowerSeries α where
  toFun f := .mk fun n => f.coeff (ℓ * n)
  map_add' _ _ := PowerSeries.ext fun _ => by simp only [map_add, coeff_mk]
  map_smul' _ _ := PowerSeries.ext fun _ => by
    simp only [map_smul, smul_eq_mul, coeff_mk, RingHom.id_apply]

theorem UOp_apply {ℓ} (f : PowerSeries α) : UOp ℓ f = .mk fun n => f.coeff (ℓ * n) := rfl

@[simp] theorem coeff_UOp {ℓ} (f : PowerSeries α) (n) : (UOp ℓ f).coeff n = f.coeff (ℓ * n) := by
  rw [UOp_apply, coeff_mk]

end PowerSeries

namespace ModularFormMod

noncomputable def UOp {ℓ} [isLargePrime ℓ] {k} : ModularFormMod ℓ k →ₗ[ZMod ℓ] ModularFormMod ℓ k where
  toFun f := {
    fourier := f.fourier.UOp ℓ
    modular := sorry }
  map_add' _ _ := fourier_inj <| by simp only [fourier_add, map_add]
  map_smul' _ _ := fourier_inj <| by simp only [fourier_smul, map_smul, RingHom.id_apply]


end ModularFormMod

end Operators


section PrimaryLemmas

variable {ℓ : ℕ} [isLargePrime ℓ] {k : ZMod (ℓ - 1)}

theorem Filt_Theta_bound (f : ModularFormMod ℓ k) : f.Theta.Filtration ≤ f.Filtration + (ℓ + 1) := sorry

-- (pt 2)
theorem Filt_Theta_iff (f : ModularFormMod ℓ k) :
    f.Theta.Filtration = f.Filtration + (ℓ + 1) ↔ ¬ ↑ℓ ∣ f.Filtration := sorry


end PrimaryLemmas
