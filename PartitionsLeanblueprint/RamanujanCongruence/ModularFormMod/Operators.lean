import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Defs
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.FieldTheory.Finite.Basic


/-
This file defines the Filtration, Theta, and UOp functions on Modular Forms Mod ℓ
This file has 2 sorries
· `Theta.modular`
· `UOp.modular`
-/

variable {ℓ : ℕ} [isLargePrime ℓ] {k j : ZMod (ℓ - 1)} (f g : ModularFormMod ℓ k) (h : ModularFormMod ℓ j)

section Filtration
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



theorem NeZero.Mcast {h : k = j} (i : NeZero (f.Mcast h)) : NeZero f where
  out := have := i.out; by contrapose! this; simp only [this, Mcast_zero]



end ModularFormMod
end Filtration

section Theta

namespace PowerSeries


variable {α : Type} [CommSemiring α]

noncomputable def Theta : PowerSeries α →ₗ[α] PowerSeries α :=
  (LinearMap.mulLeft α X).comp (derivative α).toLinearMap


theorem Theta_apply (f : PowerSeries α) : Theta f = X * derivative α f := rfl

@[simp] theorem coeff_Theta (f : PowerSeries α) : ∀ n, (Theta f).coeff n = n • f.coeff n
  | 0 => by simp [Theta]
  | n + 1 => by simp [Theta, coeff_derivative, mul_comm]


@[simp] theorem coeff_Theta_pow (f : PowerSeries α) (m n) :
    ((Theta ^ m) f).coeff n = n ^ m • f.coeff n := by
  match m with
  | 0 => simp only [pow_zero, Module.End.one_apply, one_smul]
  | m + 1 => simp [pow_succ', coeff_Theta_pow]; ring

instance (f : PowerSeries α) [h : NeZero f.Theta] : NeZero f where
  out := have := h.out; by contrapose! this; simp only [this, map_zero]


end PowerSeries

namespace ModularFormMod
open PowerSeries

-- should be a nicer way to do this? don't want to make api
noncomputable def Theta : ModularFormMod ℓ k →ₗ[ZMod ℓ] ModularFormMod ℓ (k + 2) where
  toFun f := {
    fourier := f.fourier.Theta
    modular := sorry }

  map_add' _ _ := fourier_inj <| by simp only [fourier_add, map_add]

  map_smul' _ _ := fourier_inj <| by simp only [fourier_smul, map_smul, RingHom.id_apply]

@[simp] theorem fourier_Theta : f.Theta.fourier = f.fourier.Theta := rfl

@[simp] theorem coeff_Theta (n) : f.Theta.coeff n = n • f.coeff n := by
  simp only [coeff_def, fourier_Theta, PowerSeries.coeff_Theta]


noncomputable def Theta_pow : (n : ℕ) → ModularFormMod ℓ k →ₗ[ZMod ℓ] ModularFormMod ℓ (k + n • 2)
  | 0 => McastLinearMap (by rw [zero_nsmul, add_zero])
  | n + 1 => McastLinearMap (by group) ∘ₗ (Theta.comp (Theta_pow n))


@[simp] theorem Theta_pow_zero : f.Theta_pow 0 = f.Mcast := by
  rw [Theta_pow, McastLinearMap_apply]

@[simp] theorem Theta_pow_succ (n) : f.Theta_pow (n + 1) = (f.Theta_pow n).Theta.Mcast := by
  simp only [Theta_pow, LinearMap.coe_comp, Function.comp_apply, McastLinearMap_apply]

@[simp] theorem Theta_pow_one : f.Theta_pow 1 = f.Theta.Mcast := by
  rw [Theta_pow_succ, Theta_pow_zero]; rfl

@[simp] theorem _root_.ZMod.pred_eq_one [NeZero ℓ] : (ℓ : ZMod (ℓ - 1)) = 1 := by
  rcases Nat.exists_eq_add_one.2 <| Nat.pos_of_neZero ℓ with ⟨n, rfl⟩
  simp only [Nat.cast_add, CharP.cast_eq_zero, Nat.cast_one, zero_add]


@[simp] theorem fourier_Theta_pow :
    ∀ m, (f.Theta_pow m).fourier = (PowerSeries.Theta ^ m) f.fourier
  | 0 => by simp only [Theta_pow_zero, fourier_Mcast, _root_.pow_zero, Module.End.one_apply]
  | m + 1 => by simp only [Theta_pow_succ, fourier_Mcast, fourier_Theta,
    fourier_Theta_pow m, pow_succ', Module.End.mul_apply]

@[simp] theorem coeff_Theta_pow (m n) : (f.Theta_pow m).coeff n = n ^ m • f.coeff n := by
  simp only [coeff_def, fourier_Theta_pow, PowerSeries.coeff_Theta_pow]

@[simp] theorem Theta_pow_l [NeZero ℓ] [Fact (Nat.Prime ℓ)] :
    f.Theta_pow ℓ = f.Theta.Mcast (by simp) :=
  ext fun _ => by simp [ZMod.pow_card]

lemma Filtration_Theta_cast {j m : ℕ} (h : j = m) :
    (f.Theta_pow j).Filtration = (f.Theta_pow m).Filtration :=
  h ▸ rfl

instance NeZero_of_Theta [h : NeZero f.Theta] : NeZero f where
  out := have := h.out; by contrapose! this; simp only [this, map_zero]

theorem NeZero_of_Theta_pow (m) [h : NeZero (f.Theta_pow m)] : NeZero f where
  out := have := h.out; by contrapose! this; simp only [this, map_zero]

end ModularFormMod
end Theta

section UOperator
namespace PowerSeries

variable {α : Type} [CommSemiring α]

noncomputable def UOp (ℓ : ℕ) : PowerSeries α →ₗ[α] PowerSeries α where
  toFun f := .mk fun n => f.coeff (ℓ * n)
  map_add' _ _ := ext fun _ => by simp only [map_add, coeff_mk]
  map_smul' _ _ := ext fun _ => by
    simp only [map_smul, smul_eq_mul, coeff_mk, RingHom.id_apply]

theorem UOp_apply {ℓ} (f : PowerSeries α) : UOp ℓ f = .mk fun n => f.coeff (ℓ * n) := rfl

@[simp] theorem coeff_UOp {ℓ} (f : PowerSeries α) (n) : (UOp ℓ f).coeff n = f.coeff (ℓ * n) := by
  rw [UOp_apply, coeff_mk]

end PowerSeries

namespace ModularFormMod

noncomputable def UOp : ModularFormMod ℓ k →ₗ[ZMod ℓ] ModularFormMod ℓ k where
  toFun f := {
    fourier := f.fourier.UOp ℓ
    modular := sorry }
  map_add' _ _ := fourier_inj <| by simp only [fourier_add, map_add]
  map_smul' _ _ := fourier_inj <| by simp only [fourier_smul, map_smul, RingHom.id_apply]

@[simp] theorem fourier_UOp : f.UOp.fourier = f.fourier.UOp ℓ := rfl

@[simp] theorem coeff_UOp (n) : f.UOp.coeff n = f.coeff (ℓ * n) := by
  simp only [coeff_def, fourier_UOp, PowerSeries.coeff_UOp]


end ModularFormMod
end UOperator
