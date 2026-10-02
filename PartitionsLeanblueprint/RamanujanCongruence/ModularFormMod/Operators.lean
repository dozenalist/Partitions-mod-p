import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Filtration
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.FieldTheory.Finite.Basic
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.ThetaOperator.DelOperator
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.UOperator.HeckeOperator


/-
This file defines the Filtration, Theta, and UOp functions on Modular Forms Mod ℓ
This file is sorry free
-/


variable {ℓ : ℕ} [hℓ : isLargePrime ℓ] {k j : ZMod (ℓ - 1)} (f g : ModularFormMod ℓ k)

section Theta

namespace PowerSeries


variable {α : Type} [CommSemiring α]

noncomputable def Theta : PowerSeries α →ₗ[α] PowerSeries α :=
  (LinearMap.mulLeft α X).comp derivative.toLinearMap


theorem Theta_apply (f : PowerSeries α) : Theta f = X * derivative f := rfl

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

noncomputable def Theta : ModularFormMod ℓ k →ₗ[ZMod ℓ] ModularFormMod ℓ (k + 2) where
  toFun f := {
    fourier := f.fourier.Theta
    modular := by
      show ThetaOperator.DelOperator.thetaSeries f ∈ _
      obtain ⟨g, hg⟩ := ThetaOperator.DelOperator.theta_preserves_modularity f
      rw [← hg]; exact g.modular}

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

open IntegerModularForm in

noncomputable def UOp : Module.End (ZMod ℓ) (ModularFormMod ℓ k) where
  toFun f := {
    fourier := f.fourier.UOp ℓ
    modular := by
      obtain ⟨j, j2, hj, g, hg⟩ := f.exists_hasWeight_ge 2
      simp [ZMod.reduce_set]
      use j, hj, g.T ℓ (show 1 ≤ j by lia)
      ext n
      simp only [reduce_apply, coeff_T_prime ℓ hℓ.Prime]
      push_cast
      rw [ite_eq_right_iff.mpr, add_zero, PowerSeries.coeff_UOp, ← reduce_apply, hg]
      rintro -
      apply mul_eq_zero_of_left
      simp only [CharP.cast_eq_zero, Int.pred_toNat, pow_eq_zero_iff', ne_eq, true_and]
      grind
    }
  map_add' _ _ := fourier_inj <| by simp only [fourier_add, map_add]
  map_smul' _ _ := fourier_inj <| by simp only [fourier_smul, map_smul, RingHom.id_apply]

@[simp] theorem fourier_UOp : f.UOp.fourier = f.fourier.UOp ℓ := rfl

@[simp] theorem coeff_UOp (n) : f.UOp.coeff n = f.coeff (ℓ * n) := by
  simp only [coeff_def, fourier_UOp, PowerSeries.coeff_UOp]


end ModularFormMod
end UOperator
