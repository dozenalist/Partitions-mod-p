import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions


open Complex UpperHalfPlane

open scoped MatrixGroups ModularForm

variable (Γ : Subgroup (SL(2,ℤ)))
variable (k : ℤ)

structure ModularForm where

  toFun : ℍ → ℂ

  -- holo : sorry

  modular : ∀ γ ∈ Γ, toFun ∣[k] γ = toFun


instance zero : (ModularForm Γ k) where
  toFun := fun x ↦ 0

  modular := by intro γ hγ; ext z; rw [ModularForm.slash_action_eq'_iff]; simp

--bad
