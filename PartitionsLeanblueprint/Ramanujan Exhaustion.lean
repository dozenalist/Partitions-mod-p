import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Order.Filter.Defs
import Mathlib.Analysis.Analytic.Basic

open Complex UpperHalfPlane

open scoped MatrixGroups ModularForm

variable (Γ : Subgroup (SL(2,ℤ)))
variable (k : ℤ)

structure ModularForm where

  toFun : ℂ → ℂ

  holo : AnalyticOn ℂ toFun {z | z : ℍ}

  shift : ∀ z : ℍ, toFun (z + 1) = toFun z

  squish : ∀ z : ℍ, toFun (-1/z) = z^k * toFun z

  bounded : ∃ M : ℝ, ∀ z : ℍ, z.re = 0 → (toFun z).re ≤ M ∧ (toFun z).im ≤ M

instance zero : (ModularForm k) where

  toFun := fun x ↦ 0

  holo := by intro x xS; exact analyticWithinAt_const

  shift := λ _ ↦ rfl

  squish := λ _ ↦ by simp

  bounded := ⟨0, λ _ _ ↦ by simp⟩


--better (still bad)
