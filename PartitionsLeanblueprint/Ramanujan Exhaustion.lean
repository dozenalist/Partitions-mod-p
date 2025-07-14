import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Analysis.Analytic.Basic

open Complex UpperHalfPlane

section define
variable (k : ℕ)

structure ModularForm : Type where

  toFun : ℂ → ℂ

  holo : AnalyticOn ℂ toFun {z : ℂ | z.im > 0}

  shift : ∀ z : ℍ, toFun (z + 1) = toFun z

  squish : ∀ z : ℍ, toFun (-1/z) = z ^ k * toFun z

  bounded : ∃ M : ℝ, ∀ z : ℍ, z.re = 0 → |(toFun z).re| ≤ M ∧ |(toFun z).im| ≤ M

class ModularFormClass (k : ℕ) {toFun : ℂ → ℂ}: Prop where

  holo : AnalyticOn ℂ toFun {z | z.im > 0}

  shift : ∀ z : ℍ, toFun (z + 1) = toFun z

  squish : ∀ z : ℍ, toFun (-1/z) = z ^ k * toFun z

  bounded : ∃ M : ℝ, ∀ z : ℍ, z.re = 0 → |(toFun z).re| ≤ M ∧ |(toFun z).im| ≤ M

end define

section properties

variable {k : ℕ}


instance add : Add (ModularForm k) where

  add := fun f g ↦

  { toFun := f.toFun + g.toFun
    holo := AnalyticOn.add f.holo g.holo
    shift := by simp [f.shift, g.shift]
    squish := by intro z; simp [f.squish, g.squish]; ring
    bounded := by
      obtain ⟨F, hF⟩ := f.bounded
      obtain ⟨G, hG⟩ := g.bounded
      use F + G; intro z zr0; simp
      exact ⟨Trans.simple (abs_add _ _) (add_le_add (hF z zr0).1 (hG z zr0).1),
      Trans.simple (abs_add _ _) (add_le_add (hF z zr0).2 (hG z zr0).2)⟩ }


def mul {k j : ℕ} (f : ModularForm k) (g : ModularForm j) : ModularForm (k + j) where

  toFun := f.toFun * g.toFun
  holo := AnalyticOn.mul f.holo g.holo
  shift := by simp [f.shift, g.shift]
  squish := by intro z; simp [f.squish, g.squish]; ring
  bounded := by
    obtain ⟨F, hF⟩ := f.bounded
    obtain ⟨G, hG⟩ := g.bounded
    use (|F| * |G|) + (|F| * |G|) ; intro z zr0; simp
    constructor; trans |(f.toFun ↑z).re * (g.toFun ↑z).re| + |(f.toFun ↑z).im * (g.toFun ↑z).im|
    apply abs_sub; rw[abs_mul, abs_mul]; apply add_le_add; apply mul_le_mul
    apply le_abs.2; left; exact (hF z zr0).1
    apply le_abs.2; left; exact (hG z zr0).1
    exact abs_nonneg _; exact abs_nonneg _
    apply mul_le_mul; apply le_abs.2; left; exact (hF z zr0).2
    apply le_abs.2; left; exact (hG z zr0).2
    exact abs_nonneg _; exact abs_nonneg _
    trans |(f.toFun ↑z).re * (g.toFun ↑z).im| + |(f.toFun ↑z).im * (g.toFun ↑z).re|
    apply abs_add; rw[abs_mul, abs_mul]; apply add_le_add; apply mul_le_mul
    apply le_abs.2; left; exact (hF z zr0).1
    apply le_abs.2; left; exact (hG z zr0).2
    exact abs_nonneg _; exact abs_nonneg _
    apply mul_le_mul; apply le_abs.2; left; exact (hF z zr0).2
    apply le_abs.2; left; exact (hG z zr0).1
    exact abs_nonneg _; exact abs_nonneg _


instance instSMul : SMul ℂ (ModularForm k) where
  smul c f :=
  { toFun := c • f.toFun
    holo := by
      have h1 : AnalyticOn ℂ (fun z ↦ c) {z : ℂ | z.im > 0} := analyticOn_const
      apply AnalyticOn.smul h1 f.holo
    shift := by intro z; simp; left; exact f.shift z
    squish := by intro z; simp; rw[f.squish z]; ring
    bounded := by
      obtain ⟨M,hM⟩ := f.bounded
      use (|c.re| * M) + (|c.im| * M);
      intro z zr0; simp; constructor
      trans |c.re * (f.toFun ↑z).re| + |c.im * (f.toFun ↑z).im|
      apply abs_sub; apply add_le_add <;> rw[abs_mul]
      apply mul_le_mul_of_nonneg_left (hM z zr0).1 (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left (hM z zr0).2 (abs_nonneg _)
      trans |c.re * (f.toFun ↑z).im| + |c.im * (f.toFun ↑z).re|
      apply abs_add; apply add_le_add <;> rw[abs_mul]
      apply mul_le_mul_of_nonneg_left (hM z zr0).2 (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left (hM z zr0).1 (abs_nonneg _) }


instance zero : Zero (ModularForm k) where

  zero :=

  { toFun := 0
    holo := by intro x xS; exact analyticWithinAt_const
    shift := λ _ ↦ rfl
    squish := λ _ ↦ by simp
    bounded := ⟨0, λ _ _ ↦ by simp⟩ }

def const (x : ℂ) : ModularForm 0 where
  toFun := fun z ↦ x
  holo := analyticOn_const
  shift := λ _ ↦ rfl
  squish := λ _ ↦ by simp
  bounded := ⟨|x.re| ⊔ |x.im|, λ _ _ ↦ ⟨le_max_left _ _, le_max_right _ _⟩⟩

instance : Coe ℂ (ModularForm 0) where
  coe x := const x



instance : Module ℂ (ModularForm k) :=
  Function.Injective.module ℂ coeHom DFunLike.coe_injective fun _ _ => rfl




variable {f : ModularForm k} {c : ℂ} {g : ModularForm 0}



notation "⇈" => const
-- coerces a scalar into a modular form of weight 0

infixl:60 "*" => mul
-- function multiplication

infixl:65 "•" => SMul
-- multiplication of a function by a scalar

#check c + g

instance (priority := 100) ModularForm.funLike : FunLike (ModularForm k) ℂ ℂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr


theorem ModularForm.toFun_eq_coe (f : ModularForm k) : ⇑f = (f : ℂ → ℂ) := rfl

@[simp]
theorem coe_add (f g : ModularForm k) : ⇑(f + g) = f + g := rfl
--how is this true what

@[simp]
theorem add_apply (f g : ModularForm k) (z : ℂ) : (f + g) z = f z + g z := rfl

@[simp]
theorem coe_mul (f g : ModularForm k) : ⇑(f * g) = f * g := rfl

@[simp]
theorem mul_apply (f g : ModularForm k) (z : ℂ) : (f * g) z = f z * g z := rfl

@[simp]
theorem coe_zero : ⇑(0 : ModularForm k) = (0 : ℂ → ℂ) := rfl

@[simp]
theorem zero_apply (z : ℍ) : (0 : ModularForm k) z = 0 := rfl



--bad
