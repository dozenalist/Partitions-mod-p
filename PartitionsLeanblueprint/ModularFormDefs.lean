import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Algebra

/- This file defines regular modular forms as functions on the complex plane, and
defines Integer Modular Forms as sequences whose q-series are modular forms.
It also defines Modular Forms Mod ℓ, but in a way that is innacurate.
This file is the root of the project. -/


namespace ModularFormDefs

noncomputable section ModularFormsRegular

namespace Regular

open Classical
attribute [instance] Classical.propDecidable
-- makes all propositions decidable (either True or False). needed for Filtration if / else function

open Complex UpperHalfPlane

section define

variable (k : ℕ)

structure ModularForm : Type where

  toFun : ℂ → ℂ

  holo : AnalyticOn ℂ toFun {z : ℂ | z.im > 0}

  shift : ∀ z : ℍ, toFun (z + 1) = toFun z

  squish : ∀ z : ℍ, toFun (-1/z) = z ^ k * toFun z

  bounded : ∃ M : ℝ, ∀ z : ℍ, z.re = 0 → |(toFun z).re| ≤ M ∧ |(toFun z).im| ≤ M


class ModularFormClass' (F : Type*) (k : ℕ)
    [FunLike F ℂ ℂ] : Prop where
  holo : ∀ f : F, AnalyticOn ℂ f {z | z.im > 0}

  shift : ∀ f : F, ∀ z : ℍ, f (z + 1) = f z

  squish : ∀ f : F, ∀ z : ℍ, f (-1/z) = z ^ k * f z

  bounded : ∀ f : F, ∃ M : ℝ, ∀ z : ℍ, z.re = 0 → |(f z).re| ≤ M ∧ |(f z).im| ≤ M


class ModularFormClass (k : ℕ) (toFun : ℂ → ℂ): Prop where

  holo : AnalyticOn ℂ toFun {z | z.im > 0}

  shift : ∀ z : ℍ, toFun (z + 1) = toFun z

  squish : ∀ z : ℍ, toFun (-1/z) = z ^ k * toFun z

  bounded : ∃ M : ℝ, ∀ z : ℍ, z.re = 0 → |(toFun z).re| ≤ M ∧ |(toFun z).im| ≤ M


instance (priority := 100) ModularForm.funLike : FunLike (ModularForm k) ℂ ℂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

variable {f g : ℂ → ℂ}
variable {k : ℕ}


lemma ClassofForm (f : ModularForm k) : ModularFormClass k f where
  holo := f.holo
  shift := f.shift
  squish := f.squish
  bounded := f.bounded




end define

section properties

variable {k j : ℕ}


instance Radd : Add (ModularForm k) where

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


def Rmul {k j : ℕ} (f : ModularForm k) (g : ModularForm j) : ModularForm (k + j) where

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


instance : HMul (ModularForm k) (ModularForm j) (ModularForm (k + j)) where
  hMul := Rmul


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

instance instSMulZ : SMul ℤ (ModularForm k) where
  smul c f :=
  { toFun := ↑c • f.toFun
    holo := by
      have h1 : AnalyticOn ℂ (fun z ↦ (c : ℂ)) {z : ℂ | z.im > 0} := analyticOn_const
      have aux : (fun z ↦ f.toFun z * c) = fun z ↦ c * f.toFun z := by
        ext z; exact Lean.Grind.CommSemiring.mul_comm (f.toFun z) ↑c
      suffices AnalyticOn ℂ (fun z ↦ c * f.toFun z) {z | z.im > 0} by
        rw [zsmul_eq_mul', Pi.mul_def]
        conv => lhs; simp; rw[aux]
        exact this
      apply AnalyticOn.smul h1 f.holo
    shift := by intro z; simp; left; exact f.shift z
    squish := by intro z; simp; rw[f.squish z]; ring
    bounded := by
      obtain ⟨M,hM⟩ := f.bounded
      use (|c| * M); intro z zr0; simp; constructor <;> rw[abs_mul]
      apply mul_le_mul_of_nonneg_left (hM z zr0).1 (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left (hM z zr0).2 (abs_nonneg _) }

instance instSMulN : SMul ℕ (ModularForm k) where
  smul c f :=
  { toFun := ↑c • f.toFun
    holo := by
      have h1 : AnalyticOn ℂ (fun z ↦ (c : ℂ)) {z : ℂ | z.im > 0} := analyticOn_const
      have aux : (fun z ↦ f.toFun z * c) = fun z ↦ c * f.toFun z := by
        ext z; exact Lean.Grind.CommSemiring.mul_comm (f.toFun z) ↑c
      suffices AnalyticOn ℂ (fun z ↦ c * f.toFun z) {z | z.im > 0} by
        rw [nsmul_eq_mul', Pi.mul_def]
        conv => lhs; simp; rw[aux]
        exact this
      apply AnalyticOn.smul h1 f.holo
    shift := by intro z; simp; left; exact f.shift z
    squish := by intro z; simp; rw[f.squish z]; ring
    bounded := by
      obtain ⟨M,hM⟩ := f.bounded
      use (c * M); intro z zr0; simp; constructor <;> rw[abs_mul]
      apply mul_le_mul; apply le_of_eq; exact Nat.abs_cast c
      exact (hM z zr0).1; apply abs_nonneg; exact Nat.cast_nonneg' c
      apply mul_le_mul; apply le_of_eq; exact Nat.abs_cast c
      exact (hM z zr0).2; apply abs_nonneg; exact Nat.cast_nonneg' c }

instance instNeg : Neg (ModularForm k) where
  neg := fun f ↦
    { toFun := -f.toFun
      holo := AnalyticOn.neg f.holo
      shift := λ z ↦ by simpa using f.shift z
      squish := λ z ↦ by simpa using f.squish z
      bounded := by
        obtain ⟨M,hM⟩ := f.bounded
        exact ⟨M, λ z zr0 ↦ by simpa using ⟨(hM z zr0).1,(hM z zr0).2⟩⟩ }

instance instSub : Sub (ModularForm k) :=
  ⟨fun f g => f + -g⟩

instance zero : Zero (ModularForm k) where

  zero :=

  { toFun := 0
    holo := by intro x xS; exact analyticWithinAt_const
    shift := λ _ ↦ rfl
    squish := λ _ ↦ by simp
    bounded := ⟨0, λ _ _ ↦ by simp⟩ }

def Rconst (x : ℂ) : ModularForm 0 where
  toFun := fun z ↦ x
  holo := analyticOn_const
  shift := λ _ ↦ rfl
  squish := λ _ ↦ by simp
  bounded := ⟨|x.re| ⊔ |x.im|, λ _ _ ↦ ⟨le_max_left _ _, le_max_right _ _⟩⟩

instance : Coe ℂ (ModularForm 0) where
  coe x := Rconst x



notation "⇈" => Rconst

-- notation "⇈" n => const n
-- coerces a scalar into a modular form of weight 0

infixl:65 "•" => SMul
-- multiplication of a function by a scalar

def mPow (f : ModularForm k) (n : ℕ) : (ModularForm (k * n)) :=
  match n with
    | 0 => (⇈ 1)
    | n + 1 => mPow f n * f


-- infixl:80 "⋆" => mPow
-- infixl:80 "^^" => mPow

variable {f : ModularForm k}

theorem ModularForm.toFun_eq_coe (f : ModularForm k) : ⇑f = (f : ℂ → ℂ) := rfl

@[simp]
theorem coe_add (f g : ModularForm k) : ⇑(f + g) = f + g := rfl
--how is this true what

@[simp]
theorem add_apply (f g : ModularForm k) (z : ℂ) : (f + g) z = f z + g z := rfl

@[simp]
theorem coe_mul (f g : ModularForm k) : ⇑(f * g) = f * g := rfl

@[simp]
theorem mul_coe {k j : ℕ} (f : ModularForm k) (g : ModularForm j) :
  (Rmul f g : ℂ → ℂ) = f * g := rfl

@[simp]
theorem mul_apply (f g : ModularForm k) (z : ℂ) : (f * g) z = f z * g z := rfl

@[simp]
theorem coe_smul (f : ModularForm k) (n : ℂ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem coe_smulz (f : ModularForm k) (n : ℤ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem coe_smuln (f : ModularForm k) (n : ℕ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem smul_apply (f : ModularForm k) (n : ℂ) (z : ℂ) : (n • f) z = n • f z := rfl

@[simp]
theorem coe_zero : ⇑(0 : ModularForm k) = (0 : ℂ → ℂ) := rfl

@[simp]
theorem zero_apply (z : ℍ) : (0 : ModularForm k) z = 0 := rfl

@[simp]
theorem coe_neg (f :  ModularForm k) : ⇑(-f) = -f := rfl

@[simp]
theorem coe_sub (f g : ModularForm k) : ⇑(f - g) = f - g := rfl

@[simp]
theorem sub_apply (f g : ModularForm k) (z : ℍ) : (f - g) z = f z - g z := rfl

@[ext]
theorem ModularForm.ext {f g : ModularForm k} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

instance : NatCast (ModularForm 0) where
  natCast n := Rconst n

@[simp, norm_cast]
lemma coe_natCast (n : ℕ) :
    ⇑(n : ModularForm 0) = n := rfl

instance : IntCast (ModularForm 0) where
  intCast z := Rconst z

@[simp, norm_cast]
lemma coe_intCast (z : ℤ) :
    ⇑(z : ModularForm 0) = z := rfl

end properties

section algebra

variable {k j : ℕ}

instance : AddCommGroup (ModularForm k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smuln coe_smulz

@[simps]
def coeHom : ModularForm k →+ ℂ → ℂ where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl


instance : Module ℂ (ModularForm k) :=
  Function.Injective.module ℂ coeHom DFunLike.coe_injective fun _ _ ↦ rfl

instance instGCommRing : DirectSum.GCommRing (ModularForm) := sorry

instance instGAlgebra : DirectSum.GAlgebra ℤ (ModularForm) := sorry

theorem bla (f g : ModularForm k) : 2 • f + g = g + 2 • f := by abel

variable {f g : ModularForm k} {h : ModularForm j}

@[simp]
theorem tibbles : ∀ f : ModularForm k, ModularFormClass k f :=
  fun f =>
    { holo := f.holo
      shift := f.shift
      squish := f.squish
      bounded := f.bounded }


end algebra

-- can treat modular forms as components of a module now
end Regular
end ModularFormsRegular

noncomputable section ModularFormsModulo
open Regular


variable {k j : ℕ}

section misc

open Real Complex Nat

def Choose (n k : ℕ) := n ! / (k ! * (n - k)!)

infixl:80 "𝐂" => Choose

def q z := exp (2 * π * I * z)

def σ (k n : ℕ) : ℕ :=
  ∑ d ∈ (Finset.range (n + 1)).filter (λ d ↦ d ∣ n), d ^ k

def Bernoulli (m : ℕ) : ℂ :=
  if m = 0 then 1 else
  (∑ k ∈ Finset.range (m + 1), (∑ j ∈ Finset.range (k + 1), k𝐂j * ((-1)^j * j^m)/(k+1)))


def EisensteinSeries (k : ℕ) : (ℂ → ℂ) :=
  1 + (2 * k / Bernoulli k) • ∑' n, σ (k - 1) (n + 1) * q ^ (n + 1)

variable {k : ℕ}


def Eisenstein k : (ModularForm k) where
  toFun := EisensteinSeries k
  holo := by unfold AnalyticOn AnalyticWithinAt; sorry
  shift := sorry
  squish := sorry
  bounded := sorry

end misc


lemma Class_add {f g : ℂ → ℂ} (hf : ModularFormClass k f) (hg : ModularFormClass k g) :
  ModularFormClass k (f + g) :=
  {holo := AnalyticOn.add hf.holo hg.holo
   shift := by simp [hf.shift, hg.shift]
   squish := by intro z; simp [hf.squish, hg.squish]; ring
   bounded := by
      obtain ⟨F, hF⟩ := hf.bounded
      obtain ⟨G, hG⟩ := hg.bounded
      use F + G; intro z zr0; simp
      exact ⟨Trans.simple (abs_add _ _) (add_le_add (hF z zr0).1 (hG z zr0).1),
      Trans.simple (abs_add _ _) (add_le_add (hF z zr0).2 (hG z zr0).2)⟩ }

-- how to do this automatically

namespace Integer

-- An integer modular form of weight k is an integer sequence whose infinite q series
-- converges to a modular form of weight k
structure IntegerModularForm (k : ℕ) where

  sequence : (ℕ → ℤ)
  summable : Summable (fun n ↦ sequence n * q ^ n)
  modular : ModularFormClass k (∑' n, sequence n * q ^ n)

-- maybe works idk


instance (priority := 100) : FunLike (IntegerModularForm k) ℕ ℤ where
  coe a := a.1
  coe_injective' a b c := by cases a; cases b; congr

instance : Zero (IntegerModularForm k) where

  zero :=

  { sequence := 0
    summable := by simp; unfold Summable HasSum; use 0; simp
    modular := by simp; sorry  }

def Iconst (x : ℤ) : IntegerModularForm 0 where
  sequence := fun n ↦ if n = 0 then x else 0
  summable := sorry
  modular := sorry

instance : Coe ℤ (IntegerModularForm 0) where
  coe x := Iconst x

instance : Add (IntegerModularForm k) where
  add := fun a b ↦
  { sequence := a + b
    summable := by simpa [add_mul] using Summable.add a.2 b.2
    modular := by
      simp
      have : ∑' n, ((a n) + (b n)) * q ^ n = ∑' n, (a n) * q ^ n + ∑' n,  (b n) * q ^ n := by
        simpa[add_mul] using Summable.tsum_add a.2 b.2
      rw[this]
      apply Class_add a.3 b.3 }

def Imul {k j : ℕ} (a : IntegerModularForm k) (b : IntegerModularForm j) : IntegerModularForm (k + j) where
  sequence := fun n ↦ ∑ m ∈ Finset.range (n + 1), a m * b (n - m)
  summable := sorry
  modular := sorry

instance : HMul (IntegerModularForm k) (IntegerModularForm j) (IntegerModularForm (k + j)) where
  hMul := Imul



@[simp]
theorem coe_zero' : ⇑(0 : IntegerModularForm k) = (0 : ℕ → ℤ) := rfl

@[simp]
theorem zero_apply' (z : ℤ) : (0 : ModularForm k) z = 0 := rfl

@[ext]
theorem IntegerModularForm.ext {a b : IntegerModularForm k} (h : ∀ n, a n = b n) : a = b :=
  DFunLike.ext a b h

instance : NatCast (IntegerModularForm 0) where
  natCast n := Iconst n

-- @[simp, norm_cast]
-- lemma coe_natCast (n : ℕ) :
--     ⇑(n : ModularFormMod ℓ 0) = n := rfl

instance : IntCast (IntegerModularForm 0) where
  intCast z := Iconst z

-- @[simp, norm_cast]
-- lemma coe_intCast (z : ℤ) :
--     ⇑(z : ModularFormMod ℓ 0) = z := rfl


@[simp]
theorem Iconst_zero (x : ℤ) : (Iconst x) 0 = x := rfl

@[simp]
theorem Iconst_succ (x : ℤ) (n : ℕ) : (Iconst x) n.succ = 0 := rfl

instance : AddCommGroup (IntegerModularForm k) := sorry

instance : Module ℤ (IntegerModularForm k) := sorry


instance : DirectSum.GCommRing (IntegerModularForm) := sorry

instance : DirectSum.GAlgebra ℤ (IntegerModularForm) := sorry

end Integer


end ModularFormsModulo


end ModularFormDefs
