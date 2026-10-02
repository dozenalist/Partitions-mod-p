import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.FiltrationTheta.Foundations

open ModularFormMod
open EisensteinSeries

noncomputable section

namespace FiltrationTheta

variable {ℓ : ℕ} [isLargePrime ℓ]
variable {k : ZMod (ℓ - 1)}

/-- A Fourier expansion has weight `j` when it is the reduction of an integral
modular form of weight `j`. -/
def HasWeight (f : ModularFormMod ℓ k) (j : ℤ) : Prop :=
  f.hasWeight j

/-- The filtration supplied by the infimum definition is an attained weight. -/
def HasExactFiltration (f : ModularFormMod ℓ k) (j : ℤ) : Prop :=
  HasWeight f j ∧ ∀ j' < j, ¬HasWeight f j'

/-- A form of weight `j` has lower weight if it also has a representative in
some strictly smaller integral weight. -/
def HasLowerWeight (f : ModularFormMod ℓ k) (j : ℤ) : Prop :=
  ∃ j' < j, HasWeight f j'

/-- The weight of the numerator in the theta argument. -/
def ThetaTargetWeight (f : ModularFormMod ℓ k) : ℤ :=
  f.Filtration + (ℓ + 1)

/-- The congruence condition in Proposition 1.44(2). -/
def PrimeDividesFiltration (f : ModularFormMod ℓ k) : Prop :=
  (ℓ : ℤ) ∣ f.Filtration

end FiltrationTheta
