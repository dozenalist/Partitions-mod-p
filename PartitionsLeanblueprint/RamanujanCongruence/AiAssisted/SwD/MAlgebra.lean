import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.Identities


namespace PIntegralModularForm.SwD

noncomputable section



/-!
The algebra of Fourier expansions obtained by evaluating residue polynomials.

This is represented as the range subring of `evaluateResiduePolynomial`.  In
particular, `Malgebra p` inherits its commutative-ring structure from the
power-series ring, and elements with the same Fourier expansion are identified.
!-/
abbrev Malgebra (p : ℕ) [isLargePrime p] : Type :=
  (evaluateResiduePolynomial (p := p)).range

namespace Malgebra

variable {p : ℕ} [isLargePrime p]

/-- The Fourier expansion of an element of `Malgebra`. -/
abbrev fourier (F : Malgebra p) : PowerSeries (ZMod p) := F.1

/-- The defining range-membership statement for an element of `Malgebra`. -/
theorem mem_range (F : Malgebra p) :
    F.fourier ∈ (evaluateResiduePolynomial (p := p)).range :=
  F.2

/- `Malgebra p` is a commutative ring because it is a subring of the power-
series ring.  The instance is supplied by `SubringClass.toCommRing`. -/
instance instCommRing : CommRing (Malgebra p) := by
  infer_instance

/-- The inclusion of `Malgebra` into the ambient power-series ring. -/
def inclusion : Malgebra p →+* PowerSeries (ZMod p) :=
  (evaluateResiduePolynomial (p := p)).range.subtype

@[simp]
theorem inclusion_apply (F : Malgebra p) : inclusion F = F.fourier :=
  rfl

theorem inclusion_injective : Function.Injective (inclusion (p := p)) :=
  Subtype.coe_injective

/-- Evaluation into the range algebra. -/
def evaluate : ResiduePolynomial p →+* Malgebra p :=
  (evaluateResiduePolynomial (p := p)).rangeRestrict

@[simp]
theorem inclusion_evaluate (P : ResiduePolynomial p) :
    inclusion (evaluate P) = evaluateResiduePolynomial (p := p) P := by
  exact RingHom.coe_rangeRestrict _ _

theorem evaluate_surjective : Function.Surjective (evaluate (p := p)) :=
  (evaluateResiduePolynomial (p := p)).rangeRestrict_surjective

/-- The canonical element of `Malgebra` represented by a residue polynomial. -/
def ofPolynomial (P : ResiduePolynomial p) : Malgebra p :=
  evaluate P

@[simp]
theorem inclusion_ofPolynomial (P : ResiduePolynomial p) :
    inclusion (ofPolynomial P) = evaluateResiduePolynomial (p := p) P := by
  exact inclusion_evaluate P


theorem ModularFormMod.mem_Malgebra {k} (f : ModularFormMod p k) :
    f.fourier ∈ evaluateResiduePolynomial.range := by
  obtain ⟨j, hj, g, hg⟩ := f.Exists_reduce
  let fLift : PIntegralModularForm p j :=
    PIntegralModularForm.ofInteger (p := p) g
  let Pmod : ResiduePolynomial p :=
    reducePolynomial (p := p)
      (PIntegralModularForm.polynomial (p := p) fLift)
  refine ⟨Pmod, ?_⟩
  calc
    evaluateResiduePolynomial (p := p) Pmod =
      PowerSeries.map (PIntegralModularForm.coeffToZMod (p := p)) fLift.fourier := by
      rw [evaluateResiduePolynomial_reducePolynomial (p := p)
          (PIntegralModularForm.polynomial (p := p) fLift), PIntegralModularForm.evaluate_polynomial]
    _ = (fLift.Reduce).fourier := rfl
    _ = (g.Reduce p).fourier := by
      exact congrArg ModularFormMod.fourier
        (PIntegralModularForm.Reduce_ofInteger (p := p) g)
    _ = f.fourier := by
      rw [IntegerModularForm.fourier_Reduce, hg]

/-- A modular form gives an element of `Malgebra` once its Fourier expansion is
known to lie in the evaluation range. -/
def ofModularForm {k : ZMod (p - 1)} (f : ModularFormMod p k)
    (hf : f.fourier ∈ (evaluateResiduePolynomial (p := p)).range) : Malgebra p :=
  ⟨f.fourier, hf⟩

@[simp]
theorem inclusion_ofModularForm {k : ZMod (p - 1)}
    (f : ModularFormMod p k)
    (hf : f.fourier ∈ (evaluateResiduePolynomial (p := p)).range) :
    inclusion (ofModularForm f hf) = f.fourier :=
  rfl



instance instInfinite : Infinite (Malgebra p) := by
  have hdim : ∀ n : ℕ, dim (12 * (n : ℤ)) = n + 1 := by
    intro n
    have hnonneg : (0 : ℤ) ≤ 12 * n := by positivity
    have heven : Even (12 * (n : ℤ)) := by
      refine ⟨6 * n, by ring⟩
    have hnotmod : ¬(12 * (n : ℤ)) ≡ 2 [ZMOD 12] := by
      intro h
      rw [Int.ModEq] at h
      omega
    have htoNat : (12 * (n : ℤ)).toNat = 12 * n := by omega
    simp [dim, hnonneg, heven, hnotmod, htoNat]
  let g : ℕ → Malgebra p := fun n =>
    let k : ℤ := 12 * n
    let c : Fin (dim k) := ⟨n, by rw [hdim]; omega⟩
    let f := (PIntegralModularForm.G (p := p) c).Reduce
    ofModularForm f (ModularFormMod.mem_Malgebra f)
  have hneq : ∀ {m n : ℕ}, m < n → g m ≠ g n := by
    intro m n hmn hEq
    let km : ℤ := 12 * m
    let kn : ℤ := 12 * n
    let cm : Fin (dim km) := ⟨m, by rw [show km = 12 * (m : ℤ) by rfl, hdim]; omega⟩
    let cn : Fin (dim kn) := ⟨n, by rw [show kn = 12 * (n : ℤ) by rfl, hdim]; omega⟩
    let fm := (PIntegralModularForm.G (p := p) cm).Reduce
    let fn := (PIntegralModularForm.G (p := p) cn).Reduce
    have hfourier : fm.fourier = fn.fourier := by
      have h := congrArg (fun F : Malgebra p => F.fourier) hEq
      simpa [g, ofModularForm, fm, fn, cm, cn, km, kn] using h
    have hcoeff := congrArg (fun F : PowerSeries (ZMod p) => F.coeff m) hfourier
    have hGm : (PIntegralModularForm.G (p := p) cm).coeff m = 1 := by
      simpa [cm] using
        (PIntegralModularForm.coeff_G_diagonal (p := p) cm)
    have hGn : (PIntegralModularForm.G (p := p) cn).coeff m = 0 := by
      apply PIntegralModularForm.coeff_G_lt
      simpa [cn] using hmn
    change (PIntegralModularForm.coeffToZMod (p := p))
        ((PIntegralModularForm.G (p := p) cm).coeff m) =
      (PIntegralModularForm.coeffToZMod (p := p))
        ((PIntegralModularForm.G (p := p) cn).coeff m) at hcoeff
    rw [hGm, hGn] at hcoeff
    simp at hcoeff
  apply Infinite.of_injective g
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hneq hlt hmn
  · exact hneq hgt hmn.symm



end Malgebra
