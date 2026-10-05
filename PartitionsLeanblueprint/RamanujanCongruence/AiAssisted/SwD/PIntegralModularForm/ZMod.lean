import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.Basis
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Defs

/-!
# Reduction of p-integral modular forms modulo p

The coefficient map from `ℤ_(p)` to `ZMod p` sends the Fourier expansion of a
p-integral modular form to a modular form modulo p. We construct the target
form using the `G` basis and prove that this agrees with the usual reduction
on forms coming from integer modular forms.
-/

open PowerSeries

namespace PIntegralModularForm

noncomputable section

variable {p : ℕ} [isLargePrime p] {k : ℤ}

/-- The residue map from the localization of `ℤ` at `(p)` to `ZMod p`. -/
noncomputable def coeffToZMod : CoeffRing p →+* ZMod p :=
  IsLocalization.lift (M := (primeIdeal p).primeCompl)
    (g := Int.castRingHom (ZMod p)) (by
      intro x
      apply isUnit_iff_ne_zero.mpr
      intro hx
      have hmem : (x : ℤ) ∈ primeIdeal p := by
        change (x : ℤ) ∈ Ideal.span {(p : ℤ)}
        rw [Ideal.mem_span_singleton]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x : ℤ) p).mp hx
      exact x.2 hmem)

@[simp]
theorem coeffToZMod_algebraMap (z : ℤ) :
    coeffToZMod (p := p) (algebraMap ℤ (CoeffRing p) z) = (z : ZMod p) := by
  simp [coeffToZMod]

theorem coeffToZMod_comp_algebraMap :
    (coeffToZMod (p := p)).comp (algebraMap ℤ (CoeffRing p)) =
      Int.castRingHom (ZMod p) := by
  ext z
  simp

private theorem map_fourier_ofInteger {g : IntegerModularForm k} :
    PowerSeries.map (coeffToZMod (p := p)) (ofInteger (p := p) g).fourier =
      g.reduce p := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, ofInteger,
    IntegerModularForm.reduce_apply]
  exact coeffToZMod_algebraMap (p := p) (g.fourier.coeff n)

private theorem map_smul_series {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (a : R) (F : PowerSeries R) :
    PowerSeries.map φ (a • F) = φ a • PowerSeries.map φ F := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_smul]

private theorem fourier_sum_pIntegral {α : Type*} (s : Finset α)
    (f : α → PIntegralModularForm p k) :
    (∑ a ∈ s, f a).fourier = ∑ a ∈ s, (f a).fourier := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

@[simp]
private theorem fourier_smul_pIntegral (a : CoeffRing p)
    (f : PIntegralModularForm p k) : (a • f).fourier = a • f.fourier := rfl

private theorem fourier_sum_modularFormMod {α : Type*} (s : Finset α)
    (f : α → ModularFormMod p (k : ZMod (p - 1))) :
    (∑ a ∈ s, f a).fourier = ∑ a ∈ s, (f a).fourier := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Reduce a p-local linear combination of the integral `G` forms. -/
private noncomputable def basisReduce (f : PIntegralModularForm p k) :
    ModularFormMod p (k : ZMod (p - 1)) :=
  ∑ i : Fin (dim k),
    coeffToZMod (p := p) ((GBasis (p := p) k).repr f i) •
      (IntegerModularForm.G i).Reduce p

private theorem map_fourier_eq_basisReduce (f : PIntegralModularForm p k) :
    PowerSeries.map (coeffToZMod (p := p)) f.fourier =
      (basisReduce (p := p) f).fourier := by
  let b := GBasis (p := p) k
  have hrepr : f.fourier =
      ∑ i : Fin (dim k), (b.repr f i) • (G (p := p) i).fourier := by
    have h := congrArg (fun g : PIntegralModularForm p k => g.fourier) (b.sum_repr f)
    simpa [b, fourier_sum_pIntegral, fourier_smul_pIntegral, GBasis_apply] using h.symm
  rw [hrepr, map_sum]
  simp only [map_smul_series]
  change _ = (∑ i : Fin (dim k),
    coeffToZMod (p := p) ((b.repr f) i) • (IntegerModularForm.G i).Reduce p).fourier
  rw [fourier_sum_modularFormMod]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact map_fourier_ofInteger (p := p) (g := IntegerModularForm.G i)

/-- Reduction of a p-integral modular form to a modular form modulo p. -/
noncomputable def Reduce : PIntegralModularForm p k →ₗ[ℤ] ModularFormMod p (k : ZMod (p - 1)) where
  toFun f := {
    fourier := PowerSeries.map (coeffToZMod (p := p)) f.fourier
    modular := by
      rw [map_fourier_eq_basisReduce]
      exact (basisReduce (p := p) f).modular
  }
  map_add' f g := ModularFormMod.fourier_inj <| by
    simp only [fourier_add, map_add, ModularFormMod.fourier_add]
  map_smul' c f := ModularFormMod.fourier_inj <| by
    simp only [fourier_zsmul, zsmul_eq_mul, map_mul, map_intCast,
      eq_intCast, Int.cast_eq, ModularFormMod.fourier_zsmul]


@[simp]
theorem fourier_Reduce (f : PIntegralModularForm p k) :
    (f.Reduce).fourier = PowerSeries.map (coeffToZMod (p := p)) f.fourier := rfl

@[simp]
theorem coeff_Reduce (f : PIntegralModularForm p k) (n : ℕ) :
    (f.Reduce).coeff n = coeffToZMod (p := p) (f.coeff n) := by
  simp [ModularFormMod.coeff_def]

/-- Reducing the p-integral lift of an integer modular form is its usual
reduction modulo p. -/
theorem Reduce_ofInteger (f : IntegerModularForm k) :
    (ofInteger (p := p) f).Reduce = f.Reduce p := by
  apply ModularFormMod.fourier_inj
  change PowerSeries.map (coeffToZMod (p := p)) (ofInteger (p := p) f).fourier =
    (f.Reduce p).fourier
  rw [map_fourier_ofInteger, IntegerModularForm.fourier_Reduce]



end
end PIntegralModularForm
