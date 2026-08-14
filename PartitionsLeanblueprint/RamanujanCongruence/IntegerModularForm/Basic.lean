
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Defs
import Mathlib.NumberTheory.ModularForms.Discriminant

/- This file contains the definitions of Δ and fℓ as well as some other information
-/

noncomputable section


def delta (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24

scoped [IntegerModularForm] notation:max "δ" => delta
scoped [ModularFormMod] notation:max (priority := high) "δ" => delta



open PowerSeries Finset

section ProductDefs

variable {α : Type*} [CommRing α]

/-- The power series generating function for `Δ`. Can be instantiated over any commutative ring -/

def DeltaProduct (m : ℕ) : α ⟦X⟧ :=
  X * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24

/-- The power series generating function for `fl`. Can be instantiated over any commutative ring -/
def flProduct (ℓ : ℕ) (m : ℕ) : α ⟦X⟧ :=
  X ^ (delta ℓ) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ (24 * delta ℓ)


lemma DeltaProduct_apply (m : ℕ) :
  DeltaProduct m = (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24 := rfl

lemma flProduct_apply (ℓ : ℕ) (m : ℕ) :
  flProduct ℓ m = (X : α⟦X⟧) ^ (delta ℓ) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ (24 * delta ℓ) := rfl



lemma flProduct_eq_DeltaProduct_pow (ℓ : ℕ) : (flProduct ℓ : ℕ → α ⟦X⟧) = DeltaProduct ^ (delta ℓ) := by
  ext1 n; simp_rw [flProduct, Pi.pow_apply, DeltaProduct, pow_mul, mul_pow, prod_pow]


@[simp] lemma map_DeltaProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (n : ℕ) :
    map g (DeltaProduct (α := R) n) = DeltaProduct (α := S) n := by
  simp only [DeltaProduct, map_mul, map_X, map_prod, map_pow, map_sub, map_one]

@[simp] lemma map_coeff_DeltaProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (k j : ℕ) :
    g ((coeff (R := R) k) (DeltaProduct j)) = (coeff (R := S) k) (DeltaProduct j) := by
  trans (coeff (R := S) k) (map g (DeltaProduct j)); rfl; rw [map_DeltaProduct]

@[simp, norm_cast] lemma Int.cast_coeff_DeltaProduct {S : Type*} [CommRing S] (k j : ℕ) :
    ((↑) : ℤ → S) ((coeff k) (DeltaProduct j)) = (coeff (R := S) k) (DeltaProduct j) := by
  trans (Int.castRingHom S) ((coeff k) (DeltaProduct j)); rfl; rw [map_coeff_DeltaProduct]


@[simp] lemma map_flProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (ℓ n : ℕ) :
    map g (flProduct (α := R) ℓ n) = flProduct (α := S) ℓ n := by
  simp only [flProduct_eq_DeltaProduct_pow, map_DeltaProduct, Pi.pow_apply, map_pow]

@[simp] lemma map_coeff_flProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (ℓ k j : ℕ) :
    g ((coeff (R := R) k) (flProduct ℓ j)) = (coeff (R := S) k) (flProduct ℓ j) := by
  trans (coeff (R := S) k) (map g (flProduct ℓ j)); rfl; rw [map_flProduct]

@[simp, norm_cast] lemma Int.cast_coeff_flProduct {S : Type*} [CommRing S] (ℓ k j : ℕ) :
    ((↑) : ℤ → S) ((coeff k) (flProduct ℓ j)) = (coeff (R := S) k) (flProduct ℓ j) := by
  trans (Int.castRingHom S) ((coeff k) (flProduct ℓ j)); rfl; rw [map_coeff_flProduct]


end ProductDefs

section Delta_fl_Defs

namespace IntegerModularForm

def Delta : IntegerModularForm 12 where
  fourier := .mk fun m => (DeltaProduct m).coeff m
  carrier := CuspForm.discriminant
  carrier_eq := sorry

/-- The integer modular form. Equal to `Δ ^ (δ ℓ)` -/
def fl (ℓ : ℕ) : IntegerModularForm (δ ℓ * 12) := Delta.pow (δ ℓ)

/-- The integer modular form of weight 12. Defined by the coefficients of the `DeltaProduct` -/
scoped notation "Δ" => Delta

lemma coeff_Delta (n : ℕ) : (Δ).coeff n = (DeltaProduct n).coeff n := by
  sorry
--   simp [Delta, coeff]

-- alias Delta_eq_coeff_Product := coeff_Delta


-- lemma coeff_fl {ℓ : ℕ} (n : ℕ) : (fl ℓ).coeff n = (flProduct ℓ n).coeff n := by
--   simp_rw [fl, flProduct_eq_DeltaProduct_pow, coeff_pow, Pi.pow_apply,
--       DeltaProduct, PowerSeries.coeff_pow, ← DeltaProduct_apply]

--   set f : ℕ → ℤ := fun m ↦ (DeltaProduct n).coeff m with hf
--   trans ∑ x ∈ Nat.antidiagonalTuple (δ ℓ) n, ∏ y, f (x y)
--   simp only [hf]; congr! with x xin y -
--   exact DeltaProduct_coeff_le (le_refl _) <| le_antidiag_right xin y

--   simp_rw [← finsuppAntidiag_to_antidiagonalTuple (δ ℓ) n f, hf]

-- alias fl_eq_coeff_Product := coeff_fl



@[simp] lemma Delta_zero : (Δ).coeff 0 = 0 := by simp [coeff_Delta, DeltaProduct]

@[simp] lemma Delta_one : (Δ).coeff 1 = 1 := by simp [coeff_Delta, DeltaProduct]

@[simp] lemma Delta_two : (Δ).coeff 2 = -24 := by
  simp [coeff_Delta, DeltaProduct, prod_range]
  ring_nf
  simpa only [map_add, map_sub, coeff_one, one_ne_zero, ↓reduceIte, coeff_one_mul, coeff_one_X,
    one_mul, constantCoeff_X, mul_zero, add_zero, zero_sub, coeff_X_pow_mul', Nat.not_ofNat_le_one,
    sub_zero, coeff_X_pow, OfNat.one_ne_ofNat, Int.reduceNeg, neg_inj, Nat.cast_ofNat] using
    (map_natCast _ _ : constantCoeff 24 = (24 : ℤ))

@[simp] lemma Delta_three : (Δ).coeff 3 = 252 := by
  simp [coeff_Delta, DeltaProduct, prod_range, Fin.prod_univ_three]
  ring_nf
  simp only [map_add, map_sub, coeff_one, OfNat.ofNat_ne_zero, ↓reduceIte, zero_sub,
    coeff_X_pow_mul', Std.le_refl, tsub_self, coeff_zero_eq_constantCoeff, Nat.reduceLeDiff,
    sub_zero, add_zero, coeff_X_pow, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  rw [← _root_.pow_one X, coeff_X_pow_mul']
  simp only [Nat.one_le_ofNat, ↓reduceIte, Nat.reduceSub]
  show - (C 24).coeff 1 + _ = 252
  rw [coeff_succ_C, neg_zero, zero_add]
  rfl
