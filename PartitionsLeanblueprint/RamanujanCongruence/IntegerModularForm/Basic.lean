import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Defs
import PartitionsLeanblueprint.RamanujanCongruence.EventuallyEq
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Tactic.ModCases


/- This file contains the definitions of Δ and fℓ as well as some other information
It has 3 sorries
· `num_two_mul_bernoulli (k : ℕ) : (2 * k / bernoulli k).num = (2 * k / bernoulli k : ℂ)`
· `Delta.carrier_eq`
· `dvd_coeff_succ_El (n) : ↑ℓ ∣ (El ℓ).coeff (n + 1)`
-/


lemma Finset.finsuppAntidiag.le_right {k n} {x : ℕ →₀ ℕ} (xin : x ∈ (Finset.range k).finsuppAntidiag n) :
    ∀ {y}, y ∈ Finset.range k → x y ≤ n := fun {y} yin => by
  rw [Finset.mem_finsuppAntidiag, And.comm] at xin; contrapose! xin
  intro xsupp
  apply Nat.ne_of_gt
  exact xin |> Trans.trans <| Finset.single_le_sum_of_canonicallyOrdered yin



def delta (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24

scoped [IntegerModularForm] notation:max "δ" => delta
scoped [ModularFormMod] notation:max (priority := high) "δ" => delta

section delta_facts

open scoped IntegerModularForm

class isLargePrime (ℓ : ℕ) where [Prime : ℓ.Prime] [AtLeastFive : ℓ ≥ 5]

class isLargerPrime (ℓ : ℕ) where [Prime : ℓ.Prime] [AtLeastThirteen : ℓ ≥ 13]

instance (ℓ) [h : isLargePrime ℓ] : Fact (ℓ.Prime) := ⟨h.Prime⟩
instance (ℓ) [h : isLargePrime ℓ] : Fact (ℓ ≥ 5) := ⟨h.AtLeastFive⟩
instance (ℓ) [h : isLargePrime ℓ] : ℓ.AtLeastTwo := ⟨by grind [h.AtLeastFive]⟩
instance (ℓ) [h : isLargerPrime ℓ] : Fact (ℓ.Prime) := ⟨h.Prime⟩
instance (ℓ) [h : isLargerPrime ℓ] : Fact (ℓ ≥ 13) := ⟨h.AtLeastThirteen⟩
instance (ℓ) [h : isLargerPrime ℓ] : isLargePrime ℓ := {Prime := h.Prime, AtLeastFive := by grind [h.AtLeastThirteen]}
instance (ℓ) [h : isLargerPrime ℓ] : ℓ.AtLeastTwo := ⟨by grind [h.AtLeastThirteen]⟩

instance (ℓ) [Fact (ℓ.Prime)] [Fact (ℓ ≥ 5)] : isLargePrime ℓ where
  Prime := Fact.out
  AtLeastFive := Fact.out


lemma delta_cast (ℓ) [NeZero ℓ] : (δ ℓ : ℤ) = ((ℓ : ℤ) ^ 2 - 1)/24 := by
  rw [delta, Int.natCast_ediv, Nat.cast_ofNat,
    Int.natCast_pred_of_pos <| pow_two_pos_of_ne_zero NeZero.out, Nat.cast_pow]

lemma not_dvd_filt (ℓ) [Fact (Nat.Prime ℓ)] : ¬ ℓ ∣ (ℓ ^ 2 - 1) / 2 := by
  intro h
  by_cases l2 : ℓ = 2
  simp only [l2, Nat.reducePow, Nat.add_one_sub_one, Nat.reduceDiv, Nat.dvd_one,
    OfNat.ofNat_ne_one] at h

  have : Odd ℓ := Nat.Prime.odd_of_ne_two Fact.out l2;
  have h_div_full : ℓ ∣ (ℓ ^ 2 - 1) / 2 * 2 := by
    exact Nat.dvd_mul_right_of_dvd h 2

  have : ℓ ∣ (ℓ ^ 2 - 1) := by
    trans (ℓ ^ 2 - 1) / 2 * 2
    exact Nat.dvd_mul_right_of_dvd h 2
    apply dvd_of_eq

    apply Nat.div_two_mul_two_of_even
    apply Nat.Odd.sub_odd (Odd.pow this)
    exact Nat.odd_iff.mpr rfl

  have don : ℓ ^ 2 - 1 = (ℓ + 1) * (ℓ - 1) := by
      trans ℓ * ℓ - 1
      rw[pow_two]
      exact mul_self_tsub_one ℓ

  rw[don] at this
  have bla : ℓ ∣ (ℓ + 1) ∨ ℓ ∣ (ℓ - 1) := (Nat.Prime.dvd_mul Fact.out).mp this
  have lg2 : ℓ ≥ 2 := Nat.Prime.two_le Fact.out
  rcases bla with h|h
  contrapose! h
  refine (Nat.not_dvd_iff_lt_mul_succ (ℓ + 1) ?_).mpr ?_
  exact Nat.pos_of_neZero ℓ
  use 1; constructor <;> linarith
  contrapose! h
  exact Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_sub_of_lt lg2) (Nat.sub_one_lt_of_lt lg2)

lemma delta_integer (ℓ) [hℓ : isLargePrime ℓ]: 24 ∣ ℓ ^ 2 - 1 := by

  have lg5 : ℓ ≥ 5 := isLargePrime.AtLeastFive
  have fivesq : 5 * 5 = 25 := rfl
  have lsq : ℓ ^ 2 ≥ 25 :=
    fivesq ▸ pow_two ℓ ▸ mul_le_mul lg5 lg5 (Nat.zero_le 5) (Nat.zero_le ℓ)
  have lprime : Nat.Prime ℓ := Fact.out
  have don : ℓ ^ 2 - 1 = (ℓ + 1) * (ℓ - 1) := by
    trans ℓ * ℓ - 1
    rw[pow_two]
    exact mul_self_tsub_one ℓ


  suffices h : 3 ∣ ℓ ^ 2 - 1 ∧ 8 ∣ ℓ ^ 2 - 1 by
    have : 24 = 3 * 8 := rfl
    rw[this]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h.1 h.2
  constructor

  have h : 3 ∣ ℓ ∨ 3 ∣ (ℓ - 1) ∨ 3 ∣ (ℓ + 1) := by omega
  rcases h with h | h | h
  exfalso
  simp_all only [ge_iff_le, Nat.reduceMul]
  have l3 : ℓ = 3 := by
    obtain ⟨k,rfl⟩ := h
    rcases lprime.2 rfl with h' | h'
    simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
    simp_all only [isUnit_iff_eq_one, mul_one]
  linarith
  rw[don]; exact Nat.dvd_mul_left_of_dvd h (ℓ + 1)
  rw[don]; exact Nat.dvd_mul_right_of_dvd h (ℓ - 1)

  have h : 8 ∣ ℓ ∨ 8 ∣ (ℓ - 1) ∨ 8 ∣ (ℓ - 2) ∨ 8 ∣ (ℓ - 3) ∨
    8 ∣ (ℓ - 4) ∨ 8 ∣ (ℓ - 5) ∨ 8 ∣ (ℓ + 2) ∨ 8 ∣ (ℓ + 1) := by omega

  rcases h with h | h | h | h | h | h | h | h

  {
    exfalso
    have l8 : ℓ = 8 := by
      obtain ⟨k,rfl⟩ := h
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    rw[l8] at lprime
    contrapose! lprime
    decide
  }
  { rw[don]; exact Nat.dvd_mul_left_of_dvd h (ℓ + 1) }
  {
    exfalso
    have d2l : 2 ∣ ℓ := by omega
    have l3 : ℓ = 2 := by
      obtain ⟨k,rfl⟩ := d2l
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    linarith
  }
  {
    suffices ℓ ^ 2 ≡ 1 [MOD 8] from
      (Nat.modEq_iff_dvd' (Nat.one_le_of_lt lsq)).mp (Nat.ModEq.symm this)
    trans 3 * 3
    rw[pow_two]; refine Nat.ModEq.symm (Nat.ModEq.mul ?_ ?_) <;>
    rwa[Nat.modEq_iff_dvd']
    exact le_of_add_le_right lg5
    exact le_of_add_le_right lg5
    rfl
  }
  {
    exfalso
    have d2l : 2 ∣ ℓ := by omega
    have l3 : ℓ = 2 := by
      obtain ⟨k,rfl⟩ := d2l
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    linarith
  }
  {
    suffices ℓ ^ 2 ≡ 1 [MOD 8] from
      (Nat.modEq_iff_dvd' (Nat.one_le_of_lt lsq)).mp (id (Nat.ModEq.symm this))
    trans 5 * 5
    rw[pow_two]; refine Nat.ModEq.symm (Nat.ModEq.mul ?_ ?_) <;>
    rwa[Nat.modEq_iff_dvd']
    exact lg5
    exact lg5
    rfl
  }
  {
    exfalso
    have d2l : 2 ∣ ℓ := by omega
    have l3 : ℓ = 2 := by
      obtain ⟨k,rfl⟩ := d2l
      rcases lprime.2 rfl with h' | h'
      simp_all only [isUnit_iff_eq_one, OfNat.ofNat_ne_one]
      simp_all only [isUnit_iff_eq_one, mul_one]
    linarith
  }
  { rw[don]; exact Nat.dvd_mul_right_of_dvd h (ℓ - 1) }



lemma delta_pos (ℓ) [Fact (ℓ ≥ 5)] : (ℓ^2 - 1) / 24 > 0 := by
  have lg5 : ℓ ≥ 5 := Fact.out
  have fivesq : 5 * 5 = 25 := rfl
  have lsq : ℓ ^ 2 ≥ 25 :=
    fivesq ▸ pow_two ℓ ▸ mul_le_mul lg5 ‹_› (Nat.zero_le 5) (Nat.zero_le ℓ)
  apply Nat.div_pos
  omega
  exact Nat.zero_lt_succ 23

instance delta_ne_zero {n} [Fact (n ≥ 5)] : NeZero (δ n) where
  out := have := @delta_pos n _
    by rwa [Nat.ne_zero_iff_zero_lt]


lemma twelve_delta (ℓ) [isLargePrime ℓ] : 12*(δ ℓ) = (ℓ^2 - 1) / 2 := by
  rw[delta]; refine Eq.symm (Nat.div_eq_of_eq_mul_right zero_lt_two ?_)
  trans 24 * ((ℓ ^ 2 - 1) / 24)
  exact (Nat.mul_div_cancel' <| delta_integer ℓ).symm
  rw [← mul_assoc]; rfl

lemma not_dvd_delta (ℓ) [isLargePrime ℓ] : ¬ ℓ ∣ δ ℓ := by
  have h := not_dvd_filt ℓ
  contrapose! h; calc
    _ ∣ 12 * δ ℓ := Nat.dvd_mul_left_of_dvd h 12
    _ = (ℓ ^ 2 - 1)/2 := twelve_delta ℓ


lemma twentyfour_mul_delta (ℓ) [isLargePrime ℓ] : 24 * δ ℓ = ℓ ^ 2 - 1 :=
  Nat.mul_div_cancel' <| delta_integer ℓ


end delta_facts








open PowerSeries Finset

noncomputable section ProductDefs

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

section Delta_coeff_le

open Nat PowerSeries

variable {α : Type*}

lemma DeltaProduct_coeff_le' [CommRing α] {n m j : ℕ} (nlm : n ≤ m) (mlj : m ≤ j) :
    coeff (R := α) n (DeltaProduct m) = coeff (R := α) n (DeltaProduct j) := by

  by_cases n0 : n = 0
  simp [DeltaProduct, n0]

  have npos : n > 0 := zero_lt_of_ne_zero n0
  simp only [DeltaProduct, coeff_X_mul _ npos]
  set k := n - 1 with keq; symm; calc
    _ = coeff (R := α) k ((∏ i ∈ Ico 0 m, (1 - X ^ (i + 1)) ^ 24) *
        (∏ i ∈ Ico m j, (1 - X ^ (i + 1)) ^ 24)) := by
      rw [prod_Ico_consecutive, Ico_zero_eq_range]
      exact Nat.zero_le m; exact mlj
    _ = _ := by
      rw [Ico_zero_eq_range, coeff_mul]

      have coeff_eq_ite {k : ℕ} (klt : k < m) :
          coeff (R := α) k (∏ i ∈ Ico m j, (1 - X ^ (i + 1)) ^ 24) = if k = 0 then 1 else 0 := by
        split_ifs with k0
        rw [k0]; simp

        rw [coeff_prod]; apply sum_eq_zero;
        intro x xin; rw [mem_finsuppAntidiag] at xin

        have exy : ∃ y ∈ Ico m j, x y ≠ 0 ∧ x y < m := by
          contrapose! xin

          intro sum_eq
          contrapose! sum_eq
          have fozer {k} (hk : x k ≠ 0) : k ∈ Ico m j := by
            have : k ∈ x.support := Finsupp.mem_support_iff.mpr hk
            exact sum_eq this

          by_cases ex : ∃ y, x y ≠ 0
          obtain ⟨y, yn0⟩ := ex
          have : y ≥ m := List.left_le_of_mem_range' (fozer yn0)
          apply Nat.ne_of_gt; calc
            _ < m := klt
            _ ≤ x y := xin y (fozer yn0) yn0
            _ ≤ (Ico m j).sum ⇑x := single_le_sum_of_canonicallyOrdered <| fozer yn0



          push Not at ex
          suffices (Ico m j).sum ⇑x = 0 by symm; rwa[this]
          exact sum_eq_zero (λ y _ ↦ ex y)

        obtain ⟨y, yin, xyn0, xylm⟩ := exy
        rw [prod_eq_zero]; use yin
        rw [coeff_pow]
        set f : ℕ → α := fun n ↦ (coeff (R := α) n) (1 - X ^ (y + 1)) with hf
        trans ∑ l ∈ (range 24).finsuppAntidiag (x y), ∏ i ∈ range 24, f (l i); rfl


        rw [hf]; dsimp; apply sum_eq_zero; intro z zin
        obtain ⟨zin, supp⟩ := by simpa using zin

        have exb : ∃ b ∈ range 24, z b > 0 := by
          contrapose! zin
          have : (range 24).sum z = 0 := sum_eq_zero λ x h ↦ eq_zero_of_le_zero (zin x h)
          symm; rwa [this]
        obtain ⟨b, bin, bn0⟩ := exb

        rw [prod_eq_zero bin]

        have ble : z b < y := by
          have : z b ≤ (range 24).sum z := single_le_sum_of_canonicallyOrdered bin
          have : m ≤ y := by rw [mem_Ico] at yin; exact yin.1
          omega

        simp only [map_sub, coeff_one]; rw [if_neg (Nat.ne_of_gt bn0)]
        simp only [zero_sub, neg_eq_zero, coeff_pow]

        apply sum_eq_zero; intro x xsum
        have exc : ∃ c ∈ range (y + 1), x c < 1 := by
          contrapose! xsum; simp only [mem_finsuppAntidiag, And.comm, not_and]
          intro xin; apply Nat.ne_of_gt
          have : (range (y + 1) ).sum 1 ≤ (range (y + 1)).sum x := sum_le_sum <| by simpa using xsum
          simp only [Pi.one_apply, sum_const, card_range, smul_eq_mul, mul_one, Order.add_one_le_iff] at this
          omega

        obtain ⟨c, cin, c0⟩ := exc; rw [lt_one_iff] at c0
        rw [prod_eq_zero cin]
        rw [c0, coeff_zero_X]


      calc
        _ = ∑ p ∈ antidiagonal k, (coeff (R := α) p.1) (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24) *
            if p.2 = 0 then 1 else 0 := by
          congr! with p pin
          have plt : p.2 < m := by
            have : p.2 ≤ k := HasAntidiagonal.antidiagonal.snd_le pin
            omega
          rw [coeff_eq_ite plt]

        _ =  ∑ x ∈ {(k,0)}, (coeff (R := α) x.1) (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24) := by
          simp only [mul_ite, mul_one, mul_zero, sum_ite, sum_const_zero, add_zero]
          congr with x; simp only [mem_filter, mem_antidiagonal, mem_singleton]
          simp_all only [gt_iff_lt, k]
          obtain ⟨fst, snd⟩ := x
          simp_all only [Prod.mk.injEq, and_congr_left_iff, add_zero, implies_true]

        _ = _ := by simp only [sum_singleton]


theorem DeltaProduct_coeff_le [CommRing α] {n m j : ℕ} (nlm : n ≤ m) (nlj : n ≤ j) :
    coeff (R := α) n (DeltaProduct m) = coeff (R := α) n (DeltaProduct j) :=
  (Nat.le_total m j).casesOn
    (DeltaProduct_coeff_le' nlm · )
    (.symm <| DeltaProduct_coeff_le' nlj ·)


theorem flProduct_coeff_le [CommRing α] {ℓ n m j : ℕ} (nlm : n ≤ m) (nlj : n ≤ j) :
    coeff (R := α) n (flProduct ℓ m) = coeff (R := α) n (flProduct ℓ j) := by
  simp [flProduct_eq_DeltaProduct_pow, coeff_pow]
  congr! 2 with x xin y yin
  exact DeltaProduct_coeff_le
    ((Finset.finsuppAntidiag.le_right xin yin).trans nlm)
    ((Finset.finsuppAntidiag.le_right xin yin).trans nlj)




end Delta_coeff_le

namespace IntegerModularForm

noncomputable section Delta_fl_Defs


/-- The integer modular form of weight 12. Defined by the coefficients of the `DeltaProduct` -/
def Delta : IntegerModularForm 12 where
  fourier := .mk fun m => (DeltaProduct m).coeff m
  carrier := CuspForm.discriminant
  carrier_eq := sorry


@[inherit_doc] scoped notation "Δ" => Delta


/-- The integer modular form. Equal to `Δ ^ (δ ℓ)` -/
def fl (ℓ : ℕ) : IntegerModularForm (δ ℓ * 12) := Delta.pow (δ ℓ)



lemma coeff_Delta (n : ℕ) : (Δ).coeff n = (DeltaProduct n).coeff n := by
  simp only [coeff, Delta, coeff_mk]

alias Delta_eq_coeff_Product := coeff_Delta


lemma coeff_fl {ℓ : ℕ} (n : ℕ) : (fl ℓ).coeff n = (flProduct ℓ n).coeff n := by
  simp_rw [fl, flProduct_eq_DeltaProduct_pow, coeff_pow, Pi.pow_apply,
      DeltaProduct, PowerSeries.coeff_pow, ← DeltaProduct_apply]
  congr! with x xin y yin
  rw [← DeltaProduct_coeff_le (le_refl _) <| finsuppAntidiag.le_right xin yin]
  exact coeff_Delta (x y)

alias fl_eq_coeff_Product := coeff_fl


variable {α : Type*}

theorem DeltaProduct_eventually_sum [CommRing α] :
    (DeltaProduct ·) ⟶ (∑ i ∈ range ·, Delta.coeff i • (X : α⟦X⟧) ^ i) := by

  intro n
  simp_rw [coeff_Delta]
  use n + 1; intro k kle j jg
  have : j > k := Nat.lt_of_le_of_lt kle jg
  trans (PowerSeries.coeff (R := α) k) (∑ x ∈ range j, C ((PowerSeries.coeff (R := α) x) (DeltaProduct x)) * X ^ x)
  set f : ℕ → α := fun n ↦ (PowerSeries.coeff (R := α) n) (DeltaProduct n) with feq
  rw [coeff_sum_X_pow (a := f) this, feq]; symm

  exact DeltaProduct_coeff_le (le_refl k) <| le_of_lt this
  congr! 2 with x -; rw [map_coeff_DeltaProduct, zsmul_eq_mul, Int.cast_coeff_DeltaProduct]



theorem flProduct_eventually_sum [CommRing α] (ℓ) :
    (flProduct ℓ ·) ⟶ (∑ i ∈ range ·, (fl ℓ).coeff i • (X : α⟦X⟧) ^ i) := by

  rw [flProduct_eq_DeltaProduct_pow, fl]; symm; calc

    _ ⟶ (fun x ↦ ∑ i ∈ range x, (Delta.coeff i) • (X : α ⟦X⟧) ^ i) ^ (δ ℓ) := by

      intro k; use k + 1; intro n nlek M Mgk
      dsimp
      simp_rw [coeff_pow]

      have rw1 (x) : (((∑ l ∈ (range (δ ℓ)).finsuppAntidiag x, ∏ i ∈ range (δ ℓ), IntegerModularForm.coeff (l i) Δ) : ℤ) : α ⟦X⟧) =
        C (R := α) (∑ l ∈ (range (δ ℓ)).finsuppAntidiag x, ∏ i ∈ range (δ ℓ), IntegerModularForm.coeff (l i) Δ) := by
          simp only [map_sum, map_prod, map_intCast, Int.cast_sum, Int.cast_prod]

      have rw2 (i) : (Delta.coeff i : α ⟦X⟧) = C (R := α) (IntegerModularForm.Delta.coeff i) := by
        simp only [map_intCast]

      have nlM : n < M := by omega
      simp_rw [zsmul_eq_mul, rw1, coeff_sum_X_pow nlM, PowerSeries.coeff_pow]

      apply sum_congr rfl; intro y yin
      apply prod_congr rfl; intro i ilt
      have ylen : y i ≤ n := by calc
        _ = ∑ j ∈ {i}, y j := rfl
        _ ≤ ∑ j ∈ range (δ ℓ), y j :=
          sum_le_sum_of_subset <| singleton_subset_iff.mpr ilt
        _ = n := by rw [mem_finsuppAntidiag] at yin; exact yin.1

      simp only [rw2, coeff_sum_X_pow (ylen |> Trans.trans <| nlM)]

    _ ⟶ (DeltaProduct ·) ^ δ ℓ := by
      gcongr; exact DeltaProduct_eventually_sum.symm


@[simp] lemma Delta_zero : (Δ).coeff 0 = 0 := by simp [coeff_Delta, DeltaProduct]

@[simp] lemma Delta_one : (Δ).coeff 1 = 1 := by simp [coeff_Delta, DeltaProduct]

@[simp] lemma Delta_two : (Δ).coeff 2 = -24 := by
  simp [coeff_Delta, DeltaProduct, prod_range]
  ring_nf
  simpa only [map_add, map_sub, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte, PowerSeries.coeff_one_mul,
    coeff_one_X, _root_.one_mul, constantCoeff_X, MulZeroClass.mul_zero, add_zero, zero_sub,
    coeff_X_pow_mul', Nat.not_ofNat_le_one, sub_zero, coeff_X_pow, OfNat.one_ne_ofNat,
    Int.reduceNeg, neg_inj, Nat.cast_ofNat] using (map_natCast _ _ : constantCoeff 24 = (24 : ℤ))

@[simp] lemma Delta_three : (Δ).coeff 3 = 252 := by
  simp [coeff_Delta, DeltaProduct, prod_range, Fin.prod_univ_three]
  ring_nf
  simp only [map_add, map_sub, PowerSeries.coeff_one, OfNat.ofNat_ne_zero, ↓reduceIte, zero_sub,
    coeff_X_pow_mul', Std.le_refl, tsub_self, coeff_zero_eq_constantCoeff, Nat.reduceLeDiff,
    sub_zero, add_zero, coeff_X_pow, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  rw [← _root_.pow_one X, coeff_X_pow_mul']
  simp only [Nat.one_le_ofNat, ↓reduceIte, Nat.reduceSub]
  show -(C 24).coeff 1 + _ = 252
  rw [coeff_succ_C, neg_zero, zero_add]
  rfl


lemma fl_lt_delta {ℓ n} (nlt : n < δ ℓ) : (fl ℓ).coeff n = 0 :=
  leading_pow_zeros Delta_zero nlt

@[simp] lemma fl_delta {ℓ} : (fl ℓ).coeff (δ ℓ) = 1 := by
   rw [fl, coeff_pow_of_leading_zero Delta_zero (δ ℓ), Delta_one, one_pow]


@[simp] lemma fl_delta_add_one {ℓ} [isLargePrime ℓ] : (fl ℓ).coeff (δ ℓ + 1) = 1 - ℓ ^ 2 := by
  rw [fl, coeff_succ_pow_of_leading_zero Delta_zero (δ ℓ), Delta_two, Delta_one]
  simp only [Int.reduceNeg, Int.nsmul_eq_mul, mul_neg, one_pow, _root_.mul_one]
  norm_cast
  rw [mul_comm, twentyfour_mul_delta,
    Int.natCast_pred_of_pos <| pow_two_pos_of_ne_zero NeZero.out, Nat.cast_pow, neg_sub]
  norm_cast


end Delta_fl_Defs

noncomputable section Eisenstein_defs

open ModularForm PowerSeries ArithmeticFunction.sigma UpperHalfPlane MatrixGroups


lemma num_two_mul_bernoulli (k : ℕ) : (2 * k / bernoulli k).num = (2 * k / bernoulli k : ℂ) := sorry

def EisNat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : IntegerModularForm k where
  fourier := .mk fun m => if m = 0 then 1 else -(2 * k / bernoulli k).num * (σ (k - 1) m)
  carrier := E hk
  carrier_eq := PowerSeries.ext fun m => by
    simp [qexp_eq', EisensteinSeries.E_qExpansion_coeff hk hk2, num_two_mul_bernoulli]


def EisInt {k : ℤ} (hk : 3 ≤ k) (hk2 : Even k) : IntegerModularForm k :=
  Icast (h := Int.toNat_of_nonneg (by lia)) <| EisNat (k := k.toNat) (show 3 ≤ k.toNat from
    (Int.le_toNat (by lia)).mpr hk)
    (show Even k.toNat from (Int.even_coe_nat k.toNat).mp <| by rwa [Int.toNat_of_nonneg (by lia)])

def Eis (k : ℤ) : IntegerModularForm k :=
  if hk : 3 ≤ k then if hk2 : Even k then EisInt hk hk2 else 0 else 0

theorem coeff_EisNat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n) :
    (EisNat hk hk2).coeff n = if n = 0 then 1 else -(2 * k / bernoulli k).num * (σ (k - 1) n) := by
  rw [EisNat, ← coeff_def, coeff_mk]


lemma coeff_eq_EisNat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n) :
    (EisNat hk hk2).coeff n = (qExpansion 1 (E hk)).coeff n := by
  simp [EisensteinSeries.E_qExpansion_coeff hk hk2, ← num_two_mul_bernoulli, coeff_EisNat]

lemma coeff_eq_EisInt {k : ℤ} (hk : 3 ≤ k) (hk2 : Even k) (n) :
    (EisInt hk hk2).coeff n = (qExpansion 1 (E (show 3 ≤ k.toNat by grind))).coeff n := by
  simp [EisInt, coeff_eq_EisNat]

lemma coeff_eq_Eis {k : ℤ} (hk : 3 ≤ k) (n) :
    (Eis k).coeff n = (qExpansion 1 (E (show 3 ≤ k.toNat by grind))).coeff n := by
  rw [Eis]
  split_ifs with hk2
  · rw [coeff_eq_EisInt]
  · have kodd := Int.not_even_iff_odd.1 hk2
    lift k to ℕ using by lia
    simp [ModularForm.levelOne_odd_weight_eq_zero kodd <| E _, qExpansion_zero]


lemma coeff_Eis {k} (hk : 3 ≤ k) (hk2 : Even k) (n) :
    (Eis k).coeff n = if n = 0 then 1 else -(2 * k / bernoulli k.toNat).num * (σ (k.toNat - 1) n) := by
  lift k to ℕ using by lia
  simp [Eis, EisInt, dif_pos hk, dif_pos hk2, coeff_EisNat]

lemma Eis_lt_three {k} (hk : k ≤ 2) : Eis k = 0 := dif_neg <| by lia

lemma Eis_Odd {k} (hk : Odd k) : Eis k = 0 := by
  simpa only [Eis, dite_eq_right_iff] using fun _ hk2 => (Int.not_odd_iff_even.2 hk2) hk |>.elim

lemma Eis_zero {k} (hk : 3 ≤ k) (hk2 : Even k) : (Eis k).coeff 0 = 1 := by
  rw [coeff_Eis hk hk2, if_pos rfl]

@[simp] theorem Eis_four_zero : (Eis 4).coeff 0 = 1 :=
  Eis_zero (by decide) (by decide)

@[simp] theorem Eis_six_zero : (Eis 6).coeff 0 = 1 :=
  Eis_zero (by decide) (by decide)

@[simp] theorem Eis_four_one : (Eis 4).coeff 1 = 240 := by
  rw [coeff_Eis (by decide) (by decide), if_neg one_ne_zero]
  simp [bernoulli]
  norm_num

end Eisenstein_defs



noncomputable section Eis_sub_one

variable (ℓ : ℕ)

def reduce {k : ℤ} (ℓ : ℕ) : IntegerModularForm k →ₗ[ℤ] PowerSeries (ZMod ℓ) where
  toFun f := map (Int.castRingHom (ZMod ℓ)) f.fourier
  map_add' := by simp
  map_smul' := by simp


@[simp] theorem reduce_apply {k} (ℓ) (f : IntegerModularForm k) (n) :
    (reduce ℓ f).coeff n = f.coeff n := rfl

@[simp]
theorem reduce_mul {k j : ℤ} (ℓ : ℕ) (f : IntegerModularForm k) (g : IntegerModularForm j) :
    (f.mul g).reduce ℓ = f.reduce ℓ * g.reduce ℓ := by
  simp only [reduce, LinearMap.coe_mk, AddHom.coe_mk, fourier_mul, map_mul]

@[simp]
theorem reduce_pow {k} (ℓ : ℕ) (f : IntegerModularForm k) (m : ℕ) :
    (f.pow m).reduce ℓ = f.reduce ℓ ^ m := by
  simp only [reduce, LinearMap.coe_mk, AddHom.coe_mk, fourier_pow, map_pow]

variable [hℓ : isLargePrime ℓ]

abbrev El := EisNat (show 3 ≤ ℓ - 1 by grind [hℓ.AtLeastFive]) (by
    suffices Odd ℓ by grind [hℓ.AtLeastFive]
    exact Nat.Prime.odd_iff hℓ.Prime|>.mpr <| show 3 ≤ 5 by norm_num |>.trans hℓ.AtLeastFive)

@[simp] theorem El_zero : (El ℓ).coeff 0 = 1 := by rw [coeff_EisNat, if_pos rfl]



theorem dvd_coeff_succ_El (n) : ↑ℓ ∣ (El ℓ).coeff (n + 1) := by
  rw [coeff_EisNat, if_neg n.add_one_ne_zero]
  apply Int.dvd_mul_of_dvd_left
  rw [Int.dvd_neg]

  nth_rw 1 [← _root_.pow_one (ℓ : ℤ), padicValInt_dvd_iff_of_ne_one (by sorry)]
  right; zify
  calc
    1 ≤ padicValRat ℓ (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)) := by
      sorry

    _ ≤ padicValInt ℓ (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)).num := by
      rw [padicValRat.div]
      norm_cast
      sorry
      sorry
      sorry




theorem reduce_El : (El ℓ).reduce ℓ = 1 :=
  PowerSeries.ext fun
    | 0 => by rw [reduce_apply, El_zero ℓ, Int.cast_one, PowerSeries.coeff_one, if_pos rfl]
    | n + 1 => by
      rw [reduce_apply, PowerSeries.coeff_one, if_neg n.add_one_ne_zero,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_coeff_succ_El ℓ n


theorem reduce_El_pow (m) : ((El ℓ).pow m).reduce ℓ = 1 := by
  rw [reduce_pow, reduce_El, one_pow]

@[simp] theorem El_pow_zero (m : ℕ) : ((El ℓ).pow m).coeff 0 = 1 := by
  rw [coeff_zero_pow, El_zero, one_pow]


-- theorem dvd_coeff_succ_El_pow (m n) : ↑ℓ ∣ ((El ℓ).pow m).coeff (n + 1) := by
--   suffices reduce (El ℓ)
--   have h := dvd_coeff_succ_El ℓ
--   simp_all only [← coeff_def, fourier_pow]






end Eis_sub_one
