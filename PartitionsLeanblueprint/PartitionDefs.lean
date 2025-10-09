
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.IntervalCases
import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.PrimaryLemmas



/- The goal of this file is to define the partition function, ramanujan congruences,
and the power series product expansions for these functions and Modular Forms,
and to ultimately prove that if there exists a ramanujan congruence mod ℓ then fℓ|𝓤 = 0 -/

open Nat PowerSeries Finset Modulo2 ModularFormDefs.Integer

def partition (n : ℕ) : ℕ :=
  Fintype.card (Partition n)


def ramanujan_congruence' (ℓ β : ℕ) : Prop :=
  ∀ n, ℓ ∣ partition (ℓ*n - β)


lemma ramanujan_congruence_unique (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    ∃ β, ramanujan_congruence' ℓ β → ramanujan_congruence' ℓ (δ ℓ) := by
  sorry

abbrev ramanujan_congruence ℓ := ramanujan_congruence' ℓ (δ ℓ)


noncomputable section ProductExpansion

variable {α : Type*}

/- Archive\Wiedijk100Theorems\Partition has definitions for the product expansion of
  the partition of a number into odd and distinct parts -/



open Finset.HasAntidiagonal

universe u
variable {ι : Type u}

open scoped Classical in
/-- A convenience constructor for the power series whose coefficients indicate a subset. -/
def indicatorSeries (α : Type*) [Semiring α] (s : Set ℕ) : PowerSeries α :=
  PowerSeries.mk fun n => if n ∈ s then 1 else 0

open scoped Classical in
theorem coeff_indicator (s : Set ℕ) [Semiring α] (n : ℕ) :
    coeff α n (indicatorSeries _ s) = if n ∈ s then 1 else 0 :=
  coeff_mk _ _

theorem coeff_indicator_pos (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∈ s) :
    coeff α n (indicatorSeries _ s) = 1 := by rw [coeff_indicator, if_pos h]

theorem coeff_indicator_neg (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∉ s) :
    coeff α n (indicatorSeries _ s) = 0 := by rw [coeff_indicator, if_neg h]

open scoped Classical in
theorem constantCoeff_indicator (s : Set ℕ) [Semiring α] :
    constantCoeff α (indicatorSeries _ s) = if 0 ∈ s then 1 else 0 :=
  rfl


open scoped Classical in
-- The main workhorse of the partition theorem proof.
theorem partialGF_prop (α : Type*) [CommSemiring α] (n : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, 0 < i)
    (c : ℕ → Set ℕ) (hc : ∀ i, i ∉ s → 0 ∈ c i) :
    #{p : n.Partition | (∀ j, p.parts.count j ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s} =
      coeff α n (∏ i ∈ s, indicatorSeries α ((· * i) '' c i)) := by
  simp_rw [coeff_prod, coeff_indicator, prod_boole, sum_boole]
  apply congr_arg
  simp only [mem_univ, forall_true_left, not_and, not_forall, exists_prop,
    Set.mem_image, not_exists]
  set phi : (a : Nat.Partition n) →
    a ∈ filter (fun p ↦ (∀ (j : ℕ), Multiset.count j p.parts ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s) univ →
    ℕ →₀ ℕ := fun p _ => {
      toFun := fun i => Multiset.count i p.parts • i
      support := Finset.filter (fun i => i ≠ 0) p.parts.toFinset
      mem_support_toFun := fun a => by
        simp only [smul_eq_mul, ne_eq, mul_eq_zero, Multiset.count_eq_zero]
        rw [not_or, not_not]
        simp only [Multiset.mem_toFinset, not_not, mem_filter] }
  refine Finset.card_bij phi ?_ ?_ ?_
  · intro a ha
    simp only [phi, not_forall, not_exists, not_and, exists_prop, mem_filter]
    rw [mem_finsuppAntidiag]
    dsimp only [ne_eq, smul_eq_mul, id_eq, eq_mpr_eq_cast, le_eq_subset, Finsupp.coe_mk]
    simp only [mem_univ, forall_true_left, not_and, not_forall, exists_prop,
      mem_filter, true_and] at ha
    refine ⟨⟨?_, fun i ↦ ?_⟩, fun i _ ↦ ⟨a.parts.count i, ha.1 i, rfl⟩⟩
    · conv_rhs => simp [← a.parts_sum]
      rw [sum_multiset_count_of_subset _ s]
      · simp only [smul_eq_mul]
      · intro i
        simp only [Multiset.mem_toFinset, not_not, mem_filter]
        apply ha.2
    · simp only [ne_eq, Multiset.mem_toFinset, not_not, mem_filter, and_imp]
      exact fun hi _ ↦ ha.2 i hi
  · dsimp only
    intro p₁ hp₁ p₂ hp₂ h
    apply Nat.Partition.ext
    simp only [true_and, mem_univ, mem_filter] at hp₁ hp₂
    ext i
    simp only [phi, ne_eq, Multiset.mem_toFinset, not_not, smul_eq_mul, Finsupp.mk.injEq] at h
    by_cases hi : i = 0
    · rw [hi]
      rw [Multiset.count_eq_zero_of_notMem]
      · rw [Multiset.count_eq_zero_of_notMem]
        intro a; exact Nat.lt_irrefl 0 (hs 0 (hp₂.2 0 a))
      intro a; exact Nat.lt_irrefl 0 (hs 0 (hp₁.2 0 a))
    · rw [← mul_left_inj' hi]
      rw [funext_iff] at h
      exact h.2 i
  · simp only [phi, mem_filter, mem_finsuppAntidiag, mem_univ, exists_prop, true_and, and_assoc]
    rintro f ⟨hf, hf₃, hf₄⟩
    have hf' : f ∈ finsuppAntidiag s n := mem_finsuppAntidiag.mpr ⟨hf, hf₃⟩
    simp only [mem_finsuppAntidiag] at hf'
    refine ⟨⟨∑ i ∈ s, Multiset.replicate (f i / i) i, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i hi
      simp only [exists_prop, mem_sum, mem_map, Function.Embedding.coeFn_mk] at hi
      rcases hi with ⟨t, ht, z⟩
      apply hs
      rwa [Multiset.eq_of_mem_replicate z]
    · simp_rw [Multiset.sum_sum, Multiset.sum_replicate, Nat.nsmul_eq_mul]
      rw [← hf'.1]
      refine sum_congr rfl fun i hi => Nat.div_mul_cancel ?_
      rcases hf₄ i hi with ⟨w, _, hw₂⟩
      rw [← hw₂]
      exact dvd_mul_left _ _
    · intro i
      simp_rw [Multiset.count_sum', Multiset.count_replicate, sum_ite_eq']
      split_ifs with h
      · rcases hf₄ i h with ⟨w, hw₁, hw₂⟩
        rwa [← hw₂, Nat.mul_div_cancel _ (hs i h)]
      · exact hc _ h
    · intro i hi
      rw [mem_sum] at hi
      rcases hi with ⟨j, hj₁, hj₂⟩
      rwa [Multiset.eq_of_mem_replicate hj₂]
    · ext i
      simp_rw [Multiset.count_sum', Multiset.count_replicate, sum_ite_eq']
      simp only [ne_eq, Multiset.mem_toFinset, not_not, smul_eq_mul, ite_mul,
        zero_mul, Finsupp.coe_mk]
      split_ifs with h
      · apply Nat.div_mul_cancel
        rcases hf₄ i h with ⟨w, _, hw₂⟩
        apply Dvd.intro_left _ hw₂
      · apply symm
        rw [← Finsupp.notMem_support_iff]
        exact notMem_mono hf'.2 h




/- Pretty much everything above this is from Archive\Wiedijk100Theorems\Partition,
and below is what I have done. I don't really know what's going on yet. -/

def partitionProduct (m : ℕ) [Field α] :=
  ∏ i ∈ range m, (1 - (X : α⟦X⟧) ^ i )⁻¹

def DeltaProduct [Field α] (m : ℕ)  :=
  (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ i) ^ 24

def Integer_Eta (n : ℕ) : ℤ :=
  if h : (∃ m : ℤ, n = m * (3*m - 1) / 2)
    then
      let m := Classical.choose h
      if m % 2 = 0 then 1 else -1
    else 0

def Integer_Delta : IntegerModularForm 12 where
  sequence
    | 0 => 0
    | n + 1 => (Sequencepow Integer_Eta 24) n

  summable := sorry

  modular := sorry


def Integer_fl (ℓ : ℕ) : IntegerModularForm (12 * δ ℓ) :=
  Ipow Integer_Delta (δ ℓ)


def flProduct (ℓ : ℕ) (m : ℕ) [Field α] :=
  (@DeltaProduct α _ ^ (δ ℓ)) m



theorem partitionProduct_eq [Field α] (n m : ℕ) (h : n < m) :
    partition n = coeff α n (partitionProduct m) := by
  sorry

theorem DeltaProduct_eq {ℓ} [Fact (Nat.Prime ℓ)] [Field α] (n m : ℕ) (h : n < m) :
    Integer_Delta m = coeff α n (DeltaProduct m) := by
  sorry

theorem fl_Product_eq {ℓ} [Fact (Nat.Prime ℓ)] [Field α] (n m : ℕ) (h : n < m) :
    Integer_fl ℓ m = coeff α n (flProduct ℓ m) := by
  sorry




end ProductExpansion




variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]

theorem fl_eq_reduce : f ℓ == Reduce (Integer_fl ℓ) ℓ := by
  sorry



theorem flu_eq_zero : ramanujan_congruence ℓ → f ℓ |𝓤 = 0 := by
  intro h
  ext n; simp; rw[fl_eq_reduce]; simp;
  trans ↑(0 : ℤ); rw[ZMod.intCast_eq_intCast_iff];
  sorry
  sorry
  -- calc
  --   (Integer_fl ℓ) (ℓ * n) = ((Integer_fl ℓ) (ℓ * n) : ℚ) := sorry

  --   _ = coeff ℚ (ℓ*n - δ ℓ) (partitionProduct (ℓ*n + 1)) := by


  --     sorry
  --   _ = partition (ℓ*n - δ ℓ) := by
  --     symm; apply partitionProduct_eq; omega
  --   _ ≡ 0 [ZMOD ℓ] := by
  --     norm_cast; exact h n
