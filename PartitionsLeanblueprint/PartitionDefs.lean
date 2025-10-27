
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
import PartitionsLeanblueprint.BasicOperators
import PartitionsLeanblueprint.PrimaryLemmas
-- can't figure out how to import Archive\Wiedijk100Theorems\Partition




/- This file defines the partition function, ramanujan congruences, and the power series
product expansions for some functions. It defines what it means for two sequences of
power series to be "eventually equal", and proves that if there exists a ramanujan congruence mod ℓ
then fℓ|𝓤 = 0, assuming some facts about these product expansions. -/


noncomputable section


open Nat PowerSeries Finset Modulo2 ModularFormDefs.Integer

def partition : ℕ → ℕ
  | 0 => 0
  | n => Fintype.card (Partition n)

/- needed for later (the paper assumes p (n) = 0 for n < 0)
but might break stuff with the product expansion -/
lemma partition_zero : partition 0 = 0 := rfl


def ramanujan_congruence' (ℓ β : ℕ) : Prop :=
  ∀ n, ℓ ∣ partition (ℓ*n - β)


lemma ramanujan_congruence_unique (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    ∃ β, ramanujan_congruence' ℓ β → ramanujan_congruence' ℓ (δ ℓ) := by
  sorry

abbrev ramanujan_congruence ℓ := ramanujan_congruence' ℓ (δ ℓ)


section ProductExpansion

variable {α : Type*}

/- Archive\Wiedijk100Theorems\Partition has definitions for the product expansion of
  the partition of a number into odd and distinct parts -/

open Finset.HasAntidiagonal

universe u
variable {ι : Type u}


/-- A convenience constructor for the power series whose coefficients indicate a subset. -/
def indicatorSeries (α : Type*) [Semiring α] (s : Set ℕ) : PowerSeries α :=
  PowerSeries.mk fun n => if n ∈ s then 1 else 0


theorem coeff_indicator (s : Set ℕ) [Semiring α] (n : ℕ) :
    coeff α n (indicatorSeries _ s) = if n ∈ s then 1 else 0 :=
  coeff_mk _ _

theorem coeff_indicator_pos (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∈ s) :
    coeff α n (indicatorSeries _ s) = 1 := by rw [coeff_indicator, if_pos h]

theorem coeff_indicator_neg (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∉ s) :
    coeff α n (indicatorSeries _ s) = 0 := by rw [coeff_indicator, if_neg h]


theorem constantCoeff_indicator (s : Set ℕ) [Semiring α] :
    constantCoeff α (indicatorSeries _ s) = if 0 ∈ s then 1 else 0 :=
  rfl


theorem num_series' [Field α] (i : ℕ) :
    (1 - (X : PowerSeries α) ^ (i + 1))⁻¹ = indicatorSeries α {k | i + 1 ∣ k} := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · ext n
    cases n with
    | zero => simp [mul_sub, zero_pow, constantCoeff_indicator]
    | succ n =>
      simp only [coeff_one, if_false, mul_sub, mul_one, coeff_indicator,
        LinearMap.map_sub, reduceCtorEq]
      simp_rw [coeff_mul, coeff_X_pow, coeff_indicator, @boole_mul _ _ _ _]
      rw [sum_ite (hp := fun _ ↦ Classical.propDecidable _), sum_ite]
      simp_rw [@filter_filter _ _ _ _ _, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one,
        sub_eq_iff_eq_add, zero_add]
      symm
      split_ifs with h
      · suffices #{a ∈ antidiagonal (n + 1) | i + 1 ∣ a.fst ∧ a.snd = i + 1} = 1 by
          simp only [Set.mem_setOf_eq]; convert congr_arg ((↑) : ℕ → α) this; norm_cast
        rw [card_eq_one]
        obtain ⟨p, hp⟩ := h
        refine ⟨((i + 1) * (p - 1), i + 1), ?_⟩
        ext ⟨a₁, a₂⟩
        simp only [mem_filter, Prod.mk_inj, mem_antidiagonal, mem_singleton]
        constructor
        · rintro ⟨a_left, ⟨a, rfl⟩, rfl⟩
          refine ⟨?_, rfl⟩
          rw [Nat.mul_sub_left_distrib, ← hp, ← a_left, mul_one, Nat.add_sub_cancel]
        · rintro ⟨rfl, rfl⟩
          match p with
          | 0 => rw [mul_zero] at hp; cases hp
          | p + 1 => rw [hp]; simp [mul_add]
      · suffices #{a ∈ antidiagonal (n + 1) | i + 1 ∣ a.fst ∧ a.snd = i + 1} = 0 by
          simp only [Set.mem_setOf_eq]; convert congr_arg ((↑) : ℕ → α) this; norm_cast
        rw [Finset.card_eq_zero]
        apply eq_empty_of_forall_notMem
        simp only [Prod.forall, mem_filter, not_and, mem_antidiagonal]
        rintro _ h₁ h₂ ⟨a, rfl⟩ rfl
        apply h
        simp [← h₂]
  · simp [zero_pow]

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
and below is what I have done. -/

def partitionProduct (m : ℕ) [Field α] :=
  ∏ i ∈ range m, (1 - (X : α⟦X⟧) ^ (i + 1) )⁻¹

def DeltaProduct [Field α] (m : ℕ) :=
  (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24

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

def ppart [Field α] : ℕ → α ⟦X⟧
  | 0 => 0
  | n => Fintype.card (Partition n)

lemma ppart_zero {α} [Field α] : ppart 0 = (0 : α ⟦X⟧) := rfl

lemma ppart_eq [Field α] (n : ℕ) :  ↑ (partition n) = (ppart n : α ⟦X⟧) := by
  cases n; rw[partition_zero, cast_zero]; rfl; rfl

def apart [Field α] : ℕ → α
  | 0 => 0
  | n => Fintype.card (Partition n)

lemma apart_eq [Field α] (n : ℕ) :  ↑(partition n) = (apart n : α) := by
  cases n; rw[partition_zero, cast_zero]; rfl; rfl

theorem fl_eq_reduce {ℓ : ℕ} [Fact (Nat.Prime ℓ)] : f ℓ == Reduce (Integer_fl ℓ) ℓ := by
  sorry

def mkUniv : ℕ ↪ ℕ :=
  ⟨(· + 1), λ _ _ ↦ Nat.add_right_cancel⟩

theorem partitionGF_prop [Field α] (n m : ℕ) :
    #{p : n.Partition | ∀ j ∈ p.parts, j ∈ (range m).map mkUniv} = coeff α n (partitionProduct m) := by

  rw [partitionProduct]
  convert partialGF_prop α n
    ((range m).map mkUniv) _ (fun _ => Set.univ) (fun _ _ => trivial) using 2
  congr; simp only [true_and, forall_const, Set.mem_univ]
  {
    rw [Finset.prod_map]
    simp_rw [num_series']
    congr! 2 with x
    ext k
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨p, ⟨⟩, ?_⟩
      apply mul_comm
    rintro ⟨a_w, -, rfl⟩
    apply Dvd.intro_left a_w rfl
  }
  {
    intro i
    rw [mem_map]
    rintro ⟨a, -, rfl⟩
    exact Nat.succ_pos a
  }

lemma Partition.part_le_sum {n j} {p : Partition n} (hj : j ∈ p.parts) : j ≤ n := by
  have : p.parts.sum = n := p.parts_sum
  contrapose! this; apply Nat.ne_of_gt
  exact this |> Trans.trans <| Multiset.le_sum_of_mem hj



/- this h assumption may be changed, to (h : n ≤ 2 * m) for example.
Alternatively, it suffices to prove partitionProduct_eventually_sum
and fl_Product_eventually_sum, without the dependence on these theorems. -/
theorem partitionProduct_eq [Field α] {n m : ℕ} (npos : n > 0) (h : n ≤ m) :
    partition n = coeff α n (partitionProduct m) := by

  rw [← partitionGF_prop, partition]


  have to_set : (Fintype.card n.Partition) = #{c : n.Partition | True} := by
    refine Eq.symm (card_eq_of_equiv_fintype ?_); refine Equiv.subtypeUnivEquiv ?_
    intro x; exact mem_filter.mpr ⟨mem_univ _, trivial⟩

  rw[to_set]; congr with p
  simp only [mem_map, mem_range, true_iff]
  intro j jin; use j - 1; constructor
  calc
    _ < j := sub_one_lt_of_le (Partition.parts_pos _ jin) (le_refl j)
    _ ≤ n := Partition.part_le_sum jin
    _ ≤ m := h

  unfold mkUniv; dsimp; rw[Nat.sub_add_cancel]; exact Partition.parts_pos _ jin

  show n ≠ 0
  rwa [← Nat.pos_iff_ne_zero]


def natpart (n : ℕ) : ℕ :=
  Fintype.card (Partition n)

lemma natpart_zero : natpart 0 = 1 := by
  unfold natpart; rw [Fintype.card_unique]

lemma natpart_succ (n : ℕ) : natpart (n + 1) = partition (n + 1) := by
  unfold natpart partition; rfl

theorem partitionProduct_eq_natpart [Field α] {n m : ℕ} (h : n ≤ m) :
    natpart n = coeff α n (partitionProduct m) := by
  by_cases n0 : n = 0
  simp [n0, natpart_zero, partitionProduct]
  have : ∃ k, n = k + 1 := exists_eq_succ_of_ne_zero n0
  obtain ⟨k,rfl⟩ := this; rw[← ne_eq, ← pos_iff_ne_zero] at n0
  rw[natpart_succ]; exact partitionProduct_eq n0 h





theorem fl_Product_eq {ℓ} [Fact (Nat.Prime ℓ)] [Field α] {n m : ℕ} (h : n ≤ m) :
    Integer_fl ℓ n = coeff α n (flProduct ℓ m) := by
  sorry




end ProductExpansion

section PowerSeriesFacts

variable {α} [Field α]

/- Two sequences of power series are eventually equal if for any coefficient n,
there is some number m, such that these sequences match on all coeffients
less than n from the index m onward. As an example, the function
fun n ↦ ∑ i ∈ range n, (partition i) * (X : α⟦X⟧) ^ i
is eventually equal to fun n ↦ ∏ i ∈ range n, 1 / (1 - X ^ (i + 1)) -/

def eventuallyEq (f h : ℕ → α ⟦X⟧) : Prop :=
  ∀ n, ∃ m, ∀ k ≤ n, ∀ j ≥ m, coeff α k (f j) = coeff α k (h j)

-- this clashes with the standard usage of ⟶ for a momorphism
infixl : 25 (priority := high) " ⟶ " => eventuallyEq

@[refl]
theorem eventuallyEq.refl (f : ℕ → α⟦X⟧) : f ⟶ f := λ _ ↦ ⟨0, λ _ _ _ _ ↦ rfl⟩

@[symm]
theorem eventuallyEq.symm (f h : ℕ → α⟦X⟧) : (f ⟶ h) → (h ⟶ f) := by
  intro eq n
  obtain ⟨m, fo⟩ := eq n
  use m, (λ n ngm j jgm ↦ (fo n ngm j jgm).symm)

@[trans]
theorem eventuallyEq.trans (f h g : ℕ → α⟦X⟧) : (f ⟶ h) → (h ⟶ g) → (f ⟶ g) := by
  intro feq heq n
  obtain ⟨M, fo⟩ := feq n
  obtain ⟨N, ho⟩ := heq n
  use max M N; intro k klen j jgMax
  rw [fo k klen j <| le_of_max_le_left jgMax, ho k klen j <| le_of_max_le_right jgMax]


instance : IsEquiv (ℕ → α⟦X⟧) eventuallyEq where
  refl := eventuallyEq.refl
  symm := eventuallyEq.symm
  trans := eventuallyEq.trans

@[gcongr]
theorem eventuallyEq_add {a b c d : ℕ → α ⟦X⟧} (hab : a ⟶ b) (hcd : c ⟶ d) : a + c ⟶ b + d := by
  intro k
  obtain ⟨M, fo⟩ := hab k
  obtain ⟨N, go⟩ := hcd k
  use max M N; intro n nle j jg
  simp only [Pi.add_apply, map_add]
  rw [fo n nle j <| le_of_max_le_left jg, go n nle j <| le_of_max_le_right jg]

@[gcongr]
theorem eventuallyEq_mul {a b c d : ℕ → α ⟦X⟧} (hab : a ⟶ b) (hcd : c ⟶ d) : a * c ⟶ b * d := by
  intro k
  simp only [Pi.mul_apply, coeff_mul, map_add]
  obtain ⟨M, fo⟩ := hab k
  obtain ⟨N, go⟩ := hcd k
  use max M N; intro n nle j jg

  apply sum_congr rfl; intro x xin; congr 1
  apply fo; exact antidiagonal.fst_le xin |> trans <| nle -- cool
  exact le_of_max_le_left jg
  apply go; exact antidiagonal.snd_le xin |> trans <| nle
  exact le_of_max_le_right jg


def PowerSeries.lift (a : ℕ → Polynomial α) : ℕ → α ⟦X⟧ :=
  fun n ↦ ↑(a n)

@[simp] lemma lift_apply (a : ℕ → Polynomial α) (n : ℕ) :
  lift a n = ↑(a n) := rfl


theorem eventuallyEq_zero_iff {a : ℕ → α ⟦X⟧} :
    (a ⟶ 0) ↔ ∀ n, ∃ m, ∀ k ≤ n, ∀ j ≥ m, coeff α k (a j) = 0 := by
  unfold eventuallyEq; simp only [Pi.zero_apply, map_zero]



lemma coeff_sum_X_pow {n N : ℕ} {a : ℕ → α} (h : n < N) :
    coeff α n (∑ i ∈ range N, (PowerSeries.C α (a i)) * (X : α⟦X⟧) ^ i ) = a n := by
  simp [map_sum, coeff_X_pow]
  exact λ nle ↦ (not_lt_of_ge nle h).rec


lemma coeff_sum_X_pow_mul {n N ℓ : ℕ} [NeZero ℓ] {a : ℕ → α} (h : n < N) :
    (coeff α n) (∑ i ∈ range N, (C α) (a i) * X ^ (ℓ * i)) = if ℓ ∣ n then a (n / ℓ) else 0 := by

  simp [map_sum, coeff_X_pow]
  have ln0 : ℓ ≠ 0 := Ne.symm (NeZero.ne' ℓ)
  split_ifs with ldiv; obtain ⟨k, rfl⟩ := ldiv
  simp only [mul_eq_mul_left_iff, sum_ite]
  trans a k + 0; congr
  trans ∑ x ∈ {k}, a x
  congr; ext x; constructor <;> simp only [mem_filter, mem_range, mem_singleton, and_imp]
  intro xlN keqx
  simp_all only [or_false, ne_eq]
  intro xeqk; constructor
  have : x ≤ ℓ * x := Nat.le_mul_of_pos_left x <| pos_of_neZero ℓ
  exact trans this <| xeqk ▸ h
  left; exact xeqk.symm
  rw [sum_singleton]
  rw [sum_const_zero]
  rw [add_zero]; congr; exact Nat.eq_div_of_mul_eq_right ln0 rfl
  apply sum_eq_zero; intro x xlN
  rw[dvd_def] at ldiv; push_neg at ldiv
  exact if_neg (ldiv x)


lemma sum_X_pow_eventually_zero_iff (f : ℕ → α) :
    ( (∑ i ∈ range ·, (C α) (f i) * (X : α ⟦X⟧) ^ i) ⟶ 0 ) ↔ ∀ n, f n = 0 := by
  constructor <;> intro h n
  obtain ⟨m, fo⟩ := h n
  specialize fo n (le_refl n) (max (n + 1) m) (le_max_of_le_right <| le_refl m)
  have nlt : n < max (n + 1) m := lt_max_of_lt_left <| lt_add_one n
  simp_all only [Pi.zero_apply, map_zero, coeff_sum_X_pow]
  simp only [h, map_zero, zero_mul, sum_const_zero, Pi.zero_apply, implies_true, exists_const]


lemma coeff_sum_squash {j ℓ N M : ℕ} [NeZero ℓ] {a b : ℕ → α} (jlN : ℓ * j < N) (jlM : ℓ * j < M) :
  coeff α (ℓ * j) ( (∑ i ∈ range N, (PowerSeries.C α (a i)) * (X : α⟦X⟧) ^ i)
    * (∑ i ∈ range M, (PowerSeries.C α (b i)) * (X : α⟦X⟧) ^ (ℓ * i)) )
      = ∑ ⟨x,y⟩ ∈ antidiagonal j, a (ℓ * x) * b y := by

  simp only [coeff_mul]

  have ln0 : ℓ ≠ 0 := Ne.symm (NeZero.ne' ℓ)

  have plN {p} (hp : p ∈ antidiagonal (ℓ * j)) : p.1 < N :=
    lt_of_le_of_lt (antidiagonal.fst_le hp) jlN

  have plM {p} (hp : p ∈ antidiagonal (ℓ * j)) : p.2 < M :=
    lt_of_le_of_lt (antidiagonal.snd_le hp) jlM

  calc
    _ = ∑ p ∈ antidiagonal (ℓ * j), a (p.1) * (if ℓ ∣ p.2 then b (p.2 / ℓ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp; congr
      rw [coeff_sum_X_pow (plN hp)]
      rw [coeff_sum_X_pow_mul (plM hp)]

    _ = ∑ p ∈ antidiagonal (ℓ * j) with ℓ ∣ p.2, a (p.1) * b (p.2 / ℓ) := by
      simp_rw[mul_ite, sum_ite, mul_zero, sum_const_zero, add_zero]

    _ = _ := by
      symm; apply Finset.sum_bij (fun x _ ↦ (ℓ * x.1, ℓ * x.2))
      intro p hp
      simp only [mem_filter, mem_antidiagonal, dvd_mul_right, and_true]
      trans ℓ * (p.1 + p.2); ring
      congr; exact mem_antidiagonal.mp hp
      intro p hp q hq heq
      ext; simp only [Prod.mk.injEq, mul_eq_mul_left_iff] at heq
      simp_all only [ne_eq, or_false]
      simp only [Prod.mk.injEq, mul_eq_mul_left_iff] at heq
      simp_all only [ne_eq, or_false]
      intro p hp
      simp only [mem_filter, mem_antidiagonal, dvd_mul_right, and_true] at hp
      obtain ⟨psum, ldiv⟩ := hp
      have : ℓ ∣ p.1 := by
        suffices ℓ ∣ p.1 + p.2 from (Nat.dvd_add_iff_left ldiv).mpr this
        use j
      obtain ⟨ ⟨k, hk⟩, ⟨c, hc⟩ ⟩ := (⟨ldiv, this⟩ : And ..) -- lol
      use (c, k), by
        simp only [mem_antidiagonal]
        suffices ℓ * (c + k) = ℓ * j from (Nat.mul_right_inj ln0).mp this
        rwa [mul_add, ← hk, ← hc]
      ext <;> dsimp <;> symm <;> assumption
      intro p hp; congr; dsimp
      exact Nat.eq_div_of_mul_eq_right ln0 rfl


lemma coeff_mul_shift {m N : ℕ} (f : ℕ → α ⟦X⟧) :
    X ^ m * ∑ i ∈ range N, f i * X ^ i = ∑ i ∈ Ico m (N + m), f (i - m) * X ^ i := by

  simp_rw [mul_sum, ← mul_assoc, mul_comm, mul_assoc, ← pow_add]
  apply sum_bij (fun i _ ↦ i + m)
  simp only [mem_range, mem_Ico, le_add_iff_nonneg_left, _root_.zero_le, true_and]
  intro a alN; exact add_lt_add_right alN _
  intro a alN b blN; exact (Nat.add_right_cancel ·)
  simp_all only [mem_Ico, mem_range]
  intro b bin
  use b - m, by omega
  exact Nat.sub_add_cancel bin.1
  simp only [mem_range]; intro a alN
  congr 2; apply congrArg; exact Nat.eq_sub_of_add_eq rfl
  ac_rfl


lemma coeff_mul_shift_of_zero {m N : ℕ} (f : ℕ → α ⟦X⟧) (f0 : f 0 = 0) :
    X ^ m * ∑ i ∈ range N, f i * X ^ i = ∑ i ∈ range (N + m), f (i - m) * X ^ i := by
  calc

  _ = ∑ i ∈ Ico m (N + m), f (i - m) * X ^ i := coeff_mul_shift f

  _ = (∑ i ∈ range (N + m), f (i - m) * X ^ i) - ∑ i ∈ range m, f (i - m) * X ^ i :=
    sum_Ico_eq_sub _ <| Nat.le_add_left m N

  _ = _ := by
    nth_rw 2 [← sub_zero (∑ i ∈ range (N + m), f (i - m) * X ^ i)]
    congr; apply sum_eq_zero; intro x xlm; trans 0 * X ^ x
    congr; rw[← f0]; apply congrArg; refine Nat.sub_eq_zero_of_le ?_
    exact le_of_lt <| List.mem_range.mp xlm
    rw[zero_mul]


lemma Polynomial.coe_prod (m : ℕ) (f : ℕ → Polynomial α) :
    ∏ i ∈ range m, (f i : α ⟦X⟧) = ((∏ i ∈ range m, f i : Polynomial α) : α ⟦X⟧) := by
  induction m with
  | zero => simp only [range_zero, prod_empty, Polynomial.coe_one]
  | succ m ih => simp only [prod_range_succ, ih, Polynomial.coe_mul]


lemma coeff_zero_of_ndvd {ℓ M k : ℕ} (ndvd : ¬ ℓ ∣ k) :
    coeff α k (∏ i ∈ range M, (1 - (X : α ⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ) = 0 := by

  rw[coeff_prod]
  apply sum_eq_zero; intro x xin
  rw [prod_eq_zero_iff]

  have exa : ∃ a ∈ range M, ¬ ℓ ∣ x a := by
    contrapose! xin
    simp only [mem_finsuppAntidiag, not_and_or]
    left; contrapose! ndvd; calc
    _ ∣ ∑ a ∈ range M, x a := by
      apply dvd_sum; exact xin
    _ = k := ndvd ▸ rfl

  obtain ⟨a, alt, nad⟩ := exa
  use a, alt
  rw[coeff_pow]
  apply sum_eq_zero; intro y yin
  rw [prod_eq_zero_iff]

  have exb : ∃ a ∈ range ℓ, ¬ ℓ ∣ y a := by
    contrapose! yin
    simp only [mem_finsuppAntidiag, not_and_or]
    left; contrapose! nad; calc
    _ ∣ ∑ a ∈ range ℓ, y a := by
      apply dvd_sum; exact yin
    _ = x a := nad ▸ rfl

  obtain ⟨b, blt, nbd⟩ := exb
  use b, blt

  simp only [map_sub, coeff_one]
  split_ifs with yb0
  simp_all only [dvd_zero, not_true_eq_false]
  simp only [zero_sub, neg_eq_zero]
  rw[coeff_X_pow]; apply if_neg
  rw[dvd_def] at nbd; push_neg at nbd
  exact nbd (a + 1)



lemma coeff_sum_eventually_zero (m : ℕ) (f : ℕ → Polynomial α) :
    ∃ N, ∀ n ≥ N, coeff α n (∑ i ∈ range m, f i) = 0 := by
  simp only [ge_iff_le, map_sum, Polynomial.coeff_coe]
  set M := sup (range m) (Polynomial.natDegree ∘ f) with Meq
  use M + 1; intro n Mle
  apply sum_eq_zero; intro x xlm
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_; calc
    _ ≤ M := by
      have : (f x).natDegree = (Polynomial.natDegree ∘ f) x := rfl
      rw[Meq, this]; exact le_sup xlm
    _ < n := Mle


lemma coeff_prod_eventually_zero (m : ℕ) (f : ℕ → Polynomial α) :
    ∃ N, ∀ n ≥ N, coeff α n (∏ i ∈ range m, f i) = 0 := by
  simp only [ge_iff_le, map_prod, Polynomial.coeff_coe]
  set M := ∑ i ∈ range m, (f i).natDegree with Meq
  use M + 1; intro n Mle;
  trans coeff α n (∏ i ∈ range m, f i : Polynomial α); congr
  apply Polynomial.coe_prod

  simp only [Polynomial.coeff_coe]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt; calc
    _ ≤ M := by
      rw[Meq]; exact Polynomial.natDegree_prod_le (range m) f
    _ < n := Mle


lemma prod_eq_sum (α) [Field α] (ℓ K : ℕ) [NeZero ℓ] : ∃ c : ℕ → α, ∃ M,
    (∏ i ∈ range K, (1 - (X : α ⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ) = ∑ i ∈ range M, C α (c i) * X ^ (ℓ * i) := by

  have ln0 : ℓ ≠ 0 := Ne.symm (NeZero.ne' ℓ)

  set f : ℕ → Polynomial α := fun i ↦ (1 - (Polynomial.X) ^ (ℓ * (i+1))) ^ ℓ with feq

  obtain ⟨M, hM⟩ := coeff_prod_eventually_zero K f

  use fun i ↦ coeff α (ℓ * i) (∏ i ∈ range K, (1 - (X : α ⟦X⟧) ^ (ℓ * (i + 1))) ^ ℓ)
  use M
  ext i; simp only [map_sum, coeff_C_mul, coeff_X_pow]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases ldi : ℓ ∣ i
  obtain ⟨k, rfl⟩ := ldi
  simp_all only [mul_eq_mul_left_iff, or_false, sum_ite_eq, mem_range, left_eq_ite_iff, not_lt]
  intro lek

  trans (coeff α (ℓ * k)) (∏ i ∈ range K, f i)
  simp only [feq, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
  have : ℓ * k ≥ M := by
    trans k; exact Nat.le_mul_of_pos_left k <| zero_lt_of_ne_zero ln0
    exact lek
  rw[feq]; dsimp; exact hM _ this

  trans 0; exact coeff_zero_of_ndvd ldi
  symm; apply sum_eq_zero; intro x xle
  apply if_neg; rw[dvd_def] at ldi; push_neg at ldi
  exact ldi x


theorem partitionProduct_eventually_natpart_sum :
    (partitionProduct ·) ⟶ (∑ i ∈ range ·, (natpart i) * (X : α⟦X⟧) ^ i) := by
  intro n; dsimp; use n + 1; intro k kle j jg
  have klj : k < j := by omega
  trans coeff α k (∑ i ∈ range j, (C α) (natpart i) * X ^ i)
  simp only [coeff_sum_X_pow klj, partitionProduct_eq_natpart (le_of_lt klj)]
  rfl



theorem fl_Product_eventually_sum (ℓ) [Fact (Nat.Prime ℓ)] :
    (flProduct ℓ ·) ⟶ (∑ i ∈ range ·, ((Integer_fl ℓ i) : α ⟦X⟧) * (X : α⟦X⟧) ^ i) := by
  intro n; dsimp; use n + 1; intro k kle j jg
  have klj : k < j := by omega
  set g := fun n ↦ ((Integer_fl ℓ n) : α) with geq

  trans coeff α k (∑ i ∈ range j, (C α) (g i) * X ^ i)
  simp only [coeff_sum_X_pow klj, fl_Product_eq (le_of_lt klj), geq]
  simp only [geq, map_intCast]


theorem partitionProduct_mul_eq_sum (n : ℕ) (f : ℕ → Polynomial α) :
  ∃ M, ∀ m ≥ M, (coeff α n) ( (f m) * (partitionProduct m : α⟦X⟧) ) =
    (coeff α n) ( (f m) * ∑ i ∈ range m, (partition i) * (X : α⟦X⟧) ^ i ) := by
  sorry

  -- have hf := @partitionProduct_eventually_sum
  -- obtain ⟨M, fo⟩ := (eventuallyEq_mul (eventuallyEq.refl (lift f)) hf) n
  -- use M; intro m mg; specialize fo n (le_refl _) m mg
  -- simp_all only [Pi.mul_apply, lift_apply]; congr

theorem partitionProduct_mul_eq_natpart_sum (n : ℕ) (f : ℕ → Polynomial α) :
  ∃ M, ∀ m ≥ M, (coeff α n) ( (f m) * (partitionProduct m : α⟦X⟧) ) =
    (coeff α n) ( (f m) * ∑ i ∈ range m, (natpart i) * (X : α⟦X⟧) ^ i ) := by

  have hf := @partitionProduct_eventually_natpart_sum
  obtain ⟨M, fo⟩ := (eventuallyEq_mul (eventuallyEq.refl (lift f)) hf) n
  use M; intro m mg; specialize fo n (le_refl _) m mg
  simp_all only [Pi.mul_apply, lift_apply]; congr


theorem partitionProduct_mul_eq_sum' {n : ℕ} (npos : n > 0) (f : ℕ → Polynomial α)
  (f0 : ∀ n, Polynomial.coeff (f n) 0 = 0) :
  ∃ M, ∀ m ≥ M, (coeff α n) ( (f m) * (partitionProduct m : α⟦X⟧) ) =
    (coeff α n) ( (f m) * ∑ i ∈ range m, (partition i) * (X : α⟦X⟧) ^ i ) := by

  set M := sup (range n) (Polynomial.natDegree ∘ f) with Meq
  set L := max (M + 1) (n + 1) with Leq
  use L; intro m Mle
  simp only [coeff_mul]; apply sum_congr rfl
  intro p pin
  have p2lt : p.2 < m := by calc
    _ < L := by apply lt_max_of_lt_right; rw [Nat.lt_succ]; exact antidiagonal.snd_le pin
    _ ≤ m := Mle

  have rrw (n) : (partition n : α ⟦X⟧) = (C α) (partition n) := rfl
  simp_rw [rrw, coeff_sum_X_pow p2lt]; simp only [Polynomial.coeff_coe, mul_eq_mul_left_iff]
  sorry




end PowerSeriesFacts

variable {ℓ} [Fact (Nat.Prime ℓ)]

instance : CharP ((ZMod ℓ) ⟦X⟧) ℓ := by
  refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
  trans C (ZMod ℓ) (ℓ : (ZMod ℓ)); rfl
  simp only [CharP.cast_eq_zero, map_zero]


theorem flu_eq_zero [Fact (ℓ ≥ 5)] : ramanujan_congruence ℓ → f ℓ |𝓤 = 0 := by

  intro h
  have lg5 : ℓ ≥ 5 := Fact.out
  have lsq : ℓ ^ 2 ≥ 25 := by
    trans 5 * 5; rw[pow_two]; gcongr; exact le_refl _

  ext n

  by_cases npos : n = 0
  · rw [npos, U_apply, mul_zero, fl_zero, zero_apply]

  rw [← ne_eq, ← Nat.pos_iff_ne_zero] at npos

  rw [U_apply, zero_apply, fl_eq_reduce, Reduce_apply]

  set g : ℕ → Polynomial (ZMod ℓ) :=
    fun n ↦ Polynomial.X ^ (δ ℓ) * (∏ i ∈ range n, (1 - Polynomial.X ^ (i + 1)) ^ (ℓ ^ 2)) with geq

  obtain ⟨ m, goeq ⟩ := partitionProduct_mul_eq_sum (ℓ * n) g
  obtain ⟨ m', floeq ⟩ := @fl_Product_eventually_sum (ZMod ℓ) _ ℓ _ (ℓ * n)
  dsimp at floeq

  set M := max' {m, m', ℓ * n + 1} (insert_nonempty ..) with Meq
  have mleM : m ≤ M := by
    apply le_max'; simp only [mem_insert, mem_singleton, true_or, or_true]
  have m'leM : m' ≤ M := by
    apply le_max'; simp only [mem_insert, mem_singleton, true_or, or_true]
  have elnltM : ℓ * n < M := by
    apply lt_of_succ_le; apply le_max'
    simp only [mem_insert, mem_singleton, true_or, or_true]

  have g_coe_rw : (X : (ZMod ℓ)⟦X⟧) ^ δ ℓ * ∏ i ∈ range M,
      (1 - (X : (ZMod ℓ) ⟦X⟧) ^ (i + 1)) ^ ℓ ^ 2 = ↑(g M) := by
    simp only [geq, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, ← Polynomial.coe_prod, mul_eq_mul_left_iff,
        pow_eq_zero_iff', X_ne_zero, ne_eq, false_and, or_false]
    congr; ext i : 1; simp only [Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_pow, Polynomial.coe_X]

  calc

  _ = (coeff (ZMod ℓ) (ℓ * n))
      (∑ i ∈ range M, C (ZMod ℓ) ↑( (Integer_fl ℓ) i ) * X ^ i) := by
    rwa [coeff_sum_X_pow]

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( (X * ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ 24) ^ (δ ℓ) ) := by
    simp only [map_intCast, ← floeq (ℓ * n) (le_refl _) M m'leM,
        flProduct, Pi.pow_apply, DeltaProduct]

  _ = (coeff (ZMod ℓ) (ℓ * n) )
      (X ^ (δ ℓ) * ∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2 - 1)) := by
    congr; simp only [mul_pow]; congr
    simp_rw[← prod_pow _ (δ ℓ)]
    congr; ext i : 1; rw[← pow_mul]
    congr; unfold δ; exact Nat.mul_div_cancel' delta_integer

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( X ^ (δ ℓ) *  (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
      (partitionProduct M) ) := by
    rw[mul_assoc]; congr
    trans ∏ i ∈ range M, ( (↑1 - X ^ (i + 1)) ^ (ℓ ^ 2) * (↑1 - X ^ (i + 1))⁻¹ )
    {
      congr; ext i : 1;

      refine (PowerSeries.eq_mul_inv_iff_mul_eq ?_).mpr ?_
      simp only [map_sub, constantCoeff_one, map_pow, constantCoeff_X]
      rw[zero_pow <| succ_ne_zero i, sub_zero]; exact Ne.symm (zero_ne_one' (ZMod ℓ))
      nth_rw 2[← pow_one (1 - X ^ (i + 1))]; rw[mul_comm, pow_mul_pow_sub]
      exact NeZero.one_le
    }
    exact prod_mul_distrib

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range M, (1 - X ^ (i + 1)) ^ (ℓ ^ 2)) *
        ( X ^ (δ ℓ) * ∑ i ∈ range M, (partition i) * (X : (ZMod ℓ) ⟦X⟧) ^ i ) ) := by
    rw [g_coe_rw, goeq M mleM, ← g_coe_rw]; ring_nf

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range M, ((↑1 - X ^ (ℓ * (i + 1))) ^ ℓ) ) *
      (X ^ (δ ℓ) * ∑ i ∈ range M, (partition i) * (X : (ZMod ℓ) ⟦X⟧) ^ i) ) := by
    congr; ext i : 1
    trans ((1 - X ^ (i + 1)) ^ ℓ) ^ ℓ
    rw[pow_two, pow_mul]
    congr
    rw [sub_pow_expChar_of_commute, one_pow, ← pow_mul, mul_comm]
    exact Commute.one_left _

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ((∏ i ∈ range M, (1 - X ^ (ℓ * (i + 1))) ^ ℓ) *
      ∑ i ∈ range (M + δ ℓ), C (ZMod ℓ) (partition (i - δ ℓ)) * X ^ i) := by
    simp_rw [ppart_eq, coeff_mul_shift_of_zero ppart ppart_zero]
    congr; ext i : 1; rw[← ppart_eq]; rfl

  _ = 0 := by
    obtain ⟨c, L, heq⟩ := prod_eq_sum (ZMod ℓ) ℓ M
    simp_rw [heq, apart_eq]

    rw [mul_comm (∑ i ∈ range L, (C (ZMod ℓ)) (c i) * X ^ (ℓ * i))]

    set c' : ℕ → (ZMod ℓ) := fun i ↦ if i < L then c i else 0 with hc'
    have c'rw : ∑ i ∈ range L, (C (ZMod ℓ)) (c i) * X ^ (ℓ * i) =
        ∑ i ∈ range (L + (ℓ * n + 1)), (C (ZMod ℓ)) (c' i) * X ^ (ℓ * i) := by
      rw[sum_range_add, ← add_zero (∑ i ∈ range L, (C (ZMod ℓ)) (c i) * X ^ (ℓ * i))]
      congr 1; apply sum_congr rfl; intro i ilM; congr
      rw[hc']; simp_all only [mem_range, if_pos]
      symm; apply sum_eq_zero; intro i ilm
      suffices c' (L + i) = 0 by simp only [this, map_zero, zero_mul]
      simp only [add_lt_iff_neg_left, not_lt_zero', reduceIte, c']

    rw [c'rw, coeff_sum_squash]
    simp only [← apart_eq]; apply sum_eq_zero
    intro x hx
    have : ↑(partition (ℓ * x.1 - δ ℓ)) = (0 : ZMod ℓ) := by
      rw[ZMod.natCast_zmod_eq_zero_iff_dvd]; exact h x.1
    rw[this, zero_mul]
    exact Nat.lt_add_right (δ ℓ) elnltM
    omega





end section
