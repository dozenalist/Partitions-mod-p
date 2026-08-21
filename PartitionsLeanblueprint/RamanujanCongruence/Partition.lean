import PartitionsLeanblueprint.RamanujanCongruence.EventuallyEq
import Mathlib.Combinatorics.Enumerative.Partition.Basic





open Nat

/-- The partition function, with `p 0 = 0` -/
def partition : ℕ → ℕ
  | 0 => 0
  | n => Fintype.card (Partition n)

-- needed for later (the paper assumes p (n) = 0 for n < 0)
lemma partition_zero : partition 0 = 0 := rfl


def ramanujan_congruence' (ℓ β : ℕ) : Prop :=
  ∀ n, ℓ ∣ partition (ℓ*n - β)


-- lemma ramanujan_congruence_unique (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
--     ∃ β, ramanujan_congruence' ℓ β → ramanujan_congruence' ℓ (δ ℓ) := by
--   sorry

abbrev ramanujan_congruence ℓ := ramanujan_congruence' ℓ ((ℓ^2 - 1) / 24)


noncomputable section ProductExpansion

open Classical PowerSeries Finset.HasAntidiagonal Finset

/- We work over an arbitrary field α and substitute α = (ZMod ℓ) for the proof of flu_ne_zero -/
variable {α : Type*}

/- The following few theorems are from Archive\Wiedijk100Theorems\Partition -/




/-- A convenience constructor for the power series whose coefficients indicate a subset. -/
def indicatorSeries (α : Type*) [Semiring α] (s : Set ℕ) : PowerSeries α :=
  PowerSeries.mk fun n => if n ∈ s then 1 else 0


theorem coeff_indicator (s : Set ℕ) [Semiring α] (n : ℕ) :
    coeff (R := α) n (indicatorSeries _ s) = if n ∈ s then 1 else 0 :=
  coeff_mk _ _

theorem constantCoeff_indicator (s : Set ℕ) [Semiring α] :
    constantCoeff (R := α) (indicatorSeries _ s) = if 0 ∈ s then 1 else 0 :=
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
      rw [@sum_ite _ _ _ _ _ (fun _ ↦ Classical.propDecidable _), sum_ite]
      simp_rw [@filter_filter _ _ _ _ _, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one,
        sub_eq_iff_eq_add, zero_add]
      symm
      split_ifs with h
      · suffices #{a ∈ antidiagonal (n + 1) | i + 1 ∣ a.fst ∧ a.snd = i + 1} = 1 by
          simp only [Set.mem_ofPred_eq]; convert congr_arg ((↑) : ℕ → α) this; norm_cast
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
          simp only [Set.mem_ofPred_eq]; convert congr_arg ((↑) : ℕ → α) this; norm_cast
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
      coeff (R := α) n (∏ i ∈ s, indicatorSeries α ((· * i) '' c i)) := by
  simp_rw [coeff_prod, coeff_indicator, prod_boole, sum_boole]
  apply congr_arg
  simp only [Set.mem_image]
  set phi : (a : Nat.Partition n) →
    a ∈ filter (fun p ↦ (∀ (j : ℕ), Multiset.count j p.parts ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s) univ →
    ℕ →₀ ℕ := fun p _ => {
      toFun := fun i => Multiset.count i p.parts • i
      support := Finset.filter (fun i => i ≠ 0) p.parts.toFinset
      mem_support_toFun := fun a => by
        simp only [smul_eq_mul, ne_eq, mul_eq_zero, Multiset.count_eq_zero]
        rw [not_or, not_not]
        simp only [Multiset.mem_toFinset, mem_filter] }
  refine Finset.card_bij phi ?_ ?_ ?_
  · intro a ha
    simp only [phi, mem_filter]
    rw [mem_finsuppAntidiag]
    dsimp only [ne_eq, smul_eq_mul, id_eq, eq_mpr_eq_cast, Finsupp.coe_mk]
    simp only [mem_univ, mem_filter, true_and] at ha
    refine ⟨⟨?_, fun i ↦ ?_⟩, fun i _ ↦ ⟨a.parts.count i, ha.1 i, rfl⟩⟩
    · conv_rhs => simp [← a.parts_sum]
      rw [sum_multiset_count_of_subset _ s]
      · simp only [smul_eq_mul]
      · intro i
        simp only [Multiset.mem_toFinset]
        apply ha.2
    · simp only [Multiset.mem_toFinset, mem_filter, and_imp]
      exact fun hi _ ↦ ha.2 i hi
  ·
    intro p₁ hp₁ p₂ hp₂ h
    apply Nat.Partition.ext
    simp only [true_and, mem_univ, mem_filter] at hp₁ hp₂
    ext i
    simp only [phi, ne_eq, smul_eq_mul, Finsupp.mk.injEq] at h
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
      simp only [Multiset.mem_sum] at hi
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
      simp at hi
      rcases hi with ⟨j, hj₁, hj₂⟩
      rwa [Multiset.eq_of_mem_replicate hj₂]
    · ext i
      simp_rw [Multiset.count_sum', Multiset.count_replicate, sum_ite_eq']
      simp only [ne_eq, smul_eq_mul, ite_mul, zero_mul, Finsupp.coe_mk]
      split_ifs with h
      · apply Nat.div_mul_cancel
        rcases hf₄ i h with ⟨w, _, hw₂⟩
        apply Dvd.intro_left _ hw₂
      · apply symm
        rw [← Finsupp.notMem_support_iff]
        exact notMem_mono hf'.2 h



/-- The generating function for the standard partition function, with `p 0 = 1` -/

def partitionProduct (m : ℕ) [Field α] :=
  ∏ i ∈ range m, (1 - (X : α⟦X⟧) ^ (i + 1) )⁻¹



def ppart [Field α] : ℕ → α ⟦X⟧
  | 0 => 0
  | n => Fintype.card (Partition n)

lemma ppart_zero [Field α] : ppart 0 = (0 : α ⟦X⟧) := rfl

lemma ppart_eq [Field α] (n : ℕ) : ↑(partition n) = (ppart n : α ⟦X⟧) := by
  cases n; rw [partition_zero, cast_zero]; rfl; rfl

def apart [Field α] : ℕ → α
  | 0 => 0
  | n => Fintype.card (Partition n)

lemma apart_eq [Field α] (n : ℕ) : ↑(partition n) = (apart n : α) := by
  cases n; rw [partition_zero, cast_zero]; rfl; rfl




def mkUniv : ℕ ↪ ℕ :=
  ⟨(· + 1), λ _ _ ↦ Nat.add_right_cancel⟩

lemma mkUniv_apply (n : ℕ) : mkUniv n = n + 1 := rfl

theorem partitionGF_prop [Field α] (n m : ℕ) :
    #{p : n.Partition | ∀ j ∈ p.parts, j ∈ (range m).map mkUniv} = coeff (R := α) n (partitionProduct m) := by

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


/- having npos here is inconvenient, but we can get around it using `natpart`
and some shenanigans in the proof of flu_eq_zero -/

theorem partitionProduct_eq [Field α] {n m : ℕ} (npos : n > 0) (h : n ≤ m) :
    partition n = coeff (R := α) n (partitionProduct m) := by

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

  rw[mkUniv_apply, Nat.sub_add_cancel]; exact Partition.parts_pos _ jin

  show n ≠ 0; rwa [← Nat.pos_iff_ne_zero]


def natpart (n : ℕ) : ℕ :=
  Fintype.card (Partition n)

lemma natpart_zero : natpart 0 = 1 := by
  unfold natpart; rw [Fintype.card_unique]

lemma natpart_succ (n : ℕ) : natpart (n + 1) = partition (n + 1) := rfl

lemma natpart_of_ne_zero {n : ℕ} (n0 : n ≠ 0) : natpart n = partition n := by
  have : ∃ k, n = k + 1 := exists_eq_succ_of_ne_zero n0
  obtain ⟨k,rfl⟩ := this; exact natpart_succ k

theorem partitionProduct_eq_natpart [Field α] {n m : ℕ} (h : n ≤ m) :
    natpart n = coeff (R := α) n (partitionProduct m) := by
  by_cases n0 : n = 0
  simp [n0, natpart_zero, partitionProduct]
  rw [natpart_of_ne_zero n0]
  rw [← ne_eq, ← pos_iff_ne_zero] at n0
  exact partitionProduct_eq n0 h


theorem partitionProduct_eventually_natpart_sum [Field α] :
    (partitionProduct ·) ⟶ (∑ i ∈ range ·, (natpart i) • (X : α⟦X⟧) ^ i) := by
  intro n; dsimp; use n + 1; intro k kle j jg
  have klj : k < j := by omega
  trans coeff (R := α) k (∑ i ∈ range j, C (R := α) (natpart i) * X ^ i)
  simp only [coeff_sum_X_pow klj, partitionProduct_eq_natpart (le_of_lt klj)]
  simp only [map_natCast, nsmul_eq_mul]


theorem partitionProduct_mul_eq_natpart_sum [Field α] (n : ℕ) (f : ℕ → Polynomial α) :
  ∃ M, ∀ m ≥ M, (coeff (R := α) n) ( (f m) * (partitionProduct m : α⟦X⟧) ) =
    (coeff (R := α) n) ( (f m) * ∑ i ∈ range m, (natpart i) • (X : α⟦X⟧) ^ i ) := by
  have hf := @partitionProduct_eventually_natpart_sum
  obtain ⟨M, fo⟩ := (eventuallyEq_mul (eventuallyEq.refl (lift f)) hf) n
  use M; intro m mg; specialize fo n (le_refl _) m mg
  simp_all only [Pi.mul_apply, lift_apply]
