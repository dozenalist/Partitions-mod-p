
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
and the power series product expansions for these functions and some Modular Forms,
and to ultimately prove that if there exists a ramanujan congruence mod ℓ then fℓ|𝓤 = 0 -/

open Nat PowerSeries Finset Modulo2 ModularFormDefs.Integer

def partition : ℕ → ℕ
  | 0 => 0
  | n => Fintype.card (Partition n)

-- needed for later but might break stuff
lemma partition_zero : partition 0 = 0 := rfl


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



-- open Finset.HasAntidiagonal

-- universe u
-- variable {ι : Type u}

-- open scoped Classical in
-- /-- A convenience constructor for the power series whose coefficients indicate a subset. -/
-- def indicatorSeries (α : Type*) [Semiring α] (s : Set ℕ) : PowerSeries α :=
--   PowerSeries.mk fun n => if n ∈ s then 1 else 0

-- open scoped Classical in
-- theorem coeff_indicator (s : Set ℕ) [Semiring α] (n : ℕ) :
--     coeff α n (indicatorSeries _ s) = if n ∈ s then 1 else 0 :=
--   coeff_mk _ _

-- theorem coeff_indicator_pos (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∈ s) :
--     coeff α n (indicatorSeries _ s) = 1 := by rw [coeff_indicator, if_pos h]

-- theorem coeff_indicator_neg (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∉ s) :
--     coeff α n (indicatorSeries _ s) = 0 := by rw [coeff_indicator, if_neg h]

-- open scoped Classical in
-- theorem constantCoeff_indicator (s : Set ℕ) [Semiring α] :
--     constantCoeff α (indicatorSeries _ s) = if 0 ∈ s then 1 else 0 :=
--   rfl


-- open scoped Classical in
-- -- The main workhorse of the partition theorem proof.
-- theorem partialGF_prop (α : Type*) [CommSemiring α] (n : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, 0 < i)
--     (c : ℕ → Set ℕ) (hc : ∀ i, i ∉ s → 0 ∈ c i) :
--     #{p : n.Partition | (∀ j, p.parts.count j ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s} =
--       coeff α n (∏ i ∈ s, indicatorSeries α ((· * i) '' c i)) := by
--   simp_rw [coeff_prod, coeff_indicator, prod_boole, sum_boole]
--   apply congr_arg
--   simp only [mem_univ, forall_true_left, not_and, not_forall, exists_prop,
--     Set.mem_image, not_exists]
--   set phi : (a : Nat.Partition n) →
--     a ∈ filter (fun p ↦ (∀ (j : ℕ), Multiset.count j p.parts ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s) univ →
--     ℕ →₀ ℕ := fun p _ => {
--       toFun := fun i => Multiset.count i p.parts • i
--       support := Finset.filter (fun i => i ≠ 0) p.parts.toFinset
--       mem_support_toFun := fun a => by
--         simp only [smul_eq_mul, ne_eq, mul_eq_zero, Multiset.count_eq_zero]
--         rw [not_or, not_not]
--         simp only [Multiset.mem_toFinset, not_not, mem_filter] }
--   refine Finset.card_bij phi ?_ ?_ ?_
--   · intro a ha
--     simp only [phi, not_forall, not_exists, not_and, exists_prop, mem_filter]
--     rw [mem_finsuppAntidiag]
--     dsimp only [ne_eq, smul_eq_mul, id_eq, eq_mpr_eq_cast, le_eq_subset, Finsupp.coe_mk]
--     simp only [mem_univ, forall_true_left, not_and, not_forall, exists_prop,
--       mem_filter, true_and] at ha
--     refine ⟨⟨?_, fun i ↦ ?_⟩, fun i _ ↦ ⟨a.parts.count i, ha.1 i, rfl⟩⟩
--     · conv_rhs => simp [← a.parts_sum]
--       rw [sum_multiset_count_of_subset _ s]
--       · simp only [smul_eq_mul]
--       · intro i
--         simp only [Multiset.mem_toFinset, not_not, mem_filter]
--         apply ha.2
--     · simp only [ne_eq, Multiset.mem_toFinset, not_not, mem_filter, and_imp]
--       exact fun hi _ ↦ ha.2 i hi
--   · dsimp only
--     intro p₁ hp₁ p₂ hp₂ h
--     apply Nat.Partition.ext
--     simp only [true_and, mem_univ, mem_filter] at hp₁ hp₂
--     ext i
--     simp only [phi, ne_eq, Multiset.mem_toFinset, not_not, smul_eq_mul, Finsupp.mk.injEq] at h
--     by_cases hi : i = 0
--     · rw [hi]
--       rw [Multiset.count_eq_zero_of_notMem]
--       · rw [Multiset.count_eq_zero_of_notMem]
--         intro a; exact Nat.lt_irrefl 0 (hs 0 (hp₂.2 0 a))
--       intro a; exact Nat.lt_irrefl 0 (hs 0 (hp₁.2 0 a))
--     · rw [← mul_left_inj' hi]
--       rw [funext_iff] at h
--       exact h.2 i
--   · simp only [phi, mem_filter, mem_finsuppAntidiag, mem_univ, exists_prop, true_and, and_assoc]
--     rintro f ⟨hf, hf₃, hf₄⟩
--     have hf' : f ∈ finsuppAntidiag s n := mem_finsuppAntidiag.mpr ⟨hf, hf₃⟩
--     simp only [mem_finsuppAntidiag] at hf'
--     refine ⟨⟨∑ i ∈ s, Multiset.replicate (f i / i) i, ?_, ?_⟩, ?_, ?_, ?_⟩
--     · intro i hi
--       simp only [exists_prop, mem_sum, mem_map, Function.Embedding.coeFn_mk] at hi
--       rcases hi with ⟨t, ht, z⟩
--       apply hs
--       rwa [Multiset.eq_of_mem_replicate z]
--     · simp_rw [Multiset.sum_sum, Multiset.sum_replicate, Nat.nsmul_eq_mul]
--       rw [← hf'.1]
--       refine sum_congr rfl fun i hi => Nat.div_mul_cancel ?_
--       rcases hf₄ i hi with ⟨w, _, hw₂⟩
--       rw [← hw₂]
--       exact dvd_mul_left _ _
--     · intro i
--       simp_rw [Multiset.count_sum', Multiset.count_replicate, sum_ite_eq']
--       split_ifs with h
--       · rcases hf₄ i h with ⟨w, hw₁, hw₂⟩
--         rwa [← hw₂, Nat.mul_div_cancel _ (hs i h)]
--       · exact hc _ h
--     · intro i hi
--       rw [mem_sum] at hi
--       rcases hi with ⟨j, hj₁, hj₂⟩
--       rwa [Multiset.eq_of_mem_replicate hj₂]
--     · ext i
--       simp_rw [Multiset.count_sum', Multiset.count_replicate, sum_ite_eq']
--       simp only [ne_eq, Multiset.mem_toFinset, not_not, smul_eq_mul, ite_mul,
--         zero_mul, Finsupp.coe_mk]
--       split_ifs with h
--       · apply Nat.div_mul_cancel
--         rcases hf₄ i h with ⟨w, _, hw₂⟩
--         apply Dvd.intro_left _ hw₂
--       · apply symm
--         rw [← Finsupp.notMem_support_iff]
--         exact notMem_mono hf'.2 h



/- Pretty much everything above this is from Archive\Wiedijk100Theorems\Partition,
and below is what I have done. I don't really know what's going on yet. -/

def partitionProduct (m : ℕ) [Field α] :=
  ∏ i ∈ range m, (1 - (X : α⟦X⟧) ^ i )⁻¹

def DeltaProduct [Field α] (m : ℕ) :=
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

def ppart [Field α] : ℕ → α ⟦X⟧
  | 0 => 0
  | n => Fintype.card (Partition n)

lemma ppart_zero {α} [Field α] : ppart 0 = (0 : α ⟦X⟧) := rfl

lemma ppart_eq [Field α] (n : ℕ) :  ↑ (partition n) = (ppart n : α ⟦X⟧) := by
  cases n; rw[partition_zero, cast_zero]; rfl; rfl

def apart [Field α] : ℕ → α
  | 0 => 0
  | n => Fintype.card (Partition n)

lemma apart_eq [Field α] (n : ℕ) :  ↑ (partition n) = (apart n : α) := by
  cases n; rw[partition_zero, cast_zero]; rfl; rfl

theorem partitionProduct_eq [Field α] (n m : ℕ) (h : n ≤ m) :
    partition n = coeff α n (partitionProduct m) := by
  sorry

theorem DeltaProduct_eq {ℓ} [Fact (Nat.Prime ℓ)] [Field α] (n m : ℕ) (h : n ≤ m) :
    Integer_Delta n = coeff α n (DeltaProduct m) := by
  sorry

theorem fl_Product_eq {ℓ} [Fact (Nat.Prime ℓ)] [Field α] (n m : ℕ) (h : n ≤ m) :
    Integer_fl ℓ n = coeff α n (flProduct ℓ m) := by
  sorry


theorem partitionProduct_eq_sum (m : ℕ) [Field α] :
    partitionProduct m = ∑ i ∈ range m, partition i * (X : α⟦X⟧) ^ i := by
  sorry



end ProductExpansion



theorem fl_eq_reduce {ℓ : ℕ} [Fact (Nat.Prime ℓ)] : f ℓ == Reduce (Integer_fl ℓ) ℓ := by
  sorry



lemma coeff_sum_X_pow {α} [Field α] {n N : ℕ} {a : ℕ → α} (h : n < N) :
    coeff α n (∑ i ∈ range N, (PowerSeries.C α (a i)) * (X : α⟦X⟧) ^ i ) = a n := by
  simp [map_sum, coeff_X_pow]
  exact λ nle ↦ (not_lt_of_ge nle h).rec


lemma coeff_sum_X_pow_mul {α} [Field α] {n N ℓ : ℕ} [NeZero ℓ] {a : ℕ → α} (h : n < N) :
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
  exact Trans.trans this <| xeqk ▸ h
  left; exact xeqk.symm
  rw [sum_singleton]
  rw [sum_const_zero]
  rw [add_zero]; congr; exact Nat.eq_div_of_mul_eq_right ln0 rfl
  apply sum_eq_zero; intro x xlN
  rw[dvd_def] at ldiv; push_neg at ldiv
  exact if_neg (ldiv x)


lemma coeff_sum_squash {α} [Field α] {j ℓ N M : ℕ} [NeZero ℓ] {a b : ℕ → α} (jlN : ℓ * j < N) (jlM : ℓ * j < M) :
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
      intro p hp
      congr; dsimp
      exact Nat.eq_div_of_mul_eq_right ln0 rfl


lemma coeff_mul_shift {α} [Field α] {m N : ℕ} (f : ℕ → α ⟦X⟧) :
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
  exact add_comm m a



lemma coeff_mul_shift_of_zero {α} [Field α] {m N : ℕ} (f : ℕ → α ⟦X⟧) (f0 : f 0 = 0) :
    X ^ m * ∑ i ∈ range N, f i * X ^ i = ∑ i ∈ range (N + m), f (i - m) * X ^ i := calc

  _ = ∑ i ∈ Ico m (N + m), f (i - m) * X ^ i := coeff_mul_shift f

  _ = (∑ i ∈ range (N + m), f (i - m) * X ^ i) - ∑ i ∈ range m, f (i - m) * X ^ i :=
    sum_Ico_eq_sub _ <| Nat.le_add_left m N

  _ = _ := by
    nth_rw 2 [← sub_zero (∑ i ∈ range (N + m), f (i - m) * X ^ i)]
    congr; apply sum_eq_zero; intro x xlm; trans 0 * X ^ x
    congr; rw[← f0]; apply congrArg; refine Nat.sub_eq_zero_of_le ?_
    exact le_of_lt <| List.mem_range.mp xlm
    rw[zero_mul]


lemma prod_eq_sum  (α) [Field α] (ℓ n : ℕ) : ∃ c : ℕ → α, ∃ M > ℓ * n,
    (∏ i ∈ range (ℓ * n), (1 - (X : α ⟦X⟧) ^ (ℓ * i)) ^ ℓ) = ∑ i ∈ range M, C α (c i) * X ^ (ℓ * i) := by
  induction ℓ with
  | zero => use fun _ ↦ 1, 1; simp
  | succ ℓ ih =>
    obtain ⟨c, M, hM, hc⟩ := ih
    use fun i ↦ coeff α ((ℓ + 1)* i) (∑ i ∈ range M, C α (c i) * X ^ (ℓ * i)) , M + (ℓ + 1) * n + 1
    constructor; omega
    rw [add_mul, one_mul, prod_range_add]
    have rrs : (∏ x ∈ range (ℓ * n), (1 - (X : (ZMod ℓ) ⟦X⟧) ^ ((ℓ + 1) * x)) ^ (ℓ + 1)) =
      (∏ x ∈ range (ℓ * n), (1 - (X : (ZMod ℓ) ⟦X⟧) ^ (ℓ * x)) ^ ℓ) *
      (∏ x ∈ range (ℓ * n), (1 - (X : (ZMod ℓ) ⟦X⟧) ^ (ℓ * x)) ) := by
      simp_rw [pow_succ, prod_mul_distrib]; congr; sorry
      sorry
    sorry


-- lemma prod_add_one_eq_sum_subsets {α} [Field α] (f : ℕ → α ⟦X⟧) (s : Finset ℕ) :
--     ∏ i ∈ s, (1 + f i) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
--   induction s using Finset.induction_on with
--   | empty => simp
--   | insert i s hi ih =>
--     simp [Finset.prod_insert hi, Finset.sum_powerset_insert, ih, Finset.mul_sum]
--     sorry

instance {p} [Fact (Nat.Prime p)] : CharP ((ZMod p) ⟦X⟧) p := by
  refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
  trans C (ZMod p) (p : (ZMod p)); rfl
  simp only [CharP.cast_eq_zero, map_zero]



theorem flu_eq_zero {ℓ} [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 5)] : ramanujan_congruence ℓ → f ℓ |𝓤 = 0 := by

  intro h
  have lg5 : ℓ ≥ 5 := Fact.out
  have lsq : ℓ ^ 2 ≥ 25 := by
    trans 5 * 5; rw[pow_two]; gcongr; exact le_refl _

  have ineq (n) : n ≤ ℓ * n := Nat.le_mul_of_pos_left n (pos_of_neZero ℓ)

  ext n; rw [U_apply, zero_apply, fl_eq_reduce, Reduce_apply]

  rw [fl_Product_eq _ _ (le_refl _), flProduct, Pi.pow_apply]
  unfold DeltaProduct; calc

  _ = (coeff (ZMod ℓ) (ℓ * n) )
      (X ^ (δ ℓ) * ∏ i ∈ range (ℓ * n), (1 - X ^ i) ^ (ℓ ^ 2 - 1)) := by
    congr; simp only [mul_pow]; congr
    simp_rw[← prod_pow _ (δ ℓ)]
    congr; ext i : 1; rw[← pow_mul]
    congr; unfold δ; exact Nat.mul_div_cancel' delta_integer


  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( X ^ (δ ℓ) *  (∏ i ∈ range (ℓ * n), (1 - X ^ i) ^ (ℓ ^ 2)) *
      (∏ i ∈ range (ℓ * n), (1 - X ^ i)⁻¹) ) := by
    rw[mul_assoc]; congr; calc
      _ = ∏ i ∈ range (ℓ * n), ( (↑1 - X ^ i) ^ (ℓ ^ 2) * (↑1 - X ^ i)⁻¹ ) := by
        congr; ext i : 1;
        by_cases i0 : i = 0
        simp only [i0, pow_zero, sub_self, MvPowerSeries.zero_inv, mul_zero,
            pow_eq_zero_iff', ne_eq, true_and]; apply Nat.ne_of_gt
        apply zero_lt_sub_of_lt; omega
        refine (PowerSeries.eq_mul_inv_iff_mul_eq ?_).mpr ?_
        simp only [map_sub, constantCoeff_one, map_pow, constantCoeff_X]
        rw[zero_pow i0, sub_zero]; exact Ne.symm (zero_ne_one' (ZMod ℓ))
        nth_rw 2[← pow_one (1 - X ^ i)]; rw[mul_comm, pow_mul_pow_sub]
        exact NeZero.one_le

      _ = _ := prod_mul_distrib
    rfl

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range (ℓ * n), (1 - X ^ i) ^ (ℓ ^ 2)) *
      (X ^ (δ ℓ) *  ∏ i ∈ range (ℓ * n), (1 - X ^ i)⁻¹) ) := by
    congr 1; ring

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range (ℓ * n), (↑1 - X ^ i) ^ (ℓ ^ 2)) *
      (X ^ (δ ℓ) * partitionProduct (ℓ * n)) ) := by
    congr

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ( (∏ i ∈ range (ℓ * n), ((↑1 - X ^ (ℓ * i)) ^ ℓ) ) *
      (X ^ (δ ℓ) * partitionProduct (ℓ * n)) ) := by
    congr; ext i : 1
    trans ((1 - X ^ i) ^ ℓ) ^ ℓ
    rw[pow_two, pow_mul]
    congr
    rw [sub_pow_expChar_of_commute, one_pow, ← pow_mul, mul_comm]
    exact Commute.one_left (X ^ i)

  _ = (coeff (ZMod ℓ) (ℓ * n))
      ((∏ i ∈ range (ℓ * n), (1 - X ^ (ℓ * i)) ^ ℓ) *
      ∑ i ∈ range (ℓ * n + δ ℓ), C (ZMod ℓ) (partition (i - δ ℓ)) * X ^ i) := by

    simp_rw [partitionProduct_eq_sum, ppart_eq, coeff_mul_shift_of_zero ppart ppart_zero]
    congr; ext i : 1; rw[← ppart_eq]; rfl

  _ = 0 := by
    obtain ⟨c, M, Mgt, heq⟩ := prod_eq_sum (ZMod ℓ) ℓ n
    simp_rw [heq, apart_eq]
    rw [mul_comm (∑ i ∈ range M, (C (ZMod ℓ)) (c i) * X ^ (ℓ * i))]
    rw [coeff_sum_squash]
    simp only [← apart_eq]; apply sum_eq_zero
    intro x hx
    have : ↑(partition (ℓ * x.1 - δ ℓ)) = (0 : ZMod ℓ) := by
      rw[ZMod.natCast_zmod_eq_zero_iff_dvd]; exact h x.1
    rw[this, zero_mul]
    exact Nat.lt_add_of_pos_right delta_pos
    exact Mgt
