import PartitionsLeanblueprint.Basis



/- This file defines ord, the order of vanishing of an Integer Modular Form,
and proves some basic facts about it. -/


section ord


lemma NeZero.exists {α β} [Zero β] {f : α → β} [h : NeZero f] : ∃ n, f n ≠ 0 := by
  have := h.out
  contrapose! this
  ext x; rw [this x, Pi.ofNat_apply]

instance NeZero.coe {k} {f : IntegerModularForm k} [h: NeZero f] : NeZero ⇑f :=
  ⟨by
    have := h.out
    contrapose! this
    ext n; rw [this]; rfl⟩

instance NeZero.Mcoe {ℓ k} [NeZero ℓ] (f : ModularFormMod ℓ k) [h : NeZero f] : NeZero ⇑f :=
  ⟨by
    have := h.out
    contrapose! this
    ext n; rw [this]; rfl⟩

@[simp] lemma Mcongr_NeZero {ℓ} [NeZero ℓ] {k j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k) (h : k = j) :
    NeZero (Mcongr h f) ↔ NeZero f := by
  constructor <;> intro hf <;> obtain ⟨n,hn⟩ := (NeZero.Mcoe (h := hf)).exists
  <;> apply Modulo.Exists_ne_zero ⟨n, by contrapose! hn; simp_all only [Mcongr_apply]⟩


namespace Integer

instance {k} : NoZeroSMulDivisors ℤ (IntegerModularForm k) := by
  rw [noZeroSMulDivisors_int_iff_isAddTorsionFree]
  exact ⟨ by
    intro c c0 a b h
    ext n
    rw [DFunLike.ext_iff] at h
    simpa [c0] using h n ⟩

instance instSmulNeZero {k} (a : IntegerModularForm k) [ha : NeZero a] (c : ℤ) [hc : NeZero c] : NeZero (c • a) where
  out := by
    obtain ⟨n, hn⟩ := ha.coe.exists
    contrapose! hn
    have : c = 0 ∨ a = 0 := by refine smul_eq_zero.mp hn
    rcases this with c0 | a0
    have := hc.out; contradiction
    have := ha.out; contradiction

instance instIconstNeZero (c : ℤ) [h : NeZero c] : NeZero (Iconst c) := by
  apply Exists_ne_zero
  use 0; simp only [Iconst_zero, ne_eq, h.out, not_false_eq_true]

lemma NeZero_mul_left {k j} (a : IntegerModularForm k) (b : IntegerModularForm j) [h : NeZero (a * b)] : NeZero a where
  out := have := h.out; by
    contrapose! this; ext n; rw [this, zero_apply]
    rw [mul_apply]; apply Finset.sum_eq_zero; simp

lemma NeZero_mul_right {k j} (a : IntegerModularForm k) (b : IntegerModularForm j) [h : NeZero (a * b)] : NeZero b where
  out := have := h.out; by
    contrapose! this; ext n; rw [this, zero_apply]
    rw [mul_apply]; apply Finset.sum_eq_zero; simp


instance instIcongrNeZero {k j} (a : IntegerModularForm k) (h : k = j) [ha : NeZero a] : NeZero (Icongr h a) := by
  obtain ⟨n, hn⟩ := ha.coe.exists
  apply Exists_ne_zero ⟨n, by rwa [Icongr_apply]⟩


-- why can't I make this an instance?
lemma NeZero_of_Icongr {k j} (a : IntegerModularForm k) (h : k = j) [ha : NeZero (Icongr h a)] : NeZero a := by
  obtain ⟨n, hn⟩ := ha.coe.exists
  apply Exists_ne_zero ⟨n, by rwa [Icongr_apply] at hn⟩

lemma NeZero_of_Ipow {k} (a : IntegerModularForm k) (j : ℕ) [ha : NeZero (a ** j)] [hj : NeZero j] : NeZero a where
  out := have := ha.out; by
    contrapose! this; rw [this, zero_Ipow]


variable {k m j : ℕ} {f : IntegerModularForm k} {g : IntegerModularForm j} [fn0 : NeZero f] [gn0 : NeZero g]

/-- The order of vanishing of an integer modular form at infinity.
The location of the first non-zero entry. -/
def ord (f : IntegerModularForm k) [h : NeZero f] : ℕ :=
  Nat.find h.coe.exists

theorem ord_spec (f : IntegerModularForm k) [h : NeZero f] : f (ord f) ≠ 0 :=
  Nat.find_spec h.coe.exists

theorem lt_ord_apply (f : IntegerModularForm k) [h : NeZero f] {m : ℕ} (hm : m < ord f) : f m = 0 := by
  simp only [ord, Nat.lt_find_iff, not_not] at hm
  exact hm m <| le_refl m

theorem le_ord_iff : m ≤ ord f ↔ ∀ n < m, f n = 0 := by
  simp only [ord, ne_eq, Nat.le_find_iff, Decidable.not_not]

theorem ord_eq_iff : ord f = m ↔ f m ≠ 0 ∧ ∀ n < m, f n = 0 := by
  simp only [ord, Nat.find_eq_iff, not_not]

@[simp]
theorem ord_eq_zero : ord f = 0 ↔ f 0 ≠ 0 := by
  simp only [ord_eq_iff, ne_eq, not_lt_zero', IsEmpty.forall_iff, implies_true, and_true]

theorem ord_eq_ord_iff : ord f = ord g ↔ ∃ m, f m ≠ 0 ∧ ∀ n ≤ m, f n = 0 ↔ g n = 0 := by
  constructor <;> intro h
  {
    use ord f; constructor
    exact ord_spec f
    intro n nle; constructor <;> intro h0

    have : n + 1 ≤ ord f := by
      rw [le_ord_iff]
      rintro m (mle | meq)
      exact h0
      exact le_ord_iff.mp nle m meq
    exact le_ord_iff.mp (h ▸ this) n (Nat.lt_succ_self n)

    have : n + 1 ≤ ord g := by
      rw [le_ord_iff]
      rintro m (mle | meq)
      exact h0
      exact le_ord_iff.mp (h ▸ nle) m meq
    exact le_ord_iff.mp (h ▸ this) n (Nat.lt_succ_self n)
  }
  {
    obtain ⟨m, fm0, h⟩ := h
    apply Nat.find_congr fm0
    simpa only [not_iff_not]
  }

theorem ord_eq_ord' (h : ∀ x, f x = 0 ↔ g x = 0) : ord f = ord g := by
  rw [ord_eq_ord_iff]
  use ord f, ord_spec f, fun x _ => h x

theorem ord_smul (c : ℤ) [hc : NeZero c] : ord (c • f) = ord f := by
  apply ord_eq_ord'
  intro x
  simp only [coe_smulz, Pi.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  intro h
  simp_all only [neZero_zero_iff_false]

open Finset in
theorem mul_ord_sum_ne_zero {k j} (a : IntegerModularForm k) (b : IntegerModularForm j) [ha: NeZero a] [hb: NeZero b] :
    (a * b) (ord a + ord b) ≠ 0 := by
  rw [mul_apply]; calc

    _ = ∑ x ∈ (antidiagonal (ord a + ord b)) \ {(ord a, ord b)},
        a x.1 * b x.2 + a (ord a) * b (ord b) := by
      simp only [singleton_subset_iff, mem_antidiagonal, Nat.add_left_cancel_iff,
        sum_sdiff_eq_sub, sum_singleton, sub_add_cancel]

    _ = 0 + a (ord a) * b (ord b) := by
      congr; apply sum_eq_zero fun x xin => ?_
      obtain ⟨sumeq, xne⟩ := mem_sdiff.mp xin
      simp_all only [mem_antidiagonal, mem_singleton, mul_eq_zero]
      have : x.1 < ord a ∨ x.2 < ord b := by
        have : x.1 ≠ ord a ∨ x.2 ≠ ord b := by
          contrapose! xne; ext; exacts [xne.1, xne.2]
        contrapose! sumeq; apply ne_of_gt
        rcases this with alt | blt
        apply add_lt_add_of_lt_of_le (lt_of_le_of_ne sumeq.1 alt.symm) sumeq.2
        apply add_lt_add_of_le_of_lt sumeq.1 (lt_of_le_of_ne sumeq.2 blt.symm)
      rcases this with lta | ltb
      left; exact lt_ord_apply a lta
      right; exact lt_ord_apply b ltb

    _ ≠ 0 := by rw [zero_add]; exact Int.mul_ne_zero (ord_spec a) (ord_spec b)

open Finset in
theorem mul_lt_ord_sum_zero {k j m} (a : IntegerModularForm k) (b : IntegerModularForm j)
    [ha: NeZero a] [hb: NeZero b] (hm : m < ord a + ord b) : (a * b) m = 0 := by
  rw [mul_apply]; apply sum_eq_zero fun x xin => ?_
  rw [mem_antidiagonal] at xin
  have : x.1 < ord a ∨ x.2 < ord b := by
    contrapose! hm; rw [← xin]
    gcongr; exacts [hm.1, hm.2]
  simp only [mul_eq_zero]
  rcases this with lta | ltb
  left; exact lt_ord_apply a lta
  right; exact lt_ord_apply b ltb



instance instMulNeZero {k j} (a : IntegerModularForm k) (b : IntegerModularForm j) [ha: NeZero a] [hb: NeZero b] :
    NeZero (a * b) where
  out := by
    have := mul_ord_sum_ne_zero a b
    contrapose! this; rw [this, zero_apply]

instance instPowNeZero {k j} (a : IntegerModularForm k) [ha : NeZero a] : NeZero (a ** j) := by
  induction j with
    | zero => rw [Ipow_zero]; exact Exists_ne_zero ⟨0, Iconst_zero 1 ▸ one_ne_zero⟩
    | succ j ih => rw [Ipow_succ]; infer_instance

@[simp]
theorem ord_Icongr {k j} (a : IntegerModularForm k) (h : k = j) [ha : NeZero a] : ord (Icongr h a) = ord a := by
  apply ord_eq_ord'; simp only [cast_eval, implies_true]

theorem ord_Icongr' {k j} (a : IntegerModularForm k) (h : k = j) [ha : NeZero (Icongr h a)] :
    ord (Icongr h a) = ord a (h := NeZero_of_Icongr a h) :=
  ord_Icongr a h (ha := NeZero_of_Icongr a h)

@[simp]
theorem ord_Iconst (c : ℤ) [hc : NeZero c] : ord (Iconst c) = 0 := by
  simp only [ord_eq_zero, Iconst_zero, ne_eq, hc.out, not_false_eq_true]


theorem ord_mul {k j} (a : IntegerModularForm k) (b : IntegerModularForm j) [ha: NeZero a] [hb: NeZero b] :
    ord (a * b) = ord a + ord b :=
  ord_eq_iff.mpr ⟨mul_ord_sum_ne_zero a b, fun _ => mul_lt_ord_sum_zero a b⟩


theorem ord_mul' {k j} (a : IntegerModularForm k) (b : IntegerModularForm j) [h : NeZero (a * b)] :
    ord (a * b) = ord a (h := NeZero_mul_left a b) + ord b (h := NeZero_mul_right a b) :=
  ord_mul a b (ha := NeZero_mul_left a b) (hb := NeZero_mul_right a b)


theorem ord_Ipow {k j} (a : IntegerModularForm k) [ha : NeZero a] : ord (a ** j) = j * ord a := by
  induction j with
  | zero => simp only [Nat.mul_zero, Ipow_zero, ord_Iconst, zero_mul]
  | succ j ih => simp only [Ipow_succ, ord_Icongr, ord_mul, ih]; ring


theorem ord_Ipow' {k j} (a : IntegerModularForm k) [ha : NeZero (a ** j)] [hj : NeZero j] :
    ord (a ** j) = j * ord a (h := NeZero_of_Ipow a j) :=
  ord_Ipow a (ha := NeZero_of_Ipow a j)

open Finset in
theorem ord_mul_ord (a : IntegerModularForm k) (b : IntegerModularForm j) [ha: NeZero a] [hb: NeZero b] :
    (a * b) (ord a + ord b) = a (ord a) * b (ord b) := by
  calc

  _ = ∑ x ∈ antidiagonal (ord a + ord b) \ {(ord a, ord b)},
    a (x.1) * b (x.2) + a (ord a) * b (ord b) := by simp [mul_apply]

  _ = 0 + a (ord a) * b (ord b) := by
    congr; apply Finset.sum_eq_zero fun x hx => ?_
    simp only [mem_sdiff, mem_antidiagonal, mem_singleton] at hx
    obtain ⟨xsum, xne⟩ := hx
    have : x.1 ≠ ord a ∨ x.2 ≠ ord b := by contrapose! xne; exact Prod.ext_iff.mpr xne
    have : x.1 < ord a ∨ x.2 < ord b := by omega
    rcases this with h | h
    <;> simp only [lt_ord_apply _ h, mul_zero, zero_mul]

  _ = _ := zero_add _


theorem ord_mul_ord' (a : IntegerModularForm k) (b : IntegerModularForm j) (c : ℕ) [ha: NeZero a] [hb: NeZero b]
  (hc : c = ord a + ord b) : (a * b) c = a (ord a) * b (ord b) := hc ▸ ord_mul_ord a b

open Finset Finset.Nat in
theorem ord_Ipow_ord (a : IntegerModularForm k) (j : ℕ) [ha : NeZero a] : (a ** j) (j * ord a) = a (ord a) ^ j := by
  calc

  (a ** j) (j * ord a) = ∑ x ∈ antidiagonalTuple j (j * ord a) \ {fun _ => ord a}, ∏ y, a (x y) + ∏ y, a (ord a) := by
    rw [Ipow_apply, sum_sdiff_eq_sub, sum_singleton]; ring
    rw [singleton_subset_iff, mem_antidiagonalTuple, sum_const, smul_eq_mul, card_fin]

  _ = 0 + a (ord a) ^ j := by
    congr
    {
      by_cases j0 : j = 0
      subst j0; simp

      apply sum_eq_zero fun x xin => ?_
      rw [prod_eq_zero_iff]
      rw [mem_sdiff, mem_singleton, mem_antidiagonalTuple] at xin
      obtain ⟨xsum, xne⟩ := xin


      suffices ∃ b, x b < ord a by
        obtain ⟨b, blt⟩ := this
        use b, mem_univ b, lt_ord_apply (f := a) blt
      contrapose! xsum; apply ne_of_gt
      have : ∃ b, x b ≠ ord a := by contrapose! xne; exact funext xne
      obtain ⟨b, bne⟩ := this

      calc
        j * ord a = (j - 1) * ord a + ord a := by
          apply Nat.eq_add_of_sub_eq
          exact Nat.le_mul_of_pos_left (ord a) (Nat.pos_of_ne_zero j0)
          rw [Nat.sub_mul, one_mul]

        _ < (j - 1) * ord a + x b := by
          have : x b > ord a := lt_of_le_of_ne (xsum b) bne.symm
          gcongr

        _ ≤ ∑ i ∈ (univ (α := Fin j)).erase b, x i + x b := by
          gcongr; simp_rw [← smul_eq_mul, ← card_fin j, ← card_erase_of_mem (mem_univ b), ← sum_const]
          exact sum_le_sum fun b _ => xsum b

        _ = ∑ i, x i := sum_erase_add univ x (mem_univ b)


    }
    rw [prod_const, card_fin]

  _ = a (ord a) ^ j := zero_add _


theorem ord_Ipow_ord' (a : IntegerModularForm k) (j : ℕ) [ha : NeZero a] (k : ℕ) (h : k = j * ord a) :
    (a ** j) k = a (ord a) ^ j := h ▸ ord_Ipow_ord a j


@[simp] theorem ord_Delta : ord Δ = 1 := by simp [ord_eq_iff]

@[simp] theorem ord_Eis (j : ℕ) [h : NeZero (j - 1)] : ord (Eis j) = 0 := by
  have j1 : j ≠ 1 := by have := h.out; omega
  simp [ord_eq_iff, Eis_ne_one_zero j1]

@[simp] theorem ord_fl {ℓ : ℕ} : ord (fl ℓ) = δ ℓ := by
  simp only [fl, ord_Ipow, ord_Delta, mul_one]

-- why does simp not work
@[simp]
lemma ord_Eis_mul (a b c : ℕ) : ord (Eis 2 ** a * Eis 3 ** b * Δ ** c) = c := by
  simp only [ord_mul, ord_Ipow]; simp




variable {f g : IntegerModularForm k} [fn0 : NeZero f] [gn0 : NeZero g]



theorem Fin.cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
  intro i; cases i; expose_names
  match val with
  | 0 => left; rfl
  | 1 => right; rfl



theorem not_LI_fin2 {α β} (f g : α) [AddCommGroup α] [CommRing β]
  [NoZeroDivisors β] [Module β α] [hf : NeZero f] [hg: NeZero g] [NoZeroSMulDivisors β α] :
    ¬ (LinearIndependent β ![f, g]) ↔ ∃ c d : β, c • f = d • g ∧ (c ≠ 0 ∨ d ≠ 0) := by
  simp [not_linearIndependent_iff]
  constructor <;> intro h
  {
    obtain ⟨s, l, sumeq, ⟨i, is, hi⟩⟩ := h
    use l 0, - l 1
    obtain (rfl | rfl) := Fin.cases i
    {
      have sin : 1 ∈ s := by
        contrapose! hi
        have seq : s = {0} := by
          ext x; simp only [Fin.isValue, Finset.mem_singleton]
          obtain (rfl | rfl) := Fin.cases x <;> simpa
        subst seq; simp_all
        rcases sumeq with l0 | f0
        · exact l0
        · exact absurd f0 hf.out

      have seq : s = {0,1} := by
        ext x; obtain rfl | rfl := Fin.cases x <;> simpa

      subst seq; simp_all
      rwa [eq_neg_iff_add_eq_zero]
    }
    {
      have sin : 0 ∈ s := by
        contrapose! hi
        have seq : s = {1} := by
          ext x; simp only [Fin.isValue, Finset.mem_singleton]
          obtain rfl | rfl := Fin.cases x <;> simpa
        subst seq; simp_all
        rcases sumeq with l0 | g0
        · exact l0
        · exact absurd g0 hg.out

      have seq : s = {0,1} := by
        ext x; obtain rfl | rfl := Fin.cases x <;> simpa

      subst seq; simp_all
      rwa [eq_neg_iff_add_eq_zero]
    }
  }
  {
    obtain ⟨c, d, hsmul, h⟩ := h
    use {1,2}, ![-c,d]; simp
    constructor
    rwa [← sub_eq_add_neg, sub_eq_zero, Eq.comm]
    exact h.symm
  }


theorem twice_ne_zero {c d : ℤ} (hsmul : c • f = d • g) (h0 : c ≠ 0 ∨ d ≠ 0) : c ≠ 0 ∧ d ≠ 0 := by
  rcases h0 with c0 | d0

  refine ⟨c0, ?_⟩
  contrapose! c0; subst c0
  rw [zero_smul] at hsmul
  obtain c0 | f0 := eq_zero_or_eq_zero_of_smul_eq_zero hsmul
  exact c0
  have := fn0.out; contradiction

  refine ⟨?_, d0⟩
  contrapose! d0; subst d0
  rw [zero_smul] at hsmul
  obtain d0 | f0 := eq_zero_or_eq_zero_of_smul_eq_zero hsmul.symm
  exact d0
  have := gn0.out; contradiction



theorem LI_of_ne_ord (hfg : ord f ≠ ord g) : LinearIndependent ℤ ![f, g] := by
  contrapose! hfg
  obtain ⟨c, d, h, h0⟩ := (not_LI_fin2 f g).mp hfg

  have : NeZero c := ⟨(twice_ne_zero h h0).1⟩
  have : NeZero d := ⟨(twice_ne_zero h h0).2⟩
  calc
    _ = ord (c • f) := (ord_smul c).symm
    _ = ord (d • g) := by simp_rw [h]
    _ = ord g := ord_smul d


end Integer
