import PartitionsLeanblueprint.Ord
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Set.Card
import PartitionsLeanblueprint.PreliminaryResults



/- The goal of this file is to state the valence formula in a way that is useful,
and to prove some facts about the dimension of the space of modular forms. -/

noncomputable section

open DirectSum



inductive Vars
  | X
  | Y


instance : Fintype Vars where
  elems := {.X, .Y}
  complete
    | .X => Finset.mem_insert_self ..
    | .Y => Finset.mem_insert_of_mem <| Finset.mem_singleton.mpr rfl


open AddMonoidAlgebra

/-- The polynomial ring of two variables, `X` and `Y`, over an arbitrary commutative semiring -/
notation:8000  R "[X,Y]"  => MvPolynomial Vars R


def Weight (p : Vars →₀ ℕ) :=
  4 * p .X + 6 * p .Y


def Poly.X {R} [CommSemiring R] : R[X,Y] := MvPolynomial.X .X
def Poly.Y {R} [CommSemiring R] : R[X,Y] := MvPolynomial.X .Y


def IsobaricPoly' (R : Type) [CommSemiring R] (k : ℕ) : Submodule R R[X,Y] where

  carrier := {p | ∀ (m : Vars →₀ ℕ), p.coeff m ≠ 0 → Weight m = k}

  add_mem' := by
    intro p q pin qin; simp_all only [ne_eq, Set.mem_setOf_eq, MvPolynomial.coeff_add]
    intro m h
    have : ¬MvPolynomial.coeff m p = 0 ∨ ¬ MvPolynomial.coeff m q = 0 := by
      contrapose! h; rw [h.1, h.2, zero_add]
    rcases this with p0 | q0
    exact pin m p0
    exact qin m q0

  zero_mem' := by simp

  smul_mem' := by
    simp only [ne_eq, Set.mem_setOf_eq, MvPolynomial.coeff_smul, smul_eq_mul]
    intro c p pin m h
    have : ¬ MvPolynomial.coeff m p = 0 := by contrapose! h; rw[h, mul_zero]
    exact pin m this

section IsobaricPolyDefs

/-- The isobaric polynomial ring of two variables, `X` and `Y`.
This is the polynomial ring `R[X,Y]`, but where we treat `X` as having weight 4,
`Y` as having weight 6, and only consider entries whose total weight is `k`.
As an example, `3 • X * Y ^* 2 - 2 • X ^* 4 : R[X,Y]16` -/
def IsobaricPoly (R : Type) [CommSemiring R] (k : ℕ) :=
  {p : R[X,Y] // ∀ (m : Vars →₀ ℕ), p.coeff m ≠ 0 → Weight m = k}


namespace IsobaricPoly
open MvPolynomial


@[inherit_doc] scoped notation:9000 R "[X,Y]" k => IsobaricPoly R k

variable {R : Type} [CommRing R] {k j : ℕ}


instance zero : Zero R[X,Y]k := ⟨0, by simp⟩

theorem zero_def : (0 : R[X,Y]k) = ⟨0, by simp⟩ := rfl

protected def one : R[X,Y]0 := ⟨1, by
  simp only [coeff_one, ne_eq, ite_eq_right_iff, Classical.not_imp, and_imp]
  rintro m m0 -
  simp only [← m0, Weight, Finsupp.coe_zero, Pi.zero_apply, mul_zero, add_zero]
  ⟩

instance : One R[X,Y]0 := ⟨IsobaricPoly.one⟩

theorem one_def : (1 : R[X,Y]0) = ⟨1, by
  simp only [coeff_one, ne_eq, ite_eq_right_iff, Classical.not_imp, and_imp]
  rintro m m0 -
  simp only [← m0, Weight, Finsupp.coe_zero, Pi.zero_apply, mul_zero, add_zero] ⟩ := rfl

def ofNat (n : ℕ) : R[X,Y]0 := ⟨C n, by
  intro m; simp only [coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp, and_imp]
  intro m0 nn0
  simp only [← m0, Weight, Finsupp.coe_zero, Pi.zero_apply, mul_zero, add_zero] ⟩

def ofInt (n : ℤ) : R[X,Y]0 := ⟨C n, by
  intro m; simp only [coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp, and_imp]
  intro m0 nn0
  simp only [← m0, Weight, Finsupp.coe_zero, Pi.zero_apply, mul_zero, add_zero] ⟩

protected def add : (R[X,Y]k) → (R[X,Y]k) → R[X,Y]k
  | ⟨p, pin⟩ , ⟨q, qin⟩ => ⟨p + q, by
    simp_all only [ne_eq, Set.mem_setOf_eq, MvPolynomial.coeff_add]
    intro m h
    have : ¬MvPolynomial.coeff m p = 0 ∨ ¬ MvPolynomial.coeff m q = 0 := by
      contrapose! h; rw [h.1, h.2, zero_add]
    rcases this with p0 | q0
    exact pin m p0
    exact qin m q0 ⟩

instance : Add (R[X,Y]k) := ⟨IsobaricPoly.add⟩

theorem add_def (a b : R[X,Y]k) : a + b = ⟨a.val + b.val, by
    simp_all only [ne_eq, Set.mem_setOf_eq, MvPolynomial.coeff_add]
    intro m h
    obtain ⟨p, pin⟩ := a
    obtain ⟨q, qin⟩ := b
    have : ¬MvPolynomial.coeff m p = 0 ∨ ¬ MvPolynomial.coeff m q = 0 := by
      contrapose! h; rw [h.1, h.2, zero_add]
    rcases this with p0 | q0
    exact pin m p0
    exact qin m q0 ⟩ := rfl


protected def mul [NoZeroDivisors R] : (R[X,Y]k) → (R[X,Y]j) → R[X,Y](k + j)
  | ⟨p, hp⟩ , ⟨q, hq⟩ => ⟨p * q, by
    simp_all only [ne_eq, Set.mem_setOf_eq, Weight, coeff_mul]
    intro m h
    have ex : ∃ x ∈ Finset.antidiagonal m, coeff x.1 p * coeff x.2 q ≠ 0 := by
      contrapose! h; apply Finset.sum_eq_zero h
    obtain ⟨⟨x, y⟩, xysum, h⟩ := ex
    simp_all only [Finset.mem_antidiagonal]
    obtain ⟨xn0, yn0⟩ := mul_ne_zero_iff.mp h
    rw [← xysum, ← hp x xn0, ← hq y yn0]
    dsimp; ring
  ⟩

instance Hmul [NoZeroDivisors R] : HMul (R[X,Y]k) (R[X,Y]j) R[X,Y](k + j) := ⟨IsobaricPoly.mul⟩


theorem mul_def [NoZeroDivisors R] (a : R[X,Y]k) (b : R[X,Y]j) : a * b = ⟨a.val * b.val, by
    obtain ⟨p, hp⟩ := a
    obtain ⟨q, hq⟩ := b
    simp_all only [ne_eq, Set.mem_setOf_eq, Weight, coeff_mul]
    intro m h
    have ex : ∃ x ∈ Finset.antidiagonal m, coeff x.1 p * coeff x.2 q ≠ 0 := by
      contrapose! h; apply Finset.sum_eq_zero h
    obtain ⟨⟨x, y⟩, xysum, h⟩ := ex
    simp_all only [Finset.mem_antidiagonal]
    obtain ⟨xn0, yn0⟩ := mul_ne_zero_iff.mp h
    rw [← xysum, ← hp x xn0, ← hq y yn0]
    dsimp [Weight]; ring ⟩ := rfl


instance instSMulZ : SMul ℤ (R[X,Y]k) where
  smul c
    | ⟨p, hp⟩ => ⟨c • p, by
      intro m; simp only [coeff_smul];
      intro h;
      have : coeff m p ≠ 0 := by contrapose! h; rw [h, smul_zero]
      exact hp m this
    ⟩

theorem ZSmul_def (c : ℤ) (a : R[X,Y]k) : c • a = ⟨c • a.val, by
      obtain ⟨p, hp⟩ := a
      intro m; simp only [coeff_smul];
      intro h;
      have : coeff m p ≠ 0 := by contrapose! h; rw [h, smul_zero]
      exact hp m this ⟩ := rfl


instance instSMulN : SMul ℕ (R[X,Y]k) where
  smul c
    | ⟨p, hp⟩ => ⟨c • p, by
      intro m; simp only [coeff_smul];
      intro h;
      have : coeff m p ≠ 0 := by contrapose! h; rw [h, smul_zero]
      exact hp m this
    ⟩

theorem NSmul_def (c : ℕ) (a : R[X,Y]k) : c • a = ⟨c • a.val, by
  obtain ⟨p, hp⟩ := a
  intro m; simp only [coeff_smul]
  intro h
  have : coeff m p ≠ 0 := by contrapose! h; rw [h, smul_zero]
  exact hp m this ⟩ := rfl


instance instSMulR : SMul R (R[X,Y]k) where
  smul c
    | ⟨p, hp⟩ => ⟨c • p, by
      intro m; simp only [coeff_smul];
      intro h;
      have : coeff m p ≠ 0 := by contrapose! h; rw [h, smul_zero]
      exact hp m this
    ⟩

theorem CSmul_def (c : R) (a : R[X,Y]k) : c • a = ⟨c • a.val, by
      obtain ⟨p, hp⟩ := a
      intro m; simp only [coeff_smul];
      intro h;
      have : coeff m p ≠ 0 := by contrapose! h; rw [h, smul_zero]
      exact hp m this ⟩ := rfl


instance instNeg : Neg (R[X,Y]k) where
  neg | ⟨a, ha⟩ => ⟨-a, by simpa only [coeff_neg, neg_ne_zero]⟩

theorem neg_def (a : R[X,Y]k) : -a = ⟨-a.val, by cases a; simpa only [coeff_neg, neg_ne_zero]⟩ := rfl


instance instSub : Sub (R[X,Y]k) :=
  ⟨fun f g => f + -g⟩


instance instAddCommGroup : AddCommGroup R[X,Y]k where

  add := IsobaricPoly.add
  add_assoc := fun a b c ↦ by simp only [add_def, add_assoc]
  zero := ⟨0, by simp⟩
  zero_add := fun ⟨a, ha⟩ ↦ by simp only [zero_def, add_def, zero_add]
  add_zero := fun ⟨a, ha⟩ ↦ by simp only [zero_def, add_def, add_zero]
  nsmul n a := n • a
  zsmul z a := z • a
  neg_add_cancel := fun ⟨a, ha⟩ ↦ by simp only [add_def, neg_def, ne_eq, neg_add_cancel]; rfl
  add_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ by simp only [add_def, add_comm]
  nsmul_zero := fun ⟨a, ha⟩ ↦ by simp only [NSmul_def, zero_smul]; rfl
  nsmul_succ := fun n ⟨a, ha⟩ ↦ by
    simp only [NSmul_def, add_def, ne_eq, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  zsmul_zero' := fun ⟨a, ha⟩ ↦ by simp only [ZSmul_def, zero_smul]; rfl
  zsmul_succ' := fun n ⟨a, ha⟩ ↦ by
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, ne_eq, ZSmul_def,
      zsmul_eq_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, add_mul, add_def, one_mul]
  zsmul_neg' := fun n ⟨a, ha⟩ ↦ by simp [ZSmul_def, neg_def, add_mul]



def Graded.one : GradedMonoid (IsobaricPoly R) := ⟨0, 1⟩

instance : One (GradedMonoid (IsobaricPoly R)) := ⟨Graded.one⟩

instance : GradedMonoid.GOne (IsobaricPoly R) where
  one := 1

instance [NoZeroDivisors R] : GradedMonoid.GMul (IsobaricPoly R) where
  mul f g := f * g

theorem Graded.one_def : (1 : GradedMonoid (IsobaricPoly R)) = ⟨0, 1⟩ := rfl

def Graded.mul [NoZeroDivisors R] : GradedMonoid (IsobaricPoly R) → GradedMonoid (IsobaricPoly R) → GradedMonoid (IsobaricPoly R)
  | ⟨i, a⟩, ⟨j, b⟩ => ⟨i + j, a * b⟩

instance [NoZeroDivisors R] : Mul (GradedMonoid (IsobaricPoly R)) := ⟨Graded.mul⟩


theorem Graded.mul_def [NoZeroDivisors R] (a b : GradedMonoid (IsobaricPoly R)) : a * b = ⟨a.1 + b.1 , a.2 * b.2⟩ := rfl


instance [NoZeroDivisors R] : DirectSum.GCommRing (IsobaricPoly R) where

  mul := IsobaricPoly.mul
  mul_zero := fun ⟨a, ha⟩ ↦ by simp only [IsobaricPoly.mul, ne_eq, mul_zero, zero_def]
  zero_mul := fun ⟨a, ha⟩ ↦ by simp only [IsobaricPoly.mul, ne_eq, zero_mul, zero_def]
  mul_add := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ↦ by simp only [IsobaricPoly.mul, add_def, mul_add]
  add_mul := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ↦ by simp only [IsobaricPoly.mul, add_def, add_mul]
  one := IsobaricPoly.one
  one_mul := fun ⟨i, a, ha⟩ ↦ by
    simp only [Graded.one_def, one_def, Graded.mul_def, mul_def, one_mul]
    congr!; rw[zero_add]
  mul_one := fun ⟨i, a, ha⟩ ↦ by
    simp only [Graded.one_def, one_def, Graded.mul_def, mul_def]
    congr!; rw [mul_one]
  mul_assoc a b c := by
    simp only [Graded.mul_def, mul_def]
    congr! 1; rw[add_assoc]
    congr! 1; simp only [add_assoc]
    rw [mul_assoc]
  natCast n := ofNat n
  natCast_zero := by simp only [ofNat, zero_def, Nat.cast_zero, C_0]
  natCast_succ n := by
    simp only [ofNat, ne_eq, Nat.cast_add, Nat.cast_one, C_add, map_natCast, C_1]
    simp only [add_def]; rfl
  intCast z := ofInt z
  intCast_ofNat n := by simp only [ofInt, ofNat, Int.cast_natCast, map_natCast]
  intCast_negSucc_ofNat n := by simp [ofInt, ofNat, neg_def]
  mul_comm := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ ↦ by
    simp only [Graded.mul_def, mul_def, mul_comm]
    congr! 1; rw [add_comm]
    congr!

lemma gone_def : (GradedMonoid.GOne.one : R[X,Y]0) = 1 := rfl

lemma ofInt_mul [NoZeroDivisors R] (x y : ℤ) : (ofInt (x * y) : R[X,Y]0) = ofInt x * ofInt y := by
  simp only [ofInt, Int.cast_mul, C_mul, map_intCast]; rw [mul_def]

lemma Graded.ZSmul_def (c : ℤ) (x : GradedMonoid (IsobaricPoly R)) : c • x = ⟨x.1, c • x.2⟩ := rfl

instance instGAlgebra [NoZeroDivisors R] : DirectSum.GAlgebra ℤ (IsobaricPoly R) where
  toFun := {
    toFun := ofInt
    map_zero' := by simp only [ofInt, zero_def, Int.cast_zero, C_0]
    map_add' := fun x y ↦ by simp only [ofInt, add_def, Int.cast_add, C_add] }
  map_one := by dsimp; simp only [gone_def, ofInt, one_def, Int.cast_one, C_1]
  map_mul x y := by dsimp; rw [ofInt_mul]; rfl
  commutes c x := mul_comm _ _
  smul_def c x := by
    dsimp; obtain ⟨k, x⟩ := x
    rw [Graded.ZSmul_def, ZSmul_def, Graded.mul_def]
    have r1 : (GradedMonoid.mk 0 (ofInt c) : GradedMonoid (IsobaricPoly R)).fst = 0 := rfl
    have r2 : (GradedMonoid.mk 0 (ofInt c) : GradedMonoid (IsobaricPoly R)).snd = ofInt c := rfl
    simp only [r1, r2]
    congr!; rw [r1, zero_add]
    simp only [mul_def, ofInt, ne_eq, zsmul_eq_mul, map_intCast]
    congr
    simp only [zero_add]
    simp only [zero_add, heq_eq_eq]


open GradedMonoid



def X : R[X,Y]4 where
  val := MvPolynomial.X .X
  property := by
    intro m h
    simp only [coeff_X', ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    rw [← h.1, Weight]
    simp only [Finsupp.single_eq_same, mul_one, ne_eq, reduceCtorEq,
      not_false_eq_true, Finsupp.single_eq_of_ne, mul_zero, add_zero]

def Y : R[X,Y]6 where
  val := MvPolynomial.X .Y
  property := by
    intro m h
    simp only [coeff_X', ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    rw [← h.1, Weight]
    simp only [Finsupp.single_eq_same, mul_one, ne_eq, reduceCtorEq,
      not_false_eq_true, Finsupp.single_eq_of_ne, mul_zero, add_zero]



def gnpow [NoZeroDivisors R] (a : R[X,Y]k) (n : ℕ) := GMonoid.gnpow n a

scoped infixl:85 (priority := high) "^*"  => gnpow
scoped notation:85 (priority := 0) a "^" b => gnpow a b


#check (Y ^* 2 * X ^* 3 - (Complex.I) • X ^* 6 : ℂ[X,Y]24)

end IsobaricPoly
end IsobaricPolyDefs


section

variable {k : ℕ}



namespace ModularForm


def without_two : Finset ℕ := {0, 2, 3, 4, 5, 7}

lemma mem_without_two : k ∈ without_two ↔ k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 7 := by
  simp_all only [without_two, Finset.mem_insert, Finset.mem_singleton]

def mod_without_two (k : ℕ) (ℓ : ℕ) :=

  k % ℓ + (if k ≡ 1 [MOD ℓ] then ℓ else 0)

infixl:70 " %% " => mod_without_two

lemma mod_without_two_ge {k : ℕ} (hk : ¬ k ≡ 1 [MOD 6]) : (k ≥ k %% 6) := by
  rw [mod_without_two, if_neg hk, add_zero]; exact Nat.mod_le k 6


lemma mod_without_two_mem (k : ℕ) : k %% 6 ∈ without_two := by
  rw [mod_without_two]; split_ifs with h
  suffices k % 6 + 6 = 7 by rw[this, without_two]; exact Finset.insert_eq_self.mp rfl
  simpa only [Nat.reduceEqDiff]
  rw [add_zero, mem_without_two];
  mod_cases k % 6 <;> aesop


lemma mod_without_two_sub_congr (k : ℕ) : k - k %% 6 ≡ 0 [MOD 6] := by
  by_cases h : k ≡ 1 [MOD 6]
  rw [mod_without_two, if_pos h]; { calc
  _ = (k - k % 6) - 6 := rfl
  _ ≡ 0 [MOD 6] := Nat.modEq_zero_iff_dvd.mpr <| Nat.dvd_sub (Nat.dvd_sub_mod k) (by rfl) }

  rw [mod_without_two, if_neg h, add_zero, Nat.modEq_zero_iff_dvd]
  exact Nat.dvd_sub_mod k

lemma mod_without_two_sub_even (k : ℕ) : Even (k - k %% 6) := by
  have := mod_without_two_sub_congr k
  rw [@even_iff_two_dvd]
  rw [Nat.ModEq] at this
  omega


lemma mod_without_two_congr (k : ℕ) : k ≡ k %% 6 [MOD 6] := by
  rw [mod_without_two]; split_ifs with h
  trans k % 6; exact Nat.ModEq.symm (Nat.mod_modEq k 6)
  exact Nat.ModEq.symm Nat.add_modEq_right
  rw [add_zero]; exact Nat.ModEq.symm (Nat.mod_modEq k 6)



def Gmk_dim_one : (k : ℕ) → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | 2 => (1, 0, 0)
  | 3 => (0, 1, 0)
  | 4 => (2, 0, 0)
  | 5 => (1, 1, 0)
  | 7 => (2, 1, 0)
  | _ => 0



lemma Gmk_dim_one_thrd (k : ℕ) : (Gmk_dim_one k).2.2 = 0 := by
  unfold Gmk_dim_one; split <;> dsimp





lemma Gmk_dim_one_sum (k : ℕ) (hk : k ∈ without_two) :
    4 * (Gmk_dim_one k).1 + 6 * (Gmk_dim_one k).2.1 + 12 * (Gmk_dim_one k).2.2 = 2 * k := by
  rcases mem_without_two.mp hk with h | h | h | h | h | h <;>
  simp only [h, Gmk_dim_one, mul_zero, add_zero]


def Gmk_twelve (k : ℕ) : Set (ℕ × ℕ × ℕ) := {(a,b,c) | b = 0 ∧ 4 * a + 12 * c = 2*k }

lemma Gmk_twelve_fst_ext {a b} (ha : a ∈ Gmk_twelve k) (hb : b ∈ Gmk_twelve k) :
    a.2.2 = b.2.2 ↔ a.1 = b.1 := by
  simp_all [Gmk_twelve]
  obtain ⟨⟨-,ha⟩, ⟨-,hb⟩⟩ := (⟨ha, hb⟩ : And ..)
  constructor
  · intro h; rw [h, ← hb] at ha
    linarith
  · intro h; rw [h, ← hb] at ha
    linarith

lemma Gmk_twelve_snd {a} (ha : a ∈ Gmk_twelve k) : a.2.1 = 0 := by
  simp_all only [Gmk_twelve, Set.mem_setOf_eq]

lemma Gmk_twelve_eq (k : ℕ) : Gmk_twelve k = {(a,b,c) | b = 0 ∧ 2 * a + 6 * c = k } := by
  rw [Gmk_twelve]; ext x; simp only [Set.mem_setOf_eq]; omega

lemma Gmk_twelve_sum {powers : ℕ × ℕ × ℕ} (hp : powers ∈ Gmk_twelve k) :
    4 * powers.1 + 6 * powers.2.1 + 12 * powers.2.2 = 2*k := by
  simp_all only [Gmk_twelve, Set.mem_setOf_eq, mul_zero, add_zero]

lemma Gmk_twelve_sum' {powers : ℕ × ℕ × ℕ} (hp : powers ∈ Gmk_twelve k) :
    2 * powers.1 + 3 * powers.2.1 + 6 * powers.2.2 = k := by
  convert Gmk_twelve_sum hp using 0; omega

open Nat

instance Gmk_twelve_Finite (k : ℕ) : (Gmk_twelve k).Finite := by
  rw [Set.finite_iff_bddAbove]
  use (k, k, k)
  intro x xin
  apply Gmk_twelve_sum' at xin
  simp only [Prod.le_def]; omega

instance : Finite ↑(Gmk_twelve (k - k %% 6)) :=
  Set.finite_coe_iff.mpr <| Gmk_twelve_Finite _



def Gmk_twelve_finset (k : ℕ) := (Gmk_twelve_Finite k).toFinset

theorem Gmk_twelve_card (hk : Even k) : (Gmk_twelve k).ncard = k / 6 + 1 := by
  trans {c : ℕ | 6 * c ≤ k}.ncard
  apply Set.ncard_congr fun (a,b,c) mem => c
  simp only [Gmk_twelve, Set.mem_setOf_eq, and_imp, Prod.forall]; omega
  intro a b ain bin ceq
  ext; rwa [← Gmk_twelve_fst_ext ain bin]
  rw [Gmk_twelve_snd ain, Gmk_twelve_snd bin]
  exact ceq
  intro b bin
  simp only [Set.mem_setOf_eq] at bin
  simp only [exists_prop, Prod.exists, exists_eq_right]
  use (k - 6 * b) / 2, 0
  simp only [Set.mem_setOf_eq, true_and, Gmk_twelve_eq]
  trans k - 6 * b + 6 * b; congr
  have : 2 ∣ k := even_iff_two_dvd.mp hk
  apply Nat.mul_div_cancel'; omega; omega
  trans {c | c ≤ k / 6}.ncard; congr
  ext c; simp only [Set.mem_setOf_eq]; omega
  trans (Set.Icc 0 (k/6)).ncard
  congr; ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc, zero_le, true_and]
  have hs : Set.Finite (Set.Icc 0 (k / 6)) := Finite.of_fintype ↑(Set.Icc 0 (k / 6))
  trans hs.toFinset.card
  rw [Set.ncard_eq_toFinset_card (Set.Icc 0 (k / 6)) hs]
  simp only [Set.toFinite_toFinset, Set.toFinset_Icc,
      card_Icc, tsub_zero, Nat.add_left_cancel_iff]




def Gmk_twelve_mk (k c : ℕ) : (ℕ × ℕ × ℕ) := (k/2 - 3 * c, 0, c)

lemma Gmk_twelve_mk_mem {c} (hk : Even k) (hc : 6 * c ≤ k) :
    Gmk_twelve_mk k c ∈ Gmk_twelve k := by
  simp [Gmk_twelve_mk, Gmk_twelve]
  rw [even_iff] at hk; omega


def Gmk_set (k : ℕ) : Set (ℕ × ℕ × ℕ) :=
  if k = 1 then ∅ else { Gmk_dim_one (k %% 6) + base | base ∈ Gmk_twelve (k - k %% 6) }


def Gmk_set_mk (k c) := Gmk_dim_one (k %% 6) + Gmk_twelve_mk (k - k %% 6) c


def dim (k : ℕ) := k / 6 + if k ≡ 1 [MOD 6] then 0 else 1

@[simp] lemma dim_zero : dim 0 = 1 := by
  simp only [dim, Nat.zero_div, ModEq, zero_mod, one_mod, zero_ne_one, ↓reduceIte, zero_add]

@[simp] lemma dim_one : dim 1 = 0 := by simp only [dim, reduceDiv, zero_add,
  ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not]; rfl

@[simp] lemma dim_two : dim 2 = 1 := by
  simp only [dim, reduceDiv, ModEq, reduceMod, one_mod, OfNat.ofNat_ne_one, ↓reduceIte, zero_add]

@[simp] lemma dim_three : dim 3 = 1 := by
  simp only [dim, reduceDiv, ModEq, reduceMod, one_mod, OfNat.ofNat_ne_one, ↓reduceIte, zero_add]

@[simp] lemma dim_four : dim 4 = 1 := by
  simp only [dim, reduceDiv, ModEq, reduceMod, one_mod, OfNat.ofNat_ne_one, ↓reduceIte, zero_add]

@[simp] lemma dim_five : dim 5 = 1 := by
  simp only [dim, reduceDiv, ModEq, reduceMod, one_mod, OfNat.ofNat_ne_one, ↓reduceIte, zero_add]


@[simp] lemma dim_add_six : dim (k + 6) = dim k + 1 := by
  simp only [dim, ofNat_pos, add_div_right, ModEq, add_mod_right, one_mod]
  ac_rfl


lemma mem_Gmk_set {k} (hk : k ≠ 1) (p) :
    p ∈ Gmk_set k ↔ ∃ b ∈ Gmk_twelve (k - k %% 6), p = Gmk_dim_one (k %% 6) + b := by
  simp [Gmk_set, hk, Eq.comm (b := p)]


lemma Gmk_set_mk_mem (k c) [Fact (k ≠ 1)] (hc : c ≤ dim k - 1) : Gmk_set_mk k c ∈ Gmk_set k := by
  have k1 : k ≠ 1 := Fact.out
  rw [mem_Gmk_set k1, Gmk_set_mk]
  use Gmk_twelve_mk (k - k %% 6) c, Gmk_twelve_mk_mem (mod_without_two_sub_even k) ?_
  simp_all only [dim, mod_without_two]; split_ifs with h
  simp_all only [reduceIte, add_zero]
  omega
  simp_all only [reduceIte, add_tsub_cancel_right, add_zero]
  omega




theorem Gmk_set_card (k : ℕ) : (Gmk_set k).ncard = dim k := by
  by_cases k1 : k = 1
  subst k1; simp only [Gmk_set, ↓reduceIte, Set.ncard_empty, dim_one]
  trans (Gmk_twelve (k - k %% 6)).ncard
  simp only [Gmk_set, if_neg k1, Prod.exists]
  {
    set f := fun (a,b,c) ↦ Gmk_dim_one (k %% 6) + (a, b, c) with hf
    calc
      _ = (f '' (Gmk_twelve (k - k %% 6))).ncard := by
        congr; ext x; simp only [Set.mem_setOf_eq, hf, Prod.mk.eta, Set.mem_image, Prod.exists]

      _ = _ := by
        rw [Set.ncard_image_iff, hf]
        intro x xin y yin
        dsimp
        simp only [Prod.mk.eta, add_right_inj, imp_self]
  }

  rw [Gmk_twelve_card, mod_without_two, dim]
  split_ifs with h; rw [add_zero]

  calc
    _ = (k - k % 6 - 6) / 6 + 1 := by congr 1
    _ = (k - k % 6) / 6 - 6 / 6 + 1 := by
      congr 1
      refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
      trans (k - k % 6 - 6 + 6) / 6
      congr; refine Eq.symm (Nat.sub_add_cancel ?_)
      rw [Nat.ModEq] at h; omega
      exact add_div_right (k - k % 6 - 6) <| by norm_num
    _ = _ := by rw [← div_eq_sub_mod_div, Nat.sub_add_cancel <| by rw[Nat.ModEq] at h; omega]


  rw [add_zero]; congr 1; exact Eq.symm div_eq_sub_mod_div
  have := mod_without_two_sub_congr k
  rw [Nat.modEq_zero_iff_dvd] at this
  rw [even_iff_two_dvd]; omega



@[simp] lemma Gmk_set_one : Gmk_set 1 = ∅ := rfl

lemma mem_Gmk_set' {p : ℕ × ℕ × ℕ} (hp : p ∈ Gmk_set k) :
  ∃ b ∈ Gmk_twelve (k - k %% 6), p = Gmk_dim_one (k %% 6) + b := by
  by_cases k1 : k = 1
  · simp_all only [Gmk_set, reduceIte, Set.mem_empty_iff_false]
  · simp_all only [Gmk_set, Eq.comm, Prod.exists, Set.mem_setOf_eq, reduceIte]


def Gmk (k : ℕ) := {powers : ℕ × ℕ × ℕ // powers ∈ Gmk_set k}


lemma Gmk_def (k : ℕ) : Gmk k = {powers : ℕ × ℕ × ℕ // powers ∈ Gmk_set k} := rfl


def Gmk_mk (k c) [Fact (k ≠ 1)] (hc : c ≤ dim k - 1) : Gmk k :=
  ⟨Gmk_set_mk k c, Gmk_set_mk_mem k c hc⟩


lemma Gmk_mk_thrd {k} [Fact (k ≠ 1)] (c) (hc : c ≤ dim k - 1) : (Gmk_mk k c hc).1.2.2 = c := by
  simp only [Gmk_mk, Gmk_set_mk, Gmk_twelve_mk, Prod.snd_add, Gmk_dim_one_thrd, zero_add]



lemma Gmk_sum {powers : ℕ × ℕ × ℕ} (hp : powers ∈ Gmk_set k) :
    4 * powers.1 + 6 * powers.2.1 + 12 * powers.2.2 = 2*k := by
  obtain ⟨b, bin, rfl⟩ := mem_Gmk_set' hp
  simp only [Prod.fst_add, Prod.snd_add]
  rcases mem_without_two.mp <| mod_without_two_mem k with h | h | h | h | h | h <;>
  simp_all only [Gmk_twelve, tsub_zero, Set.mem_setOf_eq, Gmk_dim_one,
    zero_add, add_zero, mul_zero, mul_one, mul_add] <;>
  have congr := h ▸ mod_without_two_congr k
  {
    rw [add_assoc, bin.2, mul_tsub]; apply Nat.add_sub_of_le
    have := mod_without_two_ge (k := k) (by simp_all [Nat.ModEq])
    omega
  }
  {
    rw [add_comm _ 6, add_assoc, bin.2, mul_tsub]; apply Nat.add_sub_of_le
    have := mod_without_two_ge (k := k) (by simp_all [Nat.ModEq])
    omega
  }
  {
    rw [add_assoc, bin.2, mul_tsub]; apply Nat.add_sub_of_le
    have := mod_without_two_ge (k := k) (by simp_all [Nat.ModEq])
    omega
  }
  {
    rw [add_comm _ 6, add_assoc, add_assoc, bin.2, ← add_assoc, mul_tsub]
    apply Nat.add_sub_of_le
    have := mod_without_two_ge (k := k) (by simp_all [Nat.ModEq])
    omega
  }
  {
    rw [add_comm _ 6, add_assoc, add_assoc, bin.2, ← add_assoc, mul_tsub]
    apply Nat.add_sub_of_le
    by_cases kle : k ≤ 6
    {
      exfalso
      have k1: k = 1 := by
          rw [Nat.modEq_iff_dvd] at congr
          omega
      simp_all
    }
    omega
  }


instance : Fintype (Gmk k) := by
  have := @Gmk_sum k
  set K := {powers : ℕ × ℕ × ℕ // 4 * powers.1 + 6 * powers.2.1 + 12 * powers.2.2 = 2 * k} with Keq
  set Kset := {(a,b,c) | 4 * a + 6 * b + 12 * c = 2 * k} with Ks
  have : Kset.Finite := by
    refine Set.finite_iff_bddAbove.mpr ?_
    use (2 * k, 2 * k, 2 * k)
    intro x xin
    simp only [Set.mem_setOf_eq, Kset] at xin
    constructor
    dsimp; omega
    constructor <;> dsimp <;> linarith

  set Kf : Finset (ℕ × ℕ × ℕ) := @Set.toFinset _ Kset this.fintype with ee

  have : Fintype K := by
    refine Fintype.ofFinset Kf fun x => ?_
    simp only [ee, Set.mem_toFinset, Ks, Set.mem_setOf_eq]
    rfl

  apply Fintype.ofInjective fun ⟨pow, mem⟩ => (⟨pow, Gmk_sum mem⟩ : K)
  rintro ⟨a, mema⟩ ⟨b, memb⟩ h
  simp_all only [Subtype.mk.injEq]



theorem Gmk_card (k : ℕ) : Fintype.card (Gmk k) = dim k := by
  simp_rw [← Gmk_set_card]

  rw [Set.ncard_eq_toFinset_card (hs := by
    refine Set.finite_iff_bddAbove.mpr ?_
    use (k,k,k)
    intro x xin; apply Gmk_sum at xin
    simp only [Prod.le_def]; omega )]
  rw [← Fintype.card_coe]
  apply Fintype.card_congr ⟨ fun ⟨p, pmem⟩ => ⟨p, by rwa [Set.Finite.mem_toFinset]⟩,
    fun ⟨p, pmem⟩ => ⟨p, by rwa [← Set.Finite.mem_toFinset]⟩, ?_, ?_⟩
  rintro ⟨p, pmem⟩; rfl
  rintro ⟨p, pmem⟩; rfl




def Gfun (k) : Gmk k → ModularForm (2*k)
  | ⟨ (a,b,c), mem ⟩ => Gmk_sum mem ▸ (Eis 2 ** a * Eis 3 ** b * Delta ** c)



@[simp] lemma Gfun_apply (n : Gmk k) :
  Gfun k n = Gmk_sum n.2 ▸ (Eis 2 ** n.1.1 * Eis 3 ** n.1.2.1 * Delta ** n.1.2.2) := rfl



open Finsupp in
theorem Gfun_LI : LinearIndependent ℂ (Gfun k) := by
  rw [linearIndependent_iff]
  intro f hf
  ext n; simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [linearCombination_apply] at hf
  simp_all only [Gfun_apply, Nat.reduceMul]
  sorry


theorem Gfun_span : ⊤ ≤ Submodule.span ℂ (Set.range (Gfun k)) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℂ).mpr ?_
  sorry



def GBasis (k : ℕ) : Basis (Gmk k) ℂ (ModularForm (2*k)) :=
  Basis.mk Gfun_LI Gfun_span




theorem finrank_eq (k : ℕ) : Module.finrank ℂ (ModularForm (2 * k)) = dim k := by
  rw [← Gmk_card, Module.finrank_eq_card_basis <| GBasis k]

-- def G (k c) [NeZero (k - 1)] (hc : c ≤ dim k - 1) : ModularForm (2*k) :=
--   GBasis k (Gmk_mk k c hc)

def GFin (k) [Fact (k ≠ 1)] (c : Fin (dim k)) : ModularForm (2*k) :=
  GBasis k (Gmk_mk k c (by omega))


theorem G_LI [Fact (k ≠ 1)] : LinearIndependent ℂ (GFin k) := by
  sorry

theorem G_span [Fact (k ≠ 1)] : ⊤ ≤ Submodule.span ℂ (Set.range (GFin k)) := sorry


/-- `G k` is the upper triangular basis for the space of Modular Forms of weight `2 * k`. -/
def G (k : ℕ) [Fact (k ≠ 1)] : Basis (Fin <| dim k) ℂ (ModularForm (2*k)) :=
  Basis.mk G_LI G_span


end ModularForm

namespace Integer
open ModularForm

def Zfun (k) : Gmk k → IntegerModularForm (2*k)
  | ⟨ (a,b,c), mem ⟩ => Icongr (Gmk_sum mem) (Eis 2 ** a * Eis 3 ** b * Delta ** c)


@[simp] lemma Zfun_apply (n : Gmk k) :
  Zfun k n = Icongr (Gmk_sum n.2) (Eis 2 ** n.1.1 * Eis 3 ** n.1.2.1 * Delta ** n.1.2.2) := rfl


open Finsupp in
theorem Zfun_LI : LinearIndependent ℤ (Zfun k) := by
  rw [linearIndependent_iff]
  intro f hf
  ext n; simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [Finsupp.linearCombination_apply] at hf
  sorry



theorem Zfun_span : ⊤ ≤ Submodule.span ℤ (Set.range (Zfun k)) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℤ).mpr ?_
  sorry


def ZBasis (k : ℕ) : Basis (Gmk k) ℤ (IntegerModularForm (2*k)) :=
  Basis.mk Zfun_LI Zfun_span


theorem finrank_eq (k : ℕ) : Module.finrank ℤ (IntegerModularForm (2 * k)) = dim k := by
  rw [← Gmk_card, Module.finrank_eq_card_basis <| ZBasis k]



def GFin (k) [Fact (k ≠ 1)] (c : Fin (dim k)) : IntegerModularForm (2*k) :=
  ZBasis k (Gmk_mk k c (by omega))

theorem G_LI [Fact (k ≠ 1)] : LinearIndependent ℤ (GFin k) := by
  sorry

theorem G_span [h : Fact (k ≠ 1)] : ⊤ ≤ Submodule.span ℤ (Set.range (GFin k)) := sorry

/-- `G k` is the upper triangular basis for the space of Integer Modular Forms of weight `2 * k`. -/
def G (k : ℕ) [h : Fact (k ≠ 1)] : Basis (Fin (dim k)) ℤ (IntegerModularForm (2*k)) :=
  Basis.mk G_LI G_span


private lemma G_Icongr (c : Fin (dim k)) [Fact (k ≠ 1)] : 2 * 2 * (Gmk_set_mk k c).1 + 2 * 3 * (Gmk_set_mk k c).2.1 + 12 * c = 2 * k := by
  nth_rw 3 [← Gmk_mk_thrd (k := k) c (by omega)]
  simpa [Gmk_mk] using Gmk_sum <| Gmk_set_mk_mem k c (by omega)



theorem G_def (k : ℕ) [h : Fact (k ≠ 1)] (c) : G k c = Icongr (G_Icongr c)
    (Eis 2**(Gmk_set_mk k ↑c).1 * Eis 3**(Gmk_set_mk k ↑c).2.1 * Δ**c) := by
  simp only [G, Basis.coe_mk, GFin, ZBasis, Zfun_apply, Nat.reduceMul]
  congr! <;> exact Gmk_mk_thrd c (by have := c.2; omega)



instance instGNeZero (k c) [Fact (k ≠ 1)] : NeZero (G k c) := by
  simp [G, GFin, ZBasis, Gmk_mk]
  apply instIcongrNeZero (ha := instMulNeZero
      (ha := instMulNeZero
          (ha := instPowNeZero (Eis 2))
          (hb := instPowNeZero (Eis 3)))
      (hb := instPowNeZero Δ))



instance [h : NeZero (k - 1)] : NeZero (2 * k - 1) where
  out := by have := h.out; omega



instance two_unique : Unique (IntegerModularForm 2) where
  default := 0
  uniq := by
    intro a
    -- have := dim_one ▸ finrank_eq 1
    -- rw [Module.finrank_zero_iff] at this
    -- exact Subsingleton.eq_zero a
    -- refine Module.finite_of_rank_eq_zero ?_
    sorry

instance odd_unique (k : ℕ) (hk : Odd k) : Unique (IntegerModularForm k) where
  default := 0
  uniq := by
    intro a
    sorry

@[simp]
theorem default_eq (k : ℕ) : (default : IntegerModularForm k) = 0 := rfl

theorem False_of_two (a : IntegerModularForm 2) [ha : NeZero a] : False :=
  two_unique.uniq a ▸ ha.out <| rfl

theorem False_of_odd (a : IntegerModularForm k) (hk : Odd k) [ha : NeZero a] : False :=
  (odd_unique k hk).uniq a ▸ ha.out <| rfl

theorem Even_weight (a : IntegerModularForm k) [ha : NeZero a] : Even k := by
  rw [← Nat.not_odd_iff_even]
  exact (False_of_odd a ·)

theorem exists_two_mul_weight (a : IntegerModularForm k) [ha : NeZero a] : ∃ j, k = 2 * j :=
  Even.exists_two_nsmul k <| Even_weight a






instance instNeZero_k_div (k : ℕ) [hk : NeZero k] (a : IntegerModularForm k) (h : NeZero a) : NeZero (k/2 - 1) where
  out := by
    by_cases keq : k = 1 ∨ k = 2 ∨ k = 3
    rcases keq with rfl | rfl | rfl
    exact .rec _ <| False_of_odd a odd_one
    exact .rec _ <| False_of_two a
    exact .rec _ <| False_of_odd a <| Nat.odd_iff.mpr rfl

    have := hk.out; omega



theorem ord_G [Fact (k ≠ 1)] (c) : ord (G k c) = c := by
  simp [G, GFin, ZBasis, ord_Icongr', ord_mul', ord_Ipow,
    ord_Ipow (ha := instEisNeZero 2), ord_Ipow (ha := instEisNeZero 3), Gmk_mk_thrd]


theorem G_ord_G [Fact (k ≠ 1)] (c) : G k c c = 1 := by
  rw [G_def, Icongr_apply, ord_mul_ord']
  simp [ord_mul', ord_Ipow, ord_Ipow (Eis 2), ord_Ipow (Eis 3)]
  trans 1 * 1 * 1; congr
  rw [ord_mul_ord' (ha := instPowNeZero (Eis 2)) (hb := instPowNeZero (Eis 3))]
  simp only [ord_Ipow (Eis 2), ord_Eis, mul_zero, ord_Ipow (Eis 3), ord_Ipow_ord']
  rw [Eis_ne_one_zero (by norm_num), Eis_ne_one_zero (by norm_num), one_pow, one_pow]
  simp only [ord_Ipow, ord_Eis, mul_zero, add_zero]
  rw [ord_Ipow_ord', ord_Delta, Delta_one, one_pow]
  rw [ord_Delta, mul_one]
  rfl
  simp only [ord_mul, ord_Ipow, ord_Eis, ord_Delta]; ring



theorem GFin_two_LI [Fact (k ≠ 1)] {c d} (h : c ≠ d) : LinearIndependent ℤ ![G k c, G k d] := by
  apply LI_of_ne_ord; simp only [ord_G]
  contrapose! h; exact Fin.eq_of_val_eq h


theorem dim_ge (k : ℕ) : dim k ≥ k / 6 := by rw [dim]; omega

theorem dim_le (k : ℕ) : dim k ≤ k / 6 + 1 := by
  simp only [dim, Nat.ModEq, Nat.one_mod, add_le_add_iff_left]
  split_ifs <;> omega


instance instdimNeZero (k : ℕ) [hk : Fact (k ≠ 1)] : NeZero (dim k) where
  out := by
    by_cases h : k < 6
    rw [dim]
    split_ifs with kcon
    rw [Nat.ModEq] at kcon
    have := hk.out
    omega
    omega
    have := dim_ge k
    omega


private lemma two_mul_div (a : IntegerModularForm k) [ha : NeZero a] : 2 * (k / 2) = k := by
  have : k % 2 = 0 := by simpa only [Nat.even_iff] using Even_weight a
  omega


theorem GFin_eq (k c) [Fact (k ≠ 1)] : GFin k c = G k c :=
  Eq.symm (Basis.mk_apply G_LI G_span c)


theorem exists_G_combo [Fact (k ≠ 1)] (a : IntegerModularForm (2 * k)) :
    ∃ l : Fin (dim k) → ℤ, ∑ c, l c • (G k) c = a := by
  have : ⊤ ≤ Submodule.span ℤ (Set.range (GFin k)) := G_span
  simp only [Submodule.top_le_span_range_iff_forall_exists_fun, GFin_eq] at this
  exact this a



private theorem sum_smul_rw [Fact (k ≠ 1)] (l : Fin (dim k) → ℤ) (n : ℕ) :
    (∑ c, l c • (G k) c) n = ∑ c, (l c • (G k) c n) := by

  convert Fintype.sum_apply n (fun c => l c • G k c)

  sorry



private theorem sum_with_smul_rw [Fact (k ≠ 1)] (l : Fin (dim k) → ℤ) (n : ℕ) (p : Fin (dim k) → Prop) :
    (∑ c with p c , l c • (G k) c) n = ∑ c with p c, (l c • (G k) c n) := by sorry


theorem exists_G_combo_apply [Fact (k ≠ 1)] (a : IntegerModularForm (2 * k)) (n : ℕ) :
    ∃ l : Fin (dim k) → ℤ, ∑ c ∈ {c : Fin (dim k) | c ≤ n}, l c • (G k) c n = a n := by
  obtain ⟨l, rfl⟩ := exists_G_combo a
  use l; rw [sum_smul_rw]
  exact Finset.sum_filter_of_ne fun m _ => by
    contrapose!; intro nlt
    rw [lt_ord_apply, smul_zero]
    rwa [ord_G]


theorem exists_GBasis_combo (a : IntegerModularForm (2 * k)) :
    ∃ l : Gmk k → ℤ, ∑ c, l c • (Zfun k) c = a := by
  have : ⊤ ≤ Submodule.span ℤ (Set.range (Zfun k)) := Zfun_span
  simp only [Submodule.top_le_span_range_iff_forall_exists_fun] at this
  exact this a

theorem Zfun_zero (c : Gmk 0) : c = ⟨(0, 0, 0), by
    simp [Gmk_set, Gmk_twelve, mod_without_two, Nat.ModEq, Gmk_dim_one]⟩ := by

  obtain ⟨c, hc⟩ := c
  simp [Gmk_set, Gmk_twelve, Gmk_dim_one, mod_without_two, Nat.ModEq] at hc
  simp_rw [hc]



open Finset in
theorem zero_of_leading_zeros (a : IntegerModularForm (2*k))
    (h : ∀ n < dim k, a n = 0) : a = 0 := by

  by_cases k1 : k = 1
  {
    subst k1
    exact two_unique.uniq a
  }

  have : Fact (k ≠ 1) := ⟨by omega⟩

  obtain ⟨l, aeq⟩ := exists_G_combo a
  suffices ∀ n, l n = 0 by
    simp [this] at aeq
    exact aeq.symm

  rintro ⟨n, prop⟩

  induction n using Nat.strong_induction_on with

  | h n ih =>
    rw [DFunLike.ext_iff] at aeq
    specialize aeq n

    rw [sum_smul_rw, h n prop] at aeq
    trans l ⟨n,prop⟩ • G k ⟨n,prop⟩ n
    rw [G_ord_G, smul_eq_mul, mul_one]
    symm; rw [← aeq, ← sub_eq_zero, ← sum_erase_eq_sub <| mem_univ _]
    apply sum_eq_zero
    rintro ⟨m, mlt⟩ mne
    simp only [mem_erase, ne_eq, Fin.mk.injEq, mem_univ, and_true] at mne
    rcases lt_trichotomy m n with mln | meq | mgn
    · rw [ih m mln, zero_smul]
    · exact False.elim <| mne meq
    · rw [lt_ord_apply, smul_zero]
      simpa only [ord_G]


theorem zero_weight (a : IntegerModularForm 0) : a = Iconst (a 0) := by
  simp [← sub_eq_zero, zero_of_leading_zeros (k := 0)]


theorem dvd_of_leading_dvds (ℓ : ℕ) (a : IntegerModularForm (2*k))
    (h : ∀ n < dim k, ↑ℓ ∣ a n) : ∀ n, ↑ℓ ∣ a n := by

  intro n
  by_cases kgt : k = 1 ∨ k = 0
  {
    rcases kgt with hk | hk <;> subst hk
    rw [two_unique.uniq a, default_eq, zero_apply]; exact Int.dvd_zero ↑ℓ
    simp [dim_zero] at h
    rw [zero_weight a]
    match n with
    | 0 => exact h
    | n + 1 => rw [Iconst_succ]; exact Int.dvd_zero _
  }

  have kn0 : Fact (k ≠ 1) := ⟨by omega⟩


  obtain ⟨l, aeq⟩ := exists_G_combo a



  suffices ∀ n, ↑ℓ ∣ l n by
    rw [← aeq, sum_smul_rw]
    have : ∀ c, ↑ℓ ∣ l c • G k c n := by
      intro c; rw [smul_eq_mul]; apply Dvd.dvd.mul_right <| this c
    exact Finset.dvd_sum fun i _ => this i

  rintro ⟨n, nlt⟩

  induction n using Nat.strong_induction_on with

  | h n ih => sorry




theorem eq_of_eq_ord_max (a b : IntegerModularForm (2*k)) [ha : NeZero a] [hb : NeZero b]
    (hao : ord a = dim k - 1) (hbo : ord b = dim k - 1) (heq : a (dim k - 1) = b (dim k - 1)) : a = b := by

  rw [← sub_eq_zero]
  apply zero_of_leading_zeros
  intro n nle
  by_cases h : n < dim k - 1
  rw [sub_apply, lt_ord_apply a (hao ▸ h), lt_ord_apply b (hbo ▸ h), sub_zero]

  have : n = dim k - 1 := by omega
  subst this
  rw [sub_apply, heq, sub_self]



theorem eq_G_of_ord_max [hk : Fact (k ≠ 1)] (a : IntegerModularForm (2 * k)) [ha : NeZero a] (hord : ord a = dim k - 1) :
    a = a (dim k - 1) • (G k ⟨dim k - 1, by have := (instdimNeZero k).out; omega⟩ ) := by
  nth_rw 1 [← hord]
  apply eq_of_eq_ord_max a (hb := instSmulNeZero _ (a (ord a)) (hc := ⟨ord_spec a⟩))
  exact hord
  rw [ord_smul (hc := ⟨ord_spec a⟩), ord_G]
  rw [zsmul_apply, G_ord_G, smul_eq_mul, mul_one, hord]





open Finset.Nat in
theorem antidiagonalTuple_three_one : antidiagonalTuple 3 1 = {![0,0,1], ![0,1,0], ![1,0,0]} := rfl

open Finset.Nat in
theorem antidiagonalTuple_two_one : antidiagonalTuple 2 1 = {![0,1], ![1,0]} := rfl


open Finset.Nat in
theorem Delta_eq_Eis : 1728 • Δ = Eis 2 ** 3 - Eis 3 ** 2 := by

  rw [← sub_eq_zero]
  apply zero_of_leading_zeros (k := 6)
  simp only [dim_add_six, dim_zero, sub_apply, sub_eq_zero, nsmul_apply, Ipow_apply]
  intro n nlt
  have neq : n = 0 ∨ n = 1 := by omega
  rcases neq with rfl | rfl
  simp [antidiagonalTuple_zero_right, Eis_ne_one_zero Nat.add_one_add_one_ne_one]

  simp [antidiagonalTuple_three_one, antidiagonalTuple_two_one]
  rw [Finset.sum_pair <| by decide, Finset.sum_insert <| by decide, Finset.sum_pair <| by decide]
  simp [Fin.prod_univ_three]
  rw [Eis_two_zero, Eis_three_zero, Eis_two_one, Eis_three_one]
  rfl




end Integer

namespace Modulo
open ModularForm Integer

variable {ℓ k : ℕ} [NeZero ℓ]
open Int


theorem Delta_eq_Eis : 1728 • (Δ : ModularFormMod ℓ 12) == (Eis 2 ** 3 -l Eis 3 ** 2) (by norm_num) := by
  intro n; rw [Delta, ← Reduce_nsmul, Integer.Delta_eq_Eis]; simp [Reduce_pow, Eis]



theorem reduce_apply (a : ℕ → ℤ) (n : ℕ) : a n = reduce ℓ a n := rfl


-- we can assume that the function that reduces to a Modular Form Mod ℓ has the maximum ord possible
theorem exists_maximal_Reduce {j p} [Fact (Nat.Prime ℓ)] (a : ModularFormMod ℓ (2 * k))
  [ha : NeZero a] (hk : ∀ n < p, a n = 0) (haw : hasWeight a (2 * j)) :
    ∃ b : IntegerModularForm (2 * j), ∃ h : NeZero b, ∃ hj : (2 * j : ℕ) = (2 * k : ZMod (ℓ - 1)),
      a = Mcongr hj (Reduce ℓ b) ∧ ord b ≥ p := by

  obtain ⟨c, ceq⟩ := haw
  obtain ⟨hj, aeqcr⟩ := Reduce_of_reduce ceq
  have : NeZero c := ⟨by
    have := ha.out; contrapose! this; ext n; apply DFunLike.ext_iff.mp at ceq
    specialize ceq n; trans a.sequence n; rfl
    trans reduce ℓ 0 n; rwa [this] at ceq; rw [← reduce_apply]
    rw [Pi.zero_apply, cast_zero, zero_apply] ⟩


  have : Fact (j ≠ 1) := ⟨by rintro rfl; exact False_of_two c⟩

  obtain ⟨l, leq⟩ := exists_G_combo c

  have aeqc : ∀ n, a n = ↑(c n) := by
    intro n
    trans a.1 n; rfl
    simp only [coe_apply]
    rw [ceq]; rfl


  set b := ∑ c, (if ↑ℓ ∣ l c then 0 else l c) • Integer.G j c with beq

  have habve : a = Mcongr hj (Reduce ℓ b) := by
    ext n; rw [Mcongr_apply, Reduce_apply, aeqc n]
    simp [beq, ← leq, Integer.add_apply, sum_smul_rw, zsmul_apply, smul_eq_mul, ite_mul, Finset.sum_ite]
    trans ↑(∑ c with ¬↑ℓ ∣ l c, (l c • (Integer.G j) c) n)
    simp only [zsmul_apply, smul_eq_mul, cast_sum, cast_mul]
    refine Eq.symm (Finset.sum_filter_of_ne ?_)

    rintro x - h ; contrapose! h
    obtain ⟨d, le⟩ := h
    simp only [le, cast_mul, cast_natCast, CharP.cast_eq_zero, zero_mul]

    congr; symm; convert @sum_with_smul_rw j this l n (¬ ↑ℓ ∣ l ·)


  have bn0 : NeZero b := by
    obtain ⟨n, hn0⟩ := (NeZero.Mcoe a).exists
    refine Integer.Exists_ne_zero ⟨n, ?_⟩
    contrapose! hn0; simp only [habve, _root_.cast_eval, Reduce_apply, hn0, cast_zero]

  use b, bn0, hj, habve

  rw [ge_iff_le, le_ord_iff, beq]; intro n nlt

  rw [sum_smul_rw]
  apply Fintype.sum_eq_zero
  rintro ⟨x,xlt⟩
  simp only [smul_eq_mul, ite_mul, zero_mul, ite_eq_left_iff, mul_eq_zero]
  intro nldiv
  by_cases xlek : x < p

  {
    left

    induction x using Nat.strong_induction_on with

    | h x ih =>
      suffices l ⟨x,xlt⟩ = a x by
        rw [hk x xlek, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
        exact (nldiv this).rec

      rw [aeqc, ← leq, sum_smul_rw]; push_cast
      trans (l ⟨x, xlt⟩ : ZMod ℓ) • ↑((Integer.G j) ⟨x,xlt⟩ ↑(⟨x,xlt⟩ : Fin (dim j)))
      rw [G_ord_G, cast_one, smul_eq_mul, mul_one]
      simp; symm; apply Fintype.sum_eq_single
      rintro ⟨m, mlt⟩ mnx
      simp only [ne_eq, Fin.mk.injEq] at mnx
      rw [mul_eq_zero]
      rcases Nat.lt_or_lt_of_ne mnx with mlx | mgx
      left
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      by_contra dvdm
      specialize ih m mlx mlt dvdm (by omega)
      exact ih ▸ dvdm <| Int.dvd_zero ↑ℓ

      right; rw [lt_ord_apply]
      exact Lean.Grind.Ring.intCast_zero
      rwa [ord_G]
  }
  {
    right
    apply lt_ord_apply
    simp only [ord_G]; omega
  }


end Modulo
