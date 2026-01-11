import PartitionsLeanblueprint.Ord
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Set.Card



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
  unfold Gmk_dim_one; sorry





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


lemma mem_Gmk_set {k} (hk : k ≠ 1) (p) :
    p ∈ Gmk_set k ↔ ∃ b ∈ Gmk_twelve (k - k %% 6), p = Gmk_dim_one (k %% 6) + b := by
  simp [Gmk_set, hk, Eq.comm (b := p)]


lemma Gmk_set_mk_mem (k c) [NeZero (k - 1)] (hc : c ≤ dim k - 1) : Gmk_set_mk k c ∈ Gmk_set k := by
  have k1 : k ≠ 1 := by
    have : k - 1 ≠ 0 := by exact Ne.symm (NeZero.ne' (k - 1))
    omega
  rw [mem_Gmk_set k1, Gmk_set_mk]
  use Gmk_twelve_mk (k - k %% 6) c, Gmk_twelve_mk_mem (mod_without_two_sub_even k) ?_
  simp_all only [dim, mod_without_two]; split_ifs with h
  simp_all only [reduceIte, add_zero]
  omega
  simp_all only [reduceIte, add_tsub_cancel_right, add_zero]
  omega




theorem Gmk_set_card (k : ℕ) : (Gmk_set k).ncard = dim k := by
  by_cases k1 : k = 1
  subst k1; simp [Gmk_set]; rfl
  trans (Gmk_twelve (k - k %% 6)).ncard
  rw [Gmk_set, if_neg k1]
  simp
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


def Gmk_mk (k c) [NeZero (k - 1)] (hc : c ≤ dim k - 1) : Gmk k :=
  ⟨Gmk_set_mk k c, Gmk_set_mk_mem k c hc⟩


lemma Gmk_mk_thrd {k} [NeZero (k - 1)] (c) (hc : c ≤ dim k - 1) : (Gmk_mk k c hc).1.2.2 = c := by
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
  simp_rw [← Gmk_set_card, Gmk]

  sorry





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



-- def G (k c) [NeZero (k - 1)] (hc : c ≤ dim k - 1) : ModularForm (2*k) :=
--   GBasis k (Gmk_mk k c hc)

def GFin (k) [NeZero (k - 1)] (c : Fin (dim k)) : ModularForm (2*k) :=
  GBasis k (Gmk_mk k c (by omega))

theorem finrank_eq (k : ℕ) : Module.finrank ℂ (ModularForm (2 * k)) = dim k := by
  rw [← Gmk_card, Module.finrank_eq_card_basis <| GBasis k]


theorem G_LI [NeZero (k - 1)] : LinearIndependent ℂ (GFin k) := by
  sorry

theorem G_span [NeZero (k - 1)] : ⊤ ≤ Submodule.span ℂ (Set.range (GFin k)) := sorry

def G (k : ℕ) [NeZero (k - 1)] : Basis (Fin <| dim k) ℂ (ModularForm (2*k)) :=
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



def GFin (k) [h : NeZero (k - 1)] (c : Fin (dim k)) : IntegerModularForm (2*k) :=
  ZBasis k (Gmk_mk k c (by omega))

theorem G_LI [h : NeZero (k - 1)] : LinearIndependent ℤ (GFin k) := by
  sorry

theorem G_span [h : NeZero (k - 1)] : ⊤ ≤ Submodule.span ℤ (Set.range (GFin k)) := sorry

def G (k : ℕ) [h : NeZero (k - 1)] : Basis (Fin (dim k)) ℤ (IntegerModularForm (2*k)) :=
  Basis.mk G_LI G_span


instance instGNeZero (k c) [NeZero (k - 1)] : NeZero (G k c) := by
  simp [G, GFin, ZBasis, Gmk_mk]
  apply instIcongrNeZero (ha := instMulNeZero
      (ha := instMulNeZero
          (ha := instPowNeZero (Eis 2))
          (hb := instPowNeZero (Eis 3)))
      (hb := instPowNeZero Δ))


variable {c : Fin (dim k)} [NeZero (k-1)]


instance [h : NeZero (k - 1)] : NeZero (2 * k - 1) where
  out := by have := h.out; omega


theorem ord_G (c) : ord (G k c) = c := by
  simp [G, GFin, ZBasis, ord_Icongr', ord_mul', ord_Ipow,
    ord_Ipow (ha := instEisNeZero 2), ord_Ipow (ha := instEisNeZero 3), Gmk_mk_thrd]

theorem GFin_two_LI {c d} (h : c ≠ d) : LinearIndependent ℤ ![G k c, G k d] := by
  apply LI_of_ne_ord; simp only [ord_G]
  contrapose! h; exact Fin.eq_of_val_eq h



end Integer

end section

section ord

namespace Integer

variable {k : ℕ} {f g : IntegerModularForm k} [NeZero f] [NeZero g]
