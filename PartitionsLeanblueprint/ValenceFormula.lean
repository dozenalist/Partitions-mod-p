import PartitionsLeanblueprint.Basis


/- The goal of this file is to state the valence formula in a way that is useful,
and to prove some facts about the dimension of the space of modular forms. -/

noncomputable section

open Integer DirectSum


instance {k i : ℕ} : AddCommMonoid {p : IntegerModularForm k // p == Eis i} := sorry

theorem hh {k : ℕ} : IntegerModularForm k = ⨁ i, {p : IntegerModularForm k // p == Eis i} := by
  sorry

theorem hb {k : ℕ} (f : IntegerModularForm k) : ∃ c : ℤ, ∃ a b : ℕ, f == c • (Eis 2 ** a * Eis 3 ** b) := sorry



inductive Vars
  | X
  | Y


instance : Fintype Vars where
  elems := {.X, .Y}
  complete
    | .X => Finset.mem_insert_self ..
    | .Y => Finset.mem_insert_of_mem <| Finset.mem_singleton.mpr rfl


open AddMonoidAlgebra


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


def IsobaricPoly (R : Type) [CommSemiring R] (k : ℕ) :=
  {p : R[X,Y] // ∀ (m : Vars →₀ ℕ), p.coeff m ≠ 0 → Weight m = k}


namespace IsobaricPoly
open MvPolynomial

scoped notation:9000 R "[X,Y]" k => IsobaricPoly R k

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

instance instGCommMonoid [NoZeroDivisors R]: GCommMonoid (IsobaricPoly R) where
  mul := IsobaricPoly.mul
  one_mul := one_mul
  mul_one := mul_one
  mul_assoc := mul_assoc
  mul_comm := mul_comm




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


open DirectSum



scoped infixl:85 (priority := high) "^*"  => Function.swap GMonoid.gnpow

#check (Y ^* 2 * X ^* 3 - 5 • X ^* 6 : ℤ[X,Y]24) -- this is a mess


#check 3 ^ 2
