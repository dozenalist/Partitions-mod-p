import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs

/- This file defines some basic operators on Modular Forms Mod ℓ, such as the
Theta and U operators, the Filtration function, and some simple functions for dealing with cast equality
It also defines notation that aligns with the paper -/

open ModularFormDefs Integer Modulo2

noncomputable section

variable {ℓ n : ℕ} {k j : ZMod (ℓ-1)} [NeZero ℓ]
variable {a b c : ModularFormMod ℓ k}
variable {d : ModularFormMod ℓ j}

-- h ▸ a works like subst h at a but works within types
def Mcongr {m n : ZMod (ℓ - 1)} (h : m = n) (a : ModularFormMod ℓ m) : ModularFormMod ℓ n :=
  h ▸ a

@[simp]
lemma cast_eval {k j : ZMod (ℓ -1)} {h : k = j} {n : ℕ} {a : ModularFormMod ℓ k} :
  Mcongr h a n = a n := by
  subst h; rfl


@[simp]
lemma triangle_eval {k j : ZMod (ℓ -1)} {h : k = j} {n : ℕ} {a : ModularFormMod ℓ k} :
  (h ▸ a) n = a n := by
  subst h; rfl


universe u
variable {α β χ  : Type u} [FunLike α ℕ (ZMod n)] [FunLike β ℕ (ZMod n)] [FunLike χ ℕ (ZMod n)]

-- two modular forms of different weight can be "equal" if they are the same sequence
-- this is an equivalence relation, so we can put it into calc blocks and such
def Mod_eq (a : α) (b : β) :=
  ∀ n, a n = b n


-- make sure it doesn't clash with boolean ==
infixl:50 (priority := high) "==" => Mod_eq



@[simp]
lemma cast_equal {k j : ZMod (ℓ - 1) } {h : k = j} {a : ModularFormMod ℓ k} :
  Mcongr h a == a := λ _ ↦ cast_eval


instance : IsRefl α Mod_eq where
  refl := λ _ _ ↦ rfl

@[refl]
theorem Mod_eq.refl {a : α} : a == a := λ _ ↦ rfl

instance : IsSymm α (. == .) where
  symm := λ _ _ h _ ↦ Eq.symm (h _)

@[symm]
theorem Mod_eq.symm {a: α} {b : β} (h : a == b) : b == a :=  λ n ↦ Eq.symm (h n)

instance : Trans (. == . : α → β → Prop) (. == . : β → χ → Prop) (. == . : α → χ → Prop) where
  trans := λ h g _ ↦ Eq.trans (h _) (g _)

@[trans]
theorem Mod_eq.trans {a : α} {b : β} {c : χ} (h : a == b) (g : b == c) : a == c :=
  λ _ ↦ Eq.trans (h _) (g _)

-- instance : Trans (. == . : α → β → Prop) (. = . : β → β → Prop) (. == . : α → β → Prop) where
--   trans := λ h g ↦ g ▸ h

-- instance : Trans (. = . : α → α → Prop) (. == . : α → β → Prop) (. == . : α → β → Prop) where
--   trans := λ h g ↦ h ▸ g


instance : IsAntisymm α Mod_eq where
  antisymm := λ _ _ h _ ↦ DFunLike.ext _ _ h

instance : IsEquiv α Mod_eq where
  refl := IsRefl.refl
  symm := IsSymm.symm
  trans := λ _ _ _ h g _ ↦ Eq.trans (h _) (g _)

instance : IsPartialOrder α Mod_eq where
  refl := IsRefl.refl
  trans := λ _ _ _ h g _ ↦ Eq.trans (h _) (g _)
  antisymm := IsAntisymm.antisymm


lemma Mod_eq_of_Eq {a b : α} (h : a = b) : a == b :=
  λ _ ↦ h ▸ rfl

lemma Eq_of_Mod_eq {a b : α} (h : a == b) : a = b :=
  DFunLike.ext _ _ h


def Theta (a : ModularFormMod ℓ k) : ModularFormMod ℓ (k + 2) where
  sequence := fun n ↦ n * a n
  modular := sorry

def U_Operator (a : ModularFormMod ℓ k) : ModularFormMod ℓ k where
  sequence := fun n ↦ a (ℓ * n)
  modular := sorry


notation "Θ" => Theta

postfix:90 "|𝓤" => U_Operator

@[simp]
lemma U_apply : (a|𝓤) n = a (ℓ * n) := rfl

@[simp]
lemma Theta_apply : Θ a n = n * a n := rfl



def Theta_pow : (n : ℕ) → ModularFormMod ℓ k → ModularFormMod ℓ (k + n * 2)
  | 0, f     => Mcongr (by simp) f
  | n + 1, f => Mcongr (by simp; group) (Theta (Theta_pow n f))


macro_rules
  | `(Θ^[$n]) => `(Theta_pow $n)

notation "Θ^["n"]" => Theta_pow n


@[simp]
lemma Theta_pow_zero' {a : ModularFormMod ℓ k} : Θ^[0] a = Mcongr (by simp) a := rfl

lemma Theta_pow_zero {a : ModularFormMod ℓ k} : Θ^[0] a == a := by
  rw[Theta_pow_zero']; exact cast_equal

@[simp]
lemma Theta_pow_succ' {n : ℕ} {a : ModularFormMod ℓ k} :
  Θ^[n + 1] a = Mcongr (by simp; group) (Θ (Θ^[n] a)) := rfl

lemma Theta_pow_succ {n : ℕ} {a : ModularFormMod ℓ k} :
    Θ^[n + 1] a == Θ (Θ^[n] a) := by
  rw[Theta_pow_succ']; exact cast_equal

lemma Theta_pow_pred {n : ℕ} [NeZero n] {a : ModularFormMod ℓ k} :
    Θ^[n] a == Θ (Θ^[n - 1] a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Ne.symm (NeZero.ne' n))
  rw[Nat.succ_eq_add_one]; simp only [Nat.add_one_sub_one, Theta_pow_succ', cast_equal]

lemma Theta_pow_cast {n j : ℕ} {a : ModularFormMod ℓ k} (h : n = j) :
    Θ^[n] a == Θ^[j] a := by
  subst h; rfl

@[simp]
lemma Theta_pow_one {a : ModularFormMod ℓ k} :
  Θ^[1] a = Mcongr (by simp) (Θ a) := by ext n; simp



@[simp]
lemma Theta_Pow_apply {n j : ℕ} {a : ModularFormMod ℓ k} : Θ^[j] a n = n ^ j * a n := by
  induction j with
  | zero => simp
  | succ j ih => simp[ih]; ring

lemma Theta_pow_l_eq_Theta {a : ModularFormMod ℓ k} [Fact (Nat.Prime ℓ)] : Θ^[ℓ] a == Θ a := by
  intro n; rw[Theta_Pow_apply, ZMod.pow_card, Theta_apply]



def add_congr_right (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) :
    ModularFormMod ℓ j :=
  (h ▸ a) + b

def add_congr_left (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) :
    ModularFormMod ℓ k :=
  a + (h ▸ b)

def sub_congr_right (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) :
    ModularFormMod ℓ j :=
  (h ▸ a) - b

def sub_congr_left (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) :
    ModularFormMod ℓ k :=
  a - (h ▸ b)

-- Use these two add or subtract modular forms of different but provably equal weights
-- with an r, the weight of the result is the weight of the right argument. with an l, the left
-- example: (a : ModularFormMod ℓ k) +r (b : ModularFormMod ℓ j) (h : k = j) : ModularFormMod ℓ j
infixl:65 " +r " => add_congr_right
infixl:65 " +l " => add_congr_left
infixl:65 " -r " => sub_congr_right
infixl:65 " -l " => sub_congr_left


@[simp]
lemma add_congr_right_apply {k j : ZMod (ℓ - 1)} (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) (n : ℕ) :
    (add_congr_right a b h) n = a n + b n := by
  rw[add_congr_right, add_apply, triangle_eval]

@[simp]
lemma add_congr_left_apply {k j : ZMod (ℓ - 1)} (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) (n : ℕ) :
    (add_congr_left a b h) n = a n + b n := by
  rw[add_congr_left, add_apply, triangle_eval]

@[simp]
lemma sub_congr_right_apply {k j : ZMod (ℓ - 1)} (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) (n : ℕ) :
    (sub_congr_right a b h) n = a n - b n := by
  rw[sub_congr_right, sub_apply, triangle_eval]

@[simp]
lemma sub_congr_left_apply {k j : ZMod (ℓ - 1)} (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) (h : k = j) (n : ℕ) :
    (sub_congr_left a b h) n = a n - b n := by
  rw[sub_congr_left, sub_apply, triangle_eval]


infixl:30 "mod" => Reduce

syntax:30 term " (mod " term ")" : term

macro_rules
  | `($a (mod $l)) => `(Reduce $a $l)


infixl:80 (priority := high) "**" => pow


-- namespace ModPow
-- scoped infixl:80 "^" => pow
-- end ModPow

@[simp]
theorem const_pow (c : ZMod ℓ) [Fact (Nat.Prime ℓ)] (j : ℕ) : (const c) ** j == const (c ^ j) := by
  intro n; simp only [pow_apply]
  match n with
  | 0 => simp[Finset.Nat.antidiagonalTuple_zero_right]
  | n + 1 =>
    have zepo : ∀ x ∈ Finset.Nat.antidiagonalTuple j (n + 1), ∏ y, (const c) (x y) = 0 := by
      intro x hx
      suffices h' : ∃ y, x y ≠ 0 by
        obtain ⟨y,h'⟩ := h'
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero h'
        have : (const c) (x y) = 0 := by
          rw[hk]; simp only [Nat.succ_eq_add_one, const_succ]
        apply Finset.prod_eq_zero_iff.2; use y; exact ⟨Finset.mem_univ y,this⟩
      by_contra! zed
      have sumo : ∑ y, x y = 0 := by
        trans ∑ y : Fin n, 0; simp_rw [zed, Finset.sum_const_zero]; exact Finset.sum_const_zero
      linarith [Finset.Nat.mem_antidiagonalTuple.1 hx]
    exact Finset.sum_eq_zero zepo



-- A modular form mod ℓ, denoted a, has weight k if there exists a modular form b
-- of weight k such that a is the reduction of b (mod ℓ)
-- A modular form mod ℓ can have many weights
def hasWeight (a : ModularFormMod ℓ k) (j : ℕ) : Prop :=
  ∃ b : IntegerModularForm j, a = reduce ℓ b

-- The filtration of a is the least natural number k such that a has weight k
def Filtration (a : ModularFormMod ℓ k) : ℕ :=
  Nat.find (let ⟨k,b,h⟩ := a.modular; ⟨k, b, h.2⟩ : ∃ k, hasWeight a k)



notation "𝔀" => Filtration

lemma Weight_eq_of_Mod_eq (h : a == d) {j} : hasWeight a j → hasWeight d j := by
  unfold hasWeight; rintro ⟨c,hc⟩
  use c; ext n; rw[← h n]; exact congrFun hc n

lemma Filt_eq_of_Mod_eq (h : a == d) : 𝔀 a = 𝔀 d := by
  unfold Filtration; congr; ext j
  exact ⟨Weight_eq_of_Mod_eq h, Weight_eq_of_Mod_eq h.symm⟩

@[simp]
lemma Filt_cast {h : k = j} {a : ModularFormMod ℓ k} : 𝔀 (Mcongr h a) = 𝔀 a :=
  Filt_eq_of_Mod_eq cast_equal


lemma Weight_of_Filt (h : 𝔀 a = n) : hasWeight a n := by
  unfold Filtration at h; rw[Nat.find_eq_iff] at h
  exact h.1


lemma Filt_decomp {j : ℕ} {a : ModularFormMod ℓ k} (wj : hasWeight a j)
    (jmin : ∀ k, k < j → ¬ hasWeight a k) : 𝔀 a = j := by
  unfold Filtration
  apply le_antisymm
  rw[Nat.find_le_iff]
  exact ⟨j, le_refl j, wj⟩
  rw[Nat.le_find_iff]
  exact jmin

lemma Filt_decomp' {j : ℕ} {a : ModularFormMod ℓ k} (wj : hasWeight a j)
    (jmin : ∀ k, hasWeight a k → k ≥ j) : 𝔀 a = j := by
  apply Filt_decomp wj; contrapose! jmin
  exact Set.inter_nonempty_iff_exists_right.mp jmin

lemma Filt_decomp_iff {j : ℕ} {a : ModularFormMod ℓ k} (wj : hasWeight a j) :
    𝔀 a = j ↔ ∀ k, k < j → ¬ hasWeight a k := by
  refine ⟨?_, Filt_decomp wj⟩
  intro filta
  rw[Filtration] at filta
  apply ge_of_eq at filta
  rw [Nat.le_find_iff] at filta
  exact filta

lemma Filt_decomp_iff' {j : ℕ} {a : ModularFormMod ℓ k} (wj : hasWeight a j) :
    𝔀 a = j ↔ ∀ k, hasWeight a k → k ≥ j := by
  refine ⟨?_, Filt_decomp' wj⟩
  intro filta k h
  contrapose! h
  exact (Filt_decomp_iff wj).1 filta k h


@[simp]
lemma Filt_const {c : ZMod ℓ} : 𝔀 (const c) = 0 := by
  unfold Filtration
  suffices h: hasWeight (const c) 0 from
    (Nat.find_eq_zero (Filtration._proof_1 (const c))).mpr h
  obtain ⟨n,b,n0,hb⟩ := (const c).modular
  use Iconst ↑c.val; ext n; rw [ZMod.natCast_val, reduce]
  match n with
  | 0 => rw [Modulo2.const_zero, Integer.Iconst_zero, ZMod.intCast_cast, ZMod.cast_id', id_eq]
  | n + 1 => rw [Modulo2.const_succ, Integer.Iconst_succ, Int.cast_zero]


@[simp]
lemma Filt_zero [NeZero (ℓ - 1)] : 𝔀 (0 : ModularFormMod ℓ k) = 0 := by
  trans 𝔀 (const 0 : ModularFormMod ℓ 0)
  apply Filt_eq_of_Mod_eq
  intro n; cases n
  rw [zero_apply, const_zero]
  rw [zero_apply, const_succ]
  exact Filt_const


namespace Filtration
-- This section is no longer in use.
-- It defines Filtration in terms of Option ℕ, where 𝔀 0 = none

variable {ℓ k : ℕ} [NeZero ℓ]

-- If a is the zero function, its filtration does not exist
-- If not, then it is the least natural number k such that a has weight k
def Option_Filtration [NeZero (ℓ - 1)] (a : ModularFormMod ℓ k) : Option ℕ :=
  if a = 0 then none else
  @Nat.find (fun k ↦ hasWeight a k) (inferInstance)
    (by obtain ⟨k,b,h⟩ := a.modular; use k; use b; exact h.2)

def Filtration_NeZero (a : ModularFormMod ℓ k) [NeZero (ℓ - 1)] [NeZero a] : ℕ :=
  @Nat.find (fun k ↦ hasWeight a k) (inferInstance)
    (by obtain ⟨k,b,h⟩ := a.modular; use k; use b; exact h.2)

-- notation "𝔀" => Option_Filtration

def Option_mul (n : Option ℕ): Option ℕ → Option ℕ
  | none => none
  | some m =>
    match n with
    | none => none
    | some n => some (n * m)

instance : HMul (Option ℕ) (Option ℕ) (Option ℕ) where
  hMul := Option_mul


instance (n : ℕ) : OfNat (Option ℕ) n where
  ofNat := some n

instance : Coe ℕ (Option ℕ) where
  coe := some

instance {a : ModularFormMod ℓ k} [NeZero (ℓ - 1)] [NeZero a] : CoeDep (Option ℕ) (Option_Filtration a) ℕ where
  coe := Filtration_NeZero a

def Option_div (n : Option ℕ): Option ℕ → Option ℕ
  | none => none
  | some m =>
    match n with
    | none => none
    | some n => some (n / m)

instance : HDiv (Option ℕ) (Option ℕ) (Option ℕ) where
  hDiv := Option_div

def Option_add (n : Option ℕ): Option ℕ → Option ℕ
  | none =>
    match n with
    | none => none
    | some n => some n
  | some m =>
    match n with
    | none => some m
    | some n => some (n + m)

def Option_sub (n : Option ℕ): Option ℕ → Option ℕ
  | none =>
    match n with
    | none => none
    | some n => some n
  | some m =>
    match n with
    | none => some 0
    | some n => some (n - m)

instance : HAdd (Option ℕ) (Option ℕ) (Option ℕ) where
  hAdd := Option_add

instance : HSub (Option ℕ) (Option ℕ) (Option ℕ) where
  hSub := Option_sub

def Option_pow (n : Option ℕ) : Option ℕ → Option ℕ
  | none => none
  | some m =>
    match n with
    | none => none
    | some n => some (n ^ m)

instance : HPow (Option ℕ) (Option ℕ) (Option ℕ) where
  hPow := Option_pow

def Option_pow_nat (n : Option ℕ) (m : ℕ) : Option ℕ :=
  match n with
  | none => none
  | some n => some (n ^ m)

instance : HPow (Option ℕ) ℕ (Option ℕ) where
  hPow := Option_pow_nat



end Filtration


end section
