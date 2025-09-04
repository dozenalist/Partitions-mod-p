import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs

/- This file defines some basic operators on Modular Forms Mod ℓ, such as the
Theta and U operators, as well as some simple functions for dealing with cast equality
It also defines some notation that aligns with the paper -/

open ModularFormDefs Integer Modulo2

noncomputable section

variable {ℓ n : ℕ} {k j : ZMod (ℓ-1)} [NeZero ℓ]
variable {a b c : ModularFormMod ℓ k}

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

-- needs some type class thing that declares α ≠ β definitionally
def Mod_eq (a : α) (b : β) :=
  ∀ n, a n = b n
-- two modular forms of different weight can be "equal" if they are the same sequence
-- might be a bad idea, idk

infixl:50 (priority := high) "==" => Mod_eq


@[simp]
lemma cast_equal {k j : ZMod (ℓ - 1) } {h : k = j} {a : ModularFormMod ℓ k} :
  Mcongr h a == a := λ _ ↦ cast_eval


instance : IsRefl α Mod_eq where
  refl := λ _ _ ↦ rfl

instance : IsSymm α Mod_eq where
  symm := λ _ _ h _ ↦ Eq.symm (h _)

instance : Trans (. == . : α → β → Prop) (. == . : β → χ → Prop) (. == . : α → χ → Prop) where
  trans := λ h g _ ↦ Eq.trans (h _) (g _)

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


-- A modular form mod ℓ, denoted a, has weight k if there exists a modular form b
-- of weight k such that a is the reduction of b (mod ℓ)
-- A modular form mod ℓ can have many weights
def hasWeight (a : ModularFormMod ℓ k) (j : ℕ) : Prop :=
  ∃ b : IntegerModularForm j, a = reduce ℓ b


-- If a is the zero function, its filtration does not exist
-- If not, then it is the least natural number k such that a has weight k
def Filtration (a : ModularFormMod ℓ k) : Option ℕ :=
  if a = 0 then none else
  @Nat.find (fun k ↦ hasWeight a k) (inferInstance)
    (by obtain ⟨k,b,h⟩ := a.modular; use k; use b; exact h.2)


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


-- no idea why its (n : ℕ) and not ℕ
def Theta_pow : (n : ℕ) → ModularFormMod ℓ k → ModularFormMod ℓ (k + n * 2)
| 0     => fun f ↦ Mcongr (by simp) f
| n + 1 => fun f ↦ Mcongr (by simp; group) (Theta (Theta_pow n f))

macro_rules
  | `(Θ^[$n]) => `(Theta_pow $n)


@[simp]
lemma Theta_pow_zero {a : ModularFormMod ℓ k} : Θ^[0] a = Mcongr (by simp) a := rfl

@[simp]
lemma Theta_pow_succ {n : ℕ} {a : ModularFormMod ℓ k} :
  Θ^[n + 1] a = Mcongr (by simp; group) (Θ (Θ^[n] a)) := rfl

@[simp]
lemma Theta_pow_one {a : ModularFormMod ℓ k} :
  Θ^[1] a = Mcongr (by simp) (Θ a) := by ext n; simp

@[simp]
lemma Theta_Pow_apply {n j : ℕ} {a : ModularFormMod ℓ k} : Θ^[j] a n = n ^ j * a n := by
  induction j with
  | zero => simp
  | succ j ih => simp[ih]; ring


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


def Option_mul (n : Option ℕ): Option ℕ → Option ℕ
  | none => none
  | some m =>
    match n with
    | none => none
    | some n => some (n * m)

instance : HMul (Option ℕ) (Option ℕ) (Option ℕ) where
  hMul := Option_mul

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


infixl:30 "mod" => Reduce

syntax:30 term " (mod " term ")" : term

macro_rules
  | `($a (mod $l)) => `(Reduce $a $l)

notation "𝔀" => Filtration

infixl:80 (priority := high) "**" => pow

-- namespace ModPow
-- scoped infixl:80 "^" => pow
-- end ModPow




def self_mul (a : ModularFormMod ℓ k) : (j : ℕ) → ModularFormMod ℓ (k * j)
  | 0 => Mcongr (by sorry) (const 1)
  | j + 1 => Mcongr (by simp; group) (a * self_mul a j)

open Finset Finset.Nat

lemma adT_succ_left {k n} : antidiagonalTuple (k+1) n =
    List.toFinset (
      (List.Nat.antidiagonal n).flatMap fun ni =>
        ((antidiagonalTuple k ni.2).toList.map fun x => (Fin.cons ni.1 x : Fin (k + 1) → ℕ))) := by
  ext; simp [antidiagonalTuple, Multiset.Nat.antidiagonalTuple, List.Nat.antidiagonalTuple]

-- lemma adT_succ_right {k n} : antidiagonalTuple k (n + 1) =
--  List.toFinset (
--       (List.Nat.antidiagonal (n + 1)).flatMap fun ni =>
--         ((antidiagonalTuple (k) ni.2).toList.map fun x =>
--           (Fin.snoc (α := fun _ => ℕ) k ni.1 : Fin k → ℕ))) := by
--   ext; simp [antidiagonalTuple, Multiset.Nat.antidiagonalTuple, List.Nat.antidiagonalTuple]


lemma Pow_eq_self_mul {a : ModularFormMod ℓ k} {j} : self_mul a j = pow a j := by
  induction j with
  | zero =>
    unfold self_mul;
    ext n; simp[pow_apply]
    cases n <;> simp
  | succ j ih =>
    unfold self_mul;
    ext n; simp[ih, pow_apply]
    induction n with
    | zero => simp[antidiagonalTuple_zero_right]; ring
    | succ n igntul =>
      simp[antidiagonal_succ', antidiagonalTuple_zero_right]
      sorry





end section
