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
variable {a b : ModularFormMod ℓ k}

-- use ▸
-- look at Data.Vector
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
variable {α β : Type u} [FunLike α ℕ (ZMod ℓ)] [FunLike β ℕ (ZMod ℓ)]

-- needs some type class thing that declares α ≠ β definitionally
def Mod_eq (a : α) (b : β) :=
  ∀ n, a n = b n
-- two modular forms of different weight can be "equal" if they are the same sequence
-- might be a bad idea, idk

infixl:30 (priority := 1001) "==" => Mod_eq


@[simp]
lemma cast_equal {k j : ZMod (ℓ -1) } {h : k = j} {a : ModularFormMod ℓ k} :
  Mcongr h a == a := λ _ ↦ cast_eval



-- A modular form mod ℓ, denoted a, has weight k if there exists a modular form b
-- of weight k such that a is the reduction of b (mod ℓ)
-- A modular form mod ℓ can have many weights
def hasWeight (a : ModularFormMod ℓ k) (j : ℕ) : Prop :=
  ∃ b : IntegerModularForm j, a = reduce ℓ b


-- If a is the zero function, its filtration does not exist
-- If not, then it is the least natural number k such that a has weight k
def Filtration (a : ModularFormMod ℓ k) [NeZero (ℓ - 1)] : Option ℕ :=
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

postfix:50 "|𝓤" => U_Operator

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
lemma Theta_pow_one {a : ModularFormMod ℓ k} [NeZero (ℓ - 1)] :
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

def Option_add (n : Option ℕ): Option ℕ → Option ℕ
  | none =>
    match n with
    | none => none
    | some n => some n
  | some m =>
    match n with
    | none => some m
    | some n => some (n + m)

instance : HAdd (Option ℕ) (Option ℕ) (Option ℕ) where
  hAdd := Option_add


infixl:30 "mod" => Reduce

syntax:30 term " (mod " term ")" : term

macro_rules
  | `($a (mod $l)) => `(Reduce $a $l)

notation "𝔀" => Filtration

infixl:80 "**" => pow

-- variable {k : ℕ} {a b : IntegerModularForm k} [NeZero (ℓ - 1)]

-- #check 𝔀 (a * b (mod ℓ))

end section
