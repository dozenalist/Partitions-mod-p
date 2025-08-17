import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs


open ModularFormDefs Integer Modulo2

infixl:30 "mod" => Reduce

syntax:30 term " (mod " term ")" : term

macro_rules
  | `($a (mod $l)) => `(Reduce $a $l)

local notation "𝔀" => Filtration

--infixl:80 "^^^" => pow
infixl:80 "**" => pow


variable {n ℓ k j : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)] [NeZero (ℓ - 1)]
variable {a b : IntegerModularForm k}

#check a (mod ℓ+1)
#check 𝔀 (a * b (mod ℓ))


-- def Theta (a : ModularFormMod ℓ k) : ModularFormMod ℓ k where
--   sequence := fun n ↦ n * a n
--   modular := sorry

-- def U_Operator (a : ModularFormMod ℓ k) : ModularFormMod ℓ k where
--   sequence := fun n ↦ a (ℓ * n)
--   modular := sorry

variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

local notation "Θ" => Theta

postfix:50 "|𝓤" => U_Operator


#check Θ (a ** 3 * b)|𝓤
-- Theta operator binds tighter
#check a ** 3 * b

@[simp]
lemma Pow_Prime {n : ℕ} {a : ModularFormMod ℓ k} :
  (a ** ℓ) n = if ℓ ∣ n then (a (n / ℓ)) ^ ℓ else 0 := by
  by_cases h : ℓ ∣ n
  simp[h]
  sorry
  sorry


-- This is by Freshman's Dream, but the definition of Pow makes it hard to work with
-- bad way of writing it


lemma flt {p : ℕ} {n : ZMod p} [Fact (Nat.Prime p)] : n ^ p = n := ZMod.pow_card n


@[simp]
lemma U_apply : (a|𝓤) n = a (ℓ * n) := rfl

@[simp]
lemma Theta_apply : Θ a n = n * a n := rfl

lemma help' {k : ZMod (ℓ - 1)} {n : ℕ} : k = (k + 0 * n) := by simp

-- no idea why its (n : ℕ) and not ℕ
def Theta_pow : (n : ℕ) → ModularFormMod ℓ k → ModularFormMod ℓ (k + n * 2)
| 0     => fun f ↦ Mcongr (by simp) f
| n + 1 => fun f ↦ Mcongr (by simpa using by group) (Theta (Theta_pow n f))


macro_rules
  | `(Θ^[$n]) => `(Theta_pow $n)


#check Theta_pow 3 (a ** 2 * b)
#check Θ^[3] (a ** 2 * b)|𝓤
#check Θ (a ** 2 * b)


lemma help (k : ZMod ℓ): (k + ↑0 * 2) = k := by simp

@[simp]
lemma Theta_pow_zero {a : ModularFormMod ℓ k} : Θ^[0] a = Mcongr (by simp) a := rfl

@[simp]
lemma Theta_pow_succ {n : ℕ} {a : ModularFormMod ℓ k} :
  Θ^[n + 1] a = Mcongr (by simp; group) (Θ (Θ^[n] a)) := rfl

def δ (ℓ : ℕ) : ℤ := (ℓ^2 - 1) / 24
-- or δℓ : ℤ := (ℓ^2 - 1) / 24


@[simp]
lemma cast_eval {k j : ZMod (ℓ -1) } {h : k = j} {n : ℕ} {a : ModularFormMod ℓ k} :
  Mcongr h a n = a n := by
  subst h; rfl


def eq {k j : ZMod (ℓ - 1)} (a : ModularFormMod ℓ k) (b : ModularFormMod ℓ j) :=
  ∀ n, a n = b n
-- two modular forms of different weight can be "equal" if they are the same sequence
-- might be a bad idea, idk

infixl:50 "=" => eq

@[simp]
lemma cast_equal {k j : ZMod (ℓ -1) } {h : k = j} {a : ModularFormMod ℓ k} :
  Mcongr h a = a := λ _ ↦ cast_eval



@[simp]
lemma Theta_Pow_apply {n j : ℕ} {a : ModularFormMod ℓ k} : Θ^[j] a n = n ^ j * a n := by
  induction j with
  | zero => simp
  | succ j ih => simp[ih]; ring





def thing (a : ModularFormMod ℓ k) :=  a - (Mcongr (by simp only [CharP.cast_eq_zero, zero_mul, add_zero]) (Θ^[ℓ - 1] a))

lemma k_l : k * ℓ = k := by
  calc
    k * ℓ = k * (ℓ - 1 + 1) := by simp
    _ = k * (ℓ - 1) + k := by ring
    _ = k * 0 + k := by
      simp only [mul_zero, zero_add, add_eq_right]; refine mul_eq_zero_of_right k ?_;
      have : ((ℓ - 1) : ZMod (ℓ - 1)) = 0 := by sorry
      simp only [this]
    _ = k := by simp only [mul_zero, zero_add]


lemma U_pow_l_eq_self_sub_Theta_pow_l_minus_one' {a : ModularFormMod ℓ k} :
  ((a|𝓤) ** ℓ) = (thing a) := by
  intro n; simp[U_apply, Theta_apply, thing]
  rw [ZMod.pow_card_sub_one]; simp; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have h' : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp[h,h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp[h,h']



-- theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one {a : ModularFormMod ℓ k} :
-- (mcast (k_l) ((a|𝓤) ** ℓ)) = thing a := by
--   ext n; simp[thing,mcast]
--   rw[ZMod.pow_card_sub_one]; simp; symm; calc
--     _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
--       by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
--     _ = _ := by
--       by_cases h : (n : ZMod ℓ) = 0
--       have h' : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
--       simp[h,h']; congr
--       rw [Nat.mul_div_cancel_left' h']
--       have h': ¬ ℓ ∣ n := by contrapose! h; exact (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
--       simp[h,h']


def Filtration_mul (i : ℕ): Option ℕ → Option ℕ
  | none => none
  | some n => i * n

instance : HMul ℕ (Option ℕ) (Option ℕ) where
  hMul := Filtration_mul


#check (mcast (by sorry) a) - (Θ^[ℓ - 1] a)

theorem Filtration_Log {i : ℕ} : 𝔀 (a ** i) = i * 𝔀 a := sorry

variable {a : Fin (3 ^ 2 - 3)} {b : Fin (6)}
#check b + a
