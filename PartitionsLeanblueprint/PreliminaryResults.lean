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
infixl:80 "⋆" => pow


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


#check Θ (a ⋆ 3 * b)|𝓤
-- Theta operator binds tighter
#check a ⋆ 3 * b

@[simp]
lemma Pow_Prime {n : ℕ} {a : ModularFormMod ℓ k} :
  (a ⋆ ℓ) n = if ℓ ∣ n then (a (n / ℓ)) ^ ℓ else 0 := by
  by_cases h : ℓ ∣ n
  simp[h]
  rw [pow_apply]
  unfold self.mul
  unfold HMul.hMul
  unfold instHMul; simp; unfold Mul.mul mul; simp; unfold Nat.iterate;
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  induction ℓ with
| zero =>
  contradiction
| succ ℓ =>
  simp only [Function.iterate_succ, Function.iterate_zero, Nat.succ_eq_add_one]

  sorry


-- This is by Freshman's Dream, but the definition of Pow makes it hard to work with
-- bad way of writing it


lemma flt {p : ℕ} {n : ZMod p} [Fact (Nat.Prime p)] : n ^ p = n := ZMod.pow_card n


@[simp]
lemma U_apply : (a|𝓤) n = a (ℓ * n) := rfl

@[simp]
lemma Theta_apply : Θ a n = n * a n := rfl

-- no idea why its (n : ℕ) and not ℕ
def Theta_pow : (n : ℕ) → ModularFormMod ℓ k → ModularFormMod ℓ (k + n * (ℓ + 1))
| 0     => fun f => cast (by group) f
| n + 1 => fun f => cast (by simp[mul_add, add_mul]; group) (Theta (Theta_pow n f))


notation "Θ ^^ n" => Theta_pow n
-- idk how to do this

#check Theta_pow 3 (a ⋆ 2 * b)



#check Θ ^^ 3 (a ⋆ 4 * b)


def δ (ℓ : ℕ) : ℤ := (ℓ^2 - 1) / 24
-- or δℓ : ℤ := (ℓ^2 - 1) / 24


@[simp]
lemma Theta_Pow {n j : ℕ} {a : ModularFormMod ℓ k} : Θ^[j] a n = n ^ j * a n := by
  induction' j with j ih; simp
  rw[iterate_succ', pow_add]; simp; rw[ih]; ring



theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one {a : ModularFormMod ℓ k} :
(a|𝓤) ⋆ ℓ = a - Θ^[ℓ - 1] a := by
  ext n; simp
  rw[ZMod.pow_card_sub_one]; simp; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have h' : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp[h,h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp[h,h']


def Filtration_mul (i : ℕ): Option ℕ → Option ℕ
  | none => none
  | some n => i * n

instance : HMul ℕ (Option ℕ) (Option ℕ) where
  hMul := Filtration_mul


theorem Filtration_Log {i : ℕ} : 𝔀 (a ⋆ i) = i * 𝔀 a := sorry
