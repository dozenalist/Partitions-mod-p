import PartitionsLeanBlueprint.PreliminaryResults


noncomputable section

open Modulo2

variable {ℓ n : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

def δ (ℓ : ℕ) : ℕ := (ℓ^2 - 1) / 24
-- δℓ ?


-- Δ : Euler's Pentagonal Theorem - generalized pentagonal numbers
def Delta : ModularFormMod ℓ 12 where

  sequence n :=
    match n with
      | 0 => 0
      | n + 1 =>
        if h : (∃ m : ℤ, n = m * (3*m - 1) / 2)
          then
            let m := Classical.choose h
            (-1) ^ m
          else 0 -- I think this is true, but it's obviously terrible

  modular := sorry

notation "Δ" => Delta

def f (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)] : ModularFormMod ℓ (12 * δ ℓ) := Δ ** δ ℓ
-- or fℓ : ModularFormMod ℓ (((ℓ^2 - 1)/2) : ℕ) := Mcongr (Δ ** δ ℓ) (by sorry)

/- wierd to have "some" here. Could probably create pow, sub, div instances
 for everything but maybe there's a way around it -/
lemma Filt_fl : 𝔀 (f ℓ) = some ((ℓ^2 - 1)/2) := sorry



--Lemma 2.1
theorem Filt_Theta_bound (a : ModularFormMod ℓ k) [NeZero a] : 𝔀 (Θ a) ≤ 𝔀 a + some (ℓ + 1) := sorry

theorem Filt_Theta_iff (a : ModularFormMod ℓ k) [NeZero a] :
  𝔀 (Θ a) = 𝔀 a + some (ℓ + 1) ↔ ℓ ∣ (𝔀 a).getD 0 := sorry



-- Lemma 3.2
theorem le_Filt_Theta_fl : ∀ m, 𝔀 (f ℓ) ≤ 𝔀 (Θ^[m] (f ℓ)) := sorry


--Lemma 3.3


-- lemma none_le : ∀ m : ℕ, @none ℕ ≤ m := by intro m; trivial
