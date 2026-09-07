import PartitionsLeanblueprint.RamanujanCongruence.FluNeZero


/-
This file proves UOp_pow_l
This file is sorry-free
Surprisingly, we don't need to use Filtration_pow in the proof
-/


open ModularFormMod

variable {ℓ : ℕ} [isLargePrime ℓ] {k j : ZMod (ℓ - 1)}

@[simp] theorem UOp_pow_l (f : ModularFormMod ℓ k) :
    f.UOp.pow ℓ = f.Mcast (by simp) - (f.Theta_pow (ℓ - 1)).Mcast (by simp) :=
  ext fun _ => by
  simp [ZMod.pow_card_sub_one, coeff_pow_Prime, ZMod.natCast_eq_zero_iff, sub_ite]
  congr! with h
  exact Nat.mul_div_cancel' h



-- theorem const_of_Filt_zero {a : ModularFormMod ℓ k} (h : a.Filtration = 0) :
--     ∃ c : ZMod ℓ, ∀ n, a.coeff n = (const c).coeff n := by
--   obtain ⟨f, hf⟩ := (h ▸ Filtration_spec a).exists
--   sorry




-- theorem Filtration_pow (f : ModularFormMod ℓ k) (m) : (f.pow m).Filtration = m * f.Filtration := sorry





-- theorem Reduce_of_reduce {a : ModularFormMod ℓ k} {b : IntegerModularForm n} (hab : ∀ n, a n = b n) :
--     ∃ h, a = Mcast h (Reduce ℓ b) := sorry



-- theorem exists_of_filt_eq (a : ModularFormMod ℓ k) (ha : 𝔀 a = n) :
--     ∃ b : IntegerModularForm n, ∃ h, a = Mcast h (Reduce ℓ b) := by
--   obtain ⟨b, aeq⟩ := Weight_of_Filt ha
--   obtain ⟨h, aeq⟩ := Reduce_of_reduce aeq
--   exact ⟨b, h, aeq⟩
