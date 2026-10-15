import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.PartitionProduct
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.PartitionBridge

/-!
Uniqueness of the Ramanujan progression, using the convention of
Kiming--Olsson: `p(0) = 1` and `p(n) = 0` for negative integers.
Both the shift and the progression index range over integers. The namespace
keeps this convention distinct from the project's historical natural-number
definition, which assigns zero at zero.
-/

namespace KOl

/-- Every integer shift giving a partition congruence has the Ramanujan residue. -/
theorem shiftedCongruence_unique {ell : ℕ} [isLargePrime ell] {beta : ℤ}
    (hbeta : shiftedCongruence ell beta) : beta ≡ delta ell [ZMOD ell] := by
  have hp := (inferInstance : isLargePrime ell).Prime
  have hell := (inferInstance : isLargePrime ell).AtLeastFive
  obtain ⟨a, _, ha, hcong, hbetaClass⟩ :=
    shiftedCongruence_normalize (by omega : 2 ≤ ell) hbeta
  have hko := kiming_olsson_theorem_one hp hell ha hcong
  have hdeltaClass : (a : ℤ) + (delta ell : ℤ) ≡ 0 [ZMOD ell] := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr
      (normalized_residue_eq_delta hp hell ha hko))
  apply Int.ModEq.add_right_cancel' (a : ℤ)
  exact hbetaClass.trans (by simpa [add_comm] using hdeltaClass.symm)

/-- An integer-shift partition congruence exists exactly when the Ramanujan one holds. -/
theorem ramanujanCongruence_unique (ell : ℕ) [isLargePrime ell] :
    (∃ beta : ℤ, shiftedCongruence ell beta) ↔ ramanujanCongruence ell := by
  constructor
  · rintro ⟨beta, hbeta⟩
    exact shiftedCongruence_of_modEq hbeta (shiftedCongruence_unique hbeta)
  · intro h
    exact ⟨delta ell, h⟩

/-- Restrict the integer progression to the project's natural-number convention. -/
lemma ramanujan_congruence_of_shiftedCongruence (ℓ : ℕ) :
    shiftedCongruence ℓ (delta ℓ) → ramanujan_congruence ℓ := by
  intro h n
  change ℓ ∣ partition (ℓ * n - delta ℓ)
  by_cases hn : delta ℓ < ℓ * n
  · have harg : (ℓ : ℤ) * (n : ℤ) - (delta ℓ : ℤ) =
        ((ℓ * n - delta ℓ : ℕ) : ℤ) := by
      rw [Nat.cast_sub hn.le, Nat.cast_mul]
    have hpart := h (n : ℤ)
    rw [harg, standardPartition_ofNat, natpart_of_ne_zero (by omega)] at hpart
    exact hpart
  · simp [Nat.sub_eq_zero_of_le (by omega : ℓ * n ≤ delta ℓ), partition_zero]

end KOl
