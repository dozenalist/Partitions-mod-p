import PartitionsLeanblueprint.RamanujanCongruence.PrimaryLemmas

/-!
The filtration bookkeeping used in the Kiming--Olsson argument.

This file isolates the local facts about theta iterates from the finite
arithmetic classification in Proposition 2.  In particular, no partition
generating function is used here.
-/

namespace KOl

open scoped IntegerModularForm

noncomputable section

variable {ell : ℕ} [isLargePrime ell]
variable {k : ZMod (ell - 1)} (f : ModularFormMod ell k)

lemma filtration_nonneg_of_ne_zero (g : ModularFormMod ell k) (hg : g ≠ 0) :
    0 ≤ g.Filtration := by
  letI : NeZero g := ⟨hg⟩
  apply le_csInf (ModularFormMod.nonempty_hasWeight_set g)
  intro j hj
  obtain ⟨b, hb⟩ := hj.exists_reduce
  by_contra! hjneg
  have hb0 : b ≠ 0 := by
    intro hbzero
    apply hg
    apply ModularFormMod.fourier_inj
    rw [hbzero, map_zero] at hb
    simpa using hb
  exact hb0 (by
    apply IntegerModularForm.carrier_inj
    ext z
    rw [ModularFormClass.levelOne_neg_weight_eq_zero hjneg]
    rfl)

/-- Indices in `1,...,ell-1` at which the filtration is divisible by `ell`. -/
noncomputable def thetaFiltrationDrops {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) : Finset ℕ :=
  (Finset.Icc 1 (ell - 1)).filter fun i =>
    (ell : ℤ) ∣ (f.Theta_pow i).Filtration

lemma theta_pow_ne_zero_le (hTheta : f.Theta ≠ 0) {i : ℕ}
    (hi : i ≤ ell) : f.Theta_pow i ≠ 0 := by
  have hone : f.Theta_pow 1 ≠ 0 := by
    letI : NeZero f.Theta := ⟨hTheta⟩
    simpa only [ModularFormMod.Theta_pow_one] using
      (inferInstance : NeZero ((f.Theta).Mcast (by simp))).out
  intro hz
  have hforward : ∀ t : ℕ, f.Theta_pow (i + t) = 0 := by
    intro t
    induction t with
    | zero => simpa using hz
    | succ t iht =>
        rw [show i + (t + 1) = (i + t) + 1 by omega,
          ModularFormMod.Theta_pow_succ, iht]
        simp
  have hzell : f.Theta_pow ell = 0 := by
    have hz := hforward (ell - i)
    rw [Nat.add_sub_of_le hi] at hz
    exact hz
  letI : NeZero (f.Theta_pow 1) := ⟨hone⟩
  have hneell : f.Theta_pow ell ≠ 0 := by
    intro hz
    apply hone
    apply ModularFormMod.ext
    intro n
    rw [ModularFormMod.Theta_pow_l] at hz
    have hcoeff := congrArg (fun g : ModularFormMod ell _ => g.coeff n) hz
    simpa [ModularFormMod.Theta_pow_one] using hcoeff
  exact hneell hzell

lemma theta_filtration_nonneg_le (hTheta : f.Theta ≠ 0) {i : ℕ}
    (hi : i ≤ ell) : 0 ≤ (f.Theta_pow i).Filtration := by
  exact filtration_nonneg_of_ne_zero _
    (theta_pow_ne_zero_le f hTheta hi)

lemma theta_filtration_drop_step {i : ℕ}
    (hi : i ∈ thetaFiltrationDrops f) (hTheta : f.Theta ≠ 0) :
    ∃ s : ℕ, 0 < s ∧
      (f.Theta_pow (i + 1)).Filtration =
        (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
          (s : ℤ) * ((ell : ℤ) - 1) := by
  have hdiv : (ell : ℤ) ∣ (f.Theta_pow i).Filtration :=
    (Finset.mem_filter.mp hi).2
  have hi_le : i + 1 ≤ ell := by
    have hiupper := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).2
    have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
    omega
  letI : NeZero (f.Theta_pow (i + 1)) :=
    ⟨theta_pow_ne_zero_le f hTheta hi_le⟩
  obtain ⟨s : ℤ, hs, hstep⟩ := Filt_Theta_congruence_of_dvd' f hdiv rfl
  refine ⟨s.toNat, ?_, ?_⟩
  · have hs' : (0 : ℤ) < (s.toNat : ℤ) := by
      simpa [Int.toNat_of_nonneg hs.le] using hs
    exact_mod_cast hs'
  · convert hstep using 1 <;> simp [Int.toNat_of_nonneg hs.le] <;> ring

noncomputable def thetaDropAmount (hTheta : f.Theta ≠ 0) : ℕ → ℕ :=
  fun i => if hi : i ∈ thetaFiltrationDrops f then
    (theta_filtration_drop_step f hi hTheta).choose else 0

lemma thetaDropAmount_pos (hTheta : f.Theta ≠ 0) {i : ℕ}
    (hi : i ∈ thetaFiltrationDrops f) : 0 < thetaDropAmount f hTheta i := by
  simp only [thetaDropAmount, dif_pos hi]
  exact (theta_filtration_drop_step f hi hTheta).choose_spec.1

lemma thetaDropAmount_step (hTheta : f.Theta ≠ 0) {i : ℕ}
    (hi : i ∈ thetaFiltrationDrops f) :
    (f.Theta_pow (i + 1)).Filtration =
      (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
        (thetaDropAmount f hTheta i : ℤ) * ((ell : ℤ) - 1) := by
  simp only [thetaDropAmount, dif_pos hi]
  exact (theta_filtration_drop_step f hi hTheta).choose_spec.2

lemma theta_filtration_no_drop_step {i : ℕ}
    (hi : i ∈ Finset.Icc 1 (ell - 1))
    (hiDrop : i ∉ thetaFiltrationDrops f) :
    (f.Theta_pow (i + 1)).Filtration =
      (f.Theta_pow i).Filtration + (ell : ℤ) + 1 := by
  have hndiv : ¬ (ell : ℤ) ∣ (f.Theta_pow i).Filtration := by
    intro hdiv
    exact hiDrop (Finset.mem_filter.mpr ⟨hi, hdiv⟩)
  convert (Filt_Theta_iff' f rfl).2 hndiv using 1 <;> ring

lemma theta_filtration_period :
    (f.Theta_pow ell).Filtration = (f.Theta_pow 1).Filtration := by
  rw [ModularFormMod.Theta_pow_l, ModularFormMod.Theta_pow_one]
  rfl

end
end KOl
