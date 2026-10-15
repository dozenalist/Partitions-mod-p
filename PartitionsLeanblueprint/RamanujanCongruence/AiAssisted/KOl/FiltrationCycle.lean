import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.FiltrationDrops

/-!
Telescoping identities for the finite theta cycle.  The classification in
Proposition 2 is an arithmetic consequence of this identity together with
the fact that a drop can occur exactly at a divisible filtration.
-/

namespace KOl

open scoped IntegerModularForm

noncomputable section

variable {ell : ℕ} [isLargePrime ell]
variable {k : ZMod (ell - 1)} (f : ModularFormMod ell k)

lemma theta_filtration_telescoping (s : ℕ → ℕ)
    (hs : ∀ i ∈ thetaFiltrationDrops f,
      (f.Theta_pow (i + 1)).Filtration =
        (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
          (s i : ℤ) * ((ell : ℤ) - 1))
    {n : ℕ} (hn : n ≤ ell - 1) :
      (f.Theta_pow (n + 1)).Filtration =
      (f.Theta_pow 1).Filtration + (n : ℤ) * ((ell : ℤ) + 1) -
        ∑ i ∈ Finset.Icc 1 n,
          (if i ∈ thetaFiltrationDrops f then (s i : ℤ) else 0) *
            ((ell : ℤ) - 1) := by
  have hstep : ∀ i ∈ Finset.Icc 1 (ell - 1),
      (f.Theta_pow (i + 1)).Filtration =
        (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
          (if i ∈ thetaFiltrationDrops f then (s i : ℤ) else 0) *
            ((ell : ℤ) - 1) := by
    intro i hi
    by_cases hdrop : i ∈ thetaFiltrationDrops f
    · rw [if_pos hdrop]
      exact hs i hdrop
    · rw [if_neg hdrop]
      have h := theta_filtration_no_drop_step f hi hdrop
      simpa using h
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : n + 1 ≤ ell - 1 := hn
      have hi : n + 1 ∈ Finset.Icc 1 (ell - 1) := by
        simp only [Finset.mem_Icc]
        omega
      have hsn := hstep (n + 1) hi
      rw [hsn, ih (by omega)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      by_cases hdrop : n + 1 ∈ thetaFiltrationDrops f
      · simp only [hdrop, if_pos]
        push_cast
        ring
      · simp only [hdrop, if_neg]
        push_cast
        ring

lemma theta_filtration_drop_sum (s : ℕ → ℕ)
    (hs : ∀ i ∈ thetaFiltrationDrops f,
      (f.Theta_pow (i + 1)).Filtration =
        (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
          (s i : ℤ) * ((ell : ℤ) - 1)) :
    ∑ i ∈ thetaFiltrationDrops f, (s i : ℤ) = (ell : ℤ) + 1 := by
  have htel := theta_filtration_telescoping f s hs (n := ell - 1) le_rfl
  have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
  rw [show ell - 1 + 1 = ell by omega] at htel
  have htel' := htel
  rw [theta_filtration_period f] at htel'
  have hsum :
      (∑ i ∈ Finset.Icc 1 (ell - 1),
        (if i ∈ thetaFiltrationDrops f then (s i : ℤ) else 0)) =
        ∑ i ∈ thetaFiltrationDrops f, (s i : ℤ) := by
    calc
      _ = ∑ i ∈ (Finset.Icc 1 (ell - 1)).filter
          (fun i => i ∈ thetaFiltrationDrops f), (s i : ℤ) := by
            rw [Finset.sum_filter]
      _ = ∑ i ∈ thetaFiltrationDrops f, (s i : ℤ) := by
        congr 1
        ext i
        simp [thetaFiltrationDrops]
  have hpos : (0 : ℤ) < (ell : ℤ) - 1 := by
    omega
  have hfactor :
      (∑ i ∈ Finset.Icc 1 (ell - 1),
        (if i ∈ thetaFiltrationDrops f then (s i : ℤ) else 0) *
          ((ell : ℤ) - 1)) =
        (∑ i ∈ Finset.Icc 1 (ell - 1),
          (if i ∈ thetaFiltrationDrops f then (s i : ℤ) else 0)) *
          ((ell : ℤ) - 1) := by
    rw [Finset.sum_mul]
  rw [hfactor, hsum] at htel'
  have hcast : ((ell - 1 : ℕ) : ℤ) = (ell : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ell)]
    norm_num
  rw [hcast] at htel'
  have hzero :
      ((ell : ℤ) - 1) * ((ell : ℤ) + 1) -
          (∑ i ∈ thetaFiltrationDrops f, (s i : ℤ)) * ((ell : ℤ) - 1) = 0 := by
    linarith only [htel']
  have hmul :
      ((ell : ℤ) - 1) * ((ell : ℤ) + 1) =
        (∑ i ∈ thetaFiltrationDrops f, (s i : ℤ)) * ((ell : ℤ) - 1) := by
    linarith only [hzero]
  have hcancel : (ell : ℤ) - 1 ≠ 0 := ne_of_gt hpos
  have heq : (ell : ℤ) + 1 =
      ∑ i ∈ thetaFiltrationDrops f, (s i : ℤ) := by
    apply mul_right_cancel₀ hcancel
    simpa [mul_comm] using hmul
  exact heq.symm

lemma theta_filtration_drops_nonempty (s : ℕ → ℕ)
    (hs : ∀ i ∈ thetaFiltrationDrops f,
      (f.Theta_pow (i + 1)).Filtration =
        (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
          (s i : ℤ) * ((ell : ℤ) - 1)) :
    (thetaFiltrationDrops f).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hsum := theta_filtration_drop_sum f s hs
  rw [hempty] at hsum
  simp at hsum
  have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
  omega

end
end KOl
