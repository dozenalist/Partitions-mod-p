import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.FiltrationCycle
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basis

/-!
The finite arithmetic part of Kiming--Olsson Proposition 2.

The only modular-form input used here is the filtration recurrence already
proved in `FiltrationCycle`: a drop can occur precisely at a divisible
filtration, and the positive drop coefficients have total `ell + 1`.
-/

namespace KOl

open scoped IntegerModularForm

noncomputable section

variable {ell : ℕ} [isLargePrime ell]
variable {k : ZMod (ell - 1)} (f : ModularFormMod ell k)

lemma filtration_ge_four_of_ne_zero {g : ModularFormMod ell k}
    (hg : g ≠ 0) (hfil : g.Filtration ≠ 0) : 4 ≤ g.Filtration := by
  have hnonneg := filtration_nonneg_of_ne_zero g hg
  by_contra hlt
  have hsmall : g.Filtration = 0 ∨ g.Filtration = 1 ∨
      g.Filtration = 2 ∨ g.Filtration = 3 := by omega
  rcases hsmall with hzero | hone | htwo | hthree
  · exact hfil hzero
  · have hweight := g.Filtration_spec
    have hweight' : g.hasWeight 1 := by simpa [hone] using hweight
    obtain ⟨b, hb⟩ := hweight'.exists_reduce
    have hbzero : b = 0 := by
      apply IntegerModularForm.carrier_inj
      ext z
      have hodd : Odd (1 : ℤ) := by norm_num
      have hbcar := ModularForm.levelOne_odd_weight_eq_zero hodd b.carrier
      rw [hbcar]
      rfl
    apply hg
    apply ModularFormMod.fourier_inj
    rw [hbzero, map_zero] at hb
    simpa using hb
  · have hweight := g.Filtration_spec
    have hweight' : g.hasWeight 2 := by simpa [htwo] using hweight
    obtain ⟨b, hb⟩ := hweight'.exists_reduce
    have hbzero : b = 0 := by
      apply IntegerModularForm.carrier_inj
      ext z
      have hbcar :=
        (rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero) b.carrier
      rw [hbcar]
      rfl
    apply hg
    apply ModularFormMod.fourier_inj
    rw [hbzero, map_zero] at hb
    simpa using hb
  · have hweight := g.Filtration_spec
    have hweight' : g.hasWeight 3 := by simpa [hthree] using hweight
    obtain ⟨b, hb⟩ := hweight'.exists_reduce
    have hbzero : b = 0 := by
      apply IntegerModularForm.carrier_inj
      ext z
      have hodd : Odd (3 : ℤ) := by norm_num
      have hbcar := ModularForm.levelOne_odd_weight_eq_zero hodd b.carrier
      rw [hbcar]
      rfl
    apply hg
    apply ModularFormMod.fourier_inj
    rw [hbzero, map_zero] at hb
    simpa using hb

private lemma filtration_between_drop (hTheta : f.Theta ≠ 0)
    {i j : ℕ} (hi : i ∈ thetaFiltrationDrops f)
    (hij : i < j) (hj : j ≤ ell - 1)
    (hno : ∀ t, i < t → t < j → t ∉ thetaFiltrationDrops f) :
    (f.Theta_pow j).Filtration =
      (f.Theta_pow i).Filtration + (j - i : ℤ) * ((ell : ℤ) + 1) -
        (thetaDropAmount f hTheta i : ℤ) * ((ell : ℤ) - 1) := by
  revert hij hj hno
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hij hj hno
      by_cases hbase : j = i + 1
      · subst j
        have hcast0 : ((i + 1 : ℕ) : ℤ) - i = 1 := by omega
        rw [hcast0]
        convert thetaDropAmount_step f hTheta hi using 1 <;> ring
      · have hprev_lt : i < j - 1 := by omega
        have hprev_bound : j - 1 ≤ ell - 1 := by omega
        have hprev_no : ∀ t, i < t → t < j - 1 →
            t ∉ thetaFiltrationDrops f := by
          intro t hit htj
          exact hno t hit (by omega)
        have hprev := ih (j - 1) (by omega) hprev_lt hprev_bound hprev_no
        have hno_prev : j - 1 ∉ thetaFiltrationDrops f := by
          exact hno (j - 1) hprev_lt (by omega)
        have hIcc : j - 1 ∈ Finset.Icc 1 (ell - 1) := by
          simp only [Finset.mem_Icc]
          omega
        have hstep := theta_filtration_no_drop_step f hIcc hno_prev
        have hstep' : (f.Theta_pow j).Filtration =
            (f.Theta_pow (j - 1)).Filtration + (ell : ℤ) + 1 := by
          convert hstep using 1
          · rw [show j = j - 1 + 1 by omega]
            simp only [ModularFormMod.Theta_pow_succ,
              ModularFormMod.Filtration_Mcast]
            congr 1
        have hprevcast : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        rw [hprevcast] at hprev
        rw [hstep', hprev]
        have hcast : ((j : ℤ) - i) = ((j - 1 - i : ℕ) : ℤ) + 1 := by
          omega
        have hcast' : ((j - 1 - i : ℕ) : ℤ) = (j - 1 : ℤ) - i := by
          calc
            ((j - 1 - i : ℕ) : ℤ) = ((j - 1 : ℕ) : ℤ) - i := by
              rw [Nat.cast_sub (by omega)]
            _ = (j - 1 : ℤ) - i := by rw [hprevcast]
        rw [hcast'] at hcast
        rw [hcast]
        ring

private lemma next_drop_position (hTheta : f.Theta ≠ 0)
    {i j : ℕ} (hi : i ∈ thetaFiltrationDrops f)
    (hj : j ∈ thetaFiltrationDrops f) (hij : i < j)
    (hno : ∀ t, i < t → t < j → t ∉ thetaFiltrationDrops f)
    (hsum : ∑ t ∈ thetaFiltrationDrops f, thetaDropAmount f hTheta t = ell + 1) :
    j = i + ell - thetaDropAmount f hTheta i := by
  have hlocal := filtration_between_drop f hTheta hi hij
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2 hno
  have hdi : (ell : ℤ) ∣ (f.Theta_pow i).Filtration :=
    (Finset.mem_filter.mp hi).2
  have hdj : (ell : ℤ) ∣ (f.Theta_pow j).Filtration :=
    (Finset.mem_filter.mp hj).2
  have hdivdiff : (ell : ℤ) ∣
      (f.Theta_pow j).Filtration - (f.Theta_pow i).Filtration :=
    dvd_sub hdj hdi
  have hdivexpr : (ell : ℤ) ∣
      (j - i : ℤ) * ((ell : ℤ) + 1) -
        (thetaDropAmount f hTheta i : ℤ) * ((ell : ℤ) - 1) := by
    rw [hlocal] at hdivdiff
    convert hdivdiff using 1 <;> ring
  have hrewrite :
      (j - i : ℤ) * ((ell : ℤ) + 1) -
          (thetaDropAmount f hTheta i : ℤ) * ((ell : ℤ) - 1) =
        ((j - i : ℤ) + thetaDropAmount f hTheta i) +
          (ell : ℤ) * ((j - i : ℤ) - thetaDropAmount f hTheta i) := by
    ring
  rcases hdivexpr with ⟨c, hc⟩
  have hdivsum : (j - i : ℤ) + thetaDropAmount f hTheta i =
      (ell : ℤ) * (c - ((j - i : ℤ) - thetaDropAmount f hTheta i)) := by
    calc
      _ = ((j - i : ℤ) * ((ell : ℤ) + 1) -
          (thetaDropAmount f hTheta i : ℤ) * ((ell : ℤ) - 1)) -
          (ell : ℤ) * ((j - i : ℤ) - thetaDropAmount f hTheta i) := by
            rw [hrewrite]
            ring
      _ = (ell : ℤ) * c -
          (ell : ℤ) * ((j - i : ℤ) - thetaDropAmount f hTheta i) := by rw [hc]
      _ = _ := by ring
  have hsi_le : thetaDropAmount f hTheta i ≤ ell := by
    have hi_sum : ∑ t ∈ thetaFiltrationDrops f, thetaDropAmount f hTheta t =
        thetaDropAmount f hTheta i +
          ∑ t ∈ (thetaFiltrationDrops f).erase i,
            thetaDropAmount f hTheta t := by
      rw [← Finset.sum_erase_add _ _ hi]
      ac_rfl
    have hsum' := hsum
    rw [hi_sum] at hsum'
    have hnonneg : 0 ≤ ∑ t ∈ (thetaFiltrationDrops f).erase i,
        thetaDropAmount f hTheta t := by positivity
    have hpos : 0 < thetaDropAmount f hTheta j :=
      thetaDropAmount_pos f hTheta hj
    have hle : thetaDropAmount f hTheta i + thetaDropAmount f hTheta j ≤ ell + 1 := by
      have hj_erase : j ∈ (thetaFiltrationDrops f).erase i := by
        exact Finset.mem_erase.mpr ⟨ne_of_gt hij, hj⟩
      have hrest : thetaDropAmount f hTheta j ≤
          ∑ t ∈ (thetaFiltrationDrops f).erase i,
            thetaDropAmount f hTheta t := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj_erase
      omega
    omega
  have hsum_pos : 0 < (j - i : ℤ) + thetaDropAmount f hTheta i := by
    have : 0 < j - i := Nat.sub_pos_of_lt hij
    omega
  have hsum_lt : (j - i : ℤ) + thetaDropAmount f hTheta i < 2 * (ell : ℤ) := by
    have hjlt : j - i ≤ ell - 2 := by
      have hjupper := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
      have hilower := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1
      omega
    have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
    omega
  have hc_eq : c - ((j - i : ℤ) - thetaDropAmount f hTheta i) = 1 := by
    have hellpos : (0 : ℤ) < ell := by omega
    have hfactor_pos : 0 < c - ((j - i : ℤ) - thetaDropAmount f hTheta i) := by
      nlinarith [hsum_pos, hdivsum]
    have hfactor_lt : c - ((j - i : ℤ) - thetaDropAmount f hTheta i) < 2 := by
      nlinarith [hsum_lt, hdivsum]
    omega
  have hsum_eq : (j - i : ℤ) + thetaDropAmount f hTheta i = (ell : ℤ) := by
    rw [hdivsum, hc_eq]
    ring
  have hsum_eq_nat : j - i + thetaDropAmount f hTheta i = ell := by
    have hcast_nat : ((j - i + thetaDropAmount f hTheta i : ℕ) : ℤ) =
        (j - i : ℤ) + thetaDropAmount f hTheta i := by
      rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hij)]
    have hsum_eq_nat_int : ((j - i + thetaDropAmount f hTheta i : ℕ) : ℤ) =
        (ell : ℤ) := by
      rw [hcast_nat]
      exact hsum_eq
    exact_mod_cast hsum_eq_nat_int
  omega

private lemma drops_card_le_two (hTheta : f.Theta ≠ 0)
    (hDnonempty : (thetaFiltrationDrops f).Nonempty)
    (hsum : ∑ t ∈ thetaFiltrationDrops f, thetaDropAmount f hTheta t = ell + 1) :
    (thetaFiltrationDrops f).card ≤ 2 := by
  classical
  let D := thetaFiltrationDrops f
  by_contra hcard
  have hcardD : ¬ D.card ≤ 2 := by simpa [D] using hcard
  have hcard3 : 3 ≤ D.card := by omega
  have hDne : D.Nonempty := by simpa [D] using hDnonempty
  let i₁ := D.min' hDne
  have hi₁ : i₁ ∈ D := by
    dsimp [i₁]
    exact D.min'_mem hDne
  let E := D.erase i₁
  have hEcard : 2 ≤ E.card := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hi₁]
    omega
  have hEne : E.Nonempty := Finset.card_pos.mp (by omega)
  let i₂ := E.min' hEne
  have hi₂E : i₂ ∈ E := by
    dsimp [i₂]
    exact E.min'_mem hEne
  have hi₂ : i₂ ∈ D := Finset.mem_of_mem_erase hi₂E
  have hi₁₂ : i₁ < i₂ := by
    have hle := D.min'_le i₂ hi₂
    have hne : i₁ ≠ i₂ := by
      exact (Finset.mem_erase.mp hi₂E).1.symm
    exact lt_of_le_of_ne hle hne
  have hno₁₂ : ∀ t, i₁ < t → t < i₂ → t ∉ D := by
    intro t ht₁ ht₂ htD
    have htE : t ∈ E := Finset.mem_erase.mpr ⟨ne_of_gt ht₁, htD⟩
    have hmin := E.min'_le t htE
    omega
  let G := E.erase i₂
  have hGcard : 1 ≤ G.card := by
    dsimp [G]
    rw [Finset.card_erase_of_mem hi₂E]
    omega
  have hGne : G.Nonempty := Finset.card_pos.mp hGcard
  let i₃ := G.min' hGne
  have hi₃G : i₃ ∈ G := by
    dsimp [i₃]
    exact G.min'_mem hGne
  have hi₃E : i₃ ∈ E := Finset.mem_of_mem_erase hi₃G
  have hi₃ : i₃ ∈ D := Finset.mem_of_mem_erase hi₃E
  have hi₂₃ : i₂ < i₃ := by
    have hle := E.min'_le i₃ hi₃E
    have hne : i₂ ≠ i₃ := by
      exact (Finset.mem_erase.mp hi₃G).1.symm
    exact lt_of_le_of_ne hle hne
  have hno₂₃ : ∀ t, i₂ < t → t < i₃ → t ∉ D := by
    intro t ht₂ ht₃ htD
    have htE : t ∈ E := Finset.mem_erase.mpr
      ⟨ne_of_gt (lt_trans hi₁₂ ht₂), htD⟩
    have htG : t ∈ G := Finset.mem_erase.mpr ⟨ne_of_gt ht₂, htE⟩
    have hmin := G.min'_le t htG
    omega
  have hsumD : ∑ t ∈ D, thetaDropAmount f hTheta t = ell + 1 := by
    simpa [D] using hsum
  have hsumE : ∑ t ∈ E, thetaDropAmount f hTheta t =
      thetaDropAmount f hTheta i₂ +
        ∑ t ∈ G, thetaDropAmount f hTheta t := by
    dsimp [G]
    rw [← Finset.sum_erase_add _ _ hi₂E]
    ac_rfl
  have hsumD' : ∑ t ∈ D, thetaDropAmount f hTheta t =
      thetaDropAmount f hTheta i₁ + ∑ t ∈ E, thetaDropAmount f hTheta t := by
    rw [← Finset.sum_erase_add _ _ hi₁]
    ac_rfl
  have hsumG : ∑ t ∈ G, thetaDropAmount f hTheta t =
      thetaDropAmount f hTheta i₃ +
        ∑ t ∈ G.erase i₃, thetaDropAmount f hTheta t := by
    rw [← Finset.sum_erase_add _ _ hi₃G]
    ac_rfl
  have hsum123 : thetaDropAmount f hTheta i₁ +
      thetaDropAmount f hTheta i₂ + thetaDropAmount f hTheta i₃ ≤ ell + 1 := by
    have hrest : 0 ≤ ∑ t ∈ G.erase i₃, thetaDropAmount f hTheta t := by positivity
    rw [hsumD', hsumE, hsumG] at hsumD
    omega
  have hnext₁₂ := next_drop_position f hTheta hi₁ hi₂ hi₁₂ hno₁₂ hsum
  have hnext₂₃ := next_drop_position f hTheta hi₂ hi₃ hi₂₃ hno₂₃ hsum
  have hs₃pos := thetaDropAmount_pos f hTheta hi₃
  have hi₃upper := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi₃).1).2
  have hi₁lower := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi₁).1).1
  omega

private lemma filtration_before_first_drop (hnotdiv : ¬ (ell : ℤ) ∣ f.Filtration)
    {j : ℕ} (hj : j ≤ ell - 1)
    (hno : ∀ i, i < j → i ∉ thetaFiltrationDrops f) :
    (f.Theta_pow j).Filtration =
      f.Filtration + (j : ℤ) * ((ell : ℤ) + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjbound : j ≤ ell - 1 := by omega
      have hprev := ih hjbound (fun i hi => hno i (by omega))
      have hdiv : ¬ (ell : ℤ) ∣ (f.Theta_pow j).Filtration := by
        by_cases hjzero : j = 0
        · subst j
          simpa using hnotdiv
        · intro hd
          apply hno j (by omega)
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hjbound⟩, hd⟩
      rw [(Filt_Theta_iff' f rfl).2 hdiv, hprev]
      push_cast
      ring

/-- The four drop patterns, with the initial point chosen at a minimum of
the theta cycle. This minimum condition is essential: rotating a theta cycle
can move its last drop away from `ell - 1` and `ell - 2`. -/
theorem theta_filtration_drop_classification (hTheta : f.Theta ≠ 0)
    (hnotdiv : ¬ (ell : ℤ) ∣ f.Filtration)
    (hminimal : ∀ i : ℕ, f.Filtration ≤ (f.Theta_pow i).Filtration) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ k₀ < ell ∧
      (f.Filtration : ℤ) ≡ -(k₀ : ℤ) [ZMOD ell] ∧
      ∃ s : ℕ → ℕ,
        (∀ i ∈ thetaFiltrationDrops f,
          (f.Theta_pow (i + 1)).Filtration =
            (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
              (s i : ℤ) * ((ell : ℤ) - 1)) ∧
        (((f.Filtration : ℤ) ≡ 1 [ZMOD ell] ∧
              thetaFiltrationDrops f = {ell - 1} ∧ s (ell - 1) = ell + 1) ∨
          ((f.Filtration : ℤ) ≡ 2 [ZMOD ell] ∧
              thetaFiltrationDrops f = {ell - 2} ∧ s (ell - 2) = ell + 1) ∨
          (¬ ((f.Filtration : ℤ) ≡ 1 [ZMOD ell]) ∧
              thetaFiltrationDrops f = {k₀, ell - 1} ∧
              s k₀ = k₀ + 1 ∧ s (ell - 1) = ell - k₀) ∨
          (¬ ((f.Filtration : ℤ) ≡ 1 [ZMOD ell]) ∧
              ¬ ((f.Filtration : ℤ) ≡ 2 [ZMOD ell]) ∧
              thetaFiltrationDrops f = {k₀, ell - 2} ∧
              s k₀ = k₀ + 2 ∧ s (ell - 2) = ell - k₀ - 1)) := by
  classical
  let s := thetaDropAmount f hTheta
  have hs : ∀ t ∈ thetaFiltrationDrops f,
      (f.Theta_pow (t + 1)).Filtration =
        (f.Theta_pow t).Filtration + (ell : ℤ) + 1 -
          (s t : ℤ) * ((ell : ℤ) - 1) := by
    intro t ht
    exact thetaDropAmount_step f hTheta ht
  have hsumInt := theta_filtration_drop_sum f s hs
  have hsum : ∑ t ∈ thetaFiltrationDrops f, s t = ell + 1 := by
    exact_mod_cast hsumInt
  have hDne := theta_filtration_drops_nonempty f s hs
  have hcard := drops_card_le_two f hTheta hDne hsum
  let i := (thetaFiltrationDrops f).min' hDne
  let j := (thetaFiltrationDrops f).max' hDne
  have hi : i ∈ thetaFiltrationDrops f := (thetaFiltrationDrops f).min'_mem hDne
  have hj : j ∈ thetaFiltrationDrops f := (thetaFiltrationDrops f).max'_mem hDne
  have hibounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1
  have hjbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
  have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
  have hfirst : ∀ t, t < i → t ∉ thetaFiltrationDrops f := by
    intro t hti ht
    have hle := (thetaFiltrationDrops f).min'_le t ht
    omega
  have hlinear := filtration_before_first_drop f hnotdiv hibounds.2 hfirst
  have hdiv : (ell : ℤ) ∣ f.Filtration + (i : ℤ) := by
    have hd := (Finset.mem_filter.mp hi).2
    rw [hlinear] at hd
    convert dvd_sub hd (dvd_mul_right (ell : ℤ) (i : ℤ)) using 1 <;> ring
  have hmod : f.Filtration ≡ -(i : ℤ) [ZMOD ell] := by
    rw [Int.modEq_iff_dvd]
    convert dvd_neg.mpr hdiv using 1 <;> ring
  have hlast : j = ell - 1 ∨ j = ell - 2 := by
    have htel := theta_filtration_telescoping f s hs hjbounds.2
    have hfilter : (Finset.Icc 1 j).filter (fun t => t ∈ thetaFiltrationDrops f) =
        thetaFiltrationDrops f := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_Icc, and_iff_right_iff_imp]
      intro ht
      exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1,
        (thetaFiltrationDrops f).le_max' t ht⟩
    have hsumj : ∑ t ∈ Finset.Icc 1 j,
        (if t ∈ thetaFiltrationDrops f then (s t : ℤ) else 0) *
          ((ell : ℤ) - 1) = ((ell : ℤ) + 1) * ((ell : ℤ) - 1) := by
      rw [← Finset.sum_mul, ← Finset.sum_filter, hfilter, hsumInt]
    have hstepzero : (f.Theta_pow 1).Filtration =
        f.Filtration + ((ell : ℤ) + 1) := by
      simpa using (Filt_Theta_iff' f (m := 1) (j := 0) rfl).2 (by simpa using hnotdiv)
    rw [hsumj, hstepzero] at htel
    have hmin := hminimal (j + 1)
    rw [htel] at hmin
    have hbound : (ell : ℤ) - 2 ≤ j := by nlinarith
    omega
  have hres (c : ℤ) (hic : (ell : ℤ) - i = c) :
      f.Filtration ≡ c [ZMOD ell] := by
    apply hmod.trans
    rw [Int.modEq_iff_dvd]
    have hdiff : c - -(i : ℤ) = (ell : ℤ) := by omega
    rw [hdiff]
  have hnotres (c : ℤ) (hcpos : 0 < c) (hclt : c < ell)
      (hic : (ell : ℤ) - i ≠ c) : ¬ f.Filtration ≡ c [ZMOD ell] := by
    intro hfc
    have hneg := hmod.symm.trans hfc
    have hd : (ell : ℤ) ∣ c + i := by
      simpa only [Int.modEq_iff_dvd, sub_neg_eq_add] using hneg
    rcases hd with ⟨a, ha⟩
    have hellpos : (0 : ℤ) < ell := by omega
    have hisumpos : (0 : ℤ) < c + i := by omega
    have hisumlt : c + i < 2 * (ell : ℤ) := by omega
    have hapos : 0 < a := by nlinarith
    have halt : a < 2 := by nlinarith
    have haone : a = 1 := by omega
    rw [haone, mul_one] at ha
    omega
  refine ⟨i, hibounds.1, by omega, hmod, s, hs, ?_⟩
  have hij : i ≤ j := (thetaFiltrationDrops f).min'_le j hj
  by_cases heq : i = j
  · have hD : thetaFiltrationDrops f = {i} := by
      ext t
      simp only [Finset.mem_singleton]
      constructor
      · intro ht
        have hmin := (thetaFiltrationDrops f).min'_le t ht
        have hmax := (thetaFiltrationDrops f).le_max' t ht
        omega
      · rintro rfl
        exact hi
    have hsi : s i = ell + 1 := by simpa [hD] using hsum
    rcases hlast with hjlast | hjlast
    · left
      have hieq : i = ell - 1 := heq.trans hjlast
      exact ⟨hres 1 (by omega), by simpa [hieq] using hD,
        by simpa [hieq] using hsi⟩
    · right; left
      have hieq : i = ell - 2 := heq.trans hjlast
      exact ⟨hres 2 (by omega), by simpa [hieq] using hD,
        by simpa [hieq] using hsi⟩
  · have hijlt : i < j := lt_of_le_of_ne hij heq
    have hsub : ({i, j} : Finset ℕ) ⊆ thetaFiltrationDrops f := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj⟩
    have hD : thetaFiltrationDrops f = {i, j} := by
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le hsub
      simpa [Finset.card_pair heq] using hcard
    have hno : ∀ t, i < t → t < j → t ∉ thetaFiltrationDrops f := by
      intro t hit htj ht
      rw [hD] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      omega
    have hnext := next_drop_position f hTheta hi hj hijlt hno hsum
    have hsumij : s i + s j = ell + 1 := by
      simpa [hD, heq] using hsum
    have hsipos := thetaDropAmount_pos f hTheta hi
    have hsjpos := thetaDropAmount_pos f hTheta hj
    change 0 < s i at hsipos
    change 0 < s j at hsjpos
    change j = i + ell - s i at hnext
    rcases hlast with hjlast | hjlast
    · right; right; left
      have hsi : s i = i + 1 := by omega
      have hsj : s (ell - 1) = ell - i := by rw [← hjlast]; omega
      exact ⟨hnotres 1 (by omega) (by omega) (by omega),
        by simpa [hjlast] using hD, hsi, hsj⟩
    · right; right; right
      have hsi : s i = i + 2 := by omega
      have hsj : s (ell - 2) = ell - i - 1 := by rw [← hjlast]; omega
      exact ⟨hnotres 1 (by omega) (by omega) (by omega),
        hnotres 2 (by omega) (by omega) (by omega),
        by simpa [hjlast] using hD, hsi, hsj⟩

end
end KOl
