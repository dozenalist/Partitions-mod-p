import PartitionsLeanblueprint.RamanujanCongruence.PreliminaryResults
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.MaximalReduce
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.FiltrationPow


/-
This file proves the lemmas in the first section of the paper
It shortcuts lemma 3.3, because we don't need it (see `Filtration_Theta_pow_sub_one`)
This file is sorry-free, borrowing the long proofs of lemma 2.1 from AiAssisted/SwD
-/

open ModularFormMod

noncomputable section




theorem ZMod.one_ne_zero' {ℓ : ℕ} [h : ℓ.AtLeastTwo] : (1 : ZMod ℓ) ≠ 0 :=
  have : Fact (1 < ℓ) := ⟨h.prop⟩; one_ne_zero


variable {ℓ : ℕ} [hℓ : isLargePrime ℓ] {k j : ZMod (ℓ - 1)} (f : ModularFormMod ℓ k)


theorem NeZero.of_coeff_ne_zero {k} {f : ModularFormMod ℓ k} (h : ∃ n, f.coeff n ≠ 0) : NeZero f where
  out := by contrapose! h; simp only [h, coeff_zero, implies_true]

theorem NeZero.coeff_ne_zero {k} {f : ModularFormMod ℓ k} [h : NeZero f] :
    ∃ n, f.coeff n ≠ 0 := have h := h.out; by contrapose! h; exact ext h

instance NeZero_Delta [ℓ.AtLeastTwo] : NeZero (Δ : ModularFormMod ℓ 12) :=
  NeZero.of_coeff_ne_zero ⟨1, by rw [Delta_one]; exact ZMod.one_ne_zero' ⟩


instance NeZero_Theta_fl : NeZero (fl ℓ).Theta :=
  NeZero.of_coeff_ne_zero ⟨δ ℓ, by simpa [ZMod.natCast_eq_zero_iff] using not_dvd_delta ℓ⟩

instance NeZero_Theta_pow_fl (m) : NeZero ((fl ℓ).Theta_pow m) :=
  NeZero.of_coeff_ne_zero ⟨δ ℓ, by simp [ZMod.natCast_eq_zero_iff, not_dvd_delta]⟩

instance NeZero_Mcast (h : k = j) [hf : NeZero f] : NeZero (f.Mcast h) := by
    obtain ⟨n, hn⟩ := hf.coeff_ne_zero
    exact NeZero.of_coeff_ne_zero ⟨n, by simpa⟩



lemma Filt_Delta : (Δ : ModularFormMod ℓ 12).Filtration = 12 :=
  le_antisymm
    (Filtration_le ⟨IntegerModularForm.Delta, by ext n; simp only [IntegerModularForm.reduce_coeff,
      Delta, fourier_Mcast, IntegerModularForm.fourier_Reduce] ⟩)
    (le_Filtration (p := 1) Δ fun n nlt => by simp_all only [Order.lt_one_iff, Delta_zero])


lemma twelve_delta_cast : ((ℓ^2 - 1)/2 : ℕ) = ((ℓ : ℤ)^2 - 1)/2 := by
  rw [Int.natCast_ediv, Nat.cast_ofNat, Int.natCast_pred_of_pos <| pow_two_pos_of_ne_zero NeZero.out, Nat.cast_pow]



lemma Filt_fl : (fl ℓ).Filtration = (ℓ^2 - 1)/2 :=
  have h1 : (12 : ℤ) * δ ℓ = (ℓ^2 - 1)/2 := by
    rw [show (12 : ℤ) = (12 : ℕ) from rfl, ← Nat.cast_mul, twelve_delta, twelve_delta_cast]
  have h2 : δ ℓ * (12 : ℤ) = (ℓ^2 - 1)/2 := by rwa [mul_comm]
  le_antisymm
    (Filtration_le ⟨(IntegerModularForm.fl ℓ).Icast h2,
        by rw [fl, fourier_Mcast, IntegerModularForm.fourier_Reduce]; rfl⟩)
    (h1 ▸ le_Filtration (p := (δ ℓ)) (fl ℓ) fun n => fl_lt_delta)


--Lemma 2.1

-- (pt 1)
theorem Filt_Theta_bound : f.Theta.Filtration ≤ f.Filtration + (ℓ + 1) :=
  SwD.Filt_Theta_bound f

-- (pt 2)
theorem Filt_Theta_iff : f.Theta.Filtration = f.Filtration + (ℓ + 1) ↔ ¬ ↑ℓ ∣ f.Filtration :=
  SwD.Filt_Theta_iff f



lemma Filt_Theta_bound' {m j : ℕ} (h : m = j + 1) :
    (f.Theta_pow m).Filtration ≤ (f.Theta_pow j).Filtration + (ℓ + 1) := by
  subst h
  simpa only [Theta_pow_succ, Filtration_Mcast] using Filt_Theta_bound <| f.Theta_pow j


lemma Filt_Theta_iff' {m j : ℕ} (h : m = j + 1) :
    (f.Theta_pow m).Filtration = (f.Theta_pow j).Filtration + (ℓ + 1) ↔
      ¬ ↑ℓ ∣ (f.Theta_pow j).Filtration := by
  subst h
  simpa only [Theta_pow_succ, Filtration_Mcast] using Filt_Theta_iff <| f.Theta_pow j


lemma Filt_Theta_congruence [NeZero f.Theta] :
    f.Theta.Filtration = f.Filtration + (ℓ + (1 : ZMod (ℓ - 1))) := by
  simp only [Filtration_congruence, ← one_add_one_eq_two, ZMod.pred_eq_one]


lemma Filt_Theta_congruence_of_dvd [hℓ : ℓ.AtLeastTwo] [hfT : NeZero f.Theta] (ldiv : ↑ℓ ∣ f.Filtration) :
    ∃ α > 0, f.Theta.Filtration = f.Filtration + (ℓ + 1) - α * (ℓ - 1) := by

  have : NeZero (ℓ - 1) := ⟨have := hℓ.prop; by omega⟩

  have bound := lt_of_le_of_ne (Filt_Theta_bound f) fun h => (Filt_Theta_iff f).1 h ldiv

  obtain ⟨α, hα⟩ := by simpa only [← AddCommGroup.modEq_iff_intModEq,
      AddCommGroup.modEq_iff_eq_add_zsmul, smul_eq_mul]
    using ZMod.intCast_eq_intCast_iff ..|>.1 <| mod_cast Filt_Theta_congruence f |>.symm

  norm_cast at bound
  rw [hα, add_lt_iff_neg_left] at bound
  have := this.out.pos

  use -α, by
    simp only [Int.neg_pos]
    zify at this
    exact Int.neg_of_mul_neg_left bound this

  rw [hα, neg_mul, sub_neg_eq_add, Nat.cast_pred <| NeZero.pos ℓ]; rfl



lemma Filt_Theta_congruence_of_dvd' {m j : ℕ} [hfT : NeZero (f.Theta_pow m)]
  (ldiv: ↑ℓ ∣ (f.Theta_pow j).Filtration) (h : m = j + 1) :
    ∃ α > 0, (f.Theta_pow m).Filtration = (f.Theta_pow j).Filtration + (ℓ + 1) - α * (ℓ - 1) := by
  subst h
  simp_all only [Theta_pow_succ, Filtration_Mcast]
  exact Filt_Theta_congruence_of_dvd _ ldiv (hfT := NeZero.Mcast _ hfT)


lemma Filt_Theta_pow_congruence (m) [hfT : ∀ m, NeZero (f.Theta_pow m)] :
    ∃ α ≥ 0, (f.Theta_pow m).Filtration = f.Filtration + m • (ℓ + 1) - α * (ℓ - 1) := by
  induction m with
  | zero => simpa using ⟨0, le_rfl, by simp⟩
  | succ m ih =>
    obtain ⟨β, hβ, hf⟩ := ih
    by_cases hdvd : ↑ℓ ∣ ((Theta_pow m) f).Filtration
    · obtain ⟨α, hα, hf'⟩ := Filt_Theta_congruence_of_dvd' f hdvd rfl
      use α + β, by positivity, by rw [hf', hf]; ring
    · use β, hβ, by rw [(Filt_Theta_iff' f rfl).mpr hdvd, hf]; ring



-- Lemma 3.2
theorem le_Filt_Theta_fl (m) : (fl ℓ).Filtration ≤ ((fl ℓ).Theta_pow m).Filtration := by
  rw [Filt_fl, ← twelve_delta_cast, ← twelve_delta, Nat.cast_mul, Nat.cast_ofNat]
  exact le_Filtration _ fun _ nlt => by rw [coeff_Theta_pow, fl_lt_delta nlt, smul_zero]



theorem Filtration_Theta_pow_sub_one (flu : (fl ℓ).UOp = 0) :
    ((fl ℓ).Theta_pow (ℓ - 1)).Filtration = (ℓ^2 - 1)/2 := by
  rw [← Filt_fl]; exact .symm <| Filtration_ext fun _ =>
  have := by simpa only [map_sub, coeff_Mcast] using ModularFormMod.ext_iff.1 <| UOp_pow_l (fl ℓ)
  by rw [← sub_eq_zero, ← this, flu, ModularFormMod.zero_pow, coeff_zero]


theorem Filt_Theta_fl : (fl ℓ).Theta.Filtration = (ℓ ^ 2 - 1) / 2 + (ℓ + 1) := by
  rw [← Filt_fl, Filt_Theta_iff]
  rw [Filt_fl, ← twelve_delta_cast, Int.natCast_dvd_natCast]
  exact not_dvd_filt ℓ


theorem Filt_Theta_pow_l : ((fl ℓ).Theta_pow ℓ).Filtration = (ℓ ^ 2 - 1) / 2 + (ℓ + 1) := by
  simpa only [Theta_pow_l, Filtration_Mcast] using Filt_Theta_fl


theorem Filt_Theta_pow_sub_one' :
  ((fl ℓ).Theta_pow (ℓ - 1)).Filtration = (ℓ^2 - 1)/2 ∨
    ↑ℓ ∣ ((fl ℓ).Theta_pow (ℓ - 1)).Filtration := by
  rw [or_iff_not_imp_right]
  intro h
  rw [← add_right_cancel_iff (a := (ℓ + 1 : ℤ)), ← Filt_Theta_pow_l,
    ← (Filt_Theta_iff' _ <| show ℓ = ℓ - 1 + 1 by grind [hℓ.AtLeastFive]).mpr h]


theorem Filt_Theta_pow_upperBound (f : ModularFormMod ℓ k) : ∀ m,
    (Theta_pow m f).Filtration ≤ f.Filtration + m • (ℓ + 1)
  | 0 => by simp
  | m + 1 => by grw [Filt_Theta_bound' f <| Eq.refl (m + 1),
      add_smul, Filt_Theta_pow_upperBound f m, one_smul, add_assoc]


theorem Filt_Theta_sub_one_upperBound (f : ModularFormMod ℓ k) :
    (Theta_pow (ℓ - 1) f).Filtration ≤ f.Filtration + ℓ ^ 2 - 1 := by
  convert Filt_Theta_pow_upperBound f (ℓ - 1)
  simp [Nat.cast_pred (show 0 < ℓ by grind [hℓ.AtLeastFive])]
  ring

theorem Filt_UOp_pow_l_bound (f : ModularFormMod ℓ k) :
    (f.UOp.pow ℓ).Filtration ≤ f.Filtration + ℓ ^ 2 - 1 := by
  rw [UOp_pow_l, sub_eq_add_neg]
  grw [Filtration_add]
  simp only [Filtration_Mcast, Filtration_neg, max_le_iff]
  constructor
  · grw [hℓ.AtLeastFive]; lia
  · exact Filt_Theta_sub_one_upperBound f


theorem Filt_UOp_bound (f : ModularFormMod ℓ k) :
    f.UOp.Filtration ≤ ℓ + (f.Filtration - 1) / ℓ := by
  have hℓpos : (0 : ℤ) < ℓ := by grind [hℓ.AtLeastFive]
  have h' : f.UOp.Filtration ≤ (f.Filtration + (ℓ : ℤ) ^ 2 - 1) / (ℓ : ℤ) :=
    (Int.le_ediv_iff_mul_le hℓpos).2 (by
      simpa only [mul_comm, Order.le_sub_one_iff] using
    Int.lt_of_le_sub_one <| Filtration_pow f.UOp ℓ ▸ Filt_UOp_pow_l_bound f)
  grw [h', show f.Filtration + (ℓ : ℤ) ^ 2 - 1 =
    (f.Filtration - 1) + (ℓ : ℤ) * ℓ by ring,
      Int.add_mul_ediv_right _ _ hℓpos.ne.symm, add_comm]
