import PartitionsLeanblueprint.RamanujanCongruence.Partition
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.ProductDefs
import PartitionsLeanblueprint.RamanujanCongruence.ModularFormMod.Operators
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.ZMod
import PartitionsLeanblueprint.RamanujanCongruence.PrimaryLemmas
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.ThetaBinomial
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.FiltrationDrops
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.WeightSeparation
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.FiltrationCycle
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.DropClassification
import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.PropositionThree

/-!
Statements extracted from Kiming--Olsson, *Congruences like Ramanujan's for
powers of the partition function* (Arch. Math. 59 (1992), 348--360).

Only the ordinary partition function is used here.  The function `natpart` in
`Partition.lean` is the usual partition function, including `p(0) = 1`.
The auxiliary function below extends it to negative integers by the standard
convention `p(n) = 0` for `n < 0`.

The partition-product bridge and the final uniqueness theorem are in
`PartitionProduct.lean` and `Unique.lean`.
-/

namespace KOl

open scoped IntegerModularForm

/-- The usual partition function on integers, with `p(n) = 0` for `n < 0`. -/
def standardPartition (n : ℤ) : ℕ :=
  if _h : 0 ≤ n then natpart n.toNat else 0

@[simp] lemma standardPartition_ofNat (n : ℕ) :
    standardPartition n = natpart n := by
  simp [standardPartition]

/-- A congruence for `p` at the residue class `a (mod ell)`. -/
def congruenceAt (ell a : ℕ) : Prop :=
  ∀ n : ℕ, ell ∣ standardPartition (ell * (n : ℤ) + a)

/-- A congruence on the whole integer progression with shift `beta`.
Negative partition arguments contribute zero. -/
def shiftedCongruence (ell : ℕ) (beta : ℤ) : Prop :=
  ∀ n : ℤ, ell ∣ standardPartition (ell * n - beta)

/-- The ordinary partition-function version of the Ramanujan progression. -/
abbrev ramanujanCongruence (ell : ℕ) : Prop :=
  shiftedCongruence ell (delta ell)

/-! ### Elementary normalization of progressions -/

/-- Congruent integer shifts describe the same progression by reindexing. -/
lemma shiftedCongruence_of_modEq {ell : ℕ} {beta gamma : ℤ}
    (h : shiftedCongruence ell beta) (hclass : beta ≡ gamma [ZMOD ell]) :
    shiftedCongruence ell gamma := by
  obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hclass
  intro n
  have harg : (ell : ℤ) * (n - c) - beta = (ell : ℤ) * n - gamma := by
    linear_combination hc
  rw [← harg]
  exact h (n - c)

lemma shiftedCongruence_iff_of_modEq {ell : ℕ} {beta gamma : ℤ}
    (hclass : beta ≡ gamma [ZMOD ell]) :
    shiftedCongruence ell beta ↔ shiftedCongruence ell gamma :=
  ⟨fun h => shiftedCongruence_of_modEq h hclass,
    fun h => shiftedCongruence_of_modEq h hclass.symm⟩

/-- For a normalized residue, negative indices have negative partition arguments. -/
lemma shiftedCongruence_neg_iff_congruenceAt {ell a : ℕ} (ha : a < ell) :
    shiftedCongruence ell (-(a : ℤ)) ↔ congruenceAt ell a := by
  constructor
  · intro h n
    simpa only [sub_neg_eq_add] using h (n : ℤ)
  · intro h n
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      simpa only [sub_neg_eq_add] using h n
    · have hn' : n ≤ -1 := by omega
      have ha' : (a : ℤ) < ell := by exact_mod_cast ha
      have harg : (ell : ℤ) * n + (a : ℤ) < 0 := by
        nlinarith [mul_le_mul_of_nonneg_left hn' (Nat.cast_nonneg (α := ℤ) ell)]
      simp [standardPartition, not_le.mpr harg]

lemma shiftedCongruence_iff_of_pos_of_lt {ell beta : ℕ}
    (hbeta : 0 < beta) (hbetaell : beta < ell) :
    shiftedCongruence ell beta ↔ congruenceAt ell (ell - beta) := by
  have hclass : (beta : ℤ) ≡ -((ell - beta : ℕ) : ℤ) [ZMOD ell] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-1, ?_⟩
    rw [Nat.cast_sub hbetaell.le]
    ring
  exact (shiftedCongruence_iff_of_modEq hclass).trans
    (shiftedCongruence_neg_iff_congruenceAt (by omega))

/-- Normalize an arbitrary signed shift to the residue used in Theorem 1. -/
lemma shiftedCongruence_normalize {ell : ℕ} {beta : ℤ}
    (hell : 2 ≤ ell) (h : shiftedCongruence ell beta) :
    ∃ a : ℕ, 0 < a ∧ a < ell ∧
      congruenceAt ell a ∧ beta + a ≡ 0 [ZMOD ell] := by
  let a := ((-beta) % (ell : ℤ)).toNat
  have hrem : 0 ≤ (-beta) % (ell : ℤ) := Int.emod_nonneg _ (by omega)
  have hacast : (a : ℤ) = (-beta) % (ell : ℤ) := Int.toNat_of_nonneg hrem
  have halt : a < ell := by
    have := Int.emod_lt_of_pos (-beta) (by omega : 0 < (ell : ℤ))
    omega
  have hclass : beta + (a : ℤ) ≡ 0 [ZMOD ell] := by
    rw [hacast]
    simpa using (Int.mod_modEq (-beta) (ell : ℤ)).add_left beta
  have hshift : shiftedCongruence ell (-(a : ℤ)) := by
    apply shiftedCongruence_of_modEq h
    simpa using hclass.add_right (-(a : ℤ))
  have hAt := (shiftedCongruence_neg_iff_congruenceAt halt).mp hshift
  have hapos : 0 < a := by
    by_contra! ha
    have ha0 : a = 0 := by omega
    have hzero := hAt 0
    simp [ha0, standardPartition, natpart_zero] at hzero
    omega
  exact ⟨a, hapos, halt, hAt, hclass⟩

/-! ### The statements used from Kiming--Olsson -/

/-- The arithmetic identity identifying the distinguished class. -/
lemma twentyfour_mul_delta_modEq {ell : ℕ}
    (hell : 5 ≤ ell) (hell_prime : Nat.Prime ell) :
    24 * delta ell ≡ ell - 1 [MOD ell] := by
  letI : Fact (Nat.Prime ell) := ⟨hell_prime⟩
  letI : Fact (ell ≥ 5) := ⟨hell⟩
  have hle : ell - 1 ≤ 24 * delta ell := by
    rw [twentyfour_mul_delta]
    have hpow : ell ≤ ell ^ 2 := by
      calc
        ell = ell * 1 := by simp
        _ ≤ ell * ell := Nat.mul_le_mul_left ell (by omega)
        _ = ell ^ 2 := by rw [pow_two]
    exact Nat.sub_le_sub_right hpow 1
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd' hle, twentyfour_mul_delta]
  refine ⟨ell - 1, ?_⟩
  rw [Nat.mul_sub_left_distrib, pow_two]
  omega

/-- The normalized residue forced by Theorem 1 is the Ramanujan residue. -/
lemma normalized_residue_eq_delta {ell a : ℕ}
    (hell_prime : Nat.Prime ell) (hell : 5 ≤ ell) (_ha : a < ell)
    (hko : 24 * a ≡ 1 [MOD ell]) :
    a + delta ell ≡ 0 [MOD ell] := by
  have hd := twentyfour_mul_delta_modEq hell hell_prime
  have hadd := hko.add hd
  have hmid : 1 + (ell - 1) = ell := by omega
  have hsum : 24 * (a + delta ell) ≡ 0 [MOD ell] := by
    calc
      24 * (a + delta ell) ≡ 1 + (ell - 1) [MOD ell] := by
        simpa [Nat.mul_add] using hadd
      _ ≡ 0 [MOD ell] := by
        rw [hmid]
        simp [Nat.ModEq]
  have hdiv : ell ∣ 24 * (a + delta ell) :=
    Nat.modEq_zero_iff_dvd.mp hsum
  have hnot24 : ¬ ell ∣ 24 := by
    intro h24
    have heq1 : 24 = 3 * 8 := by norm_num
    rw [heq1] at h24
    rcases (Nat.Prime.dvd_mul hell_prime).mp h24 with h3 | h8
    · have hle3 := Nat.le_of_dvd (by norm_num : 0 < 3) h3
      omega
    · have heq2 : 8 = 2 * 4 := by norm_num
      rw [heq2] at h8
      rcases (Nat.Prime.dvd_mul hell_prime).mp h8 with h2 | h4
      · have hle2 := Nat.le_of_dvd (by norm_num : 0 < 2) h2
        omega
      · have heq3 : 4 = 2 * 2 := by norm_num
        rw [heq3] at h4
        rcases (Nat.Prime.dvd_mul hell_prime).mp h4 with h2 | h2
        · have hle2 := Nat.le_of_dvd (by norm_num : 0 < 2) h2
          omega
        · have hle2 := Nat.le_of_dvd (by norm_num : 0 < 2) h2
          omega
  rcases (Nat.Prime.dvd_mul hell_prime).mp hdiv with h24 | hsum
  · exact (hnot24 h24).elim
  · exact Nat.modEq_zero_iff_dvd.mpr hsum

/-! ### Proposition 1: congruences and the theta operator -/

/--
The power series obtained from `Theta^(ell - 1) (q⁻ᵃ f)` after multiplying
back by `q^a`.  Its coefficient at `q^n` is `(n-a)^(ell-1) * fₙ`, with the
exponent interpreted in `ZMod ell`.
-/
noncomputable def shiftedThetaSeries {ell : ℕ} [isLargePrime ell] {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (a : ℕ) : PowerSeries (ZMod ell) :=
  PowerSeries.mk fun n =>
    (((n : ZMod ell) - a) ^ (ell - 1)) * f.coeff n

/-- The shifted theta identity from Proposition 1, with `q^a` clearing `q⁻ᵃ`. -/
def shiftedThetaIdentity {ell : ℕ} [isLargePrime ell] {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (a : ℕ) : Prop :=
  shiftedThetaSeries f a = f.fourier

/-- Proposition 1 directly in the project's modular-form reduction space. -/
theorem proposition_one_modular {ell : ℕ} [isLargePrime ell] {k : ZMod (ell - 1)}
    (g : ModularFormMod ell k) (a : ℕ) (ha : a < ell) :
    (∀ n : ℕ, g.coeff (ell * n + a) = 0) ↔ shiftedThetaIdentity g a := by
  have hexp : ell - 1 ≠ 0 := by
    have h := isLargePrime.AtLeastFive (ℓ := ell)
    omega
  have coeff_zero_of_cast_eq
      (hc : ∀ n : ℕ, g.coeff (ell * n + a) = 0)
      {n : ℕ} (hn : (n : ZMod ell) = a) : g.coeff n = 0 := by
    have hmod : n % ell = a := by
      have hm : n ≡ a [MOD ell] :=
        (ZMod.natCast_eq_natCast_iff n a ell).mp hn
      simpa [Nat.ModEq, Nat.mod_eq_of_lt ha] using hm
    have hindex : n = ell * (n / ell) + a := by
      calc
        n = n % ell + ell * (n / ell) := (Nat.mod_add_div n ell).symm
        _ = a + ell * (n / ell) := by rw [hmod]
        _ = ell * (n / ell) + a := by omega
    rw [hindex]
    exact hc (n / ell)
  constructor
  · intro h
    have hg : ∀ n : ℕ, g.coeff (ell * n + a) = 0 := h
    change shiftedThetaSeries g a = g.fourier
    apply PowerSeries.ext
    intro n
    simp only [shiftedThetaSeries, PowerSeries.coeff_mk]
    rw [← ModularFormMod.coeff_def]
    by_cases hx : (n : ZMod ell) - a = 0
    · have hcoeff : g.coeff n = 0 := by
        apply coeff_zero_of_cast_eq hg
        exact sub_eq_zero.mp hx
      rw [hx, zero_pow hexp, hcoeff]
      simp
    · have hpow : ((n : ZMod ell) - a) ^ (ell - 1) = 1 :=
        ZMod.pow_card_sub_one_eq_one hx
      rw [hpow, one_mul]
  · intro h
    change shiftedThetaSeries g a = g.fourier at h
    intro n
    change g.coeff (ell * n + a) = 0
    have hcoef := congrArg (fun s : PowerSeries (ZMod ell) => s.coeff (ell * n + a)) h
    have hcoef' : ((((ell * n + a : ℕ) : ZMod ell) - a) ^ (ell - 1)) *
        g.coeff (ell * n + a) = g.coeff (ell * n + a) := by
      simpa only [shiftedThetaSeries, PowerSeries.coeff_mk, ModularFormMod.coeff_def]
        using hcoef
    have hcast : ((ell * n + a : ℕ) : ZMod ell) - a = 0 := by
      push_cast
      simp
    rw [hcast] at hcoef'
    rw [zero_pow hexp, zero_mul] at hcoef'
    exact hcoef'.symm

/-- Proposition 1 for powers of a `p`-integral modular form. -/
theorem proposition_one {ell : ℕ} [isLargePrime ell] {k : ℤ}
    (f : PIntegralModularForm ell k) (r a : ℕ)
    (_hr : 0 < r) (ha : a < ell) :
    (∀ n : ℕ, ((f.pow r).Reduce).coeff (ell * n + a) = 0) ↔
      shiftedThetaIdentity ((f.pow r).Reduce) a :=
  proposition_one_modular _ a ha

/-! ### Proposition 2: the possible filtration-drop patterns -/

/-- The cycle classification at a minimum of the theta filtration cycle.
The minimum hypothesis is needed for the endpoint classification: an
arbitrary rotation of a theta cycle need not have its last drop at
`ell - 1` or `ell - 2`. -/
theorem proposition_two {ell : ℕ} [isLargePrime ell] {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (hTheta : f.Theta ≠ 0)
    (hfiltration : f.Filtration ≠ 0)
    (hnotdiv : ¬ (ell : ℤ) ∣ f.Filtration)
    (hminimal : ∀ i : ℕ, f.Filtration ≤ (f.Theta_pow i).Filtration) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ k₀ < ell ∧
      (f.Filtration : ℤ) ≡ -(k₀ : ℤ) [ZMOD ell] ∧
      ∃ s : ℕ → ℕ,
        (∀ i ∈ thetaFiltrationDrops f,
          (f.Theta_pow (i + 1)).Filtration =
            (f.Theta_pow i).Filtration + (ell : ℤ) + 1 -
              (s i : ℤ) * ((ell : ℤ) - 1)) ∧
        (( (f.Filtration : ℤ) ≡ 1 [ZMOD ell] ∧
              thetaFiltrationDrops f = {ell - 1} ∧ s (ell - 1) = ell + 1) ∨
          ( (f.Filtration : ℤ) ≡ 2 [ZMOD ell] ∧
              thetaFiltrationDrops f = {ell - 2} ∧ s (ell - 2) = ell + 1) ∨
          ( ¬ ((f.Filtration : ℤ) ≡ 1 [ZMOD ell]) ∧
              thetaFiltrationDrops f = {k₀, ell - 1} ∧
              s k₀ = k₀ + 1 ∧ s (ell - 1) = ell - k₀) ∨
          ( ¬ ((f.Filtration : ℤ) ≡ 1 [ZMOD ell]) ∧
              ¬ ((f.Filtration : ℤ) ≡ 2 [ZMOD ell]) ∧
              thetaFiltrationDrops f = {k₀, ell - 2} ∧
              s k₀ = k₀ + 2 ∧ s (ell - 2) = ell - k₀ - 1)) := by
  exact theta_filtration_drop_classification f hTheta hnotdiv hminimal

/-! ### Lemma 2 and Proposition 3 -/

/-- Lemma 2: the theta iterates of `Delta^m` have filtration at least `12m`. -/
theorem lemma_two {ell m : ℕ} [isLargePrime ell]
    (hm_pos : 0 < m) (hm_not_divisible : ¬ ell ∣ m) :
    (ModularFormMod.Delta (ℓ := ell)).pow m ≠ 0 ∧
      (∀ i : ℕ, ((ModularFormMod.Delta (ℓ := ell)).pow m).Theta_pow i ≠ 0) ∧
      ((ModularFormMod.Delta (ℓ := ell)).pow m).Filtration = 12 * (m : ℤ) ∧
      ∀ i : ℕ, 12 * (m : ℤ) ≤ (((ModularFormMod.Delta (ℓ := ell)).pow m).Theta_pow i).Filtration := by
  let D : ModularFormMod ell 12 := ModularFormMod.Delta
  have hDorder : PowerSeries.order D.fourier = (1 : ℕ∞) := by
    apply PowerSeries.order_eq_nat.mpr
    constructor
    · change D.coeff 1 ≠ 0
      rw [ModularFormMod.Delta_one]
      exact one_ne_zero
    · intro n hn
      have hn0 : n = 0 := by omega
      subst n
      change D.coeff 0 = 0
      exact ModularFormMod.Delta_zero
  have hpowOrder (j : ℕ) :
      PowerSeries.order ((D.pow j).fourier) = (j : ℕ∞) := by
    rw [ModularFormMod.fourier_pow, PowerSeries.order_pow, hDorder]
    simp
  have hcoeffPowFourier : (D.pow m).fourier.coeff m ≠ 0 :=
    (PowerSeries.order_eq_nat.mp (hpowOrder m)).1
  have hcoeffPow : (D.pow m).coeff m ≠ 0 := by
    simpa only [ModularFormMod.coeff_def] using hcoeffPowFourier
  have hpowNZ : D.pow m ≠ 0 := by
    intro hz
    apply hcoeffPow
    simp [hz]
  have hmcast : (m : ZMod ell) ≠ 0 := by
    intro hz
    exact hm_not_divisible ((ZMod.natCast_eq_zero_iff m ell).mp hz)
  have hthetaNZ (i : ℕ) : (D.pow m).Theta_pow i ≠ 0 := by
    have hcoeff : ((D.pow m).Theta_pow i).coeff m ≠ 0 := by
      rw [ModularFormMod.coeff_Theta_pow]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      exact mul_ne_zero (pow_ne_zero i hmcast) hcoeffPow
    intro hz
    have hzero := congrArg (fun g => g.coeff m) hz
    exact hcoeff (by simpa using hzero)
  have hDfil : D.Filtration = 12 := by
    simpa [D, ModularFormMod.Delta] using (Filt_Delta (ℓ := ell))
  have hpowFil : (D.pow m).Filtration = 12 * (m : ℤ) := by
    calc
      (D.pow m).Filtration = (m : ℤ) * D.Filtration :=
        Filtration_pow D m
      _ = 12 * (m : ℤ) := by rw [hDfil]; ring
  have hbaseZero {n : ℕ} (hn : n < m) : (D.pow m).coeff n = 0 := by
    have horder : (n : ℕ∞) < PowerSeries.order ((D.pow m).fourier) := by
      rw [hpowOrder]
      exact_mod_cast hn
    have hz := PowerSeries.coeff_of_lt_order n horder
    simpa only [ModularFormMod.coeff_def] using hz
  have hbound : ∀ i : ℕ, 12 * (m : ℤ) ≤ ((D.pow m).Theta_pow i).Filtration := by
    intro i
    let T := (D.pow m).Theta_pow i
    haveI : NeZero T := ⟨by simpa [T] using hthetaNZ i⟩
    have hvanish : ∀ n < m, T.coeff n = 0 := by
      intro n hn
      rw [ModularFormMod.coeff_Theta_pow, hbaseZero hn]
      simp
    have hfil := ModularFormMod.le_Filtration (p := m) T hvanish
    simpa [T] using hfil
  refine ⟨hpowNZ, hthetaNZ, hpowFil, hbound⟩

/-- Proposition 3 at a minimum of a theta filtration cycle. Apply this to
the reduction of `f^r` for the paper's formulation with powers. -/
theorem proposition_three {ell : ℕ} [isLargePrime ell] {k : ZMod (ell - 1)}
    (f : ModularFormMod ell k) (a : ℕ) (ha : 0 < a) (ha_lt : a < ell)
    (hTheta : f.Theta ≠ 0) (hfiltration : ¬ (ell : ℤ) ∣ f.Filtration)
    (hminimal : ∀ i : ℕ, f.Filtration ≤ (f.Theta_pow i).Filtration)
    (hcong : ∀ n : ℕ, f.coeff (ell * n + a) = 0) :
    f.Filtration ≡ (((ell + 1) / 2 : ℕ) : ℤ) [ZMOD ell] ∨
      f.Filtration ≡ (((ell + 3) / 2 : ℕ) : ℤ) [ZMOD ell] :=
  proposition_three_modular f a ha ha_lt hTheta hfiltration hminimal hcong

/-! ### Theorem 3: the theta-filtration obstruction -/

/--
Theorem 3 of Kiming--Olsson, stated for the mod-`ell` discriminant form in
`ModularFormMod`.  The hypothesis is Proposition 1's shifted theta identity
for `Delta^m`.
-/
theorem theorem_three {ell m a : ℕ} [isLargePrime ell]
    (hm_pos : 0 < m) (hm_lt : m < ell) (ha : a < ell)
    (hm_not_one : ¬ (24 * m ≡ 1 [MOD ell]))
    (hm_not_three : ¬ (24 * m ≡ 3 [MOD ell]))
    (hidentity : shiftedThetaIdentity
      ((ModularFormMod.Delta (ℓ := ell)).pow m) a) :
    a = 0 ∧
      ∀ m₀ : ℕ, 0 < m₀ → m₀ < ell →
        12 * m ≡ m₀ [MOD ell] → m₀ ≤ (ell + 3) / 2 := by
  let F := (ModularFormMod.Delta (ℓ := ell)).pow m
  have hm_not_div : ¬ ell ∣ m := by
    intro hd
    have hle : ell ≤ m := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨hFne, hFiter, hFfil, hFbound⟩ := lemma_two hm_pos hm_not_div
  have hFtheta : F.Theta ≠ 0 := by
    intro hz
    have hzPow : F.Theta_pow 1 = 0 := by
      rw [ModularFormMod.Theta_pow_one, hz, ModularFormMod.Mcast_zero]
    exact hFiter 1 hzPow
  have hFfilne : F.Filtration ≠ 0 := by
    rw [hFfil]
    positivity
  have hnotdiv12 : ¬ (ell : ℤ) ∣ (12 : ℤ) := by
    intro hd
    have hpdiv : ell ∣ 12 := by exact_mod_cast hd
    rw [show 12 = 3 * 4 by norm_num] at hpdiv
    rcases (inferInstance : isLargePrime ell).Prime.dvd_mul.mp hpdiv with h3 | h4
    · have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h3
      have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
      omega
    · have h4' : 4 = 2 * 2 := by norm_num
      rw [h4'] at h4
      rcases (inferInstance : isLargePrime ell).Prime.dvd_mul.mp h4 with h2 | h2
      · have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2
        have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
        omega
      · have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2
        have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
        omega
  have hFnotdiv : ¬ (ell : ℤ) ∣ F.Filtration := by
    rw [hFfil]
    intro hdiv
    have hnat : ell ∣ 12 * m := by exact_mod_cast hdiv
    rcases (inferInstance : isLargePrime ell).Prime.dvd_mul.mp hnat with h12 | hm
    · exact hnotdiv12 (by exact_mod_cast h12)
    · exact hm_not_div hm
  obtain ⟨k₀, hk₀pos, hk₀lt, hk₀mod, ⟨s, hs, hcases⟩⟩ :=
    proposition_two F hFtheta hFfilne hFnotdiv (by intro i; rw [hFfil]; exact hFbound i)

  have hcong := (proposition_one_modular F a ha).2 hidentity
  have haeq : a = 0 := by
    by_contra hne
    have hapos : 0 < a := Nat.pos_of_ne_zero hne
    have hres :
        (12 : ℤ) * (m : ℤ) ≡ (((ell + 1) / 2 : ℕ) : ℤ) [ZMOD ell] ∨
        (12 : ℤ) * (m : ℤ) ≡ (((ell + 3) / 2 : ℕ) : ℤ) [ZMOD ell] := by
      have h := proposition_three F a hapos ha hFtheta hFnotdiv
        (by intro i; rw [hFfil]; exact hFbound i) hcong
      grw [hFfil] at h
      exact h
    have hellodd : Odd ell :=
      (Nat.Prime.odd_iff (inferInstance : isLargePrime ell).Prime).mpr (by
        have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
        omega)
    rcases hellodd with ⟨t, ht⟩
    have hdiv1 : 2 ∣ ell + 1 := ⟨t + 1, by omega⟩
    have hdiv3 : 2 ∣ ell + 3 := ⟨t + 2, by omega⟩
    have hhalf1 : 2 * ((ell + 1) / 2) = ell + 1 := Nat.mul_div_cancel' hdiv1
    have hhalf3 : 2 * ((ell + 3) / 2) = ell + 3 := Nat.mul_div_cancel' hdiv3
    have hplus1 : ((ell + 1 : ℕ) : ℤ) ≡ 1 [ZMOD ell] := by
      rw [Int.modEq_iff_dvd]
      have heq : (1 : ℤ) - ((ell + 1 : ℕ) : ℤ) = -(ell : ℤ) := by
        push_cast
        omega
      rw [heq]
      exact dvd_neg.mpr (dvd_refl (ell : ℤ))
    have hplus3 : ((ell + 3 : ℕ) : ℤ) ≡ 3 [ZMOD ell] := by
      rw [Int.modEq_iff_dvd]
      have heq : (3 : ℤ) - ((ell + 3 : ℕ) : ℤ) = -(ell : ℤ) := by
        push_cast
        omega
      rw [heq]
      exact dvd_neg.mpr (dvd_refl (ell : ℤ))
    rcases hres with hres | hres
    · have hdouble := hres.mul_left 2
      have hleft : ((24 * m : ℕ) : ℤ) = 2 * ((12 : ℤ) * (m : ℤ)) := by
        push_cast
        ring
      have hright : (2 : ℤ) * (((ell + 1) / 2 : ℕ) : ℤ) =
          ((ell + 1 : ℕ) : ℤ) := by exact_mod_cast hhalf1
      rw [← hleft, hright] at hdouble
      have hInt : ((24 * m : ℕ) : ℤ) ≡ 1 [ZMOD ell] := hdouble.trans hplus1
      have hZ : ((24 * m : ℕ) : ZMod ell) = ((1 : ℕ) : ZMod ell) := by
        exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 hInt
      have hNat : 24 * m ≡ 1 [MOD ell] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hZ
      exact (hm_not_one hNat).elim
    · have hdouble := hres.mul_left 2
      have hleft : ((24 * m : ℕ) : ℤ) = 2 * ((12 : ℤ) * (m : ℤ)) := by
        push_cast
        ring
      have hright : (2 : ℤ) * (((ell + 3) / 2 : ℕ) : ℤ) =
          ((ell + 3 : ℕ) : ℤ) := by exact_mod_cast hhalf3
      rw [← hleft, hright] at hdouble
      have hInt : ((24 * m : ℕ) : ℤ) ≡ 3 [ZMOD ell] := hdouble.trans hplus3
      have hZ : ((24 * m : ℕ) : ZMod ell) = ((3 : ℕ) : ZMod ell) := by
        exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 hInt
      have hNat : 24 * m ≡ 3 [MOD ell] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hZ
      exact (hm_not_three hNat).elim
  refine ⟨haeq, ?_⟩
  · subst a
    intro m₀ hm₀pos hm₀lt hm₀mod
    have hfilEq : (F.Theta_pow (ell - 1)).Filtration = F.Filtration := by
      apply ModularFormMod.Filtration_ext
      intro n
      change shiftedThetaSeries F 0 = F.fourier at hidentity
      have hcoef := congrArg (fun q : PowerSeries (ZMod ell) => q.coeff n) hidentity
      have hcoef' : ((n : ZMod ell) ^ (ell - 1)) * F.coeff n = F.coeff n := by
        simpa [shiftedThetaSeries, ModularFormMod.coeff_def, F,
          ModularFormMod.fourier_pow] using hcoef
      rw [ModularFormMod.coeff_Theta_pow]
      simpa only [nsmul_eq_mul, Nat.cast_pow] using hcoef'
    have hfilzero : ¬ (ell : ℤ) ∣ F.Filtration := by
      intro hdiv
      have hcast : (F.Filtration : ZMod ell) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd F.Filtration ell).2 hdiv
      have hneg : (k₀ : ZMod ell) = 0 := by
        have hmod := hk₀mod
        rw [← ZMod.intCast_eq_intCast_iff] at hmod
        simpa [hcast] using hmod
      have hkdvd : ell ∣ k₀ := (ZMod.natCast_eq_zero_iff _ _).mp hneg
      have hkle : ell ≤ k₀ := Nat.le_of_dvd (by omega) hkdvd
      omega
    have hstep0 : (F.Theta_pow 1).Filtration =
        F.Filtration + (ell : ℤ) + 1 := by
      have hstep := (Filt_Theta_iff F).2 hfilzero
      simpa only [ModularFormMod.Theta_pow_one, ModularFormMod.Filtration_Mcast,
        add_assoc] using hstep
    have hlast : (F.Theta_pow ell).Filtration = (F.Theta_pow 1).Filtration := by
      rw [ModularFormMod.Theta_pow_l, ModularFormMod.Theta_pow_one]
      rfl
    have hlastdrop : ell - 1 ∉ thetaFiltrationDrops F := by
      intro hmem
      have hdiv : (ell : ℤ) ∣ (F.Theta_pow (ell - 1)).Filtration := by
        exact (Finset.mem_filter.mp hmem).2
      have hidx : ell = ell - 1 + 1 := by omega
      have hstrict : (F.Theta_pow ell).Filtration <
          (F.Theta_pow (ell - 1)).Filtration + (ell : ℤ) + 1 := by
        have hbound := Filt_Theta_bound' F hidx
        have hneq : (F.Theta_pow ell).Filtration ≠
            (F.Theta_pow (ell - 1)).Filtration + ((ell : ℤ) + 1) := by
          intro heq
          exact (Filt_Theta_iff' F hidx).1 heq hdiv
        simpa [add_assoc] using lt_of_le_of_ne hbound hneq
      rw [hlast, hstep0, hfilEq] at hstrict
      omega
    rcases hcases with hcase1 | hcase2 | hcase3 | hcase4
    · have hmem : ell - 1 ∈ thetaFiltrationDrops F := by
        rw [hcase1.2.1]
        simp
      exact (hlastdrop hmem).elim
    · have hmod2 : (12 * m) ≡ 2 [MOD ell] := by
        have hfilmod := hcase2.1
        rw [hFfil] at hfilmod
        exact_mod_cast hfilmod
      have hm0eq : m₀ = 2 := by
        have hmod := hm₀mod.symm.trans hmod2
        have h2lt : 2 < ell := by
          have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
          omega
        unfold Nat.ModEq at hmod
        rw [Nat.mod_eq_of_lt hm₀lt, Nat.mod_eq_of_lt h2lt] at hmod
        exact hmod
      rw [hm0eq]
      omega
    · have hmem : ell - 1 ∈ thetaFiltrationDrops F := by
        rw [hcase3.2.1]
        simp
      exact (hlastdrop hmem).elim
    · have hklt : k₀ < ell - 2 := by
        by_contra hnot
        have hle : ell - 2 ≤ k₀ := by omega
        by_cases hkeq : k₀ = ell - 2
        · have hs₁ := hcase4.2.2.2.1
          have hs₂ := hcase4.2.2.2.2
          rw [hkeq] at hs₁ hs₂
          omega
        · have hkeq' : k₀ = ell - 1 := by omega
          have hmem : ell - 1 ∈ thetaFiltrationDrops F := by
            rw [hcase4.2.2.1]
            simp [hkeq']
          exact (hlastdrop hmem).elim
      have hlinear : ∀ i ≤ k₀, (F.Theta_pow i).Filtration =
          F.Filtration + (i : ℤ) * ((ell : ℤ) + 1) := by
        intro i hi
        induction i with
        | zero => simp
        | succ i ih =>
          have hil : i < k₀ := by omega
          have hnotdrop : i ∉ thetaFiltrationDrops F := by
            intro hmem
            have hdecomp := hcase4.2.2.1
            have hi' : i ∈ ({k₀, ell - 2} : Finset ℕ) := by simpa [hdecomp] using hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
            omega
          have hdiv : ¬ (ell : ℤ) ∣ (F.Theta_pow i).Filtration := by
            by_cases hi0 : i = 0
            · subst i
              simpa only [ModularFormMod.Theta_pow_zero,
                ModularFormMod.Filtration_Mcast] using hfilzero
            · intro hdv
              apply hnotdrop
              have hiIcc : i ∈ Finset.Icc 1 (ell - 1) := by
                simp only [Finset.mem_Icc]
                constructor <;> omega
              exact Finset.mem_filter.mpr ⟨hiIcc, hdv⟩
          have hstep := (Filt_Theta_iff' F rfl).2 hdiv
          rw [hstep, ih (by omega)]
          push_cast
          ring
      have hkformula : (F.Theta_pow (k₀ + 1)).Filtration =
          F.Filtration + (k₀ : ℤ) * ((ell : ℤ) + 1) +
            (ell : ℤ) + 1 - ((k₀ + 2 : ℕ) : ℤ) * ((ell : ℤ) - 1) := by
        have hdropmem : k₀ ∈ thetaFiltrationDrops F := by
          have hdecomp := hcase4.2.2.1
          have hk : k₀ ∈ ({k₀, ell - 2} : Finset ℕ) := by simp
          rw [← hdecomp] at hk
          exact hk
        have hdiv := (Finset.mem_filter.mp hdropmem).2
        haveI : NeZero (F.Theta_pow (k₀ + 1)) := ⟨hFiter (k₀ + 1)⟩
        obtain ⟨s₀, hs₀pos, hs₀⟩ := Filt_Theta_congruence_of_dvd' F hdiv rfl
        have hsPaper := hs k₀ hdropmem
        have hmult : s₀ * ((ell : ℤ) - 1) =
            (s k₀ : ℤ) * ((ell : ℤ) - 1) := by
          linarith [hs₀, hsPaper]
        have hfac : (ell : ℤ) - 1 ≠ 0 := by
          have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
          omega
        have hs₀eq : s₀ = (s k₀ : ℤ) := mul_right_cancel₀ hfac hmult
        have hs₀' : s₀ = (k₀ + 2 : ℕ) := by
          rw [hs₀eq]
          exact_mod_cast hcase4.2.2.2.1
        rw [hs₀, hs₀']
        rw [hlinear k₀ (le_rfl)]
        ring_nf
      have hlower := hFbound (k₀ + 1)
      rw [hkformula, hFfil] at hlower
      have hcalc : (12 : ℤ) * (m : ℤ) + (k₀ : ℤ) * ((ell : ℤ) + 1) +
          (ell : ℤ) + 1 - ((k₀ + 2 : ℕ) : ℤ) * ((ell : ℤ) - 1) =
          12 * (m : ℤ) + 2 * (k₀ : ℤ) - (ell : ℤ) + 3 := by
        simp only [Nat.cast_add, Nat.cast_ofNat]
        ring
      rw [hcalc] at hlower
      have hkbound : (ell : ℤ) - 3 ≤ 2 * (k₀ : ℤ) := by
        linarith [hlower]
      have hm0class : m₀ + k₀ = ell := by
        have hFilMod : (F.Filtration : ℤ) ≡ -(k₀ : ℤ) [ZMOD ell] := hk₀mod
        have hm0Int : (12 * (m : ℕ) : ℤ) ≡ (m₀ : ℤ) [ZMOD ell] := by
          exact_mod_cast hm₀mod
        have hm0F : F.Filtration ≡ (m₀ : ℤ) [ZMOD ell] := by
          rw [hFfil]
          exact hm0Int
        have hsumMod : (m₀ : ℤ) + (k₀ : ℤ) ≡ 0 [ZMOD ell] := by
          calc
            (m₀ : ℤ) + (k₀ : ℤ) ≡ F.Filtration + (k₀ : ℤ) [ZMOD ell] := by
              exact hm0F.symm.add_right (k₀ : ℤ)
            _ ≡ 0 [ZMOD ell] := by
              simpa using hFilMod.add_right (k₀ : ℤ)
        have hdiv : (ell : ℤ) ∣ (m₀ : ℤ) + (k₀ : ℤ) :=
          Int.modEq_zero_iff_dvd.mp hsumMod
        have hboundSum : 0 < (m₀ : ℤ) + (k₀ : ℤ) ∧
            (m₀ : ℤ) + (k₀ : ℤ) < 2 * ell := by omega
        rcases hdiv with ⟨c, hc⟩
        have hcpos : 0 < c := by nlinarith
        have hclt : c < 2 := by nlinarith
        interval_cases c <;> omega
      have hkboundNat : ell - 3 ≤ 2 * k₀ := by
        have hell3 : 3 ≤ ell := by
          have hlarge := (inferInstance : isLargePrime ell).AtLeastFive
          omega
        have hboundInt : ((ell - 3 : ℕ) : ℤ) ≤ ((2 * k₀ : ℕ) : ℤ) := by
          rw [Int.natCast_sub hell3]
          exact hkbound
        exact_mod_cast hboundInt
      omega

end KOl
