import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.SwD.PIntegralModularForm.Basic
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Basis

/-!
# A basis for p-integral modular forms

The triangular family `G` is obtained by transporting the family from
`IntegerModularForm.Basis` to the p-local coefficient ring. The assumption
`isLargePrime p` is the standing hypothesis in the SwD development.
-/

open ModularForm MatrixGroups UpperHalfPlane PowerSeries

namespace PIntegralModularForm

noncomputable section

variable {p : ℕ} [isLargePrime p] {k : ℤ}

/-- 1728 is invertible in the p-local coefficient ring for the primes in the
SwD development. -/
theorem isUnit_algebraMap_1728 : IsUnit (algebraMap ℤ (CoeffRing p) (1728 : ℤ)) := by
  have hnot : (1728 : ℤ) ∉ primeIdeal p := by
    intro hmem
    have hdivInt : (p : ℤ) ∣ (1728 : ℤ) := by
      rw [← Ideal.mem_span_singleton]
      exact hmem
    have hdiv : p ∣ 1728 := Int.natCast_dvd_natCast.mp hdivInt
    have hp := (inferInstance : isLargePrime p).Prime
    have hp5 := (inferInstance : isLargePrime p).AtLeastFive
    have hfac : 1728 = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [hfac] at hdiv
    rcases hp.dvd_mul.mp hdiv with h2 | h3
    · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
      have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) h2
      omega
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
      have hp_le : p ≤ 3 := Nat.le_of_dvd (by decide) h3
      omega
  exact IsLocalization.map_units (M := (primeIdeal p).primeCompl) (CoeffRing p)
    ⟨1728, hnot⟩

private theorem integer_E4_cube_sub_E6_sq :
    (1728 : ℤ) • IntegerModularForm.Delta =
      ((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num) -
        ((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num) := by
  apply IntegerModularForm.carrier_inj
  have h4n : Even (4 : ℕ) := ⟨2, by norm_num⟩
  have h6n : Even (6 : ℕ) := ⟨3, by norm_num⟩
  have hB5 : bernoulli' 5 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have hB6 : bernoulli' 6 = (1 / 42 : ℚ) := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four, hB5]
  have hE4 : (IntegerModularForm.Eis 4).carrier =
      ModularForm.E (by norm_num : 3 ≤ 4) := by
    apply ModularForm.qexp_injective
    rw [(IntegerModularForm.Eis 4).carrier_eq]
    ext n
    rw [ModularForm.qexp_eq']
    change ((IntegerModularForm.Eis 4).coeff n : ℂ) = _
    rw [IntegerModularForm.coeff_Eis_four,
      EisensteinSeries.E_qExpansion_coeff (by norm_num) h4n]
    split_ifs with hn <;> norm_num [bernoulli, bernoulli'_four]
  have hE6 : (IntegerModularForm.Eis 6).carrier =
      ModularForm.E (by norm_num : 3 ≤ 6) := by
    apply ModularForm.qexp_injective
    rw [(IntegerModularForm.Eis 6).carrier_eq]
    ext n
    rw [ModularForm.qexp_eq']
    change ((IntegerModularForm.Eis 6).coeff n : ℂ) = _
    rw [IntegerModularForm.coeff_Eis_six,
      EisensteinSeries.E_qExpansion_coeff (by norm_num) h6n]
    split_ifs with hn <;> norm_num [bernoulli, hB6]
  ext z
  simp [IntegerModularForm.Delta]
  change (1728 : ℂ) * ModularForm.discriminant z =
    ((IntegerModularForm.Eis 4) z) ^ 3 - ((IntegerModularForm.Eis 6) z) ^ 2
  have hE4z : (IntegerModularForm.Eis 4) z =
      ModularForm.E (by norm_num : 3 ≤ 4) z := by
    simpa only [IntegerModularForm.coe_def] using congrArg (fun f => f z) hE4
  have hE6z : (IntegerModularForm.Eis 6) z =
      ModularForm.E (by norm_num : 3 ≤ 6) z := by
    simpa only [IntegerModularForm.coe_def] using congrArg (fun f => f z) hE6
  rw [hE4z, hE6z, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

/-- Transport of multiplication through `ofInteger`. -/
theorem ofInteger_mul {k j : ℤ} (f : IntegerModularForm k) (g : IntegerModularForm j) :
    (ofInteger (p := p) f).mul (ofInteger (p := p) g) =
      ofInteger (p := p) (f.mul g) := by
  apply PIntegralModularForm.ext
  intro n
  simp [coeff_ofInteger, PIntegralModularForm.coeff_mul,
    IntegerModularForm.coeff_mul, map_sum, map_mul]

/-- Transport of natural powers through `ofInteger`. -/
theorem ofInteger_pow {k : ℤ} (f : IntegerModularForm k) (n : ℕ) :
    (ofInteger (p := p) f).pow n = ofInteger (p := p) (f.pow n) := by
  apply PIntegralModularForm.ext
  intro m
  simp [coeff_ofInteger, PIntegralModularForm.coeff_pow,
    IntegerModularForm.coeff_pow, map_sum, map_prod]

@[simp]
theorem coeff_zsmul (z : ℤ) (f : PIntegralModularForm p k) (n : ℕ) :
    (z • f).coeff n = z • f.coeff n := by
  change ((z : CoeffRing p) • f.fourier).coeff n = z • f.fourier.coeff n
  rw [PowerSeries.coeff_smul]
  exact Int.cast_smul_eq_zsmul (CoeffRing p) z (f.fourier.coeff n)

@[simp]
theorem fourier_zsmul (z : ℤ) (f : PIntegralModularForm p k) :
    (z • f).fourier = z • f.fourier := by
  change (z : CoeffRing p) • f.fourier = z • f.fourier
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_smul, zsmul_eq_mul,
    PowerSeries.coeff_intCast_mul, smul_eq_mul]

/-- Transport of integer scalar multiplication through `ofInteger`. -/
theorem ofInteger_zsmul {k : ℤ} (z : ℤ) (f : IntegerModularForm k) :
    z • ofInteger (p := p) f = ofInteger (p := p) (z • f) := by
  apply PIntegralModularForm.ext
  intro n
  simp [coeff_ofInteger, coeff_zsmul, IntegerModularForm.coeff_smulz]

/-- Change the weight index along a proof of equality. -/
def castWeight {k j : ℤ} (h : k = j) (f : PIntegralModularForm p k) :
    PIntegralModularForm p j where
  fourier := f.fourier
  carrier := ModularForm.mcast h f.carrier
  carrier_eq := by subst h; exact f.carrier_eq

@[simp]
theorem coeff_castWeight {k j : ℤ} (h : k = j) (f : PIntegralModularForm p k) (n : ℕ) :
    (castWeight h f).coeff n = f.coeff n := rfl

theorem ofInteger_sub {k : ℤ} (f g : IntegerModularForm k) :
    ofInteger (p := p) (f - g) = ofInteger (p := p) f - ofInteger (p := p) g := by
  apply PIntegralModularForm.ext
  intro n
  change algebraMap ℤ (CoeffRing p) (IntegerModularForm.coeff n (f - g)) =
    (ofInteger (p := p) f + -ofInteger (p := p) g).coeff n
  simp [IntegerModularForm.coeff_sub, coeff_ofInteger,
    PIntegralModularForm.coeff_add, PIntegralModularForm.coeff_neg]
  ring

theorem ofInteger_castWeight {k j : ℤ} (h : k = j) (f : IntegerModularForm k) :
    castWeight h (ofInteger (p := p) f) =
      ofInteger (p := p) (IntegerModularForm.Icast h f) := by
  apply PIntegralModularForm.ext
  intro n
  simp [coeff_ofInteger]

theorem delta_relation :
    (1728 : ℤ) • Delta (p := p) =
      castWeight (by norm_num : 3 * (4 : ℤ) = 12) ((Eis (p := p) 4).pow 3) -
      castWeight (by norm_num : 2 * (6 : ℤ) = 12) ((Eis (p := p) 6).pow 2) := by
  change (1728 : ℤ) • ofInteger (p := p) IntegerModularForm.Delta = _
  rw [ofInteger_zsmul]
  have hcast4 : castWeight (by norm_num : 3 * (4 : ℤ) = 12)
      ((Eis (p := p) 4).pow 3) =
      ofInteger (p := p) (((IntegerModularForm.Eis 4).pow 3).Icast (by norm_num)) := by
    rw [Eis, ofInteger_pow, ofInteger_castWeight]
  have hcast6 : castWeight (by norm_num : 2 * (6 : ℤ) = 12)
      ((Eis (p := p) 6).pow 2) =
      ofInteger (p := p) (((IntegerModularForm.Eis 6).pow 2).Icast (by norm_num)) := by
    rw [Eis, ofInteger_pow, ofInteger_castWeight]
  rw [hcast4, hcast6, ← ofInteger_sub]
  exact congrArg (ofInteger (p := p)) integer_E4_cube_sub_E6_sq

/-- Nonnegative exponent pairs whose E4/E6 monomial has weight `k`. -/
def E4E6Exponent (k : ℤ) :=
  { ab : ℕ × ℕ // 4 * (ab.1 : ℤ) + 6 * (ab.2 : ℤ) = k }

/-- The weight-`k` monomial `E4^a * E6^b`, indexed by its exponent pair. -/
noncomputable def E4E6Monomial {k : ℤ} (e : E4E6Exponent k) :
    PIntegralModularForm p k := by
  have hw : (e.1.1 : ℤ) * 4 + (e.1.2 : ℤ) * 6 = k := by
    nlinarith [e.2]
  exact castWeight hw (((Eis (p := p) 4).pow e.1.1).mul
    ((Eis (p := p) 6).pow e.1.2))

theorem E4E6Monomial_eq {k : ℤ} (e : E4E6Exponent k) :
    E4E6Monomial (p := p) e =
      castWeight (by
        have h := e.2
        nlinarith [h]) (((Eis (p := p) 4).pow e.1.1).mul
        ((Eis (p := p) 6).pow e.1.2)) := by
  unfold E4E6Monomial
  congr 1

/-- The E4 exponent in the low-weight generator of a residue class. -/
def e4BaseExponent (r : ℤ) : ℕ :=
  if r = 4 then 1 else if r = 8 ∨ r = 14 then 2 else if r = 10 then 1 else 0

/-- The E6 exponent in the low-weight generator of a residue class. -/
def e6BaseExponent (r : ℤ) : ℕ :=
  if r = 6 ∨ r = 10 ∨ r = 14 then 1 else 0

/-- The standard E4/E6 monomial at triangular index `c`. -/
noncomputable def pExponent {k : ℤ} (c : Fin (dim k)) : E4E6Exponent k := by
  let r : ℤ := k %% 12
  let s : ℤ := k - r
  let q : ℕ := s.toNat / 4
  let a : ℕ := e4BaseExponent r + (q - 3 * c.1)
  let b : ℕ := e6BaseExponent r + 2 * c.1
  have hdim : 0 < dim k := Nat.zero_lt_of_lt c.2
  have hkEven : Even k := by
    have h := hdim
    simp only [dim] at h
    split_ifs at h <;> simp_all
  have hrem : r ∈ ({0, 4, 6, 8, 10, 14} : Set ℤ) := by
    dsimp [r]
    exact IntegerModularForm.of_dim_pos k hdim
  have hbase : 4 * (e4BaseExponent r : ℤ) + 6 * (e6BaseExponent r : ℤ) = r := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hrem
    rcases hrem with h | h | h | h | h | h
    all_goals rw [h] <;> norm_num [e4BaseExponent, e6BaseExponent]
  have hsnonneg : 0 ≤ s := by
    have hdimS : dim s = dim k := IntegerModularForm.dim_sub_mod_without_two k hkEven
    have hposS : 0 < dim s := by rw [hdimS]; exact hdim
    rw [dim] at hposS
    split_ifs at hposS <;> omega
  have hdiv : 4 ∣ s := by
    have h12 := IntegerModularForm.dvd_sub_mod_without_two k
    dsimp [s, r]
    exact dvd_trans (by norm_num) h12
  have hqmul : 4 * q = s.toNat := by
    dsimp [q]
    have hdivNat : 4 ∣ s.toNat := by
      have hcast : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hsnonneg
      have hdiv' : (4 : ℤ) ∣ (s.toNat : ℤ) := by simpa [hcast] using hdiv
      exact_mod_cast hdiv'
    omega
  have hdimS : dim s = dim k := IntegerModularForm.dim_sub_mod_without_two k hkEven
  have hcS : c.1 < dim s := by rw [hdimS]; exact c.2
  have hqbound : 3 * c.1 ≤ q := by
    have hmodS : s % 12 = 0 := by
      have h12 := IntegerModularForm.dvd_sub_mod_without_two k
      have hs : 12 ∣ s := by simpa [s, r] using h12
      have hm := Int.modEq_zero_iff_dvd.mpr hs
      rw [Int.ModEq] at hm
      simpa using hm
    have hsNat : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hsnonneg
    have hmodNat : s.toNat % 12 = 0 := by omega
    have hsEven : Even s := by
      obtain ⟨t, ht⟩ := hdiv
      refine ⟨2 * t, ?_⟩
      omega
    have hnotTwo : ¬ s ≡ 2 [ZMOD 12] := by
      intro hcon
      rw [Int.ModEq] at hcon
      simp [hmodS] at hcon
    have hdimFormula : dim s = s.toNat / 12 + 1 := by
      rw [dim]
      simp [hsnonneg, hsEven, hnotTwo]
    rw [hdimFormula] at hcS
    have hcBound : c.1 ≤ s.toNat / 12 := by omega
    have hqFormula : q = 3 * (s.toNat / 12) := by omega
    omega
  have hsub : (q - 3 * c.1) + 3 * c.1 = q := Nat.sub_add_cancel hqbound
  have ha : (a : ℤ) = (e4BaseExponent r : ℤ) + q - 3 * c.1 := by
    dsimp [a]
    simp only [Nat.cast_add, Nat.cast_sub hqbound, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hb : (b : ℤ) = (e6BaseExponent r : ℤ) + 2 * c.1 := by
    dsimp [b]
  have hweight : 4 * (a : ℤ) + 6 * (b : ℤ) = k := by
    rw [ha, hb]
    have hqint : 4 * ((s.toNat / 4 : ℕ) : ℤ) = s := by
      rw [← Int.toNat_of_nonneg hsnonneg]
      exact_mod_cast hqmul
    dsimp [r, s] at hbase ⊢
    nlinarith [hbase, hqint]
  exact ⟨(a, b), hweight⟩

/-- The requested E4/E6 monomial family indexed by the triangular basis index. -/
noncomputable def PMonomial {k : ℤ} (c : Fin (dim k)) : PIntegralModularForm p k :=
  E4E6Monomial (p := p) (pExponent c)

@[simp]
theorem pExponent_fst {k : ℤ} (c : Fin (dim k)) :
    (pExponent c).1.1 = e4BaseExponent (k %% 12) +
      ((k - (k %% 12)).toNat / 4 - 3 * c.1) := by
  simp [pExponent]

@[simp]
theorem pExponent_snd {k : ℤ} (c : Fin (dim k)) :
    (pExponent c).1.2 = e6BaseExponent (k %% 12) + 2 * c.1 := by
  simp [pExponent]

/-! The triangular indexing used by `pExponent` lists every nonnegative
solution of the weight equation. -/

theorem pExponent_surjective {k : ℤ} :
    Function.Surjective (pExponent (k := k)) := by
  intro e
  change {ab : ℕ × ℕ // 4 * (ab.1 : ℤ) + 6 * (ab.2 : ℤ) = k} at e
  rcases e with ⟨⟨a, b⟩, hab⟩
  change 4 * (a : ℤ) + 6 * (b : ℤ) = k at hab
  have hk_nonneg : 0 ≤ k := by nlinarith
  have hk_even : Even k := by
    refine ⟨2 * (a : ℤ) + 3 * (b : ℤ), ?_⟩
    nlinarith [hab]
  have hk_ne_two : k ≠ 2 := by
    intro h
    rw [h] at hab
    omega
  have hkmod : k ≡ 2 [ZMOD 12] → 14 ≤ k := by
    intro h
    rw [Int.ModEq] at h
    omega
  have hdim : 0 < dim k := by
    simp only [dim, if_pos hk_nonneg, if_pos hk_even]
    by_cases hmod : k ≡ 2 [ZMOD 12]
    · have hnat : 12 ≤ k.toNat := by
        have hk14 := hkmod hmod
        have hk12 : (12 : ℤ) ≤ k := by omega
        have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
        have hnatInt : (12 : ℤ) ≤ (k.toNat : ℤ) := by rw [hkcast]; exact hk12
        exact_mod_cast hnatInt
      simp only [if_pos hmod]
      exact Nat.div_pos hnat (by norm_num)
    · simp only [if_neg hmod]
      exact Nat.zero_lt_succ _
  let r : ℤ := k %% 12
  have hr : r ∈ ({0, 4, 6, 8, 10, 14} : Set ℤ) := by
    exact IntegerModularForm.of_dim_pos k hdim
  have hr_le : r ≤ k := by
    dsimp [r, IntegerModularForm.mod_without_two]
    split_ifs with hmod
    · have hk14 := hkmod hmod
      have hrem := Int.emod_lt k (by norm_num : (12 : ℤ) ≠ 0)
      omega
    · have hrem := Int.emod_nonneg k (by norm_num : (12 : ℤ) ≠ 0)
      have hrem' := Int.emod_lt k (by norm_num : (12 : ℤ) ≠ 0)
      omega
  have hdiv : 12 ∣ k - r := by
    dsimp [r]
    exact IntegerModularForm.dvd_sub_mod_without_two k
  obtain ⟨nZ, hnZ⟩ := hdiv
  have hnZ_nonneg : 0 ≤ nZ := by
    have : 0 ≤ k - r := by omega
    nlinarith [hnZ]
  let n : ℕ := nZ.toNat
  have hnZ_cast : (n : ℤ) = nZ := by
    simp [n, Int.toNat_of_nonneg hnZ_nonneg]
  have hkdecomp : k = r + 12 * (n : ℤ) := by
    have h := hnZ
    omega
  have hsubNat : (k - r).toNat = 12 * n := by
    have hsubInt : ((k - r).toNat : ℤ) = 12 * (n : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ k - r), hnZ, hnZ_cast]
    exact_mod_cast hsubInt
  have hq : (k - r).toNat / 4 = 3 * n := by
    rw [hsubNat]
    omega
  have hr' := hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr'
  have hr_nonneg : 0 ≤ r := by
    rcases hr' with h0 | h4 | h6 | h8 | h10 | h14 <;> omega
  have hkNat : k.toNat = r.toNat + 12 * n := by
    have hkNatInt : (k.toNat : ℤ) = (r.toNat : ℤ) + 12 * (n : ℤ) := by
      rw [Int.toNat_of_nonneg hk_nonneg, Int.toNat_of_nonneg hr_nonneg]
      exact hkdecomp
    exact_mod_cast hkNatInt
  have hclass : (k ≡ 2 [ZMOD 12]) ↔ r = 14 := by
    rcases hr' with h0 | h4 | h6 | h8 | h10 | h14
    · rw [h0]
      constructor
      · intro h
        rw [Int.ModEq] at h
        omega
      · norm_num
    · rw [h4]
      constructor
      · intro h
        rw [Int.ModEq] at h
        omega
      · norm_num
    · rw [h6]
      constructor
      · intro h
        rw [Int.ModEq] at h
        omega
      · norm_num
    · rw [h8]
      constructor
      · intro h
        rw [Int.ModEq] at h
        omega
      · norm_num
    · rw [h10]
      constructor
      · intro h
        rw [Int.ModEq] at h
        omega
      · norm_num
    · rw [h14]
      constructor
      · intro _
        rfl
      · intro _
        rw [Int.ModEq]
        omega
  have hdim_formula : dim k = n + 1 := by
    rcases hr' with h0 | h4 | h6 | h8 | h10 | h14
    · simp [dim, hk_nonneg, hk_even, hclass, hkNat, h0] <;> omega
    · simp [dim, hk_nonneg, hk_even, hclass, hkNat, h4] <;> omega
    · simp [dim, hk_nonneg, hk_even, hclass, hkNat, h6] <;> omega
    · simp [dim, hk_nonneg, hk_even, hclass, hkNat, h8] <;> omega
    · simp [dim, hk_nonneg, hk_even, hclass, hkNat, h10] <;> omega
    · simp [dim, hk_nonneg, hk_even, hclass, hkNat, h14] <;> omega
  have hbase :
      4 * (e4BaseExponent r : ℤ) + 6 * (e6BaseExponent r : ℤ) = r := by
    rcases hr' with h0 | h4 | h6 | h8 | h10 | h14
    · rw [h0]; norm_num [e4BaseExponent, e6BaseExponent]
    · rw [h4]; norm_num [e4BaseExponent, e6BaseExponent]
    · rw [h6]; norm_num [e4BaseExponent, e6BaseExponent]
    · rw [h8]; norm_num [e4BaseExponent, e6BaseExponent]
    · rw [h10]; norm_num [e4BaseExponent, e6BaseExponent]
    · rw [h14]; norm_num [e4BaseExponent, e6BaseExponent]
  let i : ℕ := (b - e6BaseExponent r) / 2
  have hb : b = e6BaseExponent r + 2 * i := by
    dsimp [i]
    have hweight' : 4 * (a : ℤ) + 6 * (b : ℤ) =
        4 * (e4BaseExponent r : ℤ) + 6 * (e6BaseExponent r : ℤ) +
          12 * (n : ℤ) := by
      calc
        _ = k := hab
        _ = r + 12 * (n : ℤ) := hkdecomp
        _ = 4 * (e4BaseExponent r : ℤ) + 6 * (e6BaseExponent r : ℤ) +
              12 * (n : ℤ) := by rw [hbase]
    have hEq2 : 2 * (a : ℤ) + 3 * (b : ℤ) =
        2 * (e4BaseExponent r : ℤ) + 3 * (e6BaseExponent r : ℤ) +
          6 * (n : ℤ) := by nlinarith [hweight']
    have hparity : b % 2 = e6BaseExponent r % 2 := by
      rcases hr' with h0 | h4 | h6 | h8 | h10 | h14
      · rw [h0] at hEq2 ⊢; norm_num [e6BaseExponent] at hEq2 ⊢; omega
      · rw [h4] at hEq2 ⊢; norm_num [e6BaseExponent] at hEq2 ⊢; omega
      · rw [h6] at hEq2 ⊢; norm_num [e6BaseExponent] at hEq2 ⊢; omega
      · rw [h8] at hEq2 ⊢; norm_num [e6BaseExponent] at hEq2 ⊢; omega
      · rw [h10] at hEq2 ⊢; norm_num [e6BaseExponent] at hEq2 ⊢; omega
      · rw [h14] at hEq2 ⊢; norm_num [e6BaseExponent] at hEq2 ⊢; omega
    omega
  have ha : a + 3 * i = e4BaseExponent r + 3 * n := by
    have hweight' : 4 * (a : ℤ) + 6 * (b : ℤ) =
        4 * (e4BaseExponent r : ℤ) + 6 * (e6BaseExponent r : ℤ) +
          12 * (n : ℤ) := by
      calc
        _ = k := hab
        _ = r + 12 * (n : ℤ) := hkdecomp
        _ = 4 * (e4BaseExponent r : ℤ) + 6 * (e6BaseExponent r : ℤ) +
              12 * (n : ℤ) := by rw [hbase]
    rw [hb] at hweight'
    omega
  have ha0_lt_three : e4BaseExponent r < 3 := by
    rcases hr' with h0 | h4 | h6 | h8 | h10 | h14
    · rw [h0]; norm_num [e4BaseExponent]
    · rw [h4]; norm_num [e4BaseExponent]
    · rw [h6]; norm_num [e4BaseExponent]
    · rw [h8]; norm_num [e4BaseExponent]
    · rw [h10]; norm_num [e4BaseExponent]
    · rw [h14]; norm_num [e4BaseExponent]
  have hi : i < n + 1 := by omega
  have hi_le : i ≤ n := by omega
  have hsub_add : 3 * n - 3 * i + 3 * i = 3 * n := by omega
  refine ⟨⟨i, by simpa [hdim_formula] using hi⟩, ?_⟩
  apply Subtype.ext
  change (pExponent ⟨i, by simpa [hdim_formula] using hi⟩).1 = (a, b)
  apply Prod.ext
  · rw [pExponent_fst, hq]
    change e4BaseExponent r + (3 * n - 3 * i) = a
    omega
  · rw [pExponent_snd]
    exact hb.symm

@[simp]
theorem fourier_PMonomial {k : ℤ} (c : Fin (dim k)) :
    (PMonomial (p := p) c).fourier =
      (Eis (p := p) 4).fourier ^ (pExponent c).1.1 *
        (Eis (p := p) 6).fourier ^ (pExponent c).1.2 := by
  simp [PMonomial, E4E6Monomial, castWeight]

private theorem fourier_G_dim_one (r : ℤ)
    (hr : r ∈ ({0, 4, 6, 8, 10, 14} : Set ℤ)) :
    (ofInteger (p := p) (IntegerModularForm.G_dim_one r)).fourier =
      (Eis (p := p) 4).fourier ^ e4BaseExponent r *
        (Eis (p := p) 6).fourier ^ e6BaseExponent r := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h | h | h | h | h
  · subst r
    change PowerSeries.map (algebraMap ℤ (CoeffRing p)) (PowerSeries.C (1 : ℤ)) = _
    simp [e4BaseExponent, e6BaseExponent]
  all_goals subst r <;>
    simp [IntegerModularForm.G_dim_one, e4BaseExponent, e6BaseExponent,
      Eis, ofInteger, map_mul, map_pow]

private theorem pSeries_binomial {R : Type*} [CommRing R] (A D : R) (q c : ℕ)
    (hc : 3 * c ≤ q) :
    A ^ (q - 3 * c) * (A ^ 3 - (1728 : R) * D) ^ c =
      ∑ j ∈ Finset.range (c + 1),
        (Nat.choose c j : R) * (-(1728 : R)) ^ j * A ^ (q - 3 * j) * D ^ j := by
  calc
    _ = A ^ (q - 3 * c) * ((-(1728 : R) * D + A ^ 3) ^ c) := by
      congr 1
      ring
    _ = A ^ (q - 3 * c) *
        (∑ j ∈ Finset.range (c + 1),
          (-(1728 : R) * D) ^ j * (A ^ 3) ^ (c - j) * (Nat.choose c j : R)) := by
      rw [add_pow]
    _ = ∑ j ∈ Finset.range (c + 1),
        (Nat.choose c j : R) * (-(1728 : R)) ^ j * A ^ (q - 3 * j) * D ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjc : j ≤ c := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hexp : q - 3 * c + 3 * (c - j) = q - 3 * j := by omega
      calc
        _ = (Nat.choose c j : R) * (-(1728 : R)) ^ j *
            (A ^ (q - 3 * c) * A ^ (3 * (c - j))) * D ^ j := by
          rw [mul_pow, ← pow_mul]
          ring
        _ = (Nat.choose c j : R) * (-(1728 : R)) ^ j *
            A ^ (q - 3 * j) * D ^ j := by rw [← pow_add, hexp]
        _ = _ := by ring

private theorem pSeries_binomial_fin {R : Type*} [CommRing R] (A D : R) (q c : ℕ)
    (hc : 3 * c ≤ q) :
    A ^ (q - 3 * c) * (A ^ 3 - (1728 : R) * D) ^ c =
      ∑ j : Fin (c + 1),
        (Nat.choose c j.1 : R) * (-(1728 : R)) ^ j.1 * A ^ (q - 3 * j.1) * D ^ j.1 := by
  rw [pSeries_binomial A D q c hc, ← Fin.sum_univ_eq_sum_range]

private theorem powerSeries_natCast {R : Type*} [CommSemiring R] (n : ℕ) :
    (n : PowerSeries R) = PowerSeries.C (n : R) := by
  exact (map_natCast PowerSeries.C n).symm

private theorem powerSeries_intCast {R : Type*} [CommRing R] (z : ℤ) :
    (z : PowerSeries R) = PowerSeries.C (z : R) := by
  exact (map_intCast (PowerSeries.C : R →+* PowerSeries R) z).symm

/-- The weight-12 relation in the direction used to replace powers of `E6²`
by `E4³` and `Delta`. -/
theorem eis6_sq_eq_eis4_cube_sub_delta :
    castWeight (by norm_num : 2 * (6 : ℤ) = 12) ((Eis (p := p) 6).pow 2) =
      castWeight (by norm_num : 3 * (4 : ℤ) = 12) ((Eis (p := p) 4).pow 3) -
        (1728 : ℤ) • Delta (p := p) := by
  have h := delta_relation (p := p)
  calc
    _ = castWeight (by norm_num : 3 * (4 : ℤ) = 12) ((Eis (p := p) 4).pow 3) -
        (castWeight (by norm_num : 3 * (4 : ℤ) = 12) ((Eis (p := p) 4).pow 3) -
          castWeight (by norm_num : 2 * (6 : ℤ) = 12) ((Eis (p := p) 6).pow 2)) := by
      abel
    _ = castWeight (by norm_num : 3 * (4 : ℤ) = 12) ((Eis (p := p) 4).pow 3) -
        (1728 : ℤ) • Delta (p := p) := by rw [← h]

/-- Fourier-series version of the weight-12 relation. -/
theorem fourier_eis6_sq_eq_eis4_cube_sub_delta :
    ((Eis (p := p) 6).fourier) ^ 2 =
      ((Eis (p := p) 4).fourier) ^ 3 - (1728 : ℤ) • (Delta (p := p)).fourier := by
  have h := congrArg (fun f : PIntegralModularForm p 12 => f.fourier)
    (eis6_sq_eq_eis4_cube_sub_delta (p := p))
  simpa [castWeight, sub_eq_add_neg] using h

/-- The p-integral version of the triangular family `G` from the integer
modular form basis construction. -/
def G (c : Fin (dim k)) : PIntegralModularForm p k :=
  ofInteger (p := p) (IntegerModularForm.G c)

private theorem fourier_G_formula (c : Fin (dim k)) :
    (G (p := p) c).fourier =
      (ofInteger (p := p) (IntegerModularForm.G_dim_one (k %% 12))).fourier *
        (Eis (p := p) 4).fourier ^ ((k - (k %% 12)).toNat / 4 - 3 * c.1) *
          (Delta (p := p)).fourier ^ c.1 := by
  have hdim : 0 < dim k := Nat.zero_lt_of_lt c.2
  have hkEven : Even k := by
    have h := hdim
    simp only [dim] at h
    split_ifs at h <;> simp_all
  have hsnonneg : 0 ≤ k - (k %% 12) := by
    have hdimS : dim (k - (k %% 12)) = dim k :=
      IntegerModularForm.dim_sub_mod_without_two k hkEven
    have hposS : 0 < dim (k - (k %% 12)) := by rw [hdimS]; exact hdim
    rw [dim] at hposS
    split_ifs at hposS <;> omega
  have hrle : (k %% 12) ≤ k := by omega
  simp [G, IntegerModularForm.G, IntegerModularForm.G_twelve,
    IntegerModularForm.G_twelve', hsnonneg, hrle, IntegerModularForm.fourier_Icast,
    IntegerModularForm.fourier_mul, IntegerModularForm.fourier_pow,
    ofInteger, Eis, Delta, map_mul, map_pow]
  ring

private theorem pExponent_qbound (c : Fin (dim k)) :
    3 * c.1 ≤ (k - (k %% 12)).toNat / 4 := by
  have hdim : 0 < dim k := Nat.zero_lt_of_lt c.2
  have hkEven : Even k := by
    have h := hdim
    simp only [dim] at h
    split_ifs at h <;> simp_all
  let s : ℤ := k - (k %% 12)
  have hsnonneg : 0 ≤ s := by
    have hdimS : dim s = dim k := by
      dsimp [s]
      exact IntegerModularForm.dim_sub_mod_without_two k hkEven
    have hposS : 0 < dim s := by rw [hdimS]; exact hdim
    rw [dim] at hposS
    split_ifs at hposS <;> omega
  have hdiv : 4 ∣ s := by
    have h12 := IntegerModularForm.dvd_sub_mod_without_two k
    dsimp [s]
    exact dvd_trans (by norm_num) h12
  have hdimS : dim s = dim k := by
    dsimp [s]
    exact IntegerModularForm.dim_sub_mod_without_two k hkEven
  have hcS : c.1 < dim s := by rw [hdimS]; exact c.2
  have hmodS : s % 12 = 0 := by
    have h12 := IntegerModularForm.dvd_sub_mod_without_two k
    have hs : 12 ∣ s := by dsimp [s]; exact h12
    have hm := Int.modEq_zero_iff_dvd.mpr hs
    rw [Int.ModEq] at hm
    simpa using hm
  have hsNat : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hsnonneg
  have hmodNat : s.toNat % 12 = 0 := by omega
  have hsEven : Even s := by
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨2 * t, ?_⟩
    omega
  have hnotTwo : ¬ s ≡ 2 [ZMOD 12] := by
    intro hcon
    rw [Int.ModEq] at hcon
    simp [hmodS] at hcon
  have hdimFormula : dim s = s.toNat / 12 + 1 := by
    rw [dim]
    simp [hsnonneg, hsEven, hnotTwo]
  rw [hdimFormula] at hcS
  have hcBound : c.1 ≤ s.toNat / 12 := by omega
  have hqFormula : (k - (k %% 12)).toNat / 4 = 3 * (s.toNat / 12) := by
    have hEq : s = k - (k %% 12) := rfl
    rw [← hEq]
    omega
  rw [hqFormula]
  omega

private def pBasisIndex (c : Fin (dim k)) (j : Fin (c.1 + 1)) : Fin (dim k) :=
  ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt c.2)⟩

set_option maxHeartbeats 0 in
private theorem fourier_PMonomial_eq_fin (c : Fin (dim k)) :
    (PMonomial (p := p) c).fourier =
      ∑ j : Fin (c.1 + 1),
        ((Nat.choose c.1 j.1 : CoeffRing p) *
          (-(algebraMap ℤ (CoeffRing p) (1728 : ℤ))) ^ j.1) •
          (G (p := p) (pBasisIndex c j)).fourier := by
  let r : ℤ := k %% 12
  let q : ℕ := (k - (k %% 12)).toNat / 4
  let A : PowerSeries (CoeffRing p) := (Eis (p := p) 4).fourier
  let B : PowerSeries (CoeffRing p) := (Eis (p := p) 6).fourier
  let D : PowerSeries (CoeffRing p) := (Delta (p := p)).fourier
  have hr : r ∈ ({0, 4, 6, 8, 10, 14} : Set ℤ) := by
    have hdim : 0 < dim k := Nat.zero_lt_of_lt c.2
    have hkEven : Even k := by
      have h := hdim
      simp only [dim] at h
      split_ifs at h <;> simp_all
    dsimp [r]
    exact IntegerModularForm.of_dim_pos k hdim
  have hbase :
      (ofInteger (p := p) (IntegerModularForm.G_dim_one (k %% 12))).fourier =
        A ^ e4BaseExponent r * B ^ e6BaseExponent r := by
    simpa [A, r] using fourier_G_dim_one (p := p) (k %% 12) hr
  have hqbound : 3 * c.1 ≤ q := by
    simpa [q] using pExponent_qbound (k := k) c
  have hsmul : (1728 : ℤ) • D = (1728 : PowerSeries (CoeffRing p)) * D := by
    apply PowerSeries.ext
    intro n
    simp [PowerSeries.coeff_smul, zsmul_eq_mul,
      PowerSeries.coeff_intCast_mul, smul_eq_mul]
  have hrelation :
      B ^ 2 = A ^ 3 - (1728 : PowerSeries (CoeffRing p)) * D := by
    simpa [A, B, D, hsmul] using
      (fourier_eis6_sq_eq_eis4_cube_sub_delta (p := p))
  have hleft :
      (PMonomial (p := p) c).fourier =
        (A ^ e4BaseExponent r * B ^ e6BaseExponent r) *
          A ^ (q - 3 * c.1) * (B ^ 2) ^ c.1 := by
    rw [fourier_PMonomial]
    simp only [pExponent_fst, pExponent_snd]
    rw [pow_add, pow_add, pow_mul]
    calc
      _ = (A ^ e4BaseExponent r * B ^ e6BaseExponent r) *
          A ^ (q - 3 * c.1) * (B ^ 2) ^ c.1 := by ac_rfl
      _ = _ := by rw [← hbase]
  have hbinom := pSeries_binomial_fin A D q c.1 hqbound
  rw [← hrelation] at hbinom
  rw [hleft]
  calc
    _ = (A ^ e4BaseExponent r * B ^ e6BaseExponent r) *
        (A ^ (q - 3 * c.1) * (B ^ 2) ^ c.1) := by ac_rfl
    _ = (A ^ e4BaseExponent r * B ^ e6BaseExponent r) *
        (∑ j : Fin (c.1 + 1),
          (Nat.choose c.1 j.1 : PowerSeries (CoeffRing p)) *
            (-(1728 : PowerSeries (CoeffRing p))) ^ j.1 *
              A ^ (q - 3 * j.1) * D ^ j.1) := by rw [hbinom]
    _ = ∑ j : Fin (c.1 + 1),
        (A ^ e4BaseExponent r * B ^ e6BaseExponent r) *
          ((Nat.choose c.1 j.1 : PowerSeries (CoeffRing p)) *
            (-(1728 : PowerSeries (CoeffRing p))) ^ j.1 *
              A ^ (q - 3 * j.1) * D ^ j.1) := by rw [Finset.mul_sum]
    _ = ∑ j : Fin (c.1 + 1),
        ((Nat.choose c.1 j.1 : CoeffRing p) *
          (-(algebraMap ℤ (CoeffRing p) (1728 : ℤ))) ^ j.1) •
          (G (p := p) (pBasisIndex c j)).fourier := by
      apply Finset.sum_congr rfl
      intro j hj
      let cj : Fin (dim k) := pBasisIndex c j
      have hGj := fourier_G_formula (p := p) (k := k) cj
      have hGj' : (G (p := p) cj).fourier =
          (A ^ e4BaseExponent r * B ^ e6BaseExponent r) *
            A ^ (q - 3 * j.1) * D ^ j.1 := by
        simpa [cj, pBasisIndex, A, B, D, q, r, hbase] using hGj
      have h1728 : (1728 : PowerSeries (CoeffRing p)) =
          PowerSeries.C (algebraMap ℤ (CoeffRing p) (1728 : ℤ)) := by
        simpa using powerSeries_intCast (R := CoeffRing p) (1728 : ℤ)
      have hsign : (-(1728 : PowerSeries (CoeffRing p))) ^ j.1 =
          PowerSeries.C (algebraMap ℤ (CoeffRing p) (1728 : ℤ)) ^ j.1 *
            (-1 : PowerSeries (CoeffRing p)) ^ j.1 := by
        calc
          _ = ((-1 : PowerSeries (CoeffRing p)) *
              (1728 : PowerSeries (CoeffRing p))) ^ j.1 := by congr 1 <;> ring
          _ = _ := by rw [mul_pow, h1728]; ac_rfl
      rw [hGj']
      rw [PowerSeries.smul_eq_C_mul]
      simp only [powerSeries_natCast, powerSeries_intCast,
        map_neg, map_pow, map_mul]
      rw [hsign]
      have hnegpow (x : PowerSeries (CoeffRing p)) (n : ℕ) :
          (-x) ^ n = (-1 : PowerSeries (CoeffRing p)) ^ n * x ^ n := by
        calc
          _ = ((-1 : PowerSeries (CoeffRing p)) * x) ^ n := by congr 1 <;> ring
          _ = _ := by rw [mul_pow]
      conv_rhs => rw [hnegpow]
      ac_rfl

@[simp]
theorem coeff_G_diagonal (c : Fin (dim k)) : (G (p := p) c).coeff c = 1 := by
  rw [G, coeff_ofInteger, IntegerModularForm.G_ord_G]
  simp

theorem coeff_G_lt {c : Fin (dim k)} {n : ℕ} (hn : n < c) :
    (G (p := p) c).coeff n = 0 := by
  rw [G, coeff_ofInteger, IntegerModularForm.coeff_lt_ord]
  · simp
  · rw [IntegerModularForm.ord_G]
    exact_mod_cast hn

/-- The finite initial Fourier coefficient map. -/
noncomputable def coeffTrunc : PIntegralModularForm p k →ₗ[CoeffRing p]
    (Fin (dim k) → CoeffRing p) where
  toFun f c := f.coeff c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coeffTrunc_apply (f : PIntegralModularForm p k) (c : Fin (dim k)) :
    coeffTrunc (p := p) f c = f.coeff c := rfl

@[simp]
theorem coeff_smul (a : CoeffRing p) (f : PIntegralModularForm p k) (n : ℕ) :
    (a • f).coeff n = a * f.coeff n := by
  change (a • f.fourier).coeff n = a * f.fourier.coeff n
  rw [PowerSeries.coeff_smul, smul_eq_mul]

theorem coeff_sum {α : Type*} (s : Finset α) (f : α → PIntegralModularForm p k)
    (n : ℕ) : (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih => simp [has, ih]

theorem coeffTrunc_injective : Function.Injective (coeffTrunc (p := p) (k := k)) := by
  intro f g h
  have hcar : f.carrier = g.carrier := by
    apply sub_eq_zero.mp
    apply better_sturm_bound_levelOne
    simp only [FunLike.coe_sub,
      ModularForm.qExpansion_sub (Γ := 𝒮ℒ) zero_lt_one (by simp)]
    apply PowerSeries.le_order _ _ fun n hn => by
      have hcoeff : f.coeff n = g.coeff n := by
        exact congrFun h ⟨n, by exact_mod_cast hn⟩
      simp only [map_sub, f.carrier_eq, g.carrier_eq,
        PowerSeries.coeff_map]
      simp [hcoeff]
  have hfourier : f.fourier = g.fourier := by
    apply PowerSeries.map_injective (toComplex p) (toComplex_injective p)
    calc
      map (toComplex p) f.fourier = qExpansion 1 f.carrier := f.carrier_eq.symm
      _ = qExpansion 1 g.carrier := congrArg (fun F : ModularForm 𝒮ℒ k => qExpansion 1 F) hcar
      _ = map (toComplex p) g.fourier := g.carrier_eq
  apply PIntegralModularForm.ext
  intro n
  exact congrArg (fun F : PowerSeries (CoeffRing p) => F.coeff n) hfourier

/-- Coefficients for expressing a form in the triangular `G` family. -/
noncomputable def upTriangle_coeff (f : PIntegralModularForm p k) :
  Fin (dim k) → CoeffRing p
  | ⟨0, _⟩ => f.coeff 0
  | ⟨n + 1, h⟩ => f.coeff (n + 1) -
      ∑ i : Fin (n + 1), upTriangle_coeff f ⟨i.1, lt_trans i.2 h⟩ *
        (G (p := p) ⟨i.1, lt_trans i.2 h⟩).coeff (n + 1)

theorem upTriangle_coeff_zero (f : PIntegralModularForm p k) (h : 0 < dim k) :
    upTriangle_coeff f ⟨0, h⟩ = f.coeff 0 := by
  simp [upTriangle_coeff]

theorem upTriangle_coeff_succ (f : PIntegralModularForm p k) (n : ℕ)
    (h : n + 1 < dim k) :
    upTriangle_coeff f ⟨n + 1, h⟩ = f.coeff (n + 1) -
      ∑ i : Fin (n + 1), upTriangle_coeff f ⟨i.1, lt_trans i.2 h⟩ *
      (G (p := p) ⟨i.1, lt_trans i.2 h⟩).coeff (n + 1) := by
  simp [upTriangle_coeff]

theorem G_LI : LinearIndependent (CoeffRing p) (G (p := p) (k := k)) := by
  classical
  simp only [linearIndependent_iff, Finsupp.linearCombination_apply]
  intro l hl
  ext c
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  have hcoeff (n : Fin (dim k)) :
    ∑ i ∈ l.support, l i * (G (p := p) i).coeff n = 0 := by
    have h := congrArg (fun f : PIntegralModularForm p k => f.coeff n) hl
    simpa [Finsupp.sum, coeff_sum, coeff_smul] using h
  have hzero : ∀ n (hn : n < dim k), l ⟨n, hn⟩ = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let c : Fin (dim k) := ⟨n, hn⟩
      by_cases hcn : l c = 0
      · exact hcn
      · have hcMem : c ∈ l.support := Finsupp.mem_support_iff.mpr hcn
        have heq : (∑ i ∈ l.support, l i * (G (p := p) i).coeff n) = l c := by
          rw [Finset.sum_eq_single c]
          · change l c * (G (p := p) c).coeff c = l c
            rw [coeff_G_diagonal, mul_one]
          · intro i hi hne
            by_cases hin : i.1 < n
            · rw [ih i.1 hin (by omega), zero_mul]
            · have hni : n < i.1 := lt_of_le_of_ne (Nat.not_lt.mp hin) (Ne.symm (by
                intro heq
                apply hne
                exact Fin.ext heq))
              rw [coeff_G_lt hni, mul_zero]
          · intro hmem
            exact (hmem hcMem).elim
        rw [hcoeff c] at heq
        exact heq.symm
  exact hzero c.1 c.2

theorem upTriangle_coeff_smul_G (f : PIntegralModularForm p k) :
    ∑ i, upTriangle_coeff f i • G (p := p) i = f := by
  apply coeffTrunc_injective
  ext ⟨n, nlt⟩
  simp only [coeffTrunc_apply, coeff_sum, coeff_smul]
  match n with
  | 0 =>
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ⟨0, nlt⟩), ← zero_add (f.coeff 0)]
    congr
    · apply Finset.sum_eq_zero
      intro ⟨x, hx⟩ hxmem
      have hxne : (⟨x, hx⟩ : Fin (dim k)) ≠ ⟨0, nlt⟩ :=
        (Finset.mem_erase.mp hxmem).1
      have hxpos : 0 < x := by
        by_contra hnot
        have : x = 0 := by omega
        subst x
        exact hxne (Fin.ext rfl)
      rw [coeff_G_lt (n := 0) (c := ⟨x, hx⟩) (by exact_mod_cast hxpos), mul_zero]
    · rw [upTriangle_coeff_zero _ (by omega)]
      have hdiag : (G (p := p) (⟨0, nlt⟩ : Fin (dim k))).coeff 0 = 1 := by
        simpa using coeff_G_diagonal (p := p) (k := k) (⟨0, nlt⟩ : Fin (dim k))
      rw [hdiag, mul_one]
  | n + 1 =>
    nth_rw 1 [← Finset.sum_filter_add_sum_filter_not _
      (fun (x : Fin (dim k)) => x.1 ≤ n + 1),
      ← Finset.sum_filter_add_sum_filter_not _
      (fun (x : Fin (dim k)) => x.1 = n + 1)]
    calc
      _ = (∑ x : Fin (dim k) with x.1 = n + 1,
            upTriangle_coeff f x * (G (p := p) x).coeff (n + 1)) +
          (∑ x : Fin (dim k) with x.1 < n + 1,
            upTriangle_coeff f x * (G (p := p) x).coeff (n + 1)) +
          (∑ x : Fin (dim k) with x.1 > n + 1,
            upTriangle_coeff f x * (G (p := p) x).coeff (n + 1)) := by
        congr! 3
        · ext a
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using by omega
        · ext a
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Order.lt_add_one_iff] using by omega
        simp only [not_le, gt_iff_lt]
      _ = upTriangle_coeff f ⟨n + 1, nlt⟩ * (G (p := p) ⟨n + 1, nlt⟩).coeff (n + 1) +
          (∑ x : Fin (n + 1), upTriangle_coeff f ⟨x.1, lt_trans x.2 nlt⟩ *
            (G (p := p) ⟨x.1, lt_trans x.2 nlt⟩).coeff (n + 1)) + 0 := by
        congr 2
        · apply Finset.sum_eq_single
          · intro ⟨b, hb⟩ hmem hne
            have hval : b = n + 1 := by
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
            exact (hne (Fin.ext hval)).elim
          · intro hmem
            exact (hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
        · apply Finset.sum_bij fun ⟨a, alt⟩ ha => ⟨a, by grind⟩
          · exact fun _ _ => Finset.mem_univ _
          · exact fun _ _ _ _ => by grind
          · exact fun ⟨b, blt⟩ _ => ⟨⟨b, blt.trans nlt⟩, by grind, rfl⟩
          · exact fun _ _ => rfl
        · apply Finset.sum_eq_zero
          intro ⟨x, hx⟩ hxmem
          have hlt : n + 1 < x := by simp only [Finset.mem_filter] at hxmem; omega
          rw [coeff_G_lt (n := n + 1) (c := ⟨x, hx⟩) hlt, mul_zero]
      _ = f.coeff (n + 1) := by
        rw [upTriangle_coeff_succ]
        have hdiag : (G (p := p) (⟨n + 1, nlt⟩ : Fin (dim k))).coeff (n + 1) = 1 := by
          simpa using coeff_G_diagonal (p := p) (k := k) (⟨n + 1, nlt⟩ : Fin (dim k))
        rw [hdiag]
        ring

theorem G_span : ⊤ ≤ Submodule.span (CoeffRing p)
    {G (p := p) (k := k) c | c : Fin (dim k)} := by
  intro f _
  rw [Submodule.mem_span_set']
  refine ⟨dim k, upTriangle_coeff f, fun c => ⟨G (p := p) c, c, rfl⟩,
    upTriangle_coeff_smul_G f⟩

/-- The p-integral triangular basis corresponding to the family `G` in the
integer-coefficient development. -/
noncomputable def GBasis (k : ℤ) :
    Module.Basis (Fin (dim k)) (CoeffRing p) (PIntegralModularForm p k) :=
  Module.Basis.mk (G_LI (p := p) (k := k)) (G_span (p := p) (k := k))

@[simp]
theorem GBasis_apply (c : Fin (dim k)) : GBasis (p := p) k c = G (p := p) c :=
  Module.Basis.mk_apply ..

/-- Change-of-basis matrix from `G` to the E4/E6 monomials. Its `j,c` entry
is the coefficient of `G j` in the expansion of the monomial indexed by `c`. -/
def pBasisMatrix (k : ℤ) : Matrix (Fin (dim k)) (Fin (dim k)) (CoeffRing p) :=
  fun j c => if hjc : j.1 ≤ c.1 then
    (Nat.choose c.1 j.1 : CoeffRing p) *
      (-(algebraMap ℤ (CoeffRing p) (1728 : ℤ))) ^ j.1
    else 0

theorem pBasisMatrix_upper (k : ℤ) : (pBasisMatrix (p := p) k).IsUpperTriangular := by
  intro i j hji
  change (pBasisMatrix (p := p) k) i j = 0
  simp only [pBasisMatrix]
  split_ifs with hij
  · have : i.1 ≤ j.1 := hij
    have : j.1 < i.1 := hji
    omega
  · rfl

theorem pBasisMatrix_isUnit_det (k : ℤ) : IsUnit (pBasisMatrix (p := p) k).det := by
  rw [Matrix.det_of_isUpperTriangular (pBasisMatrix_upper (p := p) k)]
  rw [IsUnit.prod_univ_iff]
  intro i
  have hu : IsUnit (-(algebraMap ℤ (CoeffRing p) (1728 : ℤ))) :=
    isUnit_algebraMap_1728.neg
  simpa [pBasisMatrix] using hu.pow i.1

/-- The p-local Eisenstein monomial basis. The following theorem identifies
its vectors with the monomials `E4^a * E6^b`. -/
noncomputable def PBasis (k : ℤ) :
    Module.Basis (Fin (dim k)) (CoeffRing p) (PIntegralModularForm p k) :=
  (GBasis (p := p) k).map
    ((pBasisMatrix (p := p) k).toLinearEquiv (GBasis (p := p) k)
      (pBasisMatrix_isUnit_det (p := p) k))

@[simp]
theorem PBasis_apply_eq_change (c : Fin (dim k)) :
    PBasis (p := p) k c =
      ∑ j : Fin (dim k), (pBasisMatrix (p := p) k) j c • G (p := p) j := by
  rw [PBasis, Module.Basis.map_apply]
  simp [Matrix.toLinearEquiv, Matrix.toLin_apply, Matrix.mulVec,
    dotProduct, Finsupp.single_apply, ← GBasis_apply]

private theorem fourier_sum_forms {α : Type*} (s : Finset α)
    (f : α → PIntegralModularForm p k) :
    (∑ a ∈ s, f a).fourier = ∑ a ∈ s, (f a).fourier := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private theorem pBasis_column_sum (c : Fin (dim k)) :
    (∑ j : Fin (dim k), (pBasisMatrix (p := p) k) j c • G (p := p) j) =
      ∑ j : Fin (c.1 + 1),
        ((Nat.choose c.1 j.1 : CoeffRing p) *
          (-(algebraMap ℤ (CoeffRing p) (1728 : ℤ))) ^ j.1) •
          G (p := p) (pBasisIndex c j) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (dim k))) (fun j => j.1 ≤ c.1)]
  have hzero :
      (∑ j ∈ (Finset.univ : Finset (Fin (dim k))).filter (fun j => ¬ j.1 ≤ c.1),
        (pBasisMatrix (p := p) k) j c • G (p := p) j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjnot : ¬ j.1 ≤ c.1 := (Finset.mem_filter.mp hj).2
    by_cases hle : j.1 ≤ c.1
    · exact (hjnot hle).elim
    · simp [pBasisMatrix, hle]
  rw [hzero, add_zero]
  apply Finset.sum_bij (fun j hj =>
    (⟨j.1, Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2⟩ : Fin (c.1 + 1)))
  · intro j hj
    exact Finset.mem_univ _
  · intro j hj l hl heq
    apply Fin.ext
    exact congrArg (fun x : Fin (c.1 + 1) => x.1) heq
  · intro b hb
    refine ⟨pBasisIndex c b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.le_of_lt_succ b.2
    · apply Fin.ext
      rfl
  · intro j hj
    have hjle : j.1 ≤ c.1 := (Finset.mem_filter.mp hj).2
    simp [pBasisMatrix, pBasisIndex, hjle]

/-- The vectors of `PBasis` are exactly the requested `E4^a * E6^b`
monomials, so `PBasis` is a basis of the p-integral modular forms. -/
theorem PBasis_apply_eq_PMonomial (c : Fin (dim k)) :
    PBasis (p := p) k c = PMonomial (p := p) c := by
  rw [PBasis_apply_eq_change, pBasis_column_sum]
  apply PIntegralModularForm.ext
  intro n
  have hseries := fourier_PMonomial_eq_fin (p := p) (k := k) c
  have hcoeff := congrArg (fun F : PowerSeries (CoeffRing p) => F.coeff n) hseries.symm
  change ((∑ j : Fin (c.1 + 1),
      ((Nat.choose c.1 j.1 : CoeffRing p) *
        (-(algebraMap ℤ (CoeffRing p) (1728 : ℤ))) ^ j.1) •
        G (p := p) (pBasisIndex c j)).fourier).coeff n =
      (PMonomial (p := p) c).fourier.coeff n
  rw [fourier_sum_forms]
  simpa [coeff_smul] using hcoeff

@[simp]
theorem PBasis_apply (c : Fin (dim k)) :
    PBasis (p := p) k c = E4E6Monomial (p := p) (pExponent c) := by
  exact PBasis_apply_eq_PMonomial (p := p) (k := k) c

end
end PIntegralModularForm
