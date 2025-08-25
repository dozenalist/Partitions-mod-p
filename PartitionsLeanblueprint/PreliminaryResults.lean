import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.BasicOperators
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs

/- This file states and proves some basic theorems, some of which are found
in the introduction of the paper -/

open ModularFormDefs Integer Modulo2

noncomputable section

variable {ℓ n : ℕ} [NeZero ℓ] [Fact (Nat.Prime ℓ)]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

open Nat Finset ZMod Finset.Nat

@[simp]
lemma flt {p : ℕ} {n : ZMod p} [Fact (Nat.Prime p)] : n ^ p = n := pow_card n

@[simp]
lemma flt2 {p : ℕ} {n : ZMod p} [Fact (Nat.Prime p)] : n ^ (p - 1) = if n ≠ 0 then 1 else 0 :=
  pow_card_sub_one n




def perm_equiv'' {n : ℕ} (a b : Fin n → ℕ) :=
  List.isPerm (List.ofFn a) (List.ofFn b)


def perm_equiv {n : ℕ} (a b : Fin n → ℕ) :=
  ∃ c : Equiv.Perm (Fin n), a = b ∘ c


theorem perm_equiv_trans {n} {a b c : Fin n → ℕ} : perm_equiv a b → perm_equiv b c → perm_equiv a c := by
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩
  refine ⟨σ.trans τ, ?_⟩
  ext i
  have : b (σ i) = (c ∘ τ) (σ i) := by simpa using congrArg (fun f => f (σ i)) hτ
  simpa [Function.comp, hσ] using this


@[simp]
lemma perm_equiv_refl {n : ℕ} (a : Fin n → ℕ) : perm_equiv a a :=
  ⟨Equiv.refl _, by simp⟩


theorem perm_equiv_symm {n} {a b : Fin n → ℕ} :
    perm_equiv a b → perm_equiv b a := by
  rintro ⟨c, hc⟩; use c⁻¹; rw[hc]; ext x; simp

theorem perm_equiv_const {n} {a b: Fin n → ℕ} (aconst : ∀ i j, a i = a j)
    (h : perm_equiv a b) : a = b := by
  obtain ⟨c,rfl⟩ := h
  ext i
  have := aconst i (c.symm i)
  -- simplify using c (c.symm i) = i
  simp [Equiv.apply_symm_apply] at this
  exact this


def perm_equiv' {k n : ℕ} (a b : antidiagonalTuple k n) :=
  perm_equiv a.1 b.1

@[simp]
lemma perm_equiv_refl' {k n : ℕ} (a : antidiagonalTuple k n) : perm_equiv' a a :=
  ⟨Equiv.refl _, by simp⟩

theorem perm_equiv_symm' {k n} {a b : antidiagonalTuple k n} :
    perm_equiv' a b → perm_equiv' b a := by
  unfold perm_equiv'; exact perm_equiv_symm

theorem perm_equiv_trans' {k n} {a b c : antidiagonalTuple k n} :
    perm_equiv' a b → perm_equiv' b c → perm_equiv' a c := by
  unfold perm_equiv'; exact perm_equiv_trans

def perm_setoid' : Setoid { x // x ∈ antidiagonalTuple n ℓ } :=
{ r := perm_equiv',
  iseqv :=
    ⟨perm_equiv_refl', perm_equiv_symm', perm_equiv_trans'⟩ }

def perm_setoid : Setoid ( Fin n → ℕ ) where
  r := perm_equiv
  iseqv := ⟨perm_equiv_refl, perm_equiv_symm, perm_equiv_trans⟩


lemma disjoint_filter_of_not_perm {n : ℕ} {s : Finset (Fin n → ℕ)} {x₁ x₂ : Fin n → ℕ}
    (hneq : ¬ perm_equiv x₁ x₂) :
    Disjoint (s.filter (fun z => perm_equiv x₁ z)) (s.filter (fun z => perm_equiv x₂ z)) := by
  refine Finset.disjoint_left.mpr ?_
  intro z hz1 hz2
  rcases (Finset.mem_filter.mp hz1) with ⟨hzs1, hx1z⟩
  rcases (Finset.mem_filter.mp hz2) with ⟨hzs2, hx2z⟩
  exact hneq (perm_equiv_trans (perm_equiv_symm (perm_equiv_symm hx1z)) (perm_equiv_symm hx2z))

lemma sum_eq_of_perm_equiv {n} {a b : Fin n → ℕ} (h : perm_equiv a b) :
    ∑ i, a i = ∑ i, b i := by
  obtain ⟨c,hc,rfl⟩ := h
  exact Equiv.sum_comp c b


def orbit_finset {k} (x : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  Finset.univ.image (fun c : Equiv.Perm (Fin k) ↦ x ∘ c)

lemma perm_of_orbit {k} {x b : Fin k → ℕ} (h : b ∈ orbit_finset x) : perm_equiv x b := by
  rcases Finset.mem_image.mp h with ⟨c, _, rfl⟩
  use c⁻¹; ext i; simp

lemma orbit_eq_tuple {k n} {x : Fin k → ℕ} (h : x ∈ antidiagonalTuple k n) :
    orbit_finset x = {b ∈ antidiagonalTuple k n | perm_equiv x b} := by
  ext b; constructor <;> intro hb
  apply mem_filter.mpr; constructor
  rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
  apply mem_antidiagonalTuple.mpr; trans ∑ i, x i
  exact Fintype.sum_equiv c (x ∘ ⇑c) x (congrFun rfl)
  exact mem_antidiagonalTuple.mp h
  exact perm_of_orbit hb
  have : perm_equiv x b := by simp_all only [mem_filter]
  obtain ⟨c,rfl⟩ := this
  apply Finset.mem_image.mpr
  use c⁻¹; constructor
  simp_all only [mem_filter, mem_univ]
  ext i; simp


lemma orbit_card {k} (x : Fin k → ℕ) : #(orbit_finset x) = sorry :=
  sorry

-- If the tuple x is not constant, ie [k,k,k, ..], then
-- ℓ | (# of permutations of x ∈ antidiagonalTuple ℓ (ℓ * k))
lemma non_diag_vanish {k n : ℕ} {x : Fin k → ℕ} [Fact (Nat.Prime k)] (h : ¬ ∀ i j, x i = x j)  :
    k ∣ #{ b ∈ antidiagonalTuple k n | perm_equiv x b } := by
  simp_all only [not_forall]
  obtain ⟨w, h⟩ := h
  obtain ⟨u, h⟩ := h

  by_cases xiT : x ∈ antidiagonalTuple k n

  {
    have perm_in_set {b} (h : perm_equiv x b) : b ∈ { b ∈ antidiagonalTuple k n | perm_equiv x b } := by
      refine mem_filter.mpr ⟨?_, h⟩
      apply mem_antidiagonalTuple.mpr
      trans ∑ i, x i
      exact sum_eq_of_perm_equiv (perm_equiv_symm h)
      apply mem_antidiagonalTuple.mp xiT


    rw[← orbit_eq_tuple xiT]
    sorry

  }

  {
    use 0; simp; apply filter_false_of_mem
    intro b hb; contrapose! xiT
    apply mem_antidiagonalTuple.mpr
    trans ∑ i, b i
    exact sum_eq_of_perm_equiv xiT
    apply mem_antidiagonalTuple.mp hb
  }

#eval antidiagonalTuple 5 2

lemma Pi_eq_of_perm_equiv {n : ℕ} {a : ℕ → ZMod n} {x y : Fin n → ℕ} (hxy : perm_equiv x y) :
    ∏ z, a (y z) = ∏ z, a (x z) := by
  symm; unfold perm_equiv at hxy
  obtain ⟨c, hc⟩ := hxy
  simp[hc]; exact Fintype.prod_equiv c (fun x ↦ a (y (c x))) (fun x ↦ a (y x)) (congrFun rfl)


lemma non_const_of_tuple_non_diag {k n : ℕ} (h : ¬ k ∣ n) (x : Fin k → ℕ) (hx : x ∈ antidiagonalTuple k n ) :
    (¬ ∀ i j, x i = x j) := by
  contrapose! hx
  suffices ∑ i, x i ≠ n by
    contrapose! this; exact mem_antidiagonalTuple.mp this
  contrapose! h
  by_cases k0 : k = 0
  have : ∑ i, x i = 0 := by
    subst k0 h
    simp_all only [IsEmpty.forall_iff, implies_true, univ_eq_empty, sum_empty]
  rw[k0]; apply Nat.zero_dvd.2; rw[← h, this]
  have : ∃ m, k = m + 1 := exists_eq_succ_of_ne_zero k0
  obtain ⟨m,hm⟩ := this
  subst hm; clear k0
  have h' : ∑ i, x i = (m + 1) * x 0 := by
    trans ∑ i : Fin (m + 1), x 0
    exact sum_congr rfl (λ x _ ↦ hx x 0)
    apply Fin.sum_const
  use x 0; rw[← h, h']


lemma non_const_of_tuple_diag {k n : ℕ} (x : Fin k → ℕ) (kn0 : k ≠ 0) (hx : x ∈ antidiagonalTuple k (k * n) \ {fun _ ↦ n}) :
    (¬ ∀ i j, x i = x j) := by
  contrapose! hx
  have hmk : ∃ m, k = m + 1 := exists_eq_succ_of_ne_zero kn0
  obtain ⟨m,hm,rfl⟩ := hmk
  by_contra! h
  have hnconst : x ≠ fun x ↦ n := by
    contrapose! h; simp; exact λ _ ↦ h
  have : ∑ i, x i = (m + 1) * n := by apply mem_antidiagonalTuple.mp; simp_all only [ne_eq, Nat.add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, mem_sdiff, mem_singleton, and_true]
  have const : ∑ i, x i = (m + 1) * x 0 := by
    specialize hx 0
    trans ∑ _ : Fin (m + 1), x 0
    exact Eq.symm (Fintype.sum_congr (fun a ↦ x 0) x hx)
    apply Fin.sum_const
  contrapose! hnconst
  funext i
  calc
   x i = x 0 := hx i 0
   x 0 = n := by
    have : (m + 1) * n = (m + 1) * x 0 := by rw[← this, ← const]
    exact (Nat.mul_right_inj kn0).mp (id (Eq.symm this))

@[simp]
theorem Pow_Prime {n : ℕ} {a : ModularFormMod ℓ k} : (a ** ℓ) n = if ℓ ∣ n then (a (n / ℓ)) else 0 := by

  by_cases h : ℓ ∣ n

  { -- antidiagonalTuple is diagonal (ie ℓ ∣ len) → only diagonal tuple remains
    simp [pow_apply,h]
    obtain ⟨k,rfl⟩ := h
    have la : ℓ * k / ℓ = k := by
      refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ rfl); exact Ne.symm (NeZero.ne' ℓ)
    rw[la]
    have vanish : ∑ x ∈ antidiagonalTuple ℓ (ℓ * k) \ {fun _ ↦ k}, ∏ y, a (x y) = 0 := by
      {
        set Tup := antidiagonalTuple ℓ (ℓ * k) \ {fun _ ↦ k} with hTup

        have blister : ∀ x ∈ Tup, ℓ ∣ #{ b ∈ antidiagonalTuple ℓ (ℓ * k) | perm_equiv x b } :=
          λ x hx ↦ non_diag_vanish (non_const_of_tuple_diag x (Ne.symm (NeZero.ne' ℓ)) hx)

        have step (x : Fin ℓ → ℕ) :
            ∑ z ∈ {b ∈ Tup | perm_equiv x b}, ∏ y, a (z y) = 0 := by
          by_cases hx : x ∈ antidiagonalTuple ℓ (ℓ * k)
          {
            by_cases xconst : x = ↑k
            {
              have empty : {z ∈ Tup | perm_equiv x z} = ∅ := by
                refine filter_false_of_mem ?_; intro z hz
                have zconst : z ≠ ↑k := by
                  subst xconst
                  simp_all only [mem_sdiff, mem_singleton, and_imp, ne_eq, Tup]
                  exact hz.2
                intro hxz
                apply perm_equiv_const at hxz
                rw[← hxz, xconst] at zconst
                contradiction
                intros; simp[xconst]
              rw[empty]; rfl
            }


            have Tup_eq : {b ∈ Tup | perm_equiv x b} = {b ∈ antidiagonalTuple ℓ (ℓ * k) | perm_equiv x b} := by
              apply Subset.antisymm_iff.mpr; constructor <;> intro c hc
              have ss : Tup ⊆ antidiagonalTuple ℓ (ℓ * k) := sdiff_subset
              refine mem_filter.mpr ?_; constructor
              have : c ∈ Tup := mem_of_mem_filter c hc
              exact ss this
              simp_all only [mem_sdiff, mem_singleton, and_imp, mem_filter, sdiff_subset, Tup]

              by_cases cc : c = ↑k
              have hxc : perm_equiv x c := by
                subst cc; simp_all only [mem_sdiff, mem_singleton, and_imp, mem_filter, Tup]

              have : ∀ i j, c i = c j := by intros; simp[cc]
              have cex : c = x := perm_equiv_const this (perm_equiv_symm hxc)
              rw[cc] at cex; exact False.elim (xconst (id (Eq.symm cex)))

              refine mem_filter.mpr ?_; constructor
              have ciT : c ∈ antidiagonalTuple ℓ (ℓ * k) := mem_of_mem_filter c hc
              exact mem_sdiff.mpr ⟨ciT,notMem_singleton.mpr cc⟩
              simp_all only [mem_sdiff, mem_singleton, and_imp, mem_filter, Tup]


            have hxx : x ∈ Tup := by
              simp_all only [mem_sdiff, mem_singleton, and_imp, ne_eq, true_and, Tup]
              exact xconst

            have pi_eq : ∀ z ∈ {b ∈ antidiagonalTuple ℓ (ℓ * k) | perm_equiv x b}, ∏ y, a (z y) = ∏ y, a (x y) := by
              intro z hz
              have hxz : perm_equiv x z := by simp_all only [mem_filter]
              exact Pi_eq_of_perm_equiv hxz

            rw[Tup_eq]

            calc
              _ = ∑ _ ∈ {b ∈ antidiagonalTuple ℓ (ℓ * k) | perm_equiv x b}, ∏ y, a (x y) := sum_congr rfl pi_eq
              _ = #{b ∈ antidiagonalTuple ℓ (ℓ * k) | perm_equiv x b} * ∏ y, a (x y) := by simp
              _ = 0 * ∏ y, a (x y) := by
                congr; exact (natCast_zmod_eq_zero_iff_dvd _ _).2 (blister x hxx)
              _ = 0 := zero_mul _
          }

          have empty : {b ∈ Tup | perm_equiv x b} = ∅ := by
            refine filter_false_of_mem ?_
            intro b hb; contrapose! hx
            refine mem_antidiagonalTuple.mpr ?_
            trans ∑ i, b i
            exact sum_eq_of_perm_equiv hx
            refine mem_antidiagonalTuple.mp ?_
            simp_all only [mem_sdiff, mem_singleton, and_imp, Tup]
          rw[empty]; rfl

        let Qfin := (Tup).image (Quotient.mk (perm_setoid))

        calc
      _  = ∑ q ∈ Qfin, ∑ z ∈ {x ∈ Tup | ⟦x⟧ = q}, ∏ y, a (z y) := by
          -- rewrite as sum over quotient partition
          apply sum_partition
      _ = ∑ q ∈ Qfin, 0 := by
          apply sum_congr rfl
          intro q hq
          rcases Quot.exists_rep q with ⟨x, rfl⟩
          trans ∑ z ∈ Tup with perm_equiv x z, ∏ y, a (z y)
          congr; funext z; apply propext
          have : ⟦z⟧ = Quot.mk (⇑perm_setoid) x ↔ perm_equiv z x := by apply Quotient.eq
          simp[this]; constructor <;> exact perm_equiv_symm
          exact step x
      _ = 0 := sum_const_zero

      }

    calc
      _ = ( ∑ x ∈ antidiagonalTuple ℓ (ℓ * k) \ {fun _ ↦ k}, ∏ y, a (x y) ) +
          ( ∑ x ∈ {fun _ ↦ k}, ∏ y : Fin ℓ, a (x y) ) := by
        apply Eq.symm (sum_sdiff ?_); apply singleton_subset_iff.2
        apply mem_antidiagonalTuple.mpr; simp[sum_const]

      _ = 0 + ∑ x ∈ {fun _ ↦ k}, ∏ y : Fin ℓ, a (x y) := by congr
      _ = ∏ _ : Fin ℓ, a k := by simp
      _ = (a k) ^ ℓ := Fin.prod_const ℓ (a k)
      _ = a k := flt
  }


  { -- antidiagonalTuple is not diagonal → no tuples remain
    simp[pow_apply,h]

    have blister : ∀ x ∈ antidiagonalTuple ℓ n, ℓ ∣ #{ b ∈ antidiagonalTuple ℓ n | perm_equiv x b } :=
      λ x hx ↦ non_diag_vanish (non_const_of_tuple_non_diag h x hx)

    have step : ∀ x : (Fin ℓ → ℕ), ∑ z ∈ {b ∈ antidiagonalTuple ℓ n | perm_equiv x b}, ∏ y, a (z y) = 0 := by
      intro x
      by_cases hx : x ∈ antidiagonalTuple ℓ n
      have pi_eq : ∀ z ∈ {b ∈ antidiagonalTuple ℓ n | perm_equiv x b}, ∏ y, a (z y) = ∏ y, a (x y) := by
        intro z hz
        have hxz : perm_equiv x z := by simp_all only [mem_filter]
        exact Pi_eq_of_perm_equiv hxz
      calc
        _ = ∑ _ ∈ {b ∈ antidiagonalTuple ℓ n | perm_equiv x b}, ∏ y, a (x y) := sum_congr rfl pi_eq
        _ = #{b ∈ antidiagonalTuple ℓ n | perm_equiv x b} * ∏ y, a (x y) := by simp
        _ = 0 * ∏ y, a (x y) := by
          congr; exact (natCast_zmod_eq_zero_iff_dvd _ _).2 (blister x hx)
        _ = 0 := zero_mul _

      have empty : {b ∈ antidiagonalTuple ℓ n | perm_equiv x b} = ∅ := by
        refine filter_false_of_mem ?_
        intro b hb; contrapose! hx
        refine mem_antidiagonalTuple.mpr ?_
        trans ∑ i, b i
        exact sum_eq_of_perm_equiv hx
        exact mem_antidiagonalTuple.mp hb
      rw[empty]; rfl

    let Qfin := (antidiagonalTuple ℓ n).image (Quotient.mk (perm_setoid))

    calc
      _  = ∑ q ∈ Qfin, ∑ z ∈ {x ∈ antidiagonalTuple ℓ n | ⟦x⟧ = q}, ∏ y, a (z y) := by
          -- rewrite as sum over quotient partition
          apply sum_partition
      _ = ∑ q ∈ Qfin, 0 := by
          apply sum_congr rfl
          intro q hq
          rcases Quot.exists_rep q with ⟨x, rfl⟩
          trans ∑ z ∈ antidiagonalTuple ℓ n with perm_equiv x z, ∏ y, a (z y)
          congr; funext z; apply propext
          have : ⟦z⟧ = Quot.mk (⇑perm_setoid) x ↔ perm_equiv z x := by apply Quotient.eq
          simp[this]; constructor <;> exact perm_equiv_symm
          exact step x
      _ = 0 := sum_const_zero
  }


theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one' {a : ModularFormMod ℓ k} :
  (a|𝓤) ** ℓ == (a -l (Θ^[ℓ - 1] a)) (by simp) := by
  intro n; simp; symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have  h' : ℓ ∣ n := (natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp[h,h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp[h,h']


-- lemma blish {a : ModularFormMod ℓ k} {n : ℕ} :
--   ((a|𝓤) ** ℓ) n = 0 := by rw[U_pow_l_eq_self_sub_Theta_pow_l_minus_one']; simp


def thing (a : ModularFormMod ℓ k) := a - (Mcongr (by simp) (Θ^[ℓ - 1] a))

lemma k_l : k * ℓ = k := by
  calc
    k * ℓ = k * (ℓ - 1 + 1) := by simp
    _ = k * (ℓ - 1) + k := by ring
    _ = k * 0 + k := by
      congr; sorry
    _ = k := by simp only [mul_zero, zero_add]


theorem U_pow_l_eq_self_sub_Theta_pow_l_minus_one {a : ModularFormMod ℓ k} :
(Mcongr (k_l) ((a|𝓤) ** ℓ)) = thing a := by
  ext n; simp[thing]
  symm; calc
    _ = if (n : ZMod ℓ) = 0 then a n else 0 := by
      by_cases h : (n : ZMod ℓ) = 0 <;> simp[h]
    _ = _ := by
      by_cases h : (n : ZMod ℓ) = 0
      have h' : ℓ ∣ n := (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h
      simp[h,h']; congr
      rw [Nat.mul_div_cancel_left' h']
      have h': ¬ ℓ ∣ n := by contrapose! h; exact (ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mpr h
      simp[h,h']


theorem Filtration_Log {i : ℕ} [NeZero (ℓ - 1)] : 𝔀 (a ** i) = i * 𝔀 a := sorry



def δ (ℓ : ℕ) : ℤ := (ℓ^2 - 1) / 24
-- or δℓ : ℤ := (ℓ^2 - 1) / 24
