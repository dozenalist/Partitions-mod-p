import PartitionsLeanblueprint.BasicOperators
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Nat.Prime.Factorial


/- This files proves some facts about powers of modular forms mod ℓ.
Namely, that (∑ a(n) * q^n) ^ ℓ is congruent to ∑ a(n) * q^(ℓ*n) mod ℓ,
but stated in the language of sequences. -/

noncomputable section

open Modulo2


variable {ℓ n : ℕ} [NeZero ℓ]
variable {k j : ZMod (ℓ-1)}
variable {a b : ModularFormMod ℓ k}

open Nat Finset ZMod Finset.Nat



attribute [simp] pow_card pow_card_sub_one


section Pow_Prime

-- Declares that two functions, which can be thought of as tuples, are permutations of one another
def perm_equiv {n : ℕ} (a b : Fin n → ℕ) :=
  ∃ c : Equiv.Perm (Fin n), a = b ∘ c

lemma perm_equiv_refl {n : ℕ} (a : Fin n → ℕ) : perm_equiv a a :=
  ⟨1, by rw [Equiv.Perm.coe_one]; rfl⟩

theorem perm_equiv_symm {n} {a b : Fin n → ℕ} : perm_equiv a b → perm_equiv b a := by
  rintro ⟨c, hc⟩; use c⁻¹; rw[hc]; ext x;
  simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]

theorem perm_equiv_trans {n} {a b c : Fin n → ℕ} : perm_equiv a b → perm_equiv b c → perm_equiv a c := by
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩
  refine ⟨σ.trans τ, ?_⟩
  ext i
  have : b (σ i) = (c ∘ τ) (σ i) := by
    simpa only [Function.comp_apply] using congrArg (fun f => f (σ i)) hτ
  simpa only [hσ, Function.comp_apply, Function.comp, Equiv.trans_apply]


theorem perm_equiv_const {n} {a b: Fin n → ℕ} (aconst : ∀ i j, a i = a j)
    (h : perm_equiv a b) : a = b := by
  obtain ⟨c,rfl⟩ := h
  ext i
  have := aconst i (c.symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply]

lemma sum_eq_of_perm_equiv {n} {a b : Fin n → ℕ} (h : perm_equiv a b) :
    ∑ i, a i = ∑ i, b i := by
  obtain ⟨c,hc,rfl⟩ := h
  exact Equiv.sum_comp c b

-- the equivalence class of functions that are permutations of x
def perm_setoid : Setoid ( Fin n → ℕ ) where
  r := perm_equiv
  iseqv := ⟨perm_equiv_refl, perm_equiv_symm, perm_equiv_trans⟩


def orbit_finset {k} (x : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  univ.image (fun c : Equiv.Perm (Fin k) ↦ x ∘ c)

def Stab {k} (x : Fin k → ℕ) : Finset (Equiv.Perm (Fin k)) := {c : Equiv.Perm (Fin k) | x ∘ c = x}

lemma orbit_equiv {k} {x y: Fin k → ℕ} : y ∈ orbit_finset x ↔ perm_equiv x y := by
  unfold perm_equiv orbit_finset; constructor <;> intro h <;>
  simp_all only [mem_image, mem_univ, true_and]
  obtain ⟨c, rfl⟩ := h
  use c⁻¹; ext; simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]
  obtain ⟨c, rfl⟩ := h
  use c⁻¹; ext; simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]


lemma perm_of_orbit {k} {x b : Fin k → ℕ} (h : b ∈ orbit_finset x) : perm_equiv x b := by
  rcases Finset.mem_image.mp h with ⟨c, _, rfl⟩
  use c⁻¹; ext i; simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]

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
  ext i; simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]


def subtype_univ_equiv {α : Type*} [Fintype α] : ({a : α // a ∈ (Finset.univ : Finset α)}) ≃ α where
    toFun := Subtype.val
    invFun := fun a => ⟨a, mem_univ a⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun _ => rfl



lemma orbit_decomp {k} (x : Fin k → ℕ) : #(Finset.univ : Finset (Equiv.Perm (Fin k))) = #(orbit_finset x) * #(Stab x) := by
      {
        let f : Equiv.Perm (Fin k) → (Fin k → ℕ) := fun g ↦ x ∘ g
        calc
          _  = ∑ y ∈ Finset.univ.image f, ((Finset.univ.filter (fun g ↦ f g = y)).card) := by
            exact card_eq_sum_card_image f Finset.univ
          _ = ∑ y ∈ orbit_finset x, #(Stab x) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            simp only [f, Stab]
            have hyy := orbit_equiv.1 hy
            obtain ⟨d, rfl⟩ := hyy
            have {c : Equiv.Perm (Fin k)} : (y ∘ ⇑d) ∘ ⇑c = y ∘ ⇑d ↔ ((y ∘ ⇑d) ∘ ⇑c) ∘ ⇑d⁻¹ = y := by
              constructor <;> intro h; rw[h]; ext
              simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]
              nth_rw 2[← h]; ext; simp only [Function.comp_apply, Equiv.Perm.inv_apply_self]

            simp only [this]

            have im_eq :  Finset.image (fun g => g * d) { g : Equiv.Perm (Fin k) | (y ∘ d) ∘ g = y } =
                ({ c : Equiv.Perm (Fin k) | ((y ∘ d) ∘ c) ∘ ⇑d⁻¹ = y } : Finset (Equiv.Perm (Fin k))) := by
              ext c
              constructor
              intro h
              simp_all; nth_rw 2[← h]; ext; simp
              intro h
              simp_all; nth_rw 2[← h]; ext; simp

            rw[← im_eq]
            refine Eq.symm (Finset.card_image_of_injOn ?_)
            intro x hx z hz
            simp_all

          _ = #(orbit_finset x) * #(Stab x) := sum_const_nat λ _ ↦ congrFun rfl
      }


lemma decomp_div {k} (x : Fin k → ℕ): #(orbit_finset x) = #(univ : Finset (Equiv.Perm (Fin k))) / #(Stab x) := by
  refine Nat.eq_div_of_mul_eq_left ?_ (id (Eq.symm (orbit_decomp x)))
  unfold Stab; apply Finset.card_ne_zero.mpr
  use 1; simp

lemma Stab_pi {k} (x : Fin k → ℕ) : #(Stab x) = ∏ m ∈ univ.image x, (#{n | x n = m})! := by

      { -- rewriting to be able to apply DomMulAct.stabilizer_card

        let y : Fin k → {m // m ∈ image x univ} :=
          fun n ↦ ⟨x n, mem_image_of_mem x (mem_univ n)⟩

        let Stab' := {g : Equiv.Perm (Fin k) // y ∘ g = y}


        have Stabsyou : #(Stab x) = Fintype.card Stab' := by
          unfold Stab' Stab
          apply card_eq_of_equiv_fintype
          apply Equiv.subtypeEquivProp
          ext c; constructor <;> intro h
          simp at h
          funext n; simp[y]
          trans (x ∘ c) n
          simp; rw[h]
          simp_all[y]
          ext n
          exact congrArg Subtype.val (congrFun h n)

        have rrw (m : ℕ) : #{n | x n = m} = Fintype.card { a // y a = m } := by
          apply card_eq_of_equiv_fintype
          apply Equiv.subtypeEquivProp
          ext n; constructor <;> intro h <;> simp_all[y]

        rw[Stabsyou]
        simp_rw [rrw]
        unfold Stab'

        have rrr : ∏ m ∈ image x univ, (Fintype.card { a // x a = m })! =
            ∏ m : {m // m ∈ image x univ}, (Fintype.card { a // y a = m })! := by

          let f (α : Type 0) [Fintype α] : ℕ := Nat.factorial (Fintype.card α)

          have eq3 {m}: (Fintype.card { a // x a = m })! = f { a // x a = m } := by simp[f]
          have eq4 {m}: (Fintype.card { a // y a = m })! = f { a // y a = m } := by simp[f]

          have eq5 {m}: f { a // x a = m } = f { a // y a = m } := by congr

          let h (m : ℕ) := f { a // y a = m }

          have eq6 {m} : f { a // y a = m } = h m := by
            obtain ⟨val, property⟩ := m
            simp_all only [Subtype.mk.injEq, h, f, y]

          simp_rw[eq3,eq4,eq5]
          simp; symm
          simp_rw[eq6]

          rw [prod_attach]

        rw[rrr]

        apply DomMulAct.stabilizer_card
      }


lemma orbit_card {k} (x : Fin k → ℕ) : #(orbit_finset x) = k ! / ∏ m ∈ univ.image x, (#{n | x n = m})! := by
  have card_univ : #(Finset.univ : Finset (Equiv.Perm (Fin k))) = (k)! := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw[← card_univ, ← Stab_pi]; exact decomp_div x

-- If the tuple x is not constant, ie [k,k,k, ..], then
-- ℓ | (# of permutations of x ∈ antidiagonalTuple ℓ n)
lemma non_diag_vanish {k n : ℕ} {x : Fin k → ℕ} [Fact (Nat.Prime k)] (h : ¬ ∀ i j, x i = x j) :
    k ∣ #{ b ∈ antidiagonalTuple k n | perm_equiv x b } := by

  push_neg at h
  obtain ⟨w, u, h⟩ := h

  by_cases xiT : x ∈ antidiagonalTuple k n

  { -- x ∈ antidiagonalTuple k n → card = (k)! / ∏ m ∈ univ.image x, (#{n | x n = m})!
    have perm_in_set {b} (h : perm_equiv x b) : b ∈ { b ∈ antidiagonalTuple k n | perm_equiv x b } := by
      refine mem_filter.mpr ⟨?_, h⟩
      apply mem_antidiagonalTuple.mpr
      trans ∑ i, x i
      exact sum_eq_of_perm_equiv (perm_equiv_symm h)
      apply mem_antidiagonalTuple.mp xiT


    rw[← orbit_eq_tuple xiT]

    -- the stabilizer : the set of permutations which leave x unchanged


    -- the orbit stabilizer theorem, stated in finset language

    have card_univ : #(Finset.univ : Finset (Equiv.Perm (Fin k))) = (k)! := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]


    rw[decomp_div, card_univ]

    have Stabpos : #(Stab x) ≠ 0 := Finset.card_ne_zero.mpr ⟨1, by simp [Stab]⟩
    have kPrime : Nat.Prime k := Fact.out
    have kn0 : k ≠ 0 := Ne.symm (NeZero.ne' k)

    suffices getStabbed : ¬ k ∣ #(Stab x) by
      have unStabbed : #(Stab x) ∣ (k)! := by
        use #(orbit_finset x); rw[mul_comm, ← (orbit_decomp x), card_univ]
      have : k ∣ k ! := dvd_factorial (zero_lt_of_ne_zero kn0) (le_refl k)
      obtain ⟨t, ht⟩ := unStabbed
      have hmul : k ∣ ((Stab x).card : ℕ) * t := by rw[← ht]; exact this

      rcases (Nat.Prime.dvd_mul kPrime).1 hmul with h|h
      contradiction
      rw[ht]; rw [mul_div_cancel_left₀ t Stabpos]
      exact h


    clear! n perm_in_set card_univ


    -- Final Step : ¬ k ∣ #Stab

    intro divStab


    have : ∀ m ∈ univ.image x, ¬ k ∣ (#{n | x n = m})! := by
      intro m hm
      suffices conned : #{n | x n = m} < k by
        contrapose! conned
        exact (Nat.Prime.dvd_factorial kPrime).1 conned

      by_cases xwm : x w = m

      have xum : u ∉ ({n | x n = m} : Finset (Fin k)) := by simp; rw[← xwm]; exact λ a ↦ h (id (Eq.symm a))
      contrapose! xum
      have : ({n | x n = m} : Finset (Fin k)) = univ := by
        apply Finset.eq_univ_of_card
        trans k
        exact le_antisymm (card_finset_fin_le {n | x n = m}) xum
        exact Eq.symm (Fintype.card_fin k)
      rw[this]; exact mem_univ u

      have xum : w ∉ ({n | x n = m} : Finset (Fin k)) := by
        contrapose! xwm; simp_all only [ne_eq, mem_univ, true_and, mem_filter]
      contrapose! xum
      have : ({n | x n = m} : Finset (Fin k)) = univ := by
        apply Finset.eq_univ_of_card
        trans k
        exact le_antisymm (card_finset_fin_le {n | x n = m}) xum
        exact Eq.symm (Fintype.card_fin k)
      rw[this]; exact mem_univ w

    contrapose! this; clear this
    rw [Stab_pi] at divStab

    have kPrime' : _root_.Prime k := prime_iff.mp kPrime

    -- Convert the finset product to a list product
    have : ∏ m ∈ (image x univ), (#{n | x n = m})! = List.prod ((image x univ).toList.map (λ m => (#{n | x n = m})!)) :=
      Eq.symm (prod_map_toList (image x univ) λ m ↦ (#{n | x n = m})!)
    rw [this] at divStab
    obtain ⟨a, ha, hka⟩ := (Prime.dvd_prod_iff kPrime').mp divStab
    rcases List.mem_map.mp ha with ⟨m, hm, rfl⟩
    exact ⟨m, Finset.mem_toList.mp hm, hka⟩
  }

  { -- x ∉ antidiagonalTuple k n → card = 0
    use 0; simp; apply filter_false_of_mem
    intro b hb; contrapose! xiT
    apply mem_antidiagonalTuple.mpr
    trans ∑ i, b i
    exact sum_eq_of_perm_equiv xiT
    exact mem_antidiagonalTuple.mp hb
  }

-- the products over two permutationally equivalent functions are equal
lemma Pi_eq_of_perm_equiv {n : ℕ} {a : ℕ → ZMod n} {x y : Fin n → ℕ} (hxy : perm_equiv x y) :
    ∏ z, a (y z) = ∏ z, a (x z) := by
  symm; unfold perm_equiv at hxy
  obtain ⟨c, hc⟩ := hxy
  simp only [hc, Function.comp_apply]
  exact Fintype.prod_equiv c (fun x ↦ a (y (c x))) (fun x ↦ a (y x)) (congrFun rfl)

lemma antidiag_of_perm_equiv {k n} {x y : Fin k → ℕ} (h : x ∈ antidiagonalTuple k n)
    (p : perm_equiv y x) : y ∈ antidiagonalTuple k n := by
  rw[mem_antidiagonalTuple] at *
  obtain ⟨c, rfl⟩ := p; trans ∑ i, x i
  exact Fintype.sum_equiv c (x ∘ ⇑c) x (congrFun rfl)
  exact h

-- every element of a non-diagonal tuple is non-constant
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

-- every non-diagonal element of a diagonal tuple is non-constant
lemma non_const_of_tuple_diag {k n : ℕ} (x : Fin k → ℕ) (kn0 : k ≠ 0) (hx : x ∈ antidiagonalTuple k (k * n) \ {fun _ ↦ n}) :
    (¬ ∀ i j, x i = x j) := by
  contrapose! hx
  have hmk : ∃ m, k = m + 1 := exists_eq_succ_of_ne_zero kn0
  obtain ⟨m,hm,rfl⟩ := hmk
  by_contra! h
  have hnconst : x ≠ fun x ↦ n := by
    contrapose! h; simp; exact λ _ ↦ h
  have : ∑ i, x i = (m + 1) * n := by apply mem_antidiagonalTuple.mp; simp_all only [mem_sdiff]
  have const : ∑ i, x i = (m + 1) * x 0 := by
    specialize hx 0
    trans ∑ _ : Fin (m + 1), x 0
    exact Eq.symm (Fintype.sum_congr (fun a ↦ x 0) x hx)
    apply Fin.sum_const
  contrapose! hnconst
  ext i
  calc
   x i = x 0 := hx i 0
   x 0 = n :=
    let this : (m + 1) * n = (m + 1) * x 0 := this ▸ const
    (Nat.mul_right_inj kn0).mp this.symm


theorem Pow_Prime {n : ℕ} {a : ModularFormMod ℓ k} [Fact (Nat.Prime ℓ)] : (a ** ℓ) n = if ℓ ∣ n then (a (n / ℓ)) else 0 := by

  by_cases h : ℓ ∣ n

  { -- antidiagonalTuple is diagonal (ie ℓ ∣ len) → only diagonal tuple remains
    simp [pow_apply,h]
    obtain ⟨k,rfl⟩ := h
    have la : ℓ * k / ℓ = k := by
      refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ rfl); exact Ne.symm (NeZero.ne' ℓ)
    rw[la]
    have vanish : ∑ x ∈ antidiagonalTuple ℓ (ℓ * k) \ {fun _ ↦ k}, ∏ y, a (x y) = 0 := by
      {
        let Tup := antidiagonalTuple ℓ (ℓ * k) \ {fun _ ↦ k}

        have blister : ∀ x ∈ Tup, ℓ ∣ #{ b ∈ antidiagonalTuple ℓ (ℓ * k) | perm_equiv x b } :=
          λ x hx ↦ non_diag_vanish (non_const_of_tuple_diag x (Ne.symm (NeZero.ne' ℓ)) hx)

        have Step (x : Fin ℓ → ℕ) : ∑ z ∈ {b ∈ Tup | perm_equiv x b}, ∏ y, a (z y) = 0 := by
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

            {
              have Tup_eq : {b ∈ Tup | perm_equiv x b} = {b ∈ antidiagonalTuple ℓ (ℓ * k) | perm_equiv x b} := by
                {
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
                  exact mem_sdiff.mpr ⟨ciT, notMem_singleton.mpr cc⟩
                  simp_all only [mem_sdiff, mem_singleton, and_imp, mem_filter, Tup]
                }

              have hxx : x ∈ Tup := by
                simp_all only [mem_sdiff, mem_singleton, true_and, Tup]
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
          }

          {
            have empty : {b ∈ Tup | perm_equiv x b} = ∅ := by
              refine filter_false_of_mem ?_
              intro b hb; contrapose! hx
              refine mem_antidiagonalTuple.mpr ?_
              trans ∑ i, b i
              exact sum_eq_of_perm_equiv hx
              refine mem_antidiagonalTuple.mp ?_
              simp_all only [mem_sdiff, mem_singleton, and_imp, Tup]
            rw[empty]; rfl
          }

        -- The Set-theoretic quotient of Tup by permutational equvalence
        let Qfin := (Tup).image (Quotient.mk (perm_setoid))

        -- Rewrite as a sum over Qfin so that we can apply Step
        calc
          _  = ∑ q ∈ Qfin, ∑ z ∈ {x ∈ Tup | ⟦x⟧ = q}, ∏ y, a (z y) := by
              apply sum_partition
          _ = ∑ q ∈ Qfin, 0 := by
              apply sum_congr rfl
              intro q hq
              rcases Quot.exists_rep q with ⟨x, rfl⟩
              trans ∑ z ∈ Tup with perm_equiv x z, ∏ y, a (z y)
              congr; funext z; apply propext
              have : ⟦z⟧ = Quot.mk (⇑perm_setoid) x ↔ perm_equiv z x := Quotient.eq
              rw[this]; constructor <;> exact perm_equiv_symm
              exact Step x
          _ = 0 := sum_const_zero

      }

    calc
      _ = ( ∑ x ∈ antidiagonalTuple ℓ (ℓ * k) \ {fun _ ↦ k}, ∏ y, a (x y) ) +
          ( ∑ x ∈ {fun _ ↦ k}, ∏ y : Fin ℓ, a (x y) ) := by
        apply Eq.symm (sum_sdiff _); apply singleton_subset_iff.2
        apply mem_antidiagonalTuple.mpr; simp[sum_const]

      _ = 0 + ∑ x ∈ {fun _ ↦ k}, ∏ y : Fin ℓ, a (x y) := by congr
      _ = ∏ _ : Fin ℓ, a k := by simp only [sum_singleton, prod_const, card_univ,
        Fintype.card_fin, pow_card, zero_add]
      _ = (a k) ^ ℓ := Fin.prod_const ℓ (a k)
      _ = a k := pow_card (a k)
  }


  { -- antidiagonalTuple is not diagonal → no tuples remain
    simp[pow_apply,h]

    have blister : ∀ x ∈ antidiagonalTuple ℓ n, ℓ ∣ #{ b ∈ antidiagonalTuple ℓ n | perm_equiv x b } :=
      λ x hx ↦ non_diag_vanish (non_const_of_tuple_non_diag h x hx)

    have Step : ∀ x : (Fin ℓ → ℕ), ∑ z ∈ {b ∈ antidiagonalTuple ℓ n | perm_equiv x b}, ∏ y, a (z y) = 0 := by
      {
        intro x
        by_cases hx : x ∈ antidiagonalTuple ℓ n
        {
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
        }

        {
          have empty : {b ∈ antidiagonalTuple ℓ n | perm_equiv x b} = ∅ := by
            refine filter_false_of_mem ?_
            intro b hb; contrapose! hx
            refine mem_antidiagonalTuple.mpr ?_
            trans ∑ i, b i
            exact sum_eq_of_perm_equiv hx
            exact mem_antidiagonalTuple.mp hb
          rw[empty]; rfl
        }
      }

    let Qfin := (antidiagonalTuple ℓ n).image (Quotient.mk (perm_setoid))

    calc
      _  = ∑ q ∈ Qfin, ∑ z ∈ {x ∈ antidiagonalTuple ℓ n | ⟦x⟧ = q}, ∏ y, a (z y) := by
          apply sum_partition
      _ = ∑ q ∈ Qfin, 0 := by
          apply sum_congr rfl
          intro q hq
          rcases Quot.exists_rep q with ⟨x, rfl⟩
          trans ∑ z ∈ antidiagonalTuple ℓ n with perm_equiv x z, ∏ y, a (z y)
          congr; funext z; apply propext
          have : ⟦z⟧ = Quot.mk (⇑perm_setoid) x ↔ perm_equiv z x := Quotient.eq
          rw[this]; constructor <;> exact perm_equiv_symm
          exact Step x
      _ = 0 := sum_const_zero
  }


theorem Pow_Prime' {a : ModularFormMod ℓ k} [Fact (Nat.Prime ℓ)] : (a ** ℓ) == fun n ↦ if ℓ ∣ n then (a (n / ℓ)) else 0 :=
  λ _ ↦ Pow_Prime


end Pow_Prime


lemma pow_2_eq_mul_self (a : ModularFormMod ℓ k) (n : ℕ) : (pow a 2) n = (a * a) n := by
  rw[pow_apply]; simp[antidiagonalTuple_two]


def self_mul (a : ModularFormMod ℓ k) : (j : ℕ) → ModularFormMod ℓ (k * j)
  | 0 => Mcongr (by rw [Nat.cast_zero, mul_zero]) (const 1)
  | j + 1 => Mcongr (by rw [Nat.cast_add, Nat.cast_one]; group) (a * self_mul a j)



instance inst_antdiagFintype {j : ℕ} : Fintype {z : Fin j → ℕ // ∑ i, z i = n} := by

  apply Fintype.subtype (antidiagonalTuple j n)
  simp only [mem_antidiagonalTuple, implies_true]



instance inst_IsEmpty_of_lt {x j : ℕ} (xn : x > n) : IsEmpty {z : Fin j → ℕ // x + ∑ i, z i = n} := by
  refine Subtype.isEmpty_of_false ?_
  intro z; apply Nat.ne_of_gt
  exact Nat.lt_add_right (∑ i, z i) xn


instance inst_antidaigFintype_add {x j : ℕ} : Fintype {z : Fin j → ℕ // x + ∑ i, z i = n} := by
  by_cases xn : x > n
  have : IsEmpty {z : Fin j → ℕ // x + ∑ i, z i = n} := inst_IsEmpty_of_lt xn
  apply Fintype.ofIsEmpty

  apply Fintype.subtype (antidiagonalTuple j (n - x))
  intro z; simp_all only [mem_antidiagonalTuple, not_gt_eq]
  constructor <;> intro h
  simp_all only [add_tsub_cancel_of_le]
  subst h
  simp_all only [add_tsub_cancel_left]


def PowFacts.Hidden.g {j} : { x : Fin (j + 1) // ↑x < j} ≃ Fin j where

  toFun := fun ⟨x, prop⟩ ↦ ⟨x.val, prop⟩

  invFun := fun ⟨x, prop⟩ ↦ ⟨ ⟨x, prop.trans (Nat.lt_succ_self j)⟩, prop⟩

  left_inv := congrFun rfl

  right_inv := congrFun rfl


lemma le_sum_fintype {α : Type} {j : α} [Fintype α] {x : α → ℕ} : x j ≤ ∑ i : α, x i := calc
  x j ≤ ∑ i ∈ univ \ {j}, x i + x j := by
    nth_rw 1 [← zero_add (x j)]; gcongr; exact Nat.zero_le _
  _ = _ := Eq.symm (sum_eq_sum_diff_singleton_add (mem_univ j) x)



def PowFacts.Hidden.e {n j} {i : Fin (n + 1)} : (i : Fin (n + 1)) × { z : Fin j → ℕ // ↑i + ∑ i, z i = n }
    ≃ { z : Fin (j + 1) → ℕ // ∑ i, z i = n } where


  toFun := fun ⟨i, ⟨z, _⟩⟩ ↦ ⟨ fun k ↦ if h : k < j then z ⟨k, h⟩ else i , by

      expose_names; rw[sum_dite, add_comm]; trans ↑i + ∑ i, z i; congr 1
      rw[sum_const, smul_eq_mul]; nth_rw 2 [← one_mul (Fin.val i)]
      congr; apply @Fintype.card_eq_one_of_forall_eq _ _ ⟨ ( ⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1) ),
                by simp only [mem_filter, mem_univ, true_and, lt_self_iff_false, not_false_eq_true]⟩
      intro k;
      obtain ⟨k, property_1⟩ := k
      simp_all only [Subtype.mk.injEq]
      simp_all only [not_lt, mem_filter, mem_univ, true_and]
      have : k ≤ j := Fin.is_le k
      apply Fin.eq_of_val_eq
      exact Eq.symm (Nat.le_antisymm property_1 this)


      trans ∑ x : {x : Fin (j + 1) // ↑x < j}, z ⟨↑↑x, x.2⟩

      apply sum_bijective (fun ⟨z,prop⟩ ↦ ⟨z, by rw[mem_filter] at prop; exact prop.2⟩)

      refine Function.bijective_iff_has_inverse.mpr ?_

      use (fun ⟨z,prop⟩ ↦ ⟨z, by rw[mem_filter]; exact ⟨mem_univ _, prop⟩⟩)
      constructor <;> intro k <;> simp only [Subtype.coe_eta]

      simp only [mem_univ, implies_true]
      intro k kuniv; rfl

      apply sum_equiv g
      simp only [mem_univ, implies_true]
      intro k kuniv
      unfold g; dsimp

      exact property  ⟩


  invFun :=
      let hj := Nat.lt_succ_self j
      let hi {k} {klj : k < j} := klj.trans hj
      fun ⟨z , zsum⟩ ↦ ⟨ ⟨z ⟨j, hj⟩, by
      apply lt_succ_of_le; exact Trans.trans le_sum_fintype zsum⟩ ,
      ⟨ fun ⟨k, klj⟩ ↦ z ⟨k, hi⟩, by

        dsimp; trans z ⟨j, hj⟩ + ∑ i : {x : Fin (j + 1) // ↑x < j}, z ⟨↑↑i, i.2.trans hj⟩
        congr 1; symm; apply sum_equiv g
        simp only [mem_univ, implies_true]
        intro k kuniv
        unfold g; dsimp
        exact λ _ _ _ _ _ ↦ id

        trans z ⟨j, hj⟩ + ∑ i ∈ univ \ { ⟨j,hj⟩ }, z i
        congr 1; refine Eq.symm (sum_subtype (univ \ {⟨j, hj⟩}) ?_ z)
        intro k; simp only [mem_sdiff, mem_univ, true_and, mem_singleton]
        constructor <;> intro hk
        contrapose! hk
        have : ↑k ≤ j := Fin.is_le k
        have : ↑k = j := Nat.le_antisymm this hk
        rename_i x this_1
        subst zsum
        simp_all only [le_refl]
        obtain ⟨val, property⟩ := x
        ext : 1
        simp_all only
        rename_i x
        subst zsum
        obtain ⟨val, property⟩ := x
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [lt_self_iff_false]

        trans ∑ i, z i
        refine Eq.symm (sum_eq_add_sum_diff_singleton (mem_univ _) z)
        exact zsum
      ⟩ ⟩


  left_inv := by
    refine Function.leftInverse_iff_comp.mpr ?_
    ext k; simp only [Function.comp_apply, lt_self_iff_false, Fin.is_lt,
        ↓reduceDIte, Fin.eta, id_eq]
    simp_all only [Function.comp_apply, lt_self_iff_false, Fin.is_lt, Fin.eta,
      dite_eq_ite, ↓reduceIte, ↓reduceDIte, subset_refl, Set.coe_inclusion, id_eq]


  right_inv := by
    refine Function.rightInverse_iff_comp.mpr ?_
    ext k; simp only [Function.comp_apply, lt_self_iff_false, Fin.is_lt,
        ↓reduceDIte, Fin.eta, id_eq]
    simp_all only [Function.comp_apply, lt_self_iff_false, Fin.is_lt, Fin.eta,
      dite_eq_ite, ↓reduceIte, ↓reduceDIte, subset_refl, Set.coe_inclusion, id_eq]
    simp_all only [ite_eq_left_iff, not_lt]
    expose_names
    intro a_1
    obtain ⟨val, property⟩ := k
    subst property
    simp_all only
    have : ↑x ≤ j := Fin.is_le x
    have : x = j := Nat.le_antisymm this a_1
    apply congrArg
    ext; simp_all only


open PowFacts.Hidden


lemma Pow_eq_self_mul {a : ModularFormMod ℓ k} {j} : self_mul a j = a ** j := by

  induction j with
  | zero =>
    unfold self_mul; ext n
    cases n <;> simp[pow_apply]
  | succ j ih =>
    unfold self_mul;
    ext n; simp only [ih, cast_eval, mul_apply, pow_apply]


    calc
      _ = ∑ x ∈ antidiagonal n, ∑ z ∈ antidiagonalTuple j x.2, a x.1 * ∏ y, a (z y) := by
        simp_rw[mul_sum]

      _ = ∑ x ∈ range (n + 1), ∑ z ∈ antidiagonalTuple j (n - x), a x * ∏ y, a (z y) := by
        apply sum_antidiagonal_eq_sum_range_succ_mk

      _ = ∑ x : Fin (n + 1),  ∑ z ∈ antidiagonalTuple j (n - x), a x * ∏ y, a (z y) := by
        apply sum_range

      _ = ∑ x : Fin (n + 1), ∑ z : {z : Fin j → ℕ // x + ∑ i, z i = n}, a x * ∏ y, a (z.1 y) := by
        congr; ext k; apply sum_subtype; intro x; simp_rw[mem_antidiagonalTuple]
        constructor <;> intro h
        have : ↑k ≤ n := Fin.is_le k
        simp_all only [add_tsub_cancel_of_le]
        exact Nat.eq_sub_of_add_eq' h


      _ = ∑ z : {z : Fin (j+1) → ℕ // ∑ i, z i = n}, ∏ y, a (z.1 y) := by
          rw[Finset.sum_sigma']; simp
          apply Finset.sum_equiv e
          intro; simp only [mem_univ]
          intro z zuniv
          unfold e; dsimp

          obtain ⟨fst, snd⟩ := z
          obtain ⟨z, property⟩ := snd
          dsimp; symm

          rw[prod_apply_dite, mul_comm]; congr 1

          rw[prod_const]; nth_rw 2 [← pow_one (a ↑fst)]
          congr; apply @Fintype.card_eq_one_of_forall_eq _ _ ⟨ ( ⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1) ),
                  by simp only [mem_filter, mem_univ, true_and, lt_self_iff_false, not_false_eq_true]⟩

          intro k;
          simp_all only [mem_univ]
          obtain ⟨k, property_1⟩ := k
          simp_all only [Subtype.mk.injEq]
          simp_all only [not_lt, mem_filter, mem_univ, true_and]
          have : k ≤ j := Fin.is_le k
          apply Fin.eq_of_val_eq
          exact Eq.symm (Nat.le_antisymm property_1 this)


          trans ∏ x : {x : Fin (j + 1) // ↑x < j}, a (z ⟨↑↑x, x.2⟩ )

          apply prod_bijective (fun ⟨z,prop⟩ ↦ ⟨z, by rw[mem_filter] at prop; exact prop.2⟩)

          refine Function.bijective_iff_has_inverse.mpr ?_

          use (fun ⟨z,prop⟩ ↦ ⟨z, by rw[mem_filter]; exact ⟨mem_univ _, prop⟩⟩)
          constructor <;> intro k <;> simp only [Subtype.coe_eta]

          simp only [mem_univ, implies_true]
          intro k kuniv; rfl

          apply prod_equiv g
          simp only [mem_univ, implies_true]
          intro k kuniv
          unfold g; dsimp


          exact Fin.ofNat (n + 1) ℓ



      _ = ∑ z ∈ antidiagonalTuple (j + 1) n, ∏ y, a (z y) := by
        symm; apply sum_subtype; intro x; simp_rw[mem_antidiagonalTuple]





lemma leading_pow_zeros [Fact (Nat.Prime ℓ)] {a : ModularFormMod ℓ k} {j n : ℕ} (h : a 0 = 0) (nltj : n < j) :
    (a ** j) n = 0 := by

  rw[pow_apply]
  have smoke : ∀ x ∈ antidiagonalTuple j n, ∃ y, x y = 0 := by
    {
      intro x hx; rw[mem_antidiagonalTuple] at hx
      apply le_of_eq at hx
      contrapose! hx
      simp only [← Nat.one_le_iff_ne_zero] at hx
      calc
        _ < j := nltj
        _ = ∑ _ : Fin j, 1 := by
          rw[sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        _ ≤ _ := sum_le_sum (λ i _ ↦ hx i)
    }
  apply sum_eq_zero
  intro x hx; apply prod_eq_zero_iff.2
  obtain ⟨y,hy⟩ := smoke x hx
  exact ⟨y, mem_univ y, hy ▸ h⟩
