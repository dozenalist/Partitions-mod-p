import PartitionsLeanblueprint.ModularFormDefs
import PartitionsLeanblueprint.ModuloDefs2
import PartitionsLeanblueprint.BasicOperators
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Nat.Prime.Factorial

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


section Pow_Prime

-- Declares that two functions, which can be thought of as tuples, are permutations of one another
def perm_equiv {n : ℕ} (a b : Fin n → ℕ) :=
  ∃ c : Equiv.Perm (Fin n), a = b ∘ c

lemma perm_equiv_refl {n : ℕ} (a : Fin n → ℕ) : perm_equiv a a :=
  ⟨1, by rw [Equiv.Perm.coe_one]; rfl⟩

theorem perm_equiv_symm {n} {a b : Fin n → ℕ} : perm_equiv a b → perm_equiv b a := by
  rintro ⟨c, hc⟩; use c⁻¹; rw[hc]; ext x; simp

theorem perm_equiv_trans {n} {a b c : Fin n → ℕ} : perm_equiv a b → perm_equiv b c → perm_equiv a c := by
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩
  refine ⟨σ.trans τ, ?_⟩
  ext i
  have : b (σ i) = (c ∘ τ) (σ i) := by simpa using congrArg (fun f => f (σ i)) hτ
  simpa [Function.comp, hσ] using this


theorem perm_equiv_const {n} {a b: Fin n → ℕ} (aconst : ∀ i j, a i = a j)
    (h : perm_equiv a b) : a = b := by
  obtain ⟨c,rfl⟩ := h
  ext i
  have := aconst i (c.symm i)
  simp [Equiv.apply_symm_apply] at this
  exact this

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

lemma orbit_equiv {k} {x y: Fin k → ℕ} : y ∈ orbit_finset x ↔ perm_equiv x y := by
  unfold perm_equiv orbit_finset; constructor <;> intro h <;>
  simp_all only [mem_image, mem_univ, true_and]
  obtain ⟨c, rfl⟩ := h
  use c⁻¹; ext; simp
  obtain ⟨c, rfl⟩ := h
  use c⁻¹; ext; simp


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


def subtype_univ_equiv {α : Type*} [Fintype α] : ({a : α // a ∈ (Finset.univ : Finset α)}) ≃ α where
    toFun := Subtype.val
    invFun := fun a => ⟨a, mem_univ a⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun _ => rfl


-- If the tuple x is not constant, ie [k,k,k, ..], then
-- ℓ | (# of permutations of x ∈ antidiagonalTuple ℓ n)
lemma non_diag_vanish {k n : ℕ} {x : Fin k → ℕ} [Fact (Nat.Prime k)] (h : ¬ ∀ i j, x i = x j)  :
    k ∣ #{ b ∈ antidiagonalTuple k n | perm_equiv x b } := by
  simp_all only [not_forall]
  obtain ⟨w, h⟩ := h
  obtain ⟨u, h⟩ := h

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
    let Stab : Finset (Equiv.Perm (Fin k)) := {c : Equiv.Perm (Fin k) | x ∘ c = x}

    -- the orbit stabilizer theorem, stated in finset language
    have decomp : #(Finset.univ : Finset (Equiv.Perm (Fin k))) = #(orbit_finset x) * #Stab := by
      {
      let f : Equiv.Perm (Fin k) → (Fin k → ℕ) := fun g ↦ x ∘ g
      calc
        _  = ∑ y ∈ Finset.univ.image f, ((Finset.univ.filter (fun g ↦ f g = y)).card) := by
          exact card_eq_sum_card_image f Finset.univ
        _ = ∑ y ∈ orbit_finset x, #Stab := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp[f,Stab]
          have hyy := orbit_equiv.1 hy
          obtain ⟨d, rfl⟩ := hyy
          have {c : Equiv.Perm (Fin k)} : (y ∘ ⇑d) ∘ ⇑c = y ∘ ⇑d ↔ ((y ∘ ⇑d) ∘ ⇑c) ∘ ⇑d⁻¹ = y := by
            constructor <;> intro h; rw[h]; ext; simp
            nth_rw 2[← h]; ext; simp

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

        _ = #(orbit_finset x) * #Stab := sum_const_nat λ _ ↦ congrFun rfl
      }

    have card_univ : #(Finset.univ : Finset (Equiv.Perm (Fin k))) = (k)! := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

    have decomp_div : #(orbit_finset x) = #(univ : Finset (Equiv.Perm (Fin k))) / #Stab := by
      refine Nat.eq_div_of_mul_eq_left ?_ (id (Eq.symm decomp))
      unfold Stab; apply Finset.card_ne_zero.mpr
      use 1; simp

    rw[decomp_div, card_univ]

    have Stabpos : #Stab ≠ 0 := Finset.card_ne_zero.mpr ⟨1, by simp [Stab]⟩
    have kPrime : Nat.Prime k := Fact.out
    have kn0 : k ≠ 0 := Ne.symm (NeZero.ne' k)

    suffices getStabbed : ¬ k ∣ #Stab by
      have unStabbed : #Stab ∣ (k)! := by
        use #(orbit_finset x); rw[mul_comm, ← decomp, card_univ]
      have : k ∣ k ! := dvd_factorial (zero_lt_of_ne_zero kn0) (le_refl k)
      obtain ⟨t, ht⟩ := unStabbed
      have hmul : k ∣ (Stab.card : ℕ) * t := by rw[← ht]; exact this

      rcases (Nat.Prime.dvd_mul kPrime).1 hmul with h|h
      contradiction
      rw[ht]; rw [mul_div_cancel_left₀ t Stabpos]
      exact h


    clear! n perm_in_set decomp card_univ decomp_div


    -- Final Step : ¬ k ∣ #Stab

    intro divStab

    have Stab_pi : #Stab = ∏ m ∈ univ.image x, (#{n | x n = m})! := by

      { -- rewriting to be able to apply DomMulAct.stabilizer_card

        clear! w u kPrime kn0 divStab Stabpos

        let y : Fin k → {m // m ∈ image x univ} :=
          fun n ↦ ⟨x n, mem_image_of_mem x (mem_univ n)⟩

        unfold Stab

        let Stab' := {g : Equiv.Perm (Fin k) // y ∘ g = y}


        have Stabsyou : #Stab = Fintype.card Stab' := by
          unfold Stab' Stab
          apply card_eq_of_equiv_fintype
          apply Equiv.subtypeEquivProp
          ext c; constructor <;> intro h
          simp at h
          funext n; simp[y]
          trans (x ∘ c) n
          simp[h]; rw[h]
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

    have : ∀ m ∈ univ.image x, ¬ k ∣ (#{n | x n = m})! := by
      intro m hm
      suffices conned : #{n | x n = m} < k by
        have necon0 : #{n | x n = m} ≠ 0 := (fiber_card_ne_zero_iff_mem_image univ x m).mpr hm
        contrapose! conned
        apply (Nat.Prime.dvd_factorial kPrime).1 conned

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
    use m
    exact ⟨Finset.mem_toList.mp hm, hka⟩

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
  simp[hc]; exact Fintype.prod_equiv c (fun x ↦ a (y (c x))) (fun x ↦ a (y x)) (congrFun rfl)

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
          simp[this]; constructor <;> exact perm_equiv_symm
          exact Step x
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
          simp[this]; constructor <;> exact perm_equiv_symm
          exact Step x
      _ = 0 := sum_const_zero
  }


end Pow_Prime


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
