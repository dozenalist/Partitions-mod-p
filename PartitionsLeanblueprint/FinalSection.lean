import PartitionsLeanblueprint.DescentArgument
import PartitionsLeanblueprint.Basis


/- The goal of this file is to prove that (f ℓ) (δ ℓ + 1) = 1,
that Θ^[(ℓ + 3)/2] (f ℓ) = δ^((ℓ + 3)/2) * E₄ * f ℓ,
and that Θ^[(ℓ + 3)/2] (f ℓ) (2) = 241, and from there derive a contradiction -/

open Modulo2 Finset.Nat Finset

variable [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 5)] [Fact (ℓ ≥ 13)]


lemma Del_two : Δ 2 = (-24 : ZMod ℓ) := sorry



instance : NeZero (δ ℓ) := {out := ne_zero_of_lt delta_pos}



lemma fl_delta_add_one : f ℓ (δ ℓ + 1) = 1 := by


  let q : Fin (δ ℓ) → ℕ
    | 0 => 2
    | n => 1

  let Q : Finset (Fin (δ ℓ) → ℕ) :=
    Finset.univ.image (fun c : Equiv.Perm (Fin (δ ℓ)) ↦ q ∘ c)

  have : ∃ k, δ ℓ = k + 1 := Nat.exists_eq_add_one.mpr delta_pos

  obtain ⟨k,hk⟩ := this


  have memQ {x} : x ∈ Q ↔ perm_equiv x q := by
    constructor <;> intro hk <;> unfold Q perm_equiv at *
    <;> rw [Finset.mem_image] at *
    obtain ⟨c, _, hc⟩ := hk
    use c, hc.symm
    obtain ⟨c,hc⟩ := hk
    use c, mem_univ c, hc.symm


  have qadd : q ∈ antidiagonalTuple (δ ℓ) (δ ℓ + 1) := by
    rw[mem_antidiagonalTuple]
    calc
      ∑ i, q i = ∑ i ∈ univ \ { (0 :Fin (δ ℓ)) }, q i + ∑ i ∈ { (0 :Fin (δ ℓ)) }, q i := by
        symm; apply sum_sdiff; exact subset_univ {0}

      _ = ∑ i ∈ univ \ { (0 :Fin (δ ℓ)) }, 1 + 2 := by
        congr 1; apply sum_congr rfl
        intro x hx
        have xn : x ∉ ({0} : Finset (Fin (δ ℓ))) := mem_compl.mp hx
        have xn0 : ¬ x = 0 := List.ne_of_not_mem_cons xn

        simp_all only [Fin.mk_zero', implies_true, q]

      _ = ∑ i : Fin (δ ℓ), 1 - ∑ i ∈ { (0 :Fin (δ ℓ)) }, 1 + 2  := by
        congr; refine Nat.eq_sub_of_add_eq' ?_
        rw[add_comm]; apply sum_sdiff; exact subset_univ {0}

      _ = δ ℓ - 1 + 2 := by
        congr; rw[sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin]

      _ = δ ℓ + 1 := by
        refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?_ rfl)
        trans 1 + 1; rfl
        apply add_le_add_right
        exact delta_pos


  have Qad : ∀ x ∈ Q, x ∈ antidiagonalTuple (δ ℓ) (δ ℓ + 1) := by
    intro x hx; apply antidiag_of_perm_equiv qadd
    exact memQ.1 hx


  unfold f; simp[pow_apply]; calc

    _ = ∑ x ∈ (antidiagonalTuple (δ ℓ) (δ ℓ + 1)) \ Q, ∏ y, Δ (x y)
      + ∑ x ∈ Q, ∏ y, Δ (x y) := Eq.symm (Finset.sum_sdiff Qad)

    _ = (0 : ZMod ℓ) + (δ ℓ) • ∏ y, Δ (q y) := by
      {
        congr; apply sum_eq_zero
        intro x hx
        have xT : x ∈ antidiagonalTuple (δ ℓ) (δ ℓ + 1) := by
          simp_all only [mem_sdiff]
        have xnQ : x ∉ Q := by simp_all only [mem_sdiff, not_false_eq_true]
        rw[prod_eq_zero_iff]
        suffices ∃ a, x a = 0 by
          obtain ⟨a, ha⟩ := this
          use a, mem_univ a, ha ▸ rfl
        contrapose! xnQ; simp_rw[← Nat.one_le_iff_ne_zero] at xnQ
        rw[memQ]

        suffices u2 : ∃! y, x y = 2 by
          {
            obtain ⟨k, hk, h⟩ := u2
            dsimp at h
            use Equiv.swap k 0
            ext i; dsimp;
            by_cases ik : i = k
            trans 2; rwa[ik]
            rw[ik]; trans q 0; rfl
            rw [Equiv.swap_apply_left]

            trans 1
            rw[mem_antidiagonalTuple] at xT
            apply le_of_eq at xT
            contrapose! xT
            have ilarge : x i ≥ 2 := by
              specialize xnQ i
              apply Nat.succ_le_of_lt (lt_of_le_of_ne xnQ xT.symm)

            calc
              _ < (δ ℓ - 2) + 2 + 2 := by omega

              _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (δ ℓ))), 1 - ∑ i ∈ ({i, k} : Finset (Fin (δ ℓ))), 1 + (x k + x i) := by
                rw[← add_assoc]; apply add_le_add; apply le_of_eq
                congr 1; rw[sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin]
                rw [sum_pair ik]
                exact hk.symm; exact ilarge

              _ = ∑ i ∈ Finset.univ \ {i, k}, 1 + ∑ i ∈ {i, k}, x i := by
                congr; symm; apply Nat.eq_sub_of_add_eq; apply sum_sdiff
                exact subset_univ {i, k}
                trans ∑ i ∈ {i}, x i + ∑ i ∈ {k}, x k
                simp only [sum_singleton, add_comm]
                exact Eq.symm (sum_pair ik)

              _ ≤ ∑ i ∈ Finset.univ \ {i, k}, x i + ∑ i ∈ {i, k}, x i := by
                apply add_le_add_right; apply sum_le_sum
                rintro y hy
                exact xnQ y

              _ = _ := sum_sdiff (subset_univ {i, k})

            by_cases i0 : i = 0
            trans q k;
            have : ¬ k = 0 := calc
              _ ≠ i := by symm; rwa[ne_eq]
              _ = 0 := i0
            have : NeZero k := {out := this}
            simp_all only [Fin.mk_zero', implies_true, q]
            rw[i0]; rw [Equiv.swap_apply_right]
            have : NeZero i := {out := i0}
            trans q i
            simp_all only [Fin.mk_zero', implies_true, q]
            symm; congr; exact Equiv.swap_apply_of_ne_of_ne ik i0
          }

        rw[mem_antidiagonalTuple] at xT
        unfold ExistsUnique; dsimp
        contrapose! xT
        by_cases y2 : ∃ y, x y = 2
        obtain ⟨k, hk⟩ := y2
        obtain ⟨i, i2, ik⟩ := xT k hk
        have ilarge : x i ≥ 2 := le_of_eq i2.symm
        apply ne_of_gt; calc

          _ < (δ ℓ - 2) + 2 + 2 := by omega

          _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (δ ℓ))), 1 - ∑ i ∈ ({i, k} : Finset (Fin (δ ℓ))), 1 + (x k + x i) := by
              rw[← add_assoc]; apply add_le_add; apply le_of_eq
              congr 1; rw[sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin]
              rw [sum_pair ik]
              exact hk.symm; exact ilarge

          _ = ∑ i ∈ Finset.univ \ {i, k}, 1 + ∑ i ∈ {i, k}, x i := by
                congr; symm; apply Nat.eq_sub_of_add_eq; apply sum_sdiff
                exact subset_univ {i, k}
                trans ∑ i ∈ {i}, x i + ∑ i ∈ {k}, x k
                simp only [sum_singleton, add_comm]
                exact Eq.symm (sum_pair ik)

          _ ≤ ∑ i ∈ Finset.univ \ {i, k}, x i + ∑ i ∈ {i, k}, x i := by
                apply add_le_add_right; apply sum_le_sum
                rintro y hy
                exact xnQ y

          _ = _ := sum_sdiff (subset_univ {i, k})


        push_neg at y2
        by_cases glarge : ∃ g, x g ≥ 3
        obtain ⟨g,glarge⟩ := glarge
        apply ne_of_gt; calc

          _ < (δ ℓ - 1) + 3 := by omega

          _ ≤  ∑ i ∈ (Finset.univ : Finset (Fin (δ ℓ))), 1 - ∑ i ∈ {g}, 1 + x g := by
            apply add_le_add; apply le_of_eq
            congr 1; rwa[sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin]

          _ = ∑ i ∈ Finset.univ \ {g}, 1 + x g := by
            congr; symm; apply Nat.eq_sub_of_add_eq; apply sum_sdiff
            exact subset_univ {g}

          _ ≤ ∑ i ∈ Finset.univ \ {g}, x i + x g := by
            apply add_le_add_right; apply sum_le_sum
            intro i hi; exact xnQ i

          _ = _ := Eq.symm (sum_eq_sum_diff_singleton_add (mem_univ g) x)


        push_neg at glarge

        have smol : ∀ i, x i = 1 := by
          intro i; specialize glarge i
          specialize y2 i; specialize xnQ i
          omega

        apply ne_of_lt; calc

          _ = ∑ i : Fin (δ ℓ), 1 :=
            Fintype.sum_congr x (fun a ↦ 1) smol
          _ = δ ℓ := by
            rw[sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin]
          _ < δ ℓ + 1 := lt_add_one _

        trans ∑ x ∈ Q, ∏ y, Δ (q y)
        apply sum_congr rfl
        intro x xQ; rw[memQ] at xQ
        obtain ⟨c,rfl⟩ := xQ
        exact Fintype.prod_equiv c (fun x ↦ Δ ((q ∘ ⇑c) x)) (fun x ↦ Δ (q x)) (congrFun rfl)
        rw[sum_const]; congr

        trans #(orbit_finset q); rfl
        rw[orbit_card]


        have delany : δ ℓ ≥ 2 := by
            have lg : ℓ ≥ 13 := Fact.out
            unfold δ; trans (169 - 1) / 24
            apply Nat.div_le_div
            rw[Nat.sub_le_sub_iff_right]
            trans 13 ^ 2; exact (le_refl _)
            exact Nat.pow_le_pow_left lg 2
            exact NeZero.one_le
            exact le_refl _
            exact Ne.symm (Nat.zero_ne_add_one 23)
            exact Nat.AtLeastTwo.prop

        have : ¬ (1 : Fin (δ ℓ)) = 0 := by
            simp_all only [ Fin.one_eq_zero_iff, Q, q]
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all only [Nat.not_ofNat_le_one]

        have qimage : image q univ = {1, 2} := by
          refine Eq.symm ((fun {α} {s₁ s₂} ↦ Finset.ext_iff.mpr) ?_)
          intro a; rw[mem_insert, mem_singleton]; constructor <;> intro ha
          rcases ha with a1|a2
          refine mem_image.mpr ?_
          use 1, mem_univ 1
          rw[a1]


          simp_all only [Fin.mk_zero', implies_true, q]
          rw[a2]
          refine mem_image.mpr ?_
          use 0, mem_univ 0
          rfl

          rw[mem_image] at ha
          obtain ⟨k,_,hk⟩ := ha
          by_cases k0 : k = 0
          right; rw[k0] at hk
          rw[← hk]; rfl
          left; rw[← hk]
          simp_all only [Fin.one_eq_zero_iff, Fin.mk_zero', implies_true, q]

        rw[qimage]

        calc
          _ = (δ ℓ).factorial / ((#{n | q n = 1}).factorial * (#{n | q n = 2}).factorial) := by
            congr; refine prod_pair ?_; exact Ne.symm Nat.add_one_add_one_ne_one

          _ = (δ ℓ).factorial / ((δ ℓ - 1).factorial * (1).factorial) := by
            congr; trans #{n : Fin (δ ℓ) | n ≠ 0}; congr; ext n
            constructor <;> intro hn
            by_contra! n0
            have : q n = 2 := by subst n0; rfl
            exact Nat.add_one_add_one_ne_one (this ▸ hn)
            simp_all only [Fin.one_eq_zero_iff, Fin.mk_zero', implies_true, q]

            trans # (univ \ {(0 : Fin (δ ℓ))})
            congr
            simp_all only [ge_iff_le, mem_image, mem_univ, true_and, Fin.one_eq_zero_iff, ne_eq, Q, q]
            ext a : 1
            simp_all only [mem_filter, mem_univ, true_and, mem_sdiff, mem_singleton, Q, q]
            trans #(univ : Finset (Fin (δ ℓ))) - #{(0 : Fin (δ ℓ))}
            refine card_sdiff ?_; exact subset_univ {0}
            congr; exact card_fin (δ ℓ)
            trans #{(0 : Fin (δ ℓ))}; congr
            refine eq_singleton_iff_unique_mem.mpr ?_
            constructor
            refine mem_filter.mpr ⟨mem_univ 0, rfl⟩
            intro x hx; rw [mem_filter] at hx
            simp_all only [ge_iff_le, mem_image, mem_univ, true_and, Fin.one_eq_zero_iff, Q, q]
            split at hx
            next x => simp_all only [Fin.mk_zero', Q, q]
            next x_1 x_2 =>
              simp_all only [mem_singleton, insert_eq_of_mem, Fin.mk_zero', imp_false, OfNat.one_ne_ofNat, Q, q]
            rfl

          _ = (δ ℓ).factorial / (δ ℓ - 1).factorial := by
            rw [Nat.factorial_one, mul_one]

          _ = δ ℓ := by
            rw[hk, Nat.add_one_sub_one]; refine Nat.div_eq_of_eq_mul_left ?_ rfl
            exact Nat.factorial_pos k
      }

    _ = δ ℓ • ((∏ n ∈ {(0 : Fin (δ ℓ))}, Δ (q 0)) * ∏ n ∈ univ \ {(0 : Fin (δ ℓ))}, Δ (q n)) := by
      rw[zero_add]; congr; symm
      rw[mul_comm]; apply prod_sdiff; exact subset_univ {0}

    _ = δ ℓ • (Δ 2 * ∏ n ∈ univ \ {(0 : Fin (δ ℓ))}, Δ (1)) := by
      congr 2; exact prod_singleton (fun x ↦ Δ (q 0)) 0
      apply prod_congr rfl
      intro x hx
      have xn : x ∉ ({0} : Finset (Fin (δ ℓ))) := mem_compl.mp hx
      have xn0 : ¬ x = 0 := List.ne_of_not_mem_cons xn

      congr; simp_all only [Fin.mk_zero', implies_true, q]

    _ =  δ ℓ • (-24 * 1) := by
      congr; exact Del_two
      apply prod_eq_one; intros
      exact Del_one

    _ = ↑((ℓ ^ 2 - 1) / 24 : ℕ) * -24 := by
      rw[mul_one, δ]; exact nsmul_eq_mul ((ℓ ^ 2 - 1) / 24) (-24)

    _ = ↑((ℓ ^ 2 - 1) : ℕ) / ↑(24 : ℕ) * -24 := by
      congr; refine Nat.cast_div ?_ ?_; exact delta_integer
      by_contra! zihn
      rw[ZMod.natCast_zmod_eq_zero_iff_dvd] at zihn
      have lg : ℓ ≥ 13 := Fact.out
      have lprime : Nat.Prime ℓ := Fact.out
      have rw24 : 24 = 8 * 3 := rfl

      have ldiv : ℓ ∣ 8 ∨ ℓ ∣ 3 := by
        rw[rw24] at zihn; exact (Nat.Prime.dvd_mul lprime).mp zihn

      rcases ldiv with div | div <;>
      apply Nat.le_of_dvd at div <;> omega

    _ = - (ℓ ^ 2 - 1) := by
      simp only [Nat.cast_ofNat, mul_neg, CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_sub, neg_neg]
      rw[neg_eq_iff_eq_neg]; trans ↑((ℓ ^ 2 - 1) : ℕ)
      refine (eq_div_iff ?_).mp rfl
      have : (24 : ZMod ℓ) = ↑(24 : ℕ) := rfl
      rw[this]
      by_contra! zihn
      rw[ZMod.natCast_zmod_eq_zero_iff_dvd] at zihn
      have lg : ℓ ≥ 13 := Fact.out
      have lprime : Nat.Prime ℓ := Fact.out
      have rw24 : 24 = 8 * 3 := rfl
      have ldiv : ℓ ∣ 8 ∨ ℓ ∣ 3 := by
        rw[rw24] at zihn; exact (Nat.Prime.dvd_mul lprime).mp zihn

      rcases ldiv with div | div <;>
      apply Nat.le_of_dvd at div <;> omega

      trans ↑(ℓ ^ 2 : ℕ) - ↑(1 : ℕ)
      refine Nat.cast_sub ?_; exact NeZero.one_le
      simp only [Nat.cast_pow, CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, Nat.cast_one, zero_sub]

    _ = 1 := by simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_sub, neg_neg]



lemma Theta_l_add_three_div_two_fl_delta_add_one :
    Θ^[(ℓ + 3)/2] (f ℓ) (δ ℓ + 1) = (δ ℓ + 1) ^ ((ℓ + 3) / 2) := by
  rw[Theta_pow_apply, fl_delta_add_one, mul_one]; congr
  exact Lean.Grind.Semiring.natCast_succ (δ ℓ)


lemma its_actually_241 (flu : f ℓ |𝓤 = 0) :
    Θ^[(ℓ + 3)/2] (f ℓ) (δ ℓ + 1) = 241 * (δ ℓ) ^ ((ℓ + 3) / 2) := sorry


lemma sike (flu : f ℓ |𝓤 = 0) : False := by

  have equel : (δ ℓ + 1) ^ ((ℓ + 3) / 2) ≡ 241 * (δ ℓ) ^ ((ℓ + 3) / 2) [ZMOD ℓ] := by
    suffices (δ ℓ + 1) ^ ((ℓ + 3) / 2) = (241 * (δ ℓ) ^ ((ℓ + 3) / 2) : ZMod ℓ) by
      rw[← ZMod.intCast_eq_intCast_iff]; norm_cast at *
    rw[← Theta_l_add_three_div_two_fl_delta_add_one, ← its_actually_241 flu]

  have nequal :  (δ ℓ + 1) ^ ((ℓ + 3) / 2) ≡ 241 * (δ ℓ) ^ ((ℓ + 3) / 2) [MOD ℓ] := by
    rw[← Int.natCast_modEq_iff]; norm_cast at *


  sorry


-- lemma slorp {a b c n : ℕ}  ( h : (a + 1) ^ b ≡ c * a ^ b [MOD n] ) : sorry := sorry
