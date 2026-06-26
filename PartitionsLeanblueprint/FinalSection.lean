import PartitionsLeanblueprint.DescentArgument
import PartitionsLeanblueprint.PartitionDefs




/- This file proves the main result of the paper:
that there does not exist a ramanujan congruence mod ℓ ≥ 13.
It is the top-most file in the import hierarchy. -/

open ModularFormMod Finset.Nat Finset

variable [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 13)]

instance inst_lge5 : Fact (ℓ ≥ 5) :=
  ⟨ @Nat.le_of_add_right_le 5 ℓ 8 Fact.out ⟩



private instance Oddl : Odd ℓ :=
  let t : ℓ ≥ 5 := Fact.out
  Nat.Prime.odd_of_ne_two Fact.out (by linarith)

instance : NeZero (δ ℓ) := ⟨ne_zero_of_lt delta_pos⟩



lemma fl_delta_add_one : fl ℓ (δ ℓ + 1) = 1 := by

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


  simp only [fl_eq_Delta, Mpow_apply, q]; calc

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
          use a, mem_univ a, ha ▸ Delta_zero
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
            unfold delta; trans (169 - 1) / 24
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
      congr; exact Delta_two
      apply prod_eq_one; intros
      exact Delta_one

    _ = ↑((ℓ ^ 2 - 1) / 24 : ℕ) * -24 := by
      rw[mul_one, delta]; exact nsmul_eq_mul ((ℓ ^ 2 - 1) / 24) (-24)

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
    Θ^[(ℓ + 3)/2] (fl ℓ) (δ ℓ + 1) = (δ ℓ + 1) ^ ((ℓ + 3) / 2) := by
  rw[Theta_pow_apply, fl_delta_add_one, mul_one]; norm_cast


section private_lemmas

omit [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 13)]


instance institobvious : NeZero (6 * δ ℓ + 2) := ⟨by decide⟩

@[norm_cast] lemma l_add_three [hl : NeZero (ℓ - 1)] : (ℓ + 3 : ℕ) = (4 : ZMod (ℓ - 1)) := by
  trans ℓ + 3; exact Mathlib.Tactic.Ring.inv_add rfl rfl
  trans (0 + 1 : ℕ) + 3; congr 1; rw [ZMod.eq_iff_modEq_nat]
  trans (ℓ - 1) + 1; rw [Nat.sub_add_cancel (by have := hl.out; omega)]
  gcongr; rw [Nat.ModEq, Nat.mod_self, Nat.zero_mod]
  norm_num



private lemma mod_caster [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 13)] :
    ((2 * (6 * δ ℓ + 2) : ℕ) : ZMod (ℓ - 1)) = 12 * ↑(δ ℓ) + ↑((ℓ + 3) / 2) * 2 := by
  conv => rhs; rhs; norm_cast; rw [Nat.div_mul_cancel (by have := Nat.odd_iff.mp Oddl; omega)]
  rw [l_add_three, mul_add, ← mul_assoc]; norm_num

open ModularForm in
lemma dim_six_delta_add_two : dim (6 * δ ℓ + 2) = δ ℓ + 1 := by
  simp [dim, if_neg, Nat.add_div]
  rw [Nat.ModEq]; omega



open ModularForm in
private lemma delta_lt_dim : δ ℓ < dim (6 * δ ℓ + 2) := dim_six_delta_add_two ▸ lt_add_one (δ ℓ)


open ModularForm in
private lemma mod_mod_six : (6 * δ ℓ + 2) %% 6 = 2 := by
  rw [mod_without_two, if_neg]
  rw [Nat.add_mod, add_zero]
  trans (0 + 2) % 6; congr
  rw [← Nat.dvd_iff_mod_eq_zero]
  apply Nat.dvd_mul_right_of_dvd <| by norm_num
  rfl

  suffices t : 6 * δ ℓ + 2 ≡ 0 + 2 [MOD 6] from fun h =>
    have := h.symm.trans t
    by rw [Nat.ModEq] at this; omega

  gcongr
  apply Nat.modEq_zero_iff_dvd.mpr
  apply Nat.dvd_mul_right_of_dvd <| by norm_num



open ModularForm in
private lemma Gmk_set_mk_delta : Gmk_set_mk (6 * δ ℓ + 2) (δ ℓ) = (1, 0, δ ℓ) := by
  simp [Gmk_set_mk, mod_mod_six, Gmk_dim_one, Gmk_twelve_mk]
  exact Nat.sub_eq_zero_of_le <| le_of_eq <| Nat.div_eq_of_eq_mul_right zero_lt_two <| by ring

end private_lemmas

set_option push_neg.use_distrib true in open IntegerModularForm in

theorem G_delta_add_one : G (h := ⟨by omega⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩ (δ ℓ + 1) = (241 : ZMod ℓ) := by
  rw [G_def, Icast_apply, mul_apply]
  simp; rw [Gmk_set_mk_delta]; dsimp
  rw [Ipow_one, Ipow_zero, mul_Iconst, one_smul]
  simp only [Icast_apply]; norm_cast
  calc

    _ = (∑ x ∈ antidiagonal (δ ℓ + 1) \ {(0, δ ℓ + 1), (1, δ ℓ)}, (Eis 2) x.1 * (Delta**δ ℓ) x.2
        + (Eis 2 0 * (Delta**δ ℓ) (δ ℓ + 1) + Eis 2 1 * (Delta**δ ℓ) (δ ℓ)) : ZMod ℓ) := by
      norm_cast; congr
      rw [sum_sdiff_eq_sub, sum_pair, sub_add_cancel]
      exact not_eq_of_beq_eq_false rfl
      intro x; simp only [mem_insert, mem_singleton, mem_antidiagonal];
      intro h; rcases h with h | h <;> simp only [h, zero_add, add_comm]

    _ = 0 + 241 := by
      congr; trans ↑(0 : ℤ); congr; apply sum_eq_zero fun x xin => ?_
      simp only [mem_sdiff, mem_antidiagonal, mem_insert, mem_singleton, not_or] at xin

      have : x.2 ≠ δ ℓ ∧ x.2 ≠ δ ℓ + 1 := by
        contrapose! xin
        rw [or_iff_not_imp_left]
        push_neg; intro h'
        rcases xin with h | h
        right; ext <;> omega
        left; ext <;> omega

      have : x.2 < δ ℓ := by omega

      rw [leading_Ipow_zeros Delta_zero this, mul_zero]
      exact Lean.Grind.Ring.intCast_zero

      rw [Eis_ne_one_zero, Int.cast_one, one_mul, Eis_two_one,
        ord_Ipow_ord' _ _ (δ ℓ), ord_Delta, Delta_one, one_pow, Int.cast_one, mul_one]

      rw [← IntegerModularForm.fl, ← ModularFormMod.fl_apply, fl_delta_add_one]; norm_num

      rw [ord_Delta, mul_one]
      exact Nat.add_one_add_one_ne_one

    _ = 241 := zero_add 241





theorem Theta_l_add_three_div_two (flu : fl ℓ |𝓤 = 0) :
  Mcast mod_caster.symm (Θ^[(ℓ + 3)/2] (fl ℓ)) = (Reduce ℓ ((δ ℓ ^ ((ℓ + 3) / 2))
    • IntegerModularForm.G (h := ⟨by decide⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩)) := by

  set fell := (Mcast (by rw[mod_caster.symm]; norm_cast) (Θ^[(ℓ + 3) / 2] (fl ℓ)) : ModularFormMod ℓ (2 * (6 * δ ℓ + 2 : ℕ))) with fellquall

  have fellply : ∀ n, (Θ^[(ℓ + 3) / 2] (fl ℓ)) n = fell n := fun n => by rw [fellquall, Mcast_apply]

  have fellell : ∀ n < δ ℓ, fell n = 0 := fun n nlt => by
    simp only [fellquall, Mcast_apply, Theta_pow_apply, fl_lt_delta nlt, mul_zero]

  have : NeZero fell := by
    rw [fellquall, Mcast_NeZero]
    infer_instance


  have haw : hasWeight fell (2 * (6 * δ ℓ + 2)) := by
    have := Weight_of_Filt (Filt_Theta_l_add_three_div_two flu)
    rw [mul_add, ← mul_assoc]; norm_num; rwa [twelve_delta, fellquall, Weight_Mcast]

  obtain ⟨b', hb, hj, aeq, ordb⟩ := exists_maximal_Reduce fell fellell haw

  ext n; simp only [fellply, aeq, Mcast_apply, Reduce_apply]

  {
    trans ((b' (δ ℓ) • IntegerModularForm.G (h := ⟨by decide⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩ n : ℤ) : ZMod ℓ)

    nth_rw 1 [IntegerModularForm.eq_G_of_ord_max b' (hk := ⟨by omega⟩)]
    simp only [dim_six_delta_add_two, Nat.add_sub_cancel]; congr
    rw [dim_six_delta_add_two, Nat.add_sub_cancel]
    rcases ordb.eq_or_gt with ordb | ordb
    exact ordb
    suffices b' = 0 from absurd this hb.out
    apply IntegerModularForm.zero_of_leading_zeros
    rw [dim_six_delta_add_two]
    intro n nlt
    apply IntegerModularForm.lt_ord_apply; omega


    trans ((((δ ℓ) ^ ((ℓ + 3) / 2) : ℤ) • IntegerModularForm.G (h := ⟨by decide⟩) (6 * δ ℓ + 2) ⟨δ ℓ, delta_lt_dim⟩ n : ℤ) : ZMod ℓ)
    simp only [IntegerModularForm.zsmul_apply, smul_eq_mul, Int.cast_mul]
    push_cast; congr 2; trans fell (δ ℓ)
    simp only [aeq, Mcast_apply, Reduce_apply]
    rw [fellquall, Mcast_apply, Theta_pow_apply, fl_delta, mul_one]

    norm_cast
  }






lemma Theta_l_add_three_div_two_eq_241 (flu : fl ℓ |𝓤 = 0) :
    Θ^[(ℓ + 3)/2] (fl ℓ) (δ ℓ + 1) = 241 * (δ ℓ) ^ ((ℓ + 3) / 2) := by

  have t := DFunLike.ext_iff.mp <| Theta_l_add_three_div_two flu
  specialize t (δ ℓ + 1); simp_all [mul_comm, G_delta_add_one]




omit [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 13)] in
private lemma pow_congr_reduce_of_dvd {a c n : ℤ} {b : ℕ} (an0 : a ≠ 0) (adiv : a ∣ (n^2 - 1))
    ( h : ((n^2 - 1)/a + 1) ^ b ≡ c * ((n^2 - 1)/a) ^ b [ZMOD n] ) :
      (-a + 1) ^ (b) ≡ c [ZMOD n] := by

  obtain ⟨k, hk⟩ := adiv
  rw[hk, Int.mul_ediv_cancel_left _ an0] at h
  have h1 : a * k ≡ -1 [ZMOD n] := by
    trans n ^ 2 - 1; rw[hk]
    trans 0 ^ 2 - 1; gcongr
    exact Final.Hidden.Int.modEq_self; rfl

  have h2 : a * (k + 1) ≡ a - 1 [ZMOD n] := calc
      a * (k + 1) = a * k + a := by ring
      _ ≡ -1 + a [ZMOD n] := by gcongr
      _ = a - 1 := by ring

  have h3 : (a - 1) ^ b ≡ c * (a * k) ^ b [ZMOD n] := calc
      _ ≡ (a * (k + 1)) ^ b [ZMOD n] := by gcongr
      _ = a ^ b * (k + 1) ^ b := by rw [mul_pow]
      _ ≡ c * (a ^ b * k ^ b) [ZMOD n] := by
        rw[← mul_assoc, mul_comm c, mul_assoc]; gcongr
      _ = c * (a * k) ^ b := by rw[mul_pow]

  calc
    (-a + 1) ^ b = (-(a - 1)) ^ b := by ring
    _ = (-1) ^ b * (a - 1) ^ b := by rw [← mul_pow]; ring
    _ ≡ (-1) ^ b * (c * (a * k) ^ b) [ZMOD n] := by gcongr
    _ ≡ c * ((-1)^b * (-1)^b) [ZMOD n] := by
      rw[mul_comm, mul_assoc]; gcongr
    _ = c * 1 := by congr; exact pow_mul_pow_eq_one b rfl
    _ = c := mul_one c

set_option linter.unusedSectionVars false

lemma flu_ne_zero [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 13)]
    (flu : fl ℓ |𝓤 = 0) : False := by

  have equel : (δ ℓ + 1) ^ ((ℓ + 3) / 2) ≡ 241 * (δ ℓ) ^ ((ℓ + 3) / 2) [ZMOD ℓ] := by
    suffices (δ ℓ + 1) ^ ((ℓ + 3) / 2) = (241 * (δ ℓ) ^ ((ℓ + 3) / 2) : ZMod ℓ) by
      rw[← ZMod.intCast_eq_intCast_iff]; exact_mod_cast this
    rw[← Theta_l_add_three_div_two_fl_delta_add_one, ← Theta_l_add_three_div_two_eq_241 flu]

  have nequal : (δ ℓ + 1) ^ ((ℓ + 3) / 2) ≡ 241 * (δ ℓ) ^ ((ℓ + 3) / 2) [MOD ℓ] := by
    rw[← Int.natCast_modEq_iff]; exact_mod_cast equel

  have delcast : (δ ℓ : ℤ) = (ℓ ^ 2 - 1) / 24 := by
    unfold delta; trans ((ℓ ^ 2 - 1) : ℕ) / 24; rfl
    congr; trans ((ℓ ^ 2) : ℕ) - 1
    exact Int.natCast_pred_of_pos (Nat.pos_of_neZero (ℓ ^ 2))
    rfl

  have deldiv : (24 : ℤ) ∣ (ℓ ^ 2 - 1) := by
    trans ↑(24 : ℕ); exact Int.dvd_of_emod_eq_zero rfl
    trans ↑((ℓ^2 - 1) : ℕ)
    rw[Int.natCast_dvd_natCast]
    exact delta_integer
    apply dvd_of_eq; rw[Int.natCast_pred_of_pos (Nat.pos_of_neZero (ℓ ^ 2))]; rfl

  have inter : (-23) ^ ((ℓ + 3)/2) ≡ 241 [ZMOD ℓ] := by
    apply pow_congr_reduce_of_dvd (OfNat.zero_ne_ofNat 24).symm deldiv
    rwa[← delcast]

  have binder : (-23) ^ 2 * (-23) ^ ((ℓ - 1)/2) ≡ 241 [ZMOD ℓ] := calc

    (-23) ^ 2 * (-23) ^ ((ℓ - 1)/2) = (-23) ^ (4/2 + (ℓ - 1)/2) := by
      rw[pow_add]

    _ = (-23) ^ ((4 + ℓ - 1)/2) := by
      congr; symm; rw[Nat.add_sub_assoc]; apply Nat.add_div_of_dvd_right
      use 2; exact NeZero.one_le

    _ = (-23) ^ ((ℓ + 3)/2) := by
      congr 2; symm; apply Nat.eq_sub_of_add_eq'
      rw[add_comm ℓ, ← add_assoc]

    _ ≡ 241 [ZMOD ℓ] := inter

  by_cases l23 : ℓ = 23
  {
    simp_all[l23]
    contrapose! inter
    simpa only [Int.modEq_iff_dvd, Int.sub_neg, Int.reduceAdd, Int.reduceDvd]
  }
  have ln0 : (-23 : ZMod ℓ) ≠ 0 := by
    contrapose! l23; rw [neg_eq_zero] at l23
    have : (23 : ℕ) = (0 : ZMod ℓ) := by
      rw[← l23]; rfl

    rw[ZMod.natCast_zmod_eq_zero_iff_dvd] at this
    rwa[← Nat.prime_dvd_prime_iff_eq]
    exact Fact.out
    exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl


  have lrw : (ℓ - 1)/ 2 = ℓ / 2 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_one.mpr (@NeZero.one_le ℓ _)
    rw[hk, add_tsub_cancel_right]; refine Eq.symm (Nat.succ_div_of_not_dvd ?_)
    have : Odd ℓ := Oddl
    have : ¬ Odd k := by
      rw[hk] at this
      exact Nat.odd_add_one.mp this
    contrapose! this; refine Nat.odd_iff.mpr ?_
    refine Nat.two_dvd_ne_zero.mp ?_
    omega


  have rcases : ((-23 : ZMod ℓ)) ^ ((ℓ - 1)/2) = 1 ∨ (-23 : ZMod ℓ) ^ ((ℓ - 1)/2) = -1 := by
    simp only [lrw]
    apply ZMod.pow_div_two_eq_neg_one_or_one
    exact ln0


  have bindf : (-23 : ZMod ℓ) ^ 2 * (-23 : ZMod ℓ) ^ ((ℓ - 1) / 2) = 241 := by
    calc
       (-23 : ZMod ℓ) ^ 2 * (-23 : ZMod ℓ) ^ ((ℓ - 1) / 2) =
          ↑ ((-23 : ℤ) ^ 2 * (-23 : ℤ) ^ ((ℓ - 1) / 2)) := by zify

      _ = ↑(241 : ℤ) := by
        rwa[ZMod.intCast_eq_intCast_iff]

      _ = 241 := Int.cast_ofNat 241

  have lprime : Nat.Prime ℓ := Fact.out
  have lg13 : ℓ ≥ 13 := Fact.out

  rcases rcases with rcases | rcases

  simp only [even_two, Even.neg_pow, rcases, mul_one] at bindf

  have : ((23 ^ 2: ℕ) : ZMod ℓ) = ((241 : ℕ) : ZMod ℓ) := by
    norm_cast at *

  simp only [ZMod.eq_iff_modEq_nat, Nat.reducePow, Nat.modEq_iff_dvd] at this
  simp only [Nat.cast_ofNat, Int.reduceSub, dvd_neg] at this
  have : ℓ ∣ 288 := by zify; exact this
  have rw288 : 288 = 2 ^ 5 * 3 ^ 2 := rfl


  have ldiv : ℓ ∣ 2 ^ 5 ∨ ℓ ∣ 3 ^ 2 := by
    rw[rw288] at this
    exact (Nat.Prime.dvd_mul lprime).mp this

  rcases ldiv with lp | lp
  <;> apply Nat.Prime.dvd_of_dvd_pow lprime at lp <;>
  apply Nat.le_of_dvd at lp <;> omega


  simp only [even_two, Even.neg_pow, rcases, mul_neg, mul_one] at bindf

  have : (-(23 ^ 2: ℕ) : ZMod ℓ) = ((241 : ℕ) : ZMod ℓ) := mod_cast bindf

  simp only [Nat.reducePow, Nat.cast_ofNat] at this
  have : ((-529 : ℤ) : ZMod ℓ) = ((241 : ℤ) : ZMod ℓ) := mod_cast this
  simp only [ZMod.intCast_eq_intCast_iff,
    Int.modEq_iff_dvd, Int.sub_neg, Int.reduceAdd] at this

  have : ℓ ∣ 770 := by zify; exact this
  have rw770 : 770 = 2 * 5 * 7 * 11 := rfl


  have ldiv : ℓ ∣ 2 ∨ ℓ ∣ 5 ∨ ℓ ∣ 7 ∨ ℓ ∣ 11 := by
    simpa only [rw770, Nat.Prime.dvd_mul lprime, or_assoc]

  rcases ldiv with lp | lp | lp | lp
  <;> apply Nat.le_of_dvd at lp <;> omega



theorem MainResult : ¬ ramanujan_congruence ℓ := (flu_ne_zero <| flu_eq_zero ·)
