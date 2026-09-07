import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Ord

/-
This file proves the sturm bound for Integer Modular Forms (see `coeff_trunc_injective`),
provides a basis for the Integer Modular Forms of a given weight (see `GBasis`),
proves the dimension formula for the space of IntegerModular Forms, (see `dimension_eq_dim`),
proves facts about an upper-triangular basis (see `upTriangle_smul_G`),
and proves some key facts about equality between Integer Modular Forms of high-order (see `eq_of_eq_ord_max`)

This file is sorry-free
-/

open ModularForm MatrixGroups UpperHalfPlane




def dim (k : ℤ) : ℕ :=
  if 0 ≤ k then if Even k then if k ≡ 2 [ZMOD 12] then k.toNat / 12 else k.toNat / 12 + 1
    else 0 else 0

theorem dim_neg (k : ℤ) (hk : k < 0) : dim k = 0 := by
  simp_all only [dim, ite_eq_right_iff, isEmpty_Prop, not_le, IsEmpty.forall_iff]


theorem ModularForm.rank_eq_dim (k : ℤ) : Module.rank ℂ (ModularForm 𝒮ℒ k) = dim k := by
  rw [dim]
  split_ifs with hk hk2 kcon
  lift k to ℕ using hk
  rw [dimension_level_one k (by grind), if_pos (by grind [Nat.ModEq, Int.ModEq])]
  rfl
  lift k to ℕ using hk
  rw [dimension_level_one k (by grind), if_neg (by grind [Nat.ModEq, Int.ModEq])]
  rfl
  simp at hk2
  rw [ModularForm.levelOne_odd_weight_rank_zero hk2, Nat.cast_zero]
  rw [ModularForm.levelOne_neg_weight_rank_zero (not_le.1 hk), Nat.cast_zero]




theorem ModularForm.better_sturm_bound_levelOne_nat {k : ℕ} {f : ModularForm 𝒮ℒ (k : ℤ)}
    (h : (dim k : ℕ∞) ≤ (qExpansion 1 f).order) : f = 0 := by
  induction k using Nat.strong_induction_on with | _ k ih =>
  have h0 : (qExpansion 1 f).coeff 0 = 0 := by
    by_cases hord : (qExpansion 1 ⇑f).order = 0
    · have : dim k = 0 := by rw [hord] at h; norm_cast at *; exact Nat.eq_zero_of_le_zero h
      rw [← Nat.cast_eq_zero (R := Cardinal.{0}), ← ModularForm.rank_eq_dim, rank_zero_iff_forall_zero] at this
      simp only [this f, coe_zero, qExpansion_zero, map_zero]
    · exact PowerSeries.coeff_of_lt_order _
        (by simpa only [CharP.cast_eq_zero] using pos_iff_ne_zero.mpr hord)
  suffices CuspForm.discriminantEquiv (toCuspForm f h0) = 0 by
    simpa [CuspForm.discriminantEquiv.map_eq_zero_iff, DFunLike.ext_iff]
  by_cases hk : k < 12 ∨ Odd k ∨ k = 14
  · obtain (hk12 | kodd | k14) := hk
    · apply rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero (by lia))
    · apply rank_zero_iff_forall_zero.mp (ModularForm.levelOne_odd_weight_rank_zero (by grind))
    subst k14; apply rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero
  · rw [← mcast_eq_zero_iff (b := ↑(k - 12)) (by lia) rfl]
    refine ih (k - 12) (by lia) ?_
    have hsucc : dim k = dim (k - 12) + 1 := by
      simp only [dim, Int.ModEq]
      grind

    rw [qExpansion_eq_qExpansion_discriminant_mul f h0, PowerSeries.order_mul,
      discriminant_qExpansion_order, add_comm, hsucc, Nat.cast_add, Nat.cast_one] at h
    simp_rw [@Nat.cast_sub _ _ 12 k (by lia)]
    exact (ENat.add_le_add_iff_right (ENat.one_ne_top)).mp h


theorem better_sturm_bound_levelOne {k : ℤ} {f : ModularForm 𝒮ℒ k}
    (h : (dim k : ℕ∞) ≤ (qExpansion 1 f).order) : f = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f
  · lift k to ℕ using hk
    exact better_sturm_bound_levelOne_nat (mod_cast h)

namespace IntegerModularForm

noncomputable def coeff_trunc {k} : IntegerModularForm k →ₗ[ℤ] (Fin (dim k)) → ℤ where
  toFun f i := f.coeff i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coeff_trunc_apply {k} (f : IntegerModularForm k) (n) : f.coeff_trunc n = f.coeff n := rfl



-- sturm bound, ish
theorem coeff_trunc_injective {k} : Function.Injective <| coeff_trunc (k := k) := fun f g h => by
  rw [← sub_eq_zero]
  apply carrier_inj
  show f.carrier - g.carrier = 0
  apply better_sturm_bound_levelOne
  simp only [ModularForm.coe_sub, ModularForm.qExpansion_sub (Γ := 𝒮ℒ) zero_lt_one (by simp)]
  apply PowerSeries.le_order _ _ fun n nlt => by
    have h' := by simpa only [coeff_trunc_apply] using funext_iff.1 h ⟨n, by norm_cast at *⟩
    simp only [map_sub, ← qexp_eq', f.carrier_eq, g.carrier_eq,
      PowerSeries.coeff_map, coeff_def, h', sub_self]




@[reducible]
def mod_without_two (k p : ℤ) := if k ≡ 2 [ZMOD p] then k % p + p else k % p

infixr:25 " %% " => mod_without_two


@[simp] theorem mod_without_two_two_mul_add (c d) : ((12 * c + d) %% 12) = (d %% 12) := by
  simp [mod_without_two]

theorem dvd_sub_mod_without_two (c) : 12 ∣ (c - (c %% 12)) := by grind

theorem blla (c : ℤ) : ((c - c % 12 : ℤ) : ZMod 12) = 0 := by
  rw [show (0 : ZMod 12) = (0 : ℤ) by rfl, ZMod.intCast_eq_intCast_iff, Int.modEq_zero_iff_dvd]
  grind

theorem bllla (c : ℤ) : ((c % 12 : ℤ) : ZMod 12) = c := by
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  grind

theorem of_dim_pos (k : ℤ) (hk : dim k > 0) : (k %% 12) ∈ ({0, 4, 6, 8, 10, 14} : Set ℤ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [dim] at hk
  split_ifs at hk with h1 h2 h3
  rw [mod_without_two, if_pos h3]
  rw [Int.ModEq] at h3
  grind

  rw [mod_without_two, if_neg h3]
  rw [Int.ModEq] at h3
  grind
  exact (0).lt_irrefl hk |>.elim
  exact (0).lt_irrefl hk |>.elim

theorem bla (c) : c - (c %% 12) ≡ 0 [ZMOD 12] := by rw [Int.modEq_zero_iff_dvd]; exact dvd_sub_mod_without_two c

theorem dim_sub_mod_without_two (c) (hc : Even c) : dim (c - (c %% 12)) = dim c := by

  simp [dim]
  split_ifs with h h1 h2

  all_goals
    try grind

  all_goals
    have := h2.symm.trans (bla c)
    have me : ¬ 2 ≡ 0 [ZMOD 12] := by decide
    exact me this |>.elim


theorem le_dim_sub_mod_without_two (c) : dim (c - (c %% 12)) ≥ dim c := by


  simp [dim, mod_without_two]
  split_ifs with h1 h2 h3 h4 h5 h6
  all_goals
    try grind
  all_goals


    rw [show (12: ℤ) = (12 : ℕ) by rfl, ← ZMod.intCast_eq_intCast_iff] at *
    simp_all []
    norm_cast at *
    try simp_all only [blla, bllla]
    grind



noncomputable def G_dim_one : (k : ℤ) → IntegerModularForm k
  | 0 => 1
  | 4 => Eis 4
  | 6 => Eis 6
  | 8 => (Eis 4).pow 2
  | 10 => (Eis 4).mul (Eis 6)
  | 14 => ((Eis 4).pow 2).mul (Eis 6)
  | _ => 0

theorem ord_G_dim_one (k) : (G_dim_one k).ord.toNat = 0 := by
  unfold G_dim_one
  split <;> simp

theorem G_dim_one_coeff_zero_of_kmem (k) (kmem : k ∈ ({0,4,6,8,10,14} : Set ℤ)) :
    (G_dim_one k).coeff 0 = 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at kmem
  unfold G_dim_one
  rcases kmem with h | h | h | h | h | h
  <;> rw [h] <;> simp



theorem ord_G_dim_one_of_dim_pos (k) (h : dim k > 0) : (G_dim_one (k %% 12)).ord = 0 := by
  rw [ord_eq_zero, G_dim_one_coeff_zero_of_kmem _ <| of_dim_pos k h]
  exact one_ne_zero

noncomputable def G_twelve' {k} (c) (hc : c < dim k) (hk : 4 ∣ k) : IntegerModularForm k :=
  if hk : 0 ≤ k then Icast (by
    lift k to ℕ using hk; simp; norm_cast
    rw [dim] at hc
    grind)
    ((((Eis 4).pow (k.toNat / 4 - 3 * c)).mul ((Δ).pow c)))
  else 0

noncomputable def G_twelve {k} (c) (hc : c < dim k) : IntegerModularForm (k - (k %% 12)) :=
    let := dvd_sub_mod_without_two k
    let := le_dim_sub_mod_without_two k
  G_twelve' c (by lia) (by lia)


theorem ord_G_twelve {k} (c) (hc : c < dim k) : (G_twelve c hc).ord = c := by
  rw [G_twelve, G_twelve']
  split_ifs with h
  simp
  have : c < dim (k - (k %% 12)) := by grind [le_dim_sub_mod_without_two]
  rw [dim, if_neg h] at this
  exact not_lt_zero this |>.elim

theorem G_twelve_ord_G_twelve {k} (c) (hc : c < dim k) : (G_twelve c hc).coeff c = 1 := by
  rw [G_twelve, G_twelve']
  split_ifs with h
  simp
  conv => lhs; lhs; rw [← zero_add c]
  rw [coeff_mul_ord]
  · simp only [coeff_zero_pow, Eis_four_zero, one_pow, _root_.one_mul,
    coeff_pow_of_leading_zero Delta_zero, Delta_one, one_pow]
  · simp only [ord_pow, ord_Eis_four, nsmul_zero, CharP.cast_eq_zero]
  · simp only [ord_pow, ord_Delta, nsmul_eq_mul, _root_.mul_one]

  have : c < dim (k - (k %% 12)) := by grind [le_dim_sub_mod_without_two]
  rw [dim, if_neg h] at this
  exact not_lt_zero this |>.elim


noncomputable def G {k} (c : Fin (dim k)) : IntegerModularForm k :=
  Icast (by group) <| (G_dim_one (k %% 12)).mul (G_twelve c.1 c.2)


variable {k : ℤ} (c : Fin (dim k))

@[simp] theorem ord_G : ord (G c) = c := by
  by_cases hk : dim k > 0
  simp only [G, ord_Icast, ord_mul, ord_G_dim_one_of_dim_pos k hk, ord_G_twelve, zero_add]
  grind


@[simp] theorem G_ord_G : (G c).coeff c = 1 := by
  simp only [G, coeff_Icast]
  nth_rw 1 [← zero_add (c : ℕ)]
  rw [coeff_mul_ord, G_dim_one_coeff_zero_of_kmem _ <| of_dim_pos k c.pos,
    G_twelve_ord_G_twelve, _root_.one_mul]
  rw [ord_G_dim_one_of_dim_pos _ c.pos, Nat.cast_zero]
  rw [ord_G_twelve]



theorem G_LI : LinearIndependent ℤ (@G k) := by

  rw [linearIndependent_iff]
  intro l hl
  ext ⟨x,xlt⟩; simp only [Finsupp.coe_zero, Pi.zero_apply]

  rw [Finsupp.linearCombination_apply] at hl

  simp_rw [IntegerModularForm.ext_iff, ← coeffLinearMap_apply] at hl

  simp [- coeffLinearMap_apply] at hl
  simp only [coeffLinearMap_apply] at hl

  induction x using Nat.strong_induction_on with

      | h x ih =>
        rw [← hl x]; symm; calc

        _ = l ⟨x, xlt⟩ * coeff x (G ⟨x,xlt⟩) := by
          refine Finset.sum_eq_single _ ?_ fun h => h (Finset.mem_univ _) |>.elim
          rintro ⟨b, blt⟩ - bne
          by_cases blx : b > x
          · rw [coeff_lt_ord, MulZeroClass.mul_zero]
            rwa [ord_G, Nat.cast_lt]
          · rw [ih b (by rw [ne_eq, Fin.mk.injEq] at bne; lia) blt, MulZeroClass.zero_mul]

        _ = _ := by rw [G_ord_G ⟨x,xlt⟩, _root_.mul_one]



noncomputable def upTriangle_coeff (f : IntegerModularForm k) : Fin (dim k) → ℤ

  | ⟨0, _⟩ => f.coeff 0
  | ⟨n + 1, nlt⟩ =>
    f.coeff (n + 1) - ∑ i : Fin (n + 1), upTriangle_coeff f ⟨i, i.2.trans nlt⟩ * (G (k := k) ⟨i, i.2.trans nlt⟩).coeff (n + 1)


theorem upTriangle_coeff_zero (f : IntegerModularForm k) (hk : 0 < dim k) : upTriangle_coeff f ⟨0,hk⟩ = f.coeff 0 := by
  simp only [upTriangle_coeff]

theorem upTriangle_coeff_succ (f : IntegerModularForm k) (n) (hk : n + 1 < dim k) :
  upTriangle_coeff f ⟨n + 1, hk⟩ =
    f.coeff (n + 1) - ∑ i : Fin (n + 1), upTriangle_coeff f ⟨i, i.2.trans hk⟩ * (G (k := k) ⟨i, i.2.trans hk⟩).coeff (n + 1)
      := by simp only [upTriangle_coeff]


theorem upTriangle_coeff_smul_G (f : IntegerModularForm k) :
    ∑ (i : Fin (dim k)), upTriangle_coeff f i • G i = f := by

  apply coeff_trunc_injective
  ext ⟨n, nlt⟩

  simp only [coeff_trunc_apply, ← coeffLinearMap_apply]
  simp only [map_sum, map_smul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq]

  simp

  match n with
  | 0 =>
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ⟨0, nlt⟩), ← zero_add (f.coeff 0)]
    congr
    apply Finset.sum_eq_zero fun ⟨x, xin⟩ xlt => by
      have : x > 0 := by grind
      rw [coeff_lt_ord, MulZeroClass.mul_zero]
      simpa only [ord_G, CharP.cast_eq_zero, Nat.cast_pos, gt_iff_lt]

    simp only [upTriangle_coeff_zero, G_ord_G ⟨0, nlt⟩, _root_.mul_one]

  | n + 1 =>
    nth_rw 1 [← Finset.sum_filter_add_sum_filter_not _ (fun (x : Fin (dim k)) => ↑x ≤ n + 1),
      ← Finset.sum_filter_add_sum_filter_not _ (fun (x : Fin (dim k)) => ↑x = n + 1)]

    calc
      _ = ∑ x : Fin (dim k) with x = ⟨n + 1, nlt⟩, f.upTriangle_coeff ↑x * coeff (n + 1) (G x) +
        ∑ x : Fin (dim k) with x.1 < n + 1, f.upTriangle_coeff ↑x * coeff (n + 1) (G x) +
          ∑ (x : Fin (dim k)) with x.1 > n + 1, f.upTriangle_coeff ↑x * coeff (n + 1) (G x) := by
        congr! 3
        ext a
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using by grind
        ext a
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Order.lt_add_one_iff]
          using by grind
        simp only [not_le, gt_iff_lt]
      _ = f.upTriangle_coeff ⟨n + 1, nlt⟩ * coeff (⟨n + 1, nlt⟩ : Fin (dim k)).1 (G ⟨n + 1,nlt⟩) +
          ∑ x : Fin (n + 1), f.upTriangle_coeff ⟨x, x.2.trans nlt⟩ * coeff (n + 1) (G ⟨x.1, x.2.trans nlt⟩) + 0 := by
        congr! 2
        apply Finset.sum_eq_single
        rintro ⟨b, blt⟩ bin bne
        have : n + 1 < b := by grind
        rw [coeff_lt_ord, MulZeroClass.mul_zero]
        rw [ord_G]; norm_cast
        intro nin
        grind
        apply Finset.sum_bij fun ⟨a, alt⟩ ha => ⟨a, by grind⟩
        · exact fun _ _ => Finset.mem_univ _
        · exact fun _ _ _ _ => by grind
        · exact fun ⟨b,blt⟩ _ => ⟨⟨b, blt.trans nlt⟩, by grind, rfl⟩
        · exact fun _ _ => rfl

        apply Finset.sum_eq_zero fun ⟨x,xlt⟩ xin => by
          have : x > n + 1 := by grind
          rw [coeff_lt_ord, MulZeroClass.mul_zero]
          rw [ord_G]; norm_cast

      _ = f.coeff (n + 1) := by
        simp only [upTriangle_coeff_succ, G_ord_G ⟨n + 1, nlt⟩,
          _root_.mul_one, sub_add_cancel, add_zero]



theorem G_span : ⊤ ≤ Submodule.span ℤ {G c | c : Fin (dim k)} := fun f _ => by
  rw [Submodule.mem_span_set']
  use dim k, upTriangle_coeff f, fun c => ⟨G c, c, rfl⟩, upTriangle_coeff_smul_G f


noncomputable def GBasis (k) : Module.Basis (Fin (dim k)) ℤ (IntegerModularForm k) :=
  Module.Basis.mk G_LI G_span

@[simp] theorem GBasis_apply (k) (c) : GBasis k c = G c := Module.Basis.mk_apply ..


theorem exists_G_combo (f : IntegerModularForm k) :
    ∃ l : Fin (dim k) → ℤ, f = ∑ c, l c • G c := by
  have : ⊤ ≤ Submodule.span ℤ (Set.range (@G k)) := G_span
  simp only [Submodule.top_le_span_range_iff_forall_exists_fun, eq_comm] at this
  exact this f

theorem dimension_eq_dim : Module.rank ℤ (IntegerModularForm k) = dim k := by 
  rw [rank_eq_card_basis <| GBasis k, Fintype.card_fin]

theorem finrank_eq_dim : Module.finrank ℤ (IntegerModularForm k) = dim k := by
  rw [Module.finrank_eq_card_basis <| GBasis k, Fintype.card_fin]


theorem eq_of_eq_ord_max {f g : IntegerModularForm k} (hao : ord f ≥ dim k - 1)
    (hbo : ord g ≥ dim k - 1) (heq : f.coeff (dim k - 1) = g.coeff (dim k - 1)) : f = g :=

  coeff_trunc_injective <| by
    ext ⟨n, nlt⟩
    simp only [coeff_trunc_apply]
    by_cases h : n < dim k - 1
    · rw [coeff_lt_ord f, coeff_lt_ord g]
      exact lt_of_lt_of_le (by norm_cast) hbo
      exact lt_of_lt_of_le (by norm_cast) hao
    · rwa [show n = dim k - 1 by lia]




theorem eq_G_of_ord_max (f : IntegerModularForm k) (hord : ord f ≥ dim k - 1) :
    f = f.coeff (dim k - 1) • (G ⟨dim k - 1, by have := c.pos; omega⟩ ) := by
  by_cases f0 : f = 0
  · simp [f0]

  apply eq_of_eq_ord_max hord
  have : NeZero <| f.coeff (dim k - 1) := ⟨ by
    contrapose! f0
    apply coeff_trunc_injective
    funext ⟨n, nlt⟩
    simp
    by_cases hn : n < dim k - 1
    rw [coeff_lt_ord]
    apply lt_of_lt_of_le (by norm_cast) hord
    grind ⟩

  simpa only [ord_smul, ord_G, ENat.natCast_sub, Nat.cast_one] using le_refl _
  rw [coeff_smulz, G_ord_G (c := ⟨dim k - 1, by have := c.pos; omega⟩), zsmul_one]
  rfl



end IntegerModularForm
