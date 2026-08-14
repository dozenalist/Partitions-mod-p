import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion


open ModularForm PowerSeries MatrixGroups UpperHalfPlane Set DirectSum


protected noncomputable def DirectSum.qexp : (⨁ k, ModularForm 𝒮ℒ k) →+* ℂ⟦X⟧ :=
  qExpansionRingHom (Γ := 𝒮ℒ) 1 zero_lt_one (by simp)


protected noncomputable def ModularForm.qexp {k : ℤ} : ModularForm 𝒮ℒ k →+ ℂ⟦X⟧ where
  toFun f := DirectSum.qexp (of _ _ f)
  map_zero' := by simp only [map_zero]
  map_add' := by simp only [map_add, implies_true]

theorem ModularForm.qexp_def {k} (f : ModularForm 𝒮ℒ k) : f.qexp = DirectSum.qexp (of _ _ f) :=
  rfl

theorem ModularForm.qexp_eq {k} (f : ModularForm 𝒮ℒ k) : f.qexp = ((of _ _ f) k).qexp := by
  simp

theorem ModularForm.qexp_eq' {k} (f : ModularForm 𝒮ℒ k) : f.qexp = qExpansion 1 f := by
  simp [ModularForm.qexp, DirectSum.qexp]

lemma ModularForm.of_mul {k j : ℤ} (f : ModularForm 𝒮ℒ k) (g : ModularForm 𝒮ℒ j) : of _ _ (f.mul g) = of _ _ f * of _ _ g := by
  simp [of]
  sorry


lemma ModularForm.qexp_mul {k j : ℤ} (f : ModularForm 𝒮ℒ k) (g : ModularForm 𝒮ℒ j) :
    (f.mul g).qexp = f.qexp * g.qexp := by
  repeat rw [qexp_eq, qexp_eq']
  rw [← qExpansion_of_mul zero_lt_one (by simp)]
  simp [of_mul]

lemma ModularForm.qexp_pow {k : ℤ} (f : ModularForm 𝒮ℒ k) (j : ℕ) : (f.pow j).qexp = f.qexp ^ j := by
  simp [ModularForm.qexp, DirectSum.qexp]
  rw [← ModularForm.coe_pow, ModularForm.qExpansion_pow zero_lt_one (by simp), ← qexp_eq']

theorem qexp_injective {k : ℤ} (f g : ModularForm 𝒮ℒ k) : f.qexp = g.qexp → f = g := by
  sorry



structure IntegerModularForm (k : ℤ) where

fourier : PowerSeries ℤ

carrier : ModularForm 𝒮ℒ k

carrier_eq : carrier.qexp = map (Int.castRingHom ℂ) fourier



-- #check algebraMap

-- structure IntegerModularForm (k : ℤ) where

-- fourier : PowerSeries ℤ

-- modform :

-- modular : ∃ f : ModularForm 𝒮ℒ k, map (Int.castRingHom ℂ) fourier = f.qexp

-- #check algebraMap
namespace IntegerModularForm
noncomputable section

variable {k : ℤ}

def coeff (n : ℕ) (f : IntegerModularForm k) := f.fourier.coeff n

instance : Zero (IntegerModularForm k) where

  zero :=

  { fourier := 0
    carrier := 0
    carrier_eq := by simp only [map_zero] }



lemma zero_def : (0 : IntegerModularForm k) = ⟨0, 0, by simp only [map_zero]⟩ := rfl

instance : Inhabited (IntegerModularForm k) := ⟨0⟩

instance : FunLike (IntegerModularForm k) ℍ ℂ where
  coe f := f.carrier
  coe_injective f g h := by
    obtain ⟨a,b,c⟩ := f
    obtain ⟨e,f,g⟩ := g
    simp_all only [DFunLike.coe_fn_eq]
    congr
    apply PowerSeries.map_injective (Int.castRingHom ℂ)
    simp [Function.Injective]
    rw [← c, h, g]

@[simp]
theorem coe_def (f : IntegerModularForm k) : f.carrier = ⇑f := rfl


@[ext]
theorem ext {f g : IntegerModularForm k} (h : ∀ n, f.coeff n = g.coeff n) : f = g := by
  apply DFunLike.coe_injective
  obtain ⟨a,b,c⟩ := f
  obtain ⟨e,f,g⟩ := g
  simp_all only [coeff, ← coe_def, DFunLike.coe_fn_eq]
  rw [← PowerSeries.ext_iff] at h
  apply qexp_injective
  rw [c, h, ← g]


theorem ext₂ {f g : IntegerModularForm k} (h : ∀ z, f z = g z) : f = g :=
  DFunLike.ext f g h


/-- Coercsion to the constant integer modular forms of weight 0 -/
def const (x : ℤ) : IntegerModularForm 0 where
  fourier := C x
  carrier := x
  carrier_eq := by simp [qexp_def]


instance : Coe ℤ (IntegerModularForm 0) where
  coe x := const x

instance : One (IntegerModularForm 0) :=
  ⟨const 1⟩

instance add : Add (IntegerModularForm k) where
  add := fun a b ↦
  { fourier := a.fourier + b.fourier
    carrier := a.carrier + b.carrier
    carrier_eq := by simp only [map_add, a.carrier_eq, b.carrier_eq]}


protected def mul {k j : ℤ} (f : IntegerModularForm k) (g : IntegerModularForm j) : IntegerModularForm (k + j) where
  fourier := f.fourier * g.fourier
  carrier := f.carrier.mul g.carrier
  carrier_eq := by rw [qexp_mul, map_mul, f.carrier_eq, g.carrier_eq]



protected def pow (f : IntegerModularForm k) (j : ℕ) : IntegerModularForm (j * k) where
  fourier := f.fourier ^ j
  carrier := f.carrier.pow j
  carrier_eq := by rw [qexp_pow, f.carrier_eq, map_pow]



instance instSMulZ : SMul ℤ (IntegerModularForm k) where
  smul c a :=
  { fourier := c • a.fourier
    carrier := c • a.carrier
    carrier_eq := by simp [qexp_def, ← a.carrier_eq] }


instance instSMulN : SMul ℕ (IntegerModularForm k) where
  smul c a :=
  { fourier := c • a.fourier
    carrier := c • a.carrier
    carrier_eq := by simp [qexp_def, ← a.carrier_eq] }

instance instNeg : Neg (IntegerModularForm k) where
  neg := fun a ↦
  { fourier := -a.fourier
    carrier := -a.carrier
    carrier_eq := by simp [a.carrier_eq] }

instance instSub : Sub (IntegerModularForm k) :=
  ⟨fun f g => f + -g⟩

instance : NatCast (IntegerModularForm 0) where
  natCast n := const n

@[simp]
lemma coe_natCast (n : ℕ) :
  ⇑(n : IntegerModularForm 0) = n := rfl

instance : IntCast (IntegerModularForm 0) where
  intCast z := const z

@[simp, norm_cast]
lemma coe_intCast (z : ℤ) :
    ⇑(z : IntegerModularForm 0) = z := rfl

open Finset.Nat Finset

variable {k j : ℤ} (z : ℍ) (n : ℕ) (f g : IntegerModularForm k) (h : IntegerModularForm j)

@[simp]
theorem toFun_eq_coe : ⇑f = (f : ℍ → ℂ) := rfl


theorem coe_apply : f.carrier z = f z := rfl

@[simp]
theorem coeff_def : f.fourier.coeff n = f.coeff n := rfl

@[simp]
theorem coe_add : ⇑(f + g) = f + g := rfl

@[simp]
theorem fourier_add : (f + g).fourier = f.fourier + g.fourier := rfl

@[simp]
theorem add_apply : (f + g) z = f z + g z := rfl

@[simp]
theorem coeff_add : (f + g).coeff n = f.coeff n + g.coeff n := rfl

@[simp]
theorem coe_mul : ⇑ (f.mul h) =
  fun z => f z * h z := rfl

@[simp]
theorem mul_coe : (f.mul h : ℍ → ℂ) = f.mul h := rfl

@[simp]
theorem fourier_mul : (f.mul h).fourier = f.fourier * h.fourier := rfl


theorem coeff_mul : (f.mul h).coeff n = ∑ p ∈ antidiagonal n, f.coeff p.1 * h.coeff p.2 := by
  simp only [coeff, fourier_mul, PowerSeries.coeff_mul]



@[simp]
theorem mul_apply : (f.mul h) z = f z * h z := rfl

@[simp]
theorem coe_smulz (x : ℤ) : ⇑(x • f) = x • ⇑f := rfl

@[simp]
theorem coeff_smulz (x : ℤ) : (x • f).coeff n = x • f.coeff n := rfl

@[simp]
theorem coe_smuln (n : ℕ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem coeff_smuln (m : ℕ): (n • f).coeff m = n • f.coeff m := rfl

@[simp]
theorem zsmul_apply (x : ℤ) : (x • f) z = x • f z := rfl

@[simp]
theorem nsmul_apply (f : IntegerModularForm k) : (n • f) z = n • f z := rfl

@[simp]
theorem coe_zero : ⇑(0 : IntegerModularForm k) = (0 : ℍ → ℂ) := rfl

@[simp]
theorem fourier_zero : (0 : IntegerModularForm k).fourier = 0 := rfl

@[simp]
theorem fourier_const (x : ℤ) : (const x).fourier = C x := rfl

@[simp]
theorem fourier_nsmul (m : ℕ) : (m • f).fourier = m • f.fourier := rfl

@[simp]
theorem fourier_zsmul (x : ℤ) : (x • f).fourier = x • f.fourier := rfl

@[simp]
theorem const_apply (x : ℤ) : const x z = x := rfl

@[simp low]
theorem coeff_const (x : ℤ) : (const x).coeff n = if n = 0 then x else 0 := by
  rw [coeff, const, coeff_C n x]

@[simp]
theorem coeff_const_zero (x : ℤ) : (const x).coeff 0 = x :=
  coeff_const _ _ ▸ if_pos rfl

@[simp]
theorem coeff_const_succ (x : ℤ) : (const x).coeff (n + 1) = 0 :=
  coeff_const _ _ ▸ if_neg (Nat.succ_ne_zero _)

@[simp]
theorem zero_apply : (0 : IntegerModularForm k) z = 0 := rfl

@[simp]
theorem coeff_zero : (0 : IntegerModularForm k).coeff n = 0 := rfl

@[simp]
theorem coe_neg : ⇑(-f) = -f := rfl

@[simp]
theorem neg_apply : (-f) z = - f z := rfl

@[simp]
theorem coeff_neg : (-f).coeff n = -f.coeff n := rfl


@[simp]
theorem coe_sub : ⇑(f - g) = f - g := rfl

@[simp]
theorem sub_apply : (f - g) z = f z - g z := rfl

@[simp]
theorem coeff_sub : (f - g).coeff n = f.coeff n - g.coeff n := rfl


theorem coe_pow (a : IntegerModularForm k) (j : ℕ) : ⇑(a.pow j) = fun z ↦ (a.pow j) z := rfl

@[simp]
theorem fourier_pow (j : ℕ) : (f.pow j).fourier = f.fourier ^ j := rfl

theorem coeff_pow (j : ℕ): (f.pow j).coeff n =
    ∑ l ∈ finsuppAntidiag (range j) n, ∏ i ∈ range j, f.coeff (l i) := by
  simp only [coeff, fourier_pow, PowerSeries.coeff_pow]


@[simp]
theorem pow_apply (a : IntegerModularForm k) (j : ℕ) : (a.pow j) z = (a z) ^ j := by
  simp [IntegerModularForm.pow, ← coe_def]


def Icast {m n : ℤ} (h : m = n := by ring) (a : IntegerModularForm m) : IntegerModularForm n where

  fourier := a.fourier

  carrier := mcast h a.carrier

  carrier_eq := by subst h; exact a.carrier_eq



@[simp]
lemma Icast_apply {k j : ℤ} {h : k = j} (a : IntegerModularForm k) :
    Icast h a z = a z := rfl

@[simp]
lemma fourier_Icast {k j : ℤ} {h : k = j} (a : IntegerModularForm k) :
  (a.Icast h).fourier = a.fourier := rfl

@[simp]
lemma coeff_Icast {k j : ℤ} {h : k = j} (a : IntegerModularForm k) :
    coeff n (a.Icast h) = a.coeff n := rfl

@[simp]
lemma triangle_eval {k j : ℤ} {h : k = j} {a : IntegerModularForm k} :
    (h ▸ a) z = a z := by
  subst h; rfl

@[simp]
lemma coeff_triangle {k j : ℤ} {h : k = j} (a : IntegerModularForm k) :
    coeff n (h ▸ a) = a.coeff n := by
  subst h; rfl



@[simp] theorem pow_zero (a : IntegerModularForm k) : a.pow 0 = (const 1).Icast (by group) :=
  IntegerModularForm.ext₂ fun x => by
    rw [pow_apply, _root_.pow_zero, Icast_apply, const_apply, Int.cast_one]


@[simp] theorem pow_one (a : IntegerModularForm k) : a.pow 1 = a.Icast (one_mul k).symm :=
  IntegerModularForm.ext₂ fun x => by rw [pow_apply, _root_.pow_one, Icast_apply]

@[simp] theorem zero_pow (j : ℕ) [hj : NeZero j] : (0 : IntegerModularForm k).pow j = 0 := by
  ext n; simp [coeff_pow, hj.out]


@[simp]
lemma const_mul (c : ℤ) (a : IntegerModularForm k) : (const c).mul a = Icast (zero_add _).symm (c • a) := by
  ext n; rw [coeff_mul, coeff_Icast, coeff_smulz]; calc

  _ = ∑ x ∈ (antidiagonal n).erase (0,n), (const c).coeff x.1 * a.coeff x.2 + (const c).coeff 0 * a.coeff n := by
    simp

  _ = 0 + c • a.coeff n := by
    rw [coeff_const_zero, smul_eq_mul]; congr
    apply sum_eq_zero fun x xin => ?_
    simp only [mem_erase, HasAntidiagonal.mem_antidiagonal] at xin
    have : x.1 ≠ 0 := by
      obtain ⟨h1, h2⟩ := xin
      have : x.1 ≠ 0 ∨ x.2 ≠ n := by contrapose! h1; ext; exacts [h1.1, h1.2]
      omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero this
    rw [hn, coeff_const_succ, zero_mul]

  _ = c • a.coeff n := zero_add _


instance : AddCommGroup (IntegerModularForm k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smuln coe_smulz


@[simps]
def coeffAddHom : IntegerModularForm k →+ ℕ → ℤ where
  toFun f n := f.coeff n
  map_zero' := by ext; rw [coeff_zero, Pi.zero_apply]
  map_add' _ _ := rfl

def coeAddHom : IntegerModularForm k →+ (ℍ → ℂ) where
  toFun f := DFunLike.coe f
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℤ (IntegerModularForm k) :=
  Function.Injective.module ℤ coeAddHom DFunLike.coe_injective fun _ _ ↦ rfl

@[ext (iff := false)]
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid IntegerModularForm}
    (h : a.fst = b.fst) (h2 : Icast h a.snd = b.snd) : a = b := by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

instance : GradedMonoid.GOne (IntegerModularForm) where
  one := 1

instance : GradedMonoid.GMul (IntegerModularForm) where
  mul f g := f.mul g

-- open Classical
-- variable ({x | x = 5}) (h : e.Nonempty)
-- #check h.choose
-- #check @Nat.find {x | x = 5} _ h
-- #check Nat.find
-- instance : DirectSum.GCommRing (IntegerModularForm) where
--   -- mul a b := a.mul b
--   -- mul_zero _ := ext₂ fun _ => by simp
--   -- zero_mul _ := ext₂  fun _ => by simp
--   -- one := 1
--   one_mul _ := gradedMonoid_eq_of_cast (zero_add _) (ext₂ fun _ => one_mul _)
--   mul_assoc _ _ _ := gradedMonoid_eq_of_cast (add_assoc _ _ _) (ext₂  fun _ => mul_assoc _ _ _)
--   mul_zero {_ _} _ := ext₂ fun _ => mul_zero _
--   zero_mul {_ _} _ := ext₂ fun _ => zero_mul _
--   mul_add {_ _} _ _ _ := ext₂ fun _ => mul_add _ _ _
--   add_mul {_ _} _ _ _ := ext₂ fun _ => add_mul _ _ _
--   mul_comm _ _ := gradedMonoid_eq_of_cast (add_comm _ _) (ext₂ fun _ => mul_comm _ _)
--   natCast := Nat.cast
--   natCast_zero := ext₂ fun _ => Nat.cast_zero
--   natCast_succ _ := ext₂ fun _ => Nat.cast_succ _
--   intCast := Int.cast
--   intCast_ofNat _ := ext₂ fun _ => AddGroupWithOne.intCast_ofNat _
--   intCast_negSucc_ofNat _ := ext₂ fun _ => AddGroupWithOne.intCast_negSucc _
--   mul_one _ := gradedMonoid_eq_of_cast (add_zero _) (ext₂ fun _ => mul_one _)
--   mul := mul


  -- mul_one:= sorry
  -- mul_assoc:= sorry
  -- natCast:= sorry
  -- natCast_zero:= sorry
  -- natCast_succ:= sorry
  -- intCast:= sorry
  -- intCast_ofNat:= sorry
  -- intCast_negSucc_ofNat:= sorry
  -- mul_comm:= sorry
  -- gnpow_zero' := sorry
  -- gnpow_succ':= sorry

-- lemma mul_comm (a : IntegerModularForm k) (b : IntegerModularForm j) : a.mul b = Icast (add_comm j k) (b.mul a) :=
--   IntegerModularForm.ext₂ _ _ fun z => by simp only [mul_apply, Icast_apply]; ac_rfl



-- instance : DirectSum.GAlgebra ℤ (IntegerModularForm) := sorry

-- @[simp] lemma mul_Iconst (c : ℤ) (a : IntegerModularForm k) : a * Iconst c = Icast (add_zero _).symm (c • a) := by
--   ext; rw [Imul_comm, Iconst_mul]; simp only [Icast_apply]


-- lemma Icast_symm {a : IntegerModularForm k} {b : IntegerModularForm j} (h : k = j) (hb : b = Icast h a) :
--     a = Icast h.symm b := by
--   ext; simp only [hb, Icast_apply]

-- @[simp] lemma Icast_Icast {j k i} {a : IntegerModularForm k} (h1 : k = j) (h2 : j = i) :
--     Icast h2 (Icast h1 a) = Icast (h1.trans h2) a := by
--   ext; simp only [Icast_apply]

-- @[simp] lemma Icast_id (a : IntegerModularForm k) (h : k = k) : Icast h a = a := rfl

-- @[simp]
-- theorem coe_sum {α : Type} [Fintype α] (l : α → IntegerModularForm k) (n : ℕ) : (∑ c, l c) n = ∑ c, (l c) n := by
--   sorry
