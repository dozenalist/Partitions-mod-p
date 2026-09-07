import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion


/-
This file defines Integer Modular Forms, proves some basic identities,
and shows that they form an AddCommGroup and Module over ℤ
This file is sorry-free
-/

open ModularForm PowerSeries MatrixGroups UpperHalfPlane Set DirectSum


noncomputable abbrev ModularForm.qexp {k} := ModularForm.qExpansionAddHom (Γ := 𝒮ℒ) zero_lt_one (by simp) k

theorem ModularForm.qexp_injective {k} : Function.Injective <| ModularForm.qexp (k := k) :=
  fun f g h => sub_eq_zero.1 (by
    rw [← ModularForm.qExpansion_eq_zero_iff zero_lt_one (by simp),
      coe_sub, ModularForm.qExpansion_sub zero_lt_one (by simp)]
    exact sub_eq_zero.mpr h )


-- protected noncomputable def ModularForm.qexp {k : ℤ} : ModularForm 𝒮ℒ k →+ ℂ⟦X⟧ where
--   toFun f := DirectSum.qexp (of _ _ f)
--   map_zero' := by simp only [map_zero]
--   map_add' := by simp only [map_add, implies_true]

-- theorem ModularForm.qexp_def {k} (f : ModularForm 𝒮ℒ k) : f.qexp = DirectSum.qexp (of _ _ f) :=
--   rfl

theorem ModularForm.qexp_eq {k} (f : ModularForm 𝒮ℒ k) : f.qexp = ((of _ _ f) k).qexp := by
  simp

theorem ModularForm.qexp_eq' {k} (f : ModularForm 𝒮ℒ k) : f.qexp = qExpansion 1 f := by
  simp [ModularForm.qexp, qExpansionAddHom]

-- lemma ModularForm.of_mul {k j : ℤ} (f : ModularForm 𝒮ℒ k) (g : ModularForm 𝒮ℒ j) :
--     of _ _ (f.mul g) = of _ _ f * of _ _ g := by



lemma ModularForm.qexp_mul {k j : ℤ} (f : ModularForm 𝒮ℒ k) (g : ModularForm 𝒮ℒ j) :
    (f.mul g).qexp = f.qexp * g.qexp := by
  simp only [qexp, qExpansionAddHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, ModularForm.qExpansion_mul (Γ := 𝒮ℒ) zero_lt_one (by simp)]


lemma ModularForm.qexp_pow {k : ℤ} (f : ModularForm 𝒮ℒ k) (j : ℕ) : (f.pow j).qexp = f.qexp ^ j := by
  simp [ModularForm.qexp, qExpansionAddHom]
  rw [← ModularForm.coe_pow, ModularForm.qExpansion_pow zero_lt_one (by simp), ← qexp_eq']

-- theorem qexp_injective {k : ℤ} (f g : ModularForm 𝒮ℒ k) : f.qexp = g.qexp → f = g := by
--   sorry



structure IntegerModularForm (k : ℤ) where

fourier : PowerSeries ℤ

carrier : ModularForm 𝒮ℒ k

carrier_eq : carrier.qexp = map (Int.castRingHom ℂ) fourier


noncomputable section

namespace IntegerModularForm

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
  carrier_eq := by simp [qExpansionAddHom, ← qExpansionRingHom_apply]




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
    carrier_eq := by simp [← a.carrier_eq] }


instance instSMulN : SMul ℕ (IntegerModularForm k) where
  smul c a :=
  { fourier := c • a.fourier
    carrier := c • a.carrier
    carrier_eq := by simp [← a.carrier_eq] }

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

theorem fourier_inj : Function.Injective (@IntegerModularForm.fourier k) := fun f g h =>
  ext fun _ => by simp only [coeff, h]

theorem carrier_inj : Function.Injective (@IntegerModularForm.carrier k) := fun f g h =>
  ext₂ fun _ => by simp only [← coe_apply, h]




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

theorem one_def : 1 = const 1 := rfl

@[simp low]
theorem coeff_one : (1 : IntegerModularForm 0).coeff n = if n = 0 then 1 else 0 := by
  rw [one_def, coeff_const]

@[simp]
theorem one_apply : (1 : IntegerModularForm 0) z = 1 := by
  rw [one_def, const_apply, Int.cast_one]

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
  ext₂ fun x => by
    rw [pow_apply, _root_.pow_zero, Icast_apply, const_apply, Int.cast_one]


@[simp] theorem pow_one (a : IntegerModularForm k) : a.pow 1 = a.Icast (one_mul k).symm :=
  ext₂ fun x => by rw [pow_apply, _root_.pow_one, Icast_apply]

@[simp] theorem zero_pow (j : ℕ) [hj : NeZero j] : (0 : IntegerModularForm k).pow j = 0 := by
  ext n; simp [coeff_pow, hj.out]

@[simp] theorem zero_mul : (0 : IntegerModularForm j).mul f = 0 :=
  ext₂ fun _ => by simp only [mul_apply, zero_apply, MulZeroClass.zero_mul]

@[simp] theorem mul_zero : f.mul (0 : IntegerModularForm j) = 0 :=
  ext₂ fun _ => by simp only [mul_apply, zero_apply, MulZeroClass.mul_zero]

@[simp] theorem one_mul : (1 : IntegerModularForm 0).mul f = f.Icast :=
  ext₂ fun _ => by simp only [mul_apply, one_apply, _root_.one_mul, Icast_apply]

@[simp] theorem mul_one : f.mul (1 : IntegerModularForm 0)= f.Icast :=
  ext₂ fun _ => by simp only [mul_apply, one_apply, _root_.mul_one, Icast_apply]


@[simp]
lemma const_mul (c : ℤ) (a : IntegerModularForm k) : (const c).mul a = (c • a).Icast :=
  ext₂ fun _ => by simp only [mul_apply, const_apply, Icast_apply, zsmul_apply, zsmul_eq_mul]

theorem mul_comm_Icast : f.mul g = (g.mul f).Icast :=
  ext₂ fun _ => by simp only [mul_apply, Icast_apply, mul_comm]


theorem leading_pow_zeros {f : IntegerModularForm k} {m} (h : f.coeff 0 = 0) :
    ∀ {n}, n < m → (f.pow m).coeff n = 0 := fun {n} nlm => by
  simpa only [coeff_pow] using sum_eq_zero fun x xin => by
    suffices ∃ y ∈ Finset.range m, x y = 0 by
      obtain ⟨y, yin, hy⟩ := this
      rw [prod_eq_zero yin]
      exact hy ▸ h

    obtain ⟨hx, xsupp⟩ := by simpa only [mem_finsuppAntidiag] using xin
    contrapose! hx
    simp_all only [← Nat.one_le_iff_ne_zero]
    apply Nat.ne_of_gt
    calc
      _ < m := nlm
      _ = ∑ _ ∈ Finset.range m, 1 := by
        simp only [sum_const, card_range, smul_eq_mul, _root_.mul_one]
      _ ≤ _ := sum_le_sum hx


theorem coeff_pow_of_leading_zero {f : IntegerModularForm k} (h : f.coeff 0 = 0) :
    ∀ m, (f.pow m).coeff m = f.coeff 1 ^ m := fun m => by
  rcases f with ⟨p,q,r⟩
  simp_all only [coeff, coeff_zero_eq_constantCoeff, fourier_pow]
  obtain ⟨q, rfl⟩ := X_dvd_iff.2 h
  nth_rw 1 [mul_pow, ← zero_add m, coeff_succ_X_mul]
  simp only [coeff_zero_eq_constantCoeff, coeff_X_pow_mul, map_pow]


open PowerSeries

@[simp] theorem coeff_zero_mul : (f.mul h).coeff 0 = f.coeff 0 * h.coeff 0 := by
  simp only [← coeff_def, fourier_mul, coeff_zero_eq_constantCoeff, map_mul]

@[simp] theorem coeff_zero_pow : (f.pow n).coeff 0 = (f.coeff 0) ^ n := by
  simp only [← coeff_def, fourier_pow, coeff_zero_eq_constantCoeff, map_pow]


private lemma _root_.PowerSeries.coeff_one_pow_succ (q : ℤ⟦X⟧) :
    ∀ n : ℕ, (q ^ (n + 1)).coeff 1 = (n + 1 : ℕ) • q.coeff 1 * (q.coeff 0) ^ n
  | 0 => by simp
  | n + 1 => by
    simp [pow_succ q (n + 1), coeff_one_mul, coeff_one_pow_succ]
    ring



theorem coeff_succ_pow_of_leading_zero {f : IntegerModularForm k} (h : f.coeff 0 = 0) :
    ∀ m, (f.pow m).coeff (m + 1) = m • f.coeff 2 * f.coeff 1 ^ (m - 1)
  | 0 => by simp
  | m + 1 => by
    rcases f with ⟨p,q,r⟩
    simp_all only [coeff, coeff_zero_eq_constantCoeff, fourier_pow]
    obtain ⟨q, rfl⟩ := X_dvd_iff.2 h
    simp [mul_pow, add_comm (m + 1), coeff_one_pow_succ]

theorem coeff_one_mul :
    (f.mul g).coeff 1 = f.coeff 1 * g.coeff 0 + g.coeff 1 * f.coeff 0 := by
  simpa only [← coeff_def, fourier_mul, coeff_zero_eq_constantCoeff] using
    PowerSeries.coeff_one_mul _ _




instance : AddCommGroup (IntegerModularForm k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smuln coe_smulz

@[simps]
def coeffLinearMap : IntegerModularForm k →ₗ[ℤ] ℕ → ℤ where
  toFun f n := f.coeff n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coeAddHom : IntegerModularForm k →+ (ℍ → ℂ) where
  toFun f := DFunLike.coe f
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℤ (IntegerModularForm k) :=
  Function.Injective.module ℤ coeAddHom DFunLike.coe_injective fun _ _ => rfl

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


end IntegerModularForm

open ModularForm UpperHalfPlane IntegerModularForm

variable {k : ℤ}

def ModularForm.toIntegerModularForm (f : ModularForm 𝒮ℒ k)
    (h : qExpansion 1 f ∈ range (map (algebraMap ℤ ℂ))) : IntegerModularForm k where
  fourier := h.choose
  carrier := f
  carrier_eq := by simpa [qExpansionAddHom] using h.choose_spec.symm
