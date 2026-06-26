import PartitionsLeanblueprint.BasicOperators
import PartitionsLeanblueprint.Dimension
import Mathlib.RingTheory.Localization.AtPrime
import PartitionsLeanblueprint.Dimension
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.MvPolynomial.Derivation

open IntegerModularForm

noncomputable section

open Ideal
variable  (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]



instance : IsPrime (Ideal.span {(ℓ : ℤ)}) := sorry

@[reducible]
def o := Localization.AtPrime (Ideal.span {(ℓ : ℤ)})


#check o ℓ
open IsobaricPoly

variable {k : ℕ}
#check (o ℓ)[X,Y]k

theorem oEqv_def_r (a c : ℤ) (b d : ↥(span {(ℓ : ℤ)}).primeCompl) : (a, b) ≈ (c, d) ↔
  (LocalizedModule.r _ _) (a,b) (c,d) := Iff.rfl

@[simp]
theorem oEqv_def (a c : ℤ) (b d : ↥(span {(ℓ : ℤ)}).primeCompl) : (a, b) ≈ (c, d) ↔
  ∃ (u : ↥(span {(ℓ : ℤ)}).primeCompl), u • d • a = u • b • c := by
    rw [oEqv_def_r, LocalizedModule.r]


def o.reduce {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] : (o ℓ) →+* (ZMod ℓ) :=
  {
    toFun := by
      unfold o Localization.AtPrime Localization OreLocalization
      exact
        Quotient.lift (fun (a, b) => a * (b : ZMod ℓ)⁻¹ ) fun (a, b) (c, d) h => by
          obtain ⟨u, v, hu, hv⟩ := h
          simp_all



          suffices u • (↑a * (b : ZMod ℓ)⁻¹) = u • (↑c * (d : ZMod ℓ)⁻¹) by
            rename_i x x_1
            obtain ⟨fst, snd⟩ := x
            obtain ⟨fst_1, snd_1⟩ := x_1
            obtain ⟨val, property⟩ := b
            obtain ⟨val_1, property_1⟩ := d
            obtain ⟨val_2, property_2⟩ := u
            obtain ⟨val_3, property_3⟩ := snd
            obtain ⟨val_4, property_4⟩ := snd_1
            simp_all only [Submonoid.mk_smul, smul_eq_mul, zsmul_eq_mul, mul_eq_mul_left_iff]
            cases this with
            | inl h => simp_all only
            | inr h_1 => sorry

          sorry


    map_one' := by simp; sorry
    map_mul' x y := by simp; sorry
    map_zero' := by simp; sorry
    map_add' := by simp; sorry
  }







def toRat : o ℓ → ℚ :=
  Quotient.lift (fun (a,b) => a / b) fun (a, b) (c, d) h => by
    obtain ⟨u, v, hu, hv⟩ := h
    simp_all
    sorry


def ofRat (q : ℚ) (h : q.den.Coprime ℓ) : o ℓ :=
  ⟦(q.num, ⟨q.den, by
    simp [primeCompl]; intro h'; rw [mem_span_singleton] at h';
    have : ¬ ↑ℓ ∣ q.den := by refine (Nat.Prime.coprime_iff_not_dvd hℓ.out).mp h.symm
    omega⟩)⟧



section gModularForm
open misc

structure gModularForm (R : Subring ℂ) (k : ℕ) where
  sequence : ℕ → R
  modular : ModularFormClass k (∑' n, (sequence n : ℂ) • q ^ n)


def ofIntegerModularForm (R : Subring ℂ) (a : IntegerModularForm k) : gModularForm R k where
  sequence n := ↑(a n)
  modular := by simpa using a.3


variable {R : Subring ℂ} {k : ℕ}

instance : FunLike (gModularForm R k) ℕ R where
  coe a := a.1
  coe_injective' a b h := by cases a; cases b; congr

instance : Coe (IntegerModularForm k) (gModularForm R k) where
  coe a := ofIntegerModularForm R a


instance : SMul R (gModularForm R k) where
  smul c f := {
    sequence n := c * f n
    modular := sorry }




instance : Zero (gModularForm R k) where

  zero := {
    sequence n := 0
    modular := sorry
  }

instance : Inhabited (IntegerModularForm k) := ⟨0⟩



/-- Coercsion to the constant integer modular forms of weight 0 -/
def oconst (x : R) : gModularForm R 0 where
  sequence := fun n ↦ if n = 0 then x else 0
  modular := sorry

instance : Coe R (gModularForm R 0) where
  coe x := oconst x

instance : Add (gModularForm R k) where
  add := fun a b ↦
  { sequence := a + b
    modular := sorry }

def omul {k j : ℕ} (f : gModularForm R k) (g : gModularForm R j) : gModularForm R (k + j) where
  sequence n := ∑ ⟨x,y⟩ ∈ (Finset.antidiagonal n), f x * g y
  modular := sorry

instance {j} : HMul (gModularForm R k) (gModularForm R j) (gModularForm R (k + j)) where
  hMul := omul

def opow (a : gModularForm R k) (j : ℕ) : gModularForm R (k * j) where
  sequence n := ∑ x ∈ Finset.Nat.antidiagonalTuple j n, ∏ y, a (x y)
  -- sum over all x1 + ... + xj = n
  modular := sorry





instance instSMulR : SMul R (gModularForm R k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}

instance instSMulZ : SMul ℤ (gModularForm R k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}

instance instSMulN : SMul ℕ (gModularForm R k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}

instance instNeg : Neg (gModularForm R k) where
  neg := fun a ↦
  { sequence := -a
    modular := sorry }

instance instSub : Sub (gModularForm R k) :=
  ⟨fun f g => f + -g⟩

instance : NatCast (gModularForm R 0) where
  natCast n := oconst n

-- @[simp, norm_cast]
-- lemma coe_natCast (n : ℕ) :
--     ⇑(n : ModularFormMod ℓ 0) = n := rfl

instance : IntCast (gModularForm R 0) where
  intCast z := oconst z

-- @[simp, norm_cast]
-- lemma coe_intCast (z : ℤ) :
--     ⇑(z : ModularFormMod ℓ 0) = z := rfl

open Finset.Nat Finset



@[simp]
theorem toFun_eq_coe (f : gModularForm R k) : ⇑f = (f : ℕ → R) := rfl

@[simp]
theorem coe_apply (f : gModularForm R k) (n : ℕ) : f.sequence n = f n := rfl

@[simp]
theorem coe_add (f g : gModularForm R k) : ⇑(f + g) = f + g := rfl

@[simp]
theorem add_apply (f g : gModularForm R k) (z : ℕ) : (f + g) z = f z + g z := rfl

@[simp]
theorem coe_mul (f g : gModularForm R k) : ⇑ (f * g) =
  fun n ↦ ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl

@[simp]
theorem mul_coe {j} (f : gModularForm R k) (g : gModularForm R j ) :
  (f * g : ℕ → R) = f * g := rfl


theorem mul_apply {j} (f : gModularForm R k) (g : gModularForm R j ) (n : ℕ) : (f * g) n =
  ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl

@[simp]
theorem coe_smulz (f : gModularForm R k) (n : ℤ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem coe_smuln (f : gModularForm R k) (n : ℕ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem zsmul_apply (f : gModularForm R k) (n : ℤ) (z : ℕ) : (n • f) z = n • f z := rfl

@[simp]
theorem nsmul_apply (f : gModularForm R k) (n z : ℕ) : (n • f) z = n • f z := rfl

@[simp]
theorem coe_zero : ⇑(0 : gModularForm R k) = (0 : ℕ → R) := rfl

@[simp]
theorem zero_apply (z : ℕ) : (0 : gModularForm R k) z = 0 := rfl

@[simp]
theorem coe_neg (f : gModularForm R k) : ⇑(-f) = -f := rfl

@[simp]
theorem neg_apply (f : gModularForm R k) (n : ℕ) : (-f) n = - f n := rfl

@[simp]
theorem coe_sub (f g : gModularForm R k) : ⇑(f - g) = f - g :=
  Eq.symm (Mathlib.Tactic.Abel.unfold_sub (⇑f) (⇑g) (⇑(f - g)) rfl)

@[simp]
theorem sub_apply (f g : gModularForm R k) (z : ℕ) : (f - g) z = f z - g z :=
  Eq.symm (Mathlib.Tactic.Abel.unfold_sub (f z) (g z) ((f - g) z) rfl)


theorem coe_opow (a : gModularForm R k) (j : ℕ) : ⇑(opow a j) = fun n ↦ ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl

theorem opow_apply (a : gModularForm R k) (j n : ℕ) : (opow a j) n = ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl



@[simp]
theorem oconst_zero (x : R) : (oconst x) 0 = x := rfl

@[simp]
theorem oconst_succ (x : R) (n : ℕ) : (oconst x) n.succ = 0 := rfl



@[ext]
theorem ext {a b : gModularForm R k} (h : ∀ n, a n = b n) : a = b :=
  DFunLike.ext a b h

@[simp] theorem opow_zero (a : gModularForm R k) : opow a 0 = oconst 1 := by
  ext n; rw [opow_apply]
  match n with
  | 0 => simp
  | n + 1 => simp

/-- Casts an integer modular form to a different but provably equal weight -/
def ocast {m n : ℕ} (h : m = n) (a : gModularForm R m) : gModularForm R n :=
  h ▸ a

@[simp]
lemma ocast_apply {k j : ℕ} {h : k = j} {n : ℕ} {a : gModularForm R k} :
  ocast h a n = a n := by
  subst h; rfl




@[simp]
lemma triangle_eval {k j : ℕ} {h : k = j} {n : ℕ} {a : gModularForm R k} :
  (h ▸ a) n = a n := by
  subst h; rfl

@[simp] theorem opow_one (a : gModularForm R k) : opow a 1 = ocast (by norm_num) a := by
  ext n; simp [opow_apply]








instance : AddCommGroup (gModularForm R k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smuln coe_smulz


@[simps]
def coeHom : gModularForm R k →+ ℕ → R where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

instance : Module R (gModularForm R k) :=
  Function.Injective.module R _root_.coeHom DFunLike.coe_injective fun _ _ ↦ rfl


instance : DirectSum.GCommRing (gModularForm R) :=
{ mul a b := a * b, mul_zero:= sorry, zero_mul := sorry, mul_add := sorry, add_mul := sorry, one := Iconst 1, one_mul:= sorry, mul_one:= sorry, mul_assoc:= sorry, natCast:= sorry, natCast_zero:= sorry, natCast_succ:= sorry, intCast:= sorry, intCast_ofNat:= sorry, intCast_negSucc_ofNat:= sorry, mul_comm:= sorry, gnpow_zero' := sorry, gnpow_succ':= sorry}




noncomputable def toModularForm (f : gModularForm R k) : ModularForm k :=
  ⟨∑' n, (f.1 n : ℂ) • q ^ n, sorry, sorry, sorry, sorry⟩


def ol : Subring ℂ where
  carrier := {((toRat ℓ b) : ℂ) | b : o ℓ}
  mul_mem':= sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry

instance : Coe (o ℓ) (ol ℓ) where
  coe b := by
    unfold ol
    simp only [Subring.mem_mk]
    apply Subtype.mk
    use b

instance : Coe (ol ℓ) (o ℓ) where
  coe x := Classical.choose x.property


@[reducible]
def oModularForm (ℓ) := gModularForm (ol ℓ)

instance : Coe (IntegerModularForm k) (oModularForm ℓ k) := inferInstance

def ol.reduce : (ol ℓ) →+* (ZMod ℓ) :=
  {
    toFun b := o.reduce b

    map_one' := by simp; sorry
    map_mul' x y := by simp; sorry
    map_zero' := by simp; sorry
    map_add' := by simp; sorry
  }


end gModularForm


section basis
def ofun (k) (m : ModularForm.Gmk k) : oModularForm ℓ (2 * k) := Zfun k m


open Finsupp in
theorem ofun_LI : LinearIndependent (ol ℓ) (ofun ℓ k) := by
  rw [linearIndependent_iff]
  intro f hf
  ext n; simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [Finsupp.linearCombination_apply] at hf
  sorry


theorem ofun_span : ⊤ ≤ Submodule.span (ol ℓ) (Set.range (ofun ℓ k)) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun (ol ℓ)).mpr ?_
  sorry


def oBasis (k : ℕ) : Basis (ModularForm.Gmk k) (ol ℓ) (oModularForm ℓ (2*k)) :=
  Basis.mk (ofun_LI ℓ) (ofun_span ℓ)

@[reducible] def M k := (o ℓ)[X,Y]k

def IsoSet (k : ℕ) := {(x,y) : ℕ × ℕ | 4*x + 6*y = k}

def Isomk (k : ℕ) := {x // x ∈ IsoSet k}

lemma mem_IsoSet {k} (x) : x ∈ IsoSet k ↔ 4 * x.1 + 6 * x.2 = k := Iff.rfl

instance : Fintype (Isomk k) := sorry


def IsoFun (k) (m : Isomk k) : oModularForm ℓ k := Icast m.2 (Eis 2 ** m.1.1 * Eis 3 ** m.1.2)

theorem IsoFun_LI : LinearIndependent (ol ℓ) (IsoFun ℓ k) := sorry

theorem IsoFun_span [Fact (ℓ ≥ 5)] : ⊤ ≤ Submodule.span (ol ℓ) (Set.range (IsoFun ℓ k)) := sorry

def IsoBasis (k : ℕ) [Fact (ℓ ≥ 5)] : Basis (Isomk k) (ol ℓ) (oModularForm ℓ k) :=
  Basis.mk (IsoFun_LI ℓ) (IsoFun_span ℓ)


theorem exists_IsoFun_combo [Fact (ℓ ≥ 5)] (a : oModularForm ℓ k) :
    ∃ l : Isomk k → (ol ℓ), ∑ c, l c • (IsoBasis ℓ k) c = a := sorry

def oModularForm.coeffs {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 5)] (a : oModularForm ℓ k) : Isomk k → ol ℓ :=
  Classical.choose <| exists_IsoFun_combo ℓ a

theorem coeffs_eq [Fact (ℓ ≥ 5)] (a : oModularForm ℓ k) :
  ∑ c, a.coeffs c • (IsoBasis ℓ k) c = a :=
    Classical.choose_spec <| exists_IsoFun_combo ℓ a

end basis



open IntegerModularForm

def of_Isomk (l : Isomk k → ol ℓ) : M ℓ k :=
  ∑ x : Isomk k, (l x : o ℓ) • Polycast (by simp; rw[mul_comm, mul_comm _ 6, ← mem_IsoSet]; exact x.2)
    ((X ^* x.1.1 : M ℓ (x.1.1 • 4)) * (Y ^* x.1.2 : M ℓ (x.1.2 • 6)))



def push : M ℓ k → oModularForm ℓ k
  | ⟨⟨a,b,c⟩, prop⟩ => ∑ x : {x // x ∈ a}, (b x.1 : ol ℓ) • ↑(Icast (by
    have : x.1 ∈ a := x.2
    apply prop
    simp_all only [ne_eq]
    exact this)

      ((Eis 2) ** (x.1 Vars.X) * (Eis 3) ** (x.1 Vars.Y)) : IntegerModularForm k)

def pull [Fact (ℓ ≥ 5)] : oModularForm ℓ k → M ℓ k
  | a => of_Isomk ℓ a.coeffs




def iso [Fact (ℓ ≥ 5)] : M ℓ k ≅ oModularForm ℓ k where
  hom := fun ⟨⟨a,b,c⟩, prop⟩ => ∑ x : {x // x ∈ a}, (b x.1 : ol ℓ) • ↑(Icast (by
    have : x.1 ∈ a := x.2
    apply prop
    simp_all only [ne_eq]
    exact this)

      ((Eis 2) ** (x.1 Vars.X) * (Eis 3) ** (x.1 Vars.Y)) : IntegerModularForm k)

  inv a := of_Isomk ℓ a.coeffs

  hom_inv_id := by
    ext a
    simp
    sorry

  inv_hom_id := by
    ext b n
    simp
    sorry

def A [Fact (ℓ ≥ 5)] := pull ℓ (ofIntegerModularForm (ol ℓ) (Eis (ℓ - 1)))

-- theorem main_ker {a : oModularForm ℓ k} (h : push a = 0) : a ∈ Ideal.span


theorem main_dvd (a : oModularForm ℓ k) (h : ∀ n, (a n : o ℓ).reduce = 0) [Fact (ℓ ≥ 5)] :
  (A ℓ).1 - 1 ∣ (pull ℓ a).1 := sorry


#check (ZMod ℓ)[X,Y]k

def poly_reduce : M ℓ k → (ZMod ℓ)[X,Y]k
  | ⟨⟨a,b,c⟩, p⟩ => ⟨⟨a, fun n => (b n).reduce, by simp [c]; intro a; apply Iff.not; sorry⟩, by sorry⟩



section RingHomModForm

structure RingHomModForm {R : Subring ℂ} {Z} [CommRing Z] (hom : R →+* Z) (k : ℕ) where
  sequence : ℕ → Z
  modular : ∃ a : gModularForm R k, sequence = fun n => hom (a n)


variable {R : Subring ℂ} {Z} [CommRing Z] {hom : R →+* Z}

instance : FunLike (RingHomModForm hom k) ℕ Z where
  coe := RingHomModForm.sequence
  coe_injective' a b h := by cases a; cases b; congr




instance : SMul Z (RingHomModForm hom k) where
  smul c f := {
    sequence n := c * f n
    modular := sorry }




instance : Zero (RingHomModForm hom k) where

  zero := {
    sequence n := 0
    modular := sorry
  }



/-- Coercsion to the constant integer modular forms of weight 0 -/
def hconst (x : Z) : RingHomModForm hom 0 where
  sequence := fun n ↦ if n = 0 then x else 0
  modular := sorry

instance : Coe Z (RingHomModForm hom 0) where
  coe x := hconst x

instance : Add (RingHomModForm hom k) where
  add := fun a b ↦
  { sequence := a + b
    modular := sorry }

def hmul {k j : ℕ} (f : RingHomModForm hom k) (g : RingHomModForm hom j) : RingHomModForm hom (k + j) where
  sequence n := ∑ ⟨x,y⟩ ∈ (Finset.antidiagonal n), f x * g y
  modular := sorry

instance {j} : HMul (RingHomModForm hom k) (RingHomModForm hom j) (RingHomModForm hom (k + j)) where
  hMul := hmul

def hpow (a : RingHomModForm hom k) (j : ℕ) : RingHomModForm hom (k * j) where
  sequence n := ∑ x ∈ Finset.Nat.antidiagonalTuple j n, ∏ y, a (x y)
  -- sum over all x1 + ... + xj = n
  modular := sorry





instance instSMul : SMul Z (RingHomModForm hom k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}

instance instSMuz : SMul ℤ (RingHomModForm hom k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}

instance instSMuN : SMul ℕ (RingHomModForm hom k) where
  smul c a :=
  { sequence := c • a
    modular := sorry}


instance instNegx : Neg (RingHomModForm hom k) where
  neg := fun a ↦
  { sequence := -a
    modular := sorry }

instance instSubx : Sub (RingHomModForm hom k) where
  sub f g := f + -g




-- @[simp, norm_cast]
-- lemma coe_natCast (n : ℕ) :
--     ⇑(n : ModularFormMod ℓ 0) = n := rfl


-- @[simp, norm_cast]
-- lemma coe_intCast (z : ℤ) :
--     ⇑(z : ModularFormMod ℓ 0) = z := rfl

open Finset.Nat Finset

namespace RingHomModForm

@[simp]
theorem toFun_eq_coe (f : RingHomModForm hom k) : ⇑f = (f : ℕ → Z) := rfl

@[simp]
theorem coe_apply (f : RingHomModForm hom k) (n : ℕ) : f.sequence n = f n := rfl

@[simp]
theorem coe_add (f g : RingHomModForm hom k) : ⇑(f + g) = f + g := rfl

@[simp]
theorem add_apply (f g : RingHomModForm hom k) (z : ℕ) : (f + g) z = f z + g z := rfl

@[simp]
theorem coe_mul (f g : RingHomModForm hom k) : ⇑ (f * g) =
  fun n ↦ ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl

@[simp]
theorem mul_coe {j} (f : RingHomModForm hom k) (g : RingHomModForm hom j) :
  (f * g : ℕ → Z) = f * g := rfl


theorem mul_apply {j} (f : RingHomModForm hom k) (g : RingHomModForm hom j ) (n : ℕ) : (f * g) n =
  ∑ ⟨x,y⟩ ∈ antidiagonal n, f x * g y := rfl


@[simp]
theorem coe_smulz (f : RingHomModForm hom k) (n : ℤ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem coe_smuln (f : RingHomModForm hom k) (n : ℕ) : ⇑(n • f) = n • ⇑f := rfl

@[simp]
theorem zsmul_apply (f : RingHomModForm hom k) (n : ℤ) (z : ℕ) : (n • f) z = n • f z := rfl

@[simp]
theorem nsmul_apply (f : RingHomModForm hom k) (n z : ℕ) : (n • f) z = n • f z := rfl


@[simp]
theorem coe_zero : ⇑(0 : RingHomModForm hom k) = (0 : ℕ → Z) := rfl

@[simp]
theorem zero_apply (z : ℕ) : (0 : RingHomModForm hom k) z = 0 := rfl

@[simp]
theorem coe_neg (f : RingHomModForm hom k) : ⇑(-f) = -f := rfl

@[simp]
theorem neg_apply (f : RingHomModForm hom k) (n : ℕ) : (-f) n = - f n := rfl

@[simp]
theorem coe_sub (f g : RingHomModForm hom k) : ⇑(f - g) = f - g :=
  Eq.symm (Mathlib.Tactic.Abel.unfold_sub (⇑f) (⇑g) (⇑(f - g)) rfl)

@[simp]
theorem sub_apply (f g : RingHomModForm hom k) (z : ℕ) : (f - g) z = f z - g z :=
  Eq.symm (Mathlib.Tactic.Abel.unfold_sub (f z) (g z) ((f - g) z) rfl)


theorem coe_hpow (a : RingHomModForm hom k) (j : ℕ) : ⇑(hpow a j) = fun n ↦ ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl

theorem hpow_apply (a : RingHomModForm hom k) (j n : ℕ) : (hpow a j) n = ∑ x ∈ antidiagonalTuple j n, ∏ y, a (x y) := rfl



-- @[simp]
-- theorem oconst_zero (x : R) : (oconst x) 0 = x := rfl

-- @[simp]
-- theorem oconst_succ (x : R) (n : ℕ) : (oconst x) n.succ = 0 := rfl



@[ext]
theorem ext {a b : RingHomModForm hom k} (h : ∀ n, a n = b n) : a = b :=
  DFunLike.ext a b h

-- @[simp] theorem opow_zero (a : gModularForm R k) : opow a 0 = oconst 1 := by
--   ext n; rw [opow_apply]
--   match n with
--   | 0 => simp
--   | n + 1 => simp

/-- Casts an integer modular form to a different but provably equal weight -/
def hcast {m n : ℕ} (h : m = n) (a : RingHomModForm hom m) : RingHomModForm hom n :=
  h ▸ a

@[simp]
lemma hcast_apply {k j : ℕ} {h : k = j} {n : ℕ} {a : RingHomModForm hom k} :
  hcast h a n = a n := by
  subst h; rfl


@[simp]
lemma triangle_eval {k j : ℕ} {h : k = j} {n : ℕ} {a : RingHomModForm hom k} :
  (h ▸ a) n = a n := by
  subst h; rfl


instance : AddCommGroup (RingHomModForm hom k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smuln coe_smulz


@[simps]
def coeHom : RingHomModForm hom k →+ ℕ → Z where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

instance : Module Z (RingHomModForm hom k) :=
  Function.Injective.module Z RingHomModForm.coeHom DFunLike.coe_injective fun _ _ ↦ rfl


instance : DirectSum.GCommRing (RingHomModForm hom) :=
{ mul a b := a * b, mul_zero:= sorry, zero_mul := sorry, mul_add := sorry, add_mul := sorry, one := sorry, one_mul:= sorry, mul_one:= sorry, mul_assoc:= sorry, natCast:= sorry, natCast_zero:= sorry, natCast_succ:= sorry, intCast:= sorry, intCast_ofNat:= sorry, intCast_negSucc_ofNat:= sorry, mul_comm:= sorry, gnpow_zero' := sorry, gnpow_succ':= sorry}

end RingHomModForm

abbrev ModularFormMod' (ℓ : ℕ) [Fact (Nat.Prime ℓ)] := RingHomModForm <| ol.reduce ℓ

def oModularForm.Reduce (a : oModularForm ℓ k) : ModularFormMod' ℓ k :=
  ⟨fun n => ol.reduce ℓ (a n), by use a⟩


end RingHomModForm


def red_push : ((ZMod ℓ)[X,Y]k) → ModularFormMod' ℓ k :=
  fun ⟨⟨a,b,c⟩, prop⟩ => ∑ x : {x // x ∈ a}, (b x.1) • (RingHomModForm.hcast (by
    have : x.1 ∈ a := x.2
    apply prop
    simp_all only [ne_eq]
    exact this)
      (oModularForm.Reduce ℓ <| ofIntegerModularForm (ol ℓ) ((Eis 2) ** (x.1 Vars.X) * (Eis 3) ** (x.1 Vars.Y))))


def A_tilde [Fact (ℓ ≥ 5)] := poly_reduce ℓ (A ℓ)


theorem main [Fact (ℓ ≥ 5)] (p : (ZMod ℓ)[X,Y]k) (h : red_push ℓ p = 0) :
    (A_tilde ℓ).1 - 1 ∣ p.1 := sorry




-- theorem ModularFormMod'_congr' {k k'} (a : ModularFormMod' ℓ k) (h : ∃ m, a = hcast m 1) :

-- GOAL
theorem ModularFormMod'_congr {k k'} (a : ModularFormMod' ℓ k) (b : ModularFormMod' ℓ k')
  (h : ∀ n, a n = b n) : k ≡ k' [MOD (ℓ - 1)] := sorry





section Algebra

open DirectSum Sigma

namespace Algebra

#check DirectSum


@[reducible] def M (ℓ : ℕ) : Type := (⨁ i, oModularForm ℓ i)

instance : Module (o ℓ) (M ℓ) := sorry

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [Fact (ℓ ≥ 5)]

-- coercison to a sequence (formal power series)
def M.qexp (f : M ℓ) : ℕ → o ℓ :=
  f.support.sum (f · ·)
-- ∑ i ∈ f.support, fun n => f i n

lemma qexp_of (f : oModularForm ℓ k) : M.qexp (of _ _ f) = fun n => (f n : o ℓ) := by
  rw [of, M.qexp]
  sorry



def ofPoly_mono : (Vars →₀ ℕ) → (M ℓ)
  | ⟨_, f, _⟩ => of _ _ (ofIntegerModularForm _ ((Eis 2) ** (f .X) * (Eis 3) ** (f .Y)))


def ofPoly : (o ℓ)[X,Y] →ₗ[o ℓ] (M ℓ) :=
  Basis.constr (MvPolynomial.basisMonomials _ _) (o ℓ) ofPoly_mono



def M.pexp (f : M ℓ) : (o ℓ)[X,Y] :=
  ∑ i ∈ f.support, (pull ℓ (f i)).forget

def Iso : M ℓ ≅ (o ℓ)[X,Y] where
  hom := M.pexp
  inv p := ofPoly p
  hom_inv_id := by sorry
    -- ext f a b
    -- simp [ofPoly]
    -- sorry



def A : (o ℓ)[X,Y] := M.pexp (of _ _ (ofIntegerModularForm (ol ℓ) (Eis (((ℓ - 1) / 2)))))


def M_tilde_set (ℓ) [Fact (Nat.Prime ℓ)] : Set (ℕ → ZMod ℓ) :=
    {fun n => (f.qexp n).reduce | f : M ℓ}



def M_tilde (ℓ) [Fact (Nat.Prime ℓ)] : Type :=
    {x // x ∈ M_tilde_set ℓ}

def M.reduce : M ℓ → M_tilde ℓ
  | f => ⟨fun n => (f.qexp n).reduce, by use f⟩


def M_t (ℓ) [Fact (Nat.Prime ℓ)] (k : ℕ) : Set (ℕ → ZMod ℓ) :=
  {fun n => ol.reduce ℓ (⇑f n) | f : oModularForm ℓ k}


def ModularFormMod'' (ℓ) [Fact (Nat.Prime ℓ)] (k : ZMod (ℓ - 1)) :=
  ⋃ j : ℕ, M_t ℓ (k.val + j * (ℓ - 1))


section M_tilde

instance : CommRing <| M_tilde ℓ := sorry
instance : Module (ZMod ℓ) (M_tilde ℓ) := sorry

variable [∀ i, AddCommMonoid ((fun i ↦ ↑(ModularFormMod'' ℓ i)) i)]


def iso : M_tilde ℓ ≅ ⨁ i, ModularFormMod'' ℓ i := sorry


end M_tilde

def M.reduce_hom : M ℓ →+* M_tilde ℓ where
  toFun := M.reduce
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry



def ofModularFormMod (a : ModularFormMod' ℓ k) : M_tilde ℓ :=
  ⟨⇑a, by
    obtain ⟨b,p⟩ := a.modular; use of _ _ b;
    trans a.sequence
    simp [qexp_of, p]
    ext n; rfl
    rfl ⟩


def MvPolynomial.reduce : (o ℓ)[X,Y] → (ZMod ℓ)[X,Y]
  | ⟨a, b, c⟩ =>
    ⟨{x ∈ a | (b x).reduce ≠ 0}, fun x => (b x).reduce, fun x => by
      simp [c x]; contrapose!
      intro h; rw [h]; sorry ⟩

-- def MvPolynomial.reduce_hom : (o ℓ)[X,Y] →+* (ZMod ℓ)[X,Y] where
--   toFun := MvPolynomial.reduce


def A_tilde : (ZMod ℓ)[X,Y] := MvPolynomial.reduce A


def ofPoly'_mono (f : Vars →₀ ℕ) : (M_tilde ℓ) :=
  (ofPoly_mono f).reduce

def ofPoly' : (ZMod ℓ)[X,Y] →ₗ[ZMod ℓ] (M_tilde ℓ) :=
  Basis.constr (MvPolynomial.basisMonomials _ _) (ZMod ℓ) ofPoly'_mono

def ofPoly'_hom : (ZMod ℓ)[X,Y] →+* (M_tilde ℓ) where
  toFun := ofPoly'
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry



theorem ofPoly'_eq_reduce (f : (o ℓ)[X,Y]) :
    ofPoly' (MvPolynomial.reduce f) = (ofPoly f).reduce := sorry



#check DirectSum
section Del
open PowerSeries

variable {R : Type} [CommRing R]

def Theta (f : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.X * f.derivativeFun



def oModularForm.Del (k : ℕ) (f : oModularForm ℓ k) : oModularForm ℓ (k + 2) := sorry

def oModularForm.De (k : ℕ) : oModularForm ℓ k →+ M ℓ where
  toFun f := (of _ _ <| oModularForm.Del _ f)
  map_zero' := sorry
  map_add' := sorry


-- toModule
def M.Del : M ℓ →+ M ℓ := DirectSum.toAddMonoid oModularForm.De


def ofPoly'_mono'  :

  Derivation (o ℓ) ((o ℓ)[X,Y]) ((o ℓ)[X,Y]) :=

  MvPolynomial.mkDerivation (o ℓ) fun

  | Var.x => dX

  | Var.y => dY




end Del




#check PowerSeries

theorem A_tilde_irreducible : Irreducible (A_tilde - (1 : (ZMod ℓ)[X,Y])) := sorry


theorem A_tilde_prime : Ideal.IsPrime <| Ideal.span {A_tilde - (1 : (ZMod ℓ)[X,Y])} := sorry


theorem main_ker : RingHom.ker ofPoly'_hom = Ideal.span {A_tilde - (1 : (ZMod ℓ)[X,Y])} := sorry



theorem ModularFormMod'_congr {k k'} (a : ModularFormMod' ℓ k) (b : ModularFormMod' ℓ k')
  (h : ∀ n, a n = b n) : k ≡ k' [MOD (ℓ - 1)] := sorry
















def congruence_eqv : Setoid (M ℓ) where

  r f g := ∀ n, (f.qexp n).reduce = (g.qexp n).reduce

  iseqv := sorry






def Mtilde (ℓ : ℕ) [Fact (Nat.Prime ℓ)] := ∀ i, ModularFormMod' ℓ i



def Mtilde (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :=
  @Quotient (M ℓ) congruence_eqv

namespace Mtilde

def add : Mtilde ℓ → Mtilde ℓ → Mtilde ℓ :=
  Quotient.lift₂ (fun a b : M ℓ => ⟦a + b⟧) (by sorry)

instance : Add (Mtilde ℓ) where
  add := add

def mul : Mtilde ℓ → Mtilde ℓ → Mtilde ℓ :=
  Quotient.lift₂ (fun a b : M ℓ => ⟦a * b⟧) (by sorry)

instance : Mul (Mtilde ℓ) where
  mul := mul





structure Mdrop_weight (ℓ) [Fact (Nat.Prime ℓ)] where
  val : ℕ → ZMod ℓ
  ofModularFormMod' : ∃ (i : ℕ) (a : ModularFormMod' ℓ i), val = ⇑a








def M_tilde : Submodule (ZMod ℓ) (ℕ → ZMod ℓ) :=
  Submodule.span (ZMod ℓ) (M_tilde_set)



-- doesn't equate elements of different weights
@[reducible] def M_tilde (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : Type := Π i, ModularFormMod' ℓ i

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]


def M.Reduce (a : M ℓ) : M_tilde ℓ :=
  fun i => (a i).Reduce ℓ
