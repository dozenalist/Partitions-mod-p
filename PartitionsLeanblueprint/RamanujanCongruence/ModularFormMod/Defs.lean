
import PartitionsLeanblueprint.RamanujanCongruence.IntegerModularForm.Defs



noncomputable section

open PowerSeries


def IntegerModularForm.reduce {k : ℤ} (ℓ : ℕ) : IntegerModularForm k →ₗ[ℤ] PowerSeries (ZMod ℓ) where
  toFun f := map (Int.castRingHom (ZMod ℓ)) f.fourier
  map_add' := by simp
  map_smul' := by simp

@[simp]
theorem IntegerModularForm.reduce_mul {k j : ℤ} (ℓ : ℕ) (f : IntegerModularForm k) (g : IntegerModularForm j) :
  (f.mul g).reduce ℓ = f.reduce ℓ * g.reduce ℓ := by simp [reduce]

def IntegerModularForm.ZMod.reduce_set {ℓ : ℕ} (k : ZMod (ℓ - 1)) : AddSubgroup (PowerSeries (ZMod ℓ)) where
  carrier := ⋃ j ∈ {j : ℤ | ↑j = k}, Set.range (@IntegerModularForm.reduce j ℓ)
  add_mem' := sorry -- multiply by E (ℓ - 1)
  zero_mem' := by simpa using ⟨k.cast, by simp, 0, map_zero _⟩
  neg_mem' {f} h := by
    simp_all only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range, exists_prop]
    obtain ⟨i, hi, g, hg⟩ := h
    use i, hi, -g, hg ▸ map_neg _ _




open IntegerModularForm Set

theorem IntegerModularForm.reduce_set_mul_mem {ℓ : ℕ} {k j : ZMod (ℓ - 1)} {f g : (ZMod ℓ)⟦X⟧}
    (hf : f ∈ k.reduce_set) (hg : g ∈ j.reduce_set) : f * g ∈ (k + j).reduce_set := by
    simp_all [ZMod.reduce_set, mem_iUnion]
    obtain ⟨kk, hk, ff, hf⟩ := hf
    obtain ⟨jj, hj, gg, hg⟩ := hg
    use kk + jj, by rw [Int.cast_add, hk, hj]
    use ff.mul gg, by rw [reduce_mul, hf, hg]



structure ModularFormMod (ℓ : ℕ) (k : ZMod (ℓ - 1)) where

  fourier : PowerSeries (ZMod ℓ)

  modular : fourier ∈ k.reduce_set


namespace ModularFormMod

variable {ℓ : ℕ} {k j : ZMod (ℓ - 1)}


instance : Zero (ModularFormMod ℓ k) where

  zero :=

  { fourier := 0
    modular := zero_mem _}


instance : Inhabited (ModularFormMod ℓ k) := ⟨0⟩


theorem fourier_inj : Function.Injective (@ModularFormMod.fourier ℓ k) :=
  fun f g h => by
  cases f
  cases g
  simpa only [mk.injEq] using h


lemma Exists_reduce (f : ModularFormMod ℓ k) :
    ∃ j : ℤ, ↑j = k ∧ ∃ g : IntegerModularForm j, g.reduce ℓ = f.fourier := by
  obtain ⟨ff, hf⟩ := f
  simpa [ZMod.reduce_set, mem_iUnion] using hf

def choose (f : ModularFormMod ℓ k) :=
  f.Exists_reduce.choose_spec.right.choose

def choose_spec (f : ModularFormMod ℓ k) :=
  f.Exists_reduce.choose_spec.right.choose_spec


def const (x : ZMod ℓ) : ModularFormMod ℓ 0 where
  fourier := C x
  modular := by simpa [ZMod.reduce_set, mem_iUnion] using
    ⟨0, by simp, IntegerModularForm.const x.cast, by ext; simp [- fourier_const, reduce, coeff_C]⟩


instance : Coe (ZMod ℓ) (ModularFormMod ℓ 0) where
  coe x := const x

instance : One (ModularFormMod ℓ 0) :=
  ⟨const 1⟩

instance add : Add (ModularFormMod ℓ k) where
  add := fun a b ↦
  { fourier := a.fourier + b.fourier
    modular := add_mem a.modular b.modular }


protected def mul (f : ModularFormMod ℓ k) (g : ModularFormMod ℓ j) : ModularFormMod ℓ (k + j) where
  fourier := f.fourier * g.fourier
  modular := reduce_set_mul_mem f.modular g.modular


protected def pow (f : ModularFormMod ℓ k) (j : ℕ) : ModularFormMod ℓ (j * k) where
  fourier := f.fourier ^ j
  modular := by
    induction j with
    | zero => simpa [ZMod.reduce_set, reduce] using
      ⟨0, Int.cast_zero, IntegerModularForm.const 1, by simp [IntegerModularForm.const]⟩
    | succ m ih => simpa [pow_succ, add_mul] using reduce_set_mul_mem ih f.modular


instance instSMulZ : SMul ℤ (ModularFormMod ℓ k) where
  smul c a :=
  { fourier := c • a.fourier
    modular := zsmul_mem a.modular _ }


instance instSMulN : SMul ℕ (ModularFormMod ℓ k) where
  smul c a :=
  { fourier := c • a.fourier
    modular := nsmul_mem a.modular _ }

instance instSMulZMod : SMul (ZMod ℓ) (ModularFormMod ℓ k) where
  smul c a :=
  { fourier := c • a.fourier
    modular := by
      rw [← ZMod.intCast_zmod_cast c]; norm_cast; exact zsmul_mem a.modular c.cast
  }

instance instNeg : Neg (ModularFormMod ℓ k) where
  neg a :=
  { fourier := -a.fourier
    modular := neg_mem a.modular }

instance instSub : Sub (ModularFormMod ℓ k) :=
  ⟨fun f g =>
    { fourier := f.fourier - g.fourier
      modular := sub_mem f.modular g.modular }⟩

instance : NatCast (ModularFormMod ℓ 0) where
  natCast n := const n

instance : IntCast (ModularFormMod ℓ 0) where
  intCast z := const z

variable (f g : ModularFormMod ℓ k) (h : ModularFormMod ℓ j)

@[simp] theorem fourier_zero : (0 : ModularFormMod ℓ k).fourier = 0 := rfl

@[simp] theorem fourier_const (x : ZMod ℓ) : (const x).fourier = C x := rfl

@[simp] theorem fourier_add : (f + g).fourier = f.fourier + g.fourier := rfl

@[simp] theorem fourier_neg : (-f).fourier = -f.fourier := rfl

@[simp] theorem fourier_sub : (f - g).fourier = f.fourier - g.fourier := rfl

@[simp] theorem fourier_mul : (f.mul h).fourier = f.fourier * h.fourier := rfl

@[simp] theorem fourier_pow (n) : (f.pow n).fourier = f.fourier ^ n := rfl

@[simp] theorem fourier_nsmul (n : ℕ) : (n • f).fourier = n • f.fourier := rfl

@[simp] theorem fourier_zsmul (x : ℤ) : (x • f).fourier = x • f.fourier := rfl

@[simp] theorem fourier_smul (x : ZMod ℓ) : (x • f).fourier = x • f.fourier := rfl



instance : AddCommGroup (ModularFormMod ℓ k) :=
  fourier_inj.addCommGroup _ rfl fourier_add fourier_neg fourier_sub fourier_nsmul fourier_zsmul


def fourierAddHom : (ModularFormMod ℓ k) →+ PowerSeries (ZMod ℓ) where
  toFun := fourier
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module (ZMod ℓ) (ModularFormMod ℓ k) :=
  Function.Injective.module (ZMod ℓ) fourierAddHom fourier_inj fun _ _ ↦ rfl



def coeff (n : ℕ) : ModularFormMod ℓ k →ₗ[ZMod ℓ] ZMod ℓ where
  toFun f := f.fourier.coeff n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


@[ext]
theorem ext {f g : ModularFormMod ℓ k} (h : ∀ n, f.coeff n = g.coeff n) : f = g :=
  fourier_inj <| PowerSeries.ext h


variable (n : ℕ)


theorem coeff_def : f.coeff n = f.fourier.coeff n := rfl

@[simp low]
theorem coeff_const (x : ZMod ℓ) : (const x).coeff n = if n = 0 then x else 0 := by
  rw [coeff_def, const, coeff_C n x]

@[simp]
theorem coeff_const_zero (x : ZMod ℓ) : (const x).coeff 0 = x :=
  coeff_const _ _ ▸ if_pos rfl

@[simp]
theorem coeff_const_succ (x : ZMod ℓ) : (const x).coeff (n + 1) = 0 :=
  coeff_const _ _ ▸ if_neg (Nat.succ_ne_zero _)


open Finset

theorem coeff_mul : (f.mul h).coeff n = ∑ p ∈ antidiagonal n, f.coeff p.1 * h.coeff p.2 := by
  simp only [coeff_def, fourier_mul, PowerSeries.coeff_mul]

theorem coeff_pow (j : ℕ) : (f.pow j).coeff n =
    ∑ l ∈ finsuppAntidiag (range j) n, ∏ i ∈ range j, f.coeff (l i) := by
  simp only [coeff_def, fourier_pow, PowerSeries.coeff_pow]


/-- Casts a modular form mod ℓ to a different but provably equal weight -/
def Mcast {m n : ZMod (ℓ - 1)} (h : m = n := by grind) (a : ModularFormMod ℓ m) : ModularFormMod ℓ n where
  fourier := a.fourier
  modular := h ▸ a.modular


@[simp]
lemma fourier_Mcast {h : k = j} (a : ModularFormMod ℓ k) : (a.Mcast h).fourier = a.fourier := rfl

@[simp]
lemma coeff_Mcast {k j : ZMod (ℓ - 1)} {h : k = j} {n : ℕ} (a : ModularFormMod ℓ k) :
  (Mcast h a).coeff n = a.coeff n := rfl


@[simp]
lemma coeff_triangle {k j : ZMod (ℓ -1)} {h : k = j} {n : ℕ} (a : ModularFormMod ℓ k) :
  (h ▸ a).coeff n = a.coeff n := by
  subst h; rfl


@[simp] theorem pow_zero (a : ModularFormMod ℓ k) : a.pow 0 = (const 1).Mcast :=
  fourier_inj <| by simp

@[simp] theorem pow_one (a : ModularFormMod ℓ k) : a.pow 1 = a.Mcast :=
  fourier_inj <| by simp

@[simp] theorem zero_pow (j : ℕ) [hj : NeZero j] : (0 : ModularFormMod ℓ k).pow j = 0 :=
  fourier_inj <| by simp [hj.out]


@[simp] theorem const_mul (c : ZMod ℓ) (a : ModularFormMod ℓ k) : (const c).mul a = (c • a).Mcast :=
  fourier_inj <| by simp [smul_eq_C_mul]


theorem mul_comm : f.mul g = (g.mul f).Mcast :=
  fourier_inj <| by simp [_root_.mul_comm]


@[ext (iff := false)]
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid <| ModularFormMod ℓ}
    (h : a.fst = b.fst) (h2 : Mcast h a.snd = b.snd) : a = b := by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

instance : GradedMonoid.GOne (ModularFormMod ℓ) where
  one := 1

instance : GradedMonoid.GMul (ModularFormMod ℓ) where
  mul f g := f.mul g

instance : DirectSum.GCommRing (ModularFormMod ℓ) := sorry

  -- one_mul _ := gradedMonoid_eq_of_cast (zero_add _) (ext fun _ => one_mul _)
  -- mul_one _ := gradedMonoid_eq_of_cast (add_zero _) (ext fun _ => mul_one _)
  -- mul_assoc _ _ _ := gradedMonoid_eq_of_cast (add_assoc _ _ _) (ext fun _ => mul_assoc _ _ _)
  -- mul_zero {_ _} _ := ext fun _ => mul_zero _
  -- zero_mul {_ _} _ := ext fun _ => zero_mul _
  -- mul_add {_ _} _ _ _ := ext fun _ => mul_add _ _ _
  -- add_mul {_ _} _ _ _ := ext fun _ => add_mul _ _ _
  -- mul_comm f g := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => by sorry)
  -- natCast := Nat.cast
  -- natCast_zero := ext fun _ => Nat.cast_zero
  -- natCast_succ _ := ext fun _ => Nat.cast_succ _
  -- intCast := Int.cast
  -- intCast_ofNat _ := ext fun _ => AddGroupWithOne.intCast_ofNat _
  -- intCast_negSucc_ofNat _ := fourier_inj <| by simp [AddGroupWithOne.intCast_negSucc _]



end ModularFormMod

open ModularFormMod

namespace IntegerModularForm

def Reduce {k} (ℓ : ℕ) : IntegerModularForm k →ₗ[ℤ] ModularFormMod ℓ ↑k where
  toFun f := {
    fourier := f.reduce ℓ
    modular := by simpa [ZMod.reduce_set, mem_iUnion] using ⟨k, rfl, f, rfl⟩ }
  map_add' _ _ := fourier_inj <| by simp only [map_add, ModularFormMod.fourier_add]
  map_smul' _ _ := fourier_inj <| by simp

variable {ℓ : ℕ} {k j : ℤ} (f g : IntegerModularForm k) (h : IntegerModularForm j)

@[simp] theorem fourier_Reduce : (f.Reduce ℓ).fourier = f.reduce ℓ := rfl

@[simp, norm_cast] theorem Reduce_Icast (a : IntegerModularForm k) (h : k = j) :
    (a.Icast h).Reduce ℓ = (a.Reduce ℓ).Mcast (h ▸ rfl) :=
  fourier_inj <| by simp [reduce]

@[simp] theorem coeff_Reduce (n) : (f.Reduce ℓ).coeff n = ↑(f.coeff n) := rfl

@[simp] theorem Reduce_mul : (f.mul g).Reduce ℓ = ((f.Reduce ℓ).mul (g.Reduce ℓ)).Mcast :=
  fourier_inj <| by simp

@[simp] theorem Reduce_pow (m) : (f.pow m).Reduce ℓ = ((f.Reduce ℓ).pow m).Mcast (by norm_cast) :=
  fourier_inj <| by simp [reduce]
