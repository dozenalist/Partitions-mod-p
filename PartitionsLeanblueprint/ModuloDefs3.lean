import PartitionsLeanblueprint.ModularFormDefs
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Multinomial



-- structure ModularFormMod (ℓ : ℕ) (k : ZMod (ℓ - 1)) where
--   sequence : ℕ → ZMod ℓ
--   weight : ℕ
--   carrier : IntegerModularForm weight
--   weight_congr : k = weight
--   carrier_congr (n) : sequence n = carrier n

-- namespace ModularFormMod


-- def Reduce {k} (ℓ : ℕ) (a : IntegerModularForm k) : ModularFormMod ℓ k :=
--   ⟨fun n => a n, k, a, rfl, fun _ => rfl⟩


-- variable {ℓ m n : ℕ} {k j : ZMod (ℓ - 1)}

-- instance : CoeFun (ModularFormMod ℓ k) (fun _ => ℕ → ZMod ℓ) where
--   coe a := a.sequence

-- @[reducible]
-- def hasWeight (a : ModularFormMod ℓ k) (j : ℕ) :=
--   ∃ b : ModularFormMod ℓ k, b.weight = j ∧ ∀ n, a n = b n

-- noncomputable def Filtration (a : ModularFormMod ℓ k) :=
--   Nat.find (⟨a.weight, a, rfl, fun _ => rfl⟩ : ∃ k, hasWeight a k)

-- noncomputable def lift (a : ModularFormMod ℓ k) (h : hasWeight a m) : ModularFormMod ℓ k := sorry


-- setoid on IntegerModularForm, then Reduce

namespace halp

instance Reqv (ℓ k : ℕ) : Setoid (IntegerModularForm k) where
  r a b := ∀ n, a n = (b n : ZMod ℓ)
  iseqv := sorry



inductive ModularFormModCon (ℓ : ℕ) (j : ZMod (ℓ - 1)) : Type where
  | Reduce (k : ℕ) (a : IntegerModularForm k) (h : k = j) : ModularFormModCon ℓ j


end halp



namespace old
inductive ModularFormMod : (ℓ : ℕ) → ZMod (ℓ - 1) → Type where

  | Reduce (ℓ : ℕ) {j} : IntegerModularForm j → ModularFormMod ℓ j





#check ModularFormMod.noConfusion
#check ModularFormMod.noConfusionType

open ModularFormMod

-- We need FunLike
instance {ℓ k} : CoeFun (ModularFormMod ℓ k) (fun _ => ℕ → ZMod ℓ) where

  coe := fun | Reduce ℓ (b : IntegerModularForm _) => fun n => ↑(b n)


universe u
variable {α β χ R : Type u} [CoeFun α fun _ => ℕ → R] [CoeFun β fun _ => ℕ → R] [CoeFun χ fun _ => ℕ → R]


def Mod_eq (a : α) (b : β) :=
  ∀ n, a n = b n


/-- Two modular forms of different weight can be "equal" if they are the same sequence.
This is an equivalence relation, so we can put it into calc blocks and such. -/
infixl:50 (priority := high) "==" => Mod_eq


instance : IsRefl α Mod_eq where
  refl := λ _ _ ↦ rfl

@[refl]
theorem Mod_eq.refl (a : α) : a == a := λ _ ↦ rfl

instance : IsSymm α (. == .) where
  symm := λ _ _ h _ ↦ Eq.symm (h _)

@[symm]
theorem Mod_eq.symm {a: α} {b : β} (h : a == b) : b == a :=  λ n ↦ Eq.symm (h n)

instance : Trans (. == . : α → β → Prop) (. == . : β → χ → Prop) (. == . : α → χ → Prop) where
  trans := λ h g _ ↦ Eq.trans (h _) (g _)

@[trans]
theorem Mod_eq.trans {a : α} {b : β} {c : χ} (h : a == b) (g : b == c) : a == c :=
  λ _ ↦ Eq.trans (h _) (g _)

-- instance : Trans (. == . : α → β → Prop) (. = . : β → β → Prop) (. == . : α → β → Prop) where
--   trans := λ h g ↦ g ▸ h

-- instance : Trans (. = . : α → α → Prop) (. == . : α → β → Prop) (. == . : α → β → Prop) where
--   trans := λ h g ↦ h ▸ g





instance inst : IsEquiv α Mod_eq where
  refl := IsRefl.refl
  symm := IsSymm.symm
  trans := λ _ _ _ h g _ ↦ Eq.trans (h _) (g _)

def Meqv {ℓ k} : Setoid (ModularFormMod ℓ k) where
  r := (· == ·)
  iseqv := ⟨.refl, .symm, .trans⟩


def ModularFormMod2 (ℓ : ℕ) (k : ZMod (ℓ - 1)): Type :=
    Quotient (@Meqv ℓ k)

instance {ℓ k} : FunLike (ModularFormMod2 ℓ k) ℕ (ZMod ℓ) where
  coe := Quotient.lift (⇑·) fun _ _ h => funext (h ·)

  coe_injective' a b h := Quotient.inductionOn a fun c => Quotient.inductionOn b fun d => by
    apply Quotient.sound
    intro n






--Quotient.lift (fun (a b : ModularFormMod ℓ k) => (by sorry : ⟦a⟧  ) (by sorry)


variable {ℓ k} (a : ModularFormMod2 ℓ k)



theorem Reduce_apply {ℓ k n} (a : IntegerModularForm k) : Reduce ℓ a n = (a n : ZMod ℓ) := rfl


end old

namespace new -- doesnt work



def redeq (ℓ : ℕ) {k} (a b : IntegerModularForm k) :=
  ∀ n, (a n : ZMod ℓ) = (b n : ZMod ℓ)

instance ee {ℓ k} : IsEquiv (IntegerModularForm k) (redeq ℓ) where
  refl _ _ := rfl
  symm _ _ h n := (h n).symm
  trans _ _ _ h g n := (h n).trans <| g n

def redeqv {ℓ k : ℕ} : Setoid (IntegerModularForm k) where
  r := redeq ℓ
  iseqv := ⟨ee.refl, @ee.symm, @ee.trans⟩

def IntegerModularFormEquiv (ℓ : ℕ) (k : ℕ) :=
  Quotient (@redeqv ℓ k)

instance {ℓ k} : CoeFun (IntegerModularFormEquiv ℓ k) (fun _ => ℕ → ZMod ℓ) where
  coe := Quotient.lift ↑(· ·) fun _ _ h => funext (h ·)



@[match_pattern]
inductive ModularFormMod : (ℓ : ℕ) → (j : ZMod (ℓ - 1)) → Type where

  | Reduce {ℓ : ℕ} {k} : IntegerModularFormEquiv ℓ k → ModularFormMod ℓ ↑k

#check Group

-- instance {ℓ} {k : ZMod (ℓ - 1)} : FunLike (ModularFormMod ℓ k) ℕ (ZMod ℓ) where
--   coe := fun | .Reduce k a h, n => ↑(a n)
--   coe_injective' := fun | .Reduce k1 a ha, .Reduce k2 b hb, h => by congr

#check Eq


-- make a function that gives the set of integermodularforms that reduce to a mod ℓ