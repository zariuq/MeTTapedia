import Mettapedia.CategoryTheory.WriterActionSlice

/-!
# Transport of free accounts and their observations

A monoid homomorphism changes account labels while a generator map changes
values.  The resulting map is equivariant into the target action restricted
along that homomorphism.  Mathlib's existing restriction and slice functors
also express a simultaneous change of observation carrier.

These maps prove algebraic identity, composition, unit and multiplication
comparisons.  No substitution operation on authored Cost terms is supplied.
-/

open CategoryTheory CategoryTheory.Category

namespace Mettapedia.CategoryTheory.WriterActionTransport

open WriterActionAdjunction

set_option autoImplicit false

universe u

variable {M N P X Y Z K L : Type u} [Monoid M] [Monoid N] [Monoid P]

/-- Change accounts and generators, using the existing target action with
scalars restricted along the chosen monoid homomorphism. -/
def freeMap (accounts : M →* N) (values : X → Y) :
    freeObject M X ⟶ (Action.res (Type u) accounts).obj (freeObject N Y) where
  hom := TypeCat.ofHom fun pair => (accounts pair.1, values pair.2)
  comm := by
    intro account
    apply ConcreteCategory.ext_apply
    intro pair
    exact Prod.ext (accounts.map_mul account pair.1) rfl

theorem freeMap_apply (accounts : M →* N) (values : X → Y) (pair : M × X) :
    (freeMap accounts values).hom pair = (accounts pair.1, values pair.2) := rfl

/-- Identity transport keeps the complete account-value pair. -/
theorem freeMap_id :
    (freeMap (MonoidHom.id M) (id : X → X)).hom = 𝟙 (M × X) := rfl

/-- Identity transport is also the identity action arrow after the canonical
restriction-of-scalars comparison. -/
theorem freeMap_resId :
    freeMap (MonoidHom.id M) (id : X → X) ≫
      (Action.resId (Type u) (G := M)).hom.app (freeObject M X) = 𝟙 (freeObject M X) := by
  apply Action.Hom.ext
  rfl

/-- Transport composition is the composition of the account and value maps. -/
theorem freeMap_comp (firstAccounts : M →* N) (secondAccounts : N →* P)
    (firstValues : X → Y) (secondValues : Y → Z) :
    (freeMap firstAccounts firstValues).hom ≫
      (freeMap secondAccounts secondValues).hom =
    (freeMap (secondAccounts.comp firstAccounts) (secondValues ∘ firstValues)).hom := rfl

/-- Action-arrow composition uses Mathlib's canonical comparison of two
successive restrictions with restriction along the composite homomorphism. -/
theorem freeMap_resComp (firstAccounts : M →* N) (secondAccounts : N →* P)
    (firstValues : X → Y) (secondValues : Y → Z) :
    freeMap firstAccounts firstValues ≫
      (Action.res (Type u) firstAccounts).map (freeMap secondAccounts secondValues) ≫
      (Action.resComp (Type u) firstAccounts secondAccounts).hom.app (freeObject P Z) =
    freeMap (secondAccounts.comp firstAccounts) (secondValues ∘ firstValues) := by
  apply Action.Hom.ext
  rfl

/-- Changing the account monoid preserves pure return. -/
theorem freeMap_unit (accounts : M →* N) (values : X → Y) :
    (writerMonad M).η.app X ≫ (freeMap accounts values).hom =
      TypeCat.ofHom values ≫ (writerMonad N).η.app Y := by
  apply ConcreteCategory.ext_apply
  intro value
  exact Prod.ext accounts.map_one rfl

/-- A monoid homomorphism respects account flattening in chronological order. -/
theorem freeMap_multiplication (accounts : M →* N) (values : X → Y) :
    (writerMonad M).μ.app X ≫ (freeMap accounts values).hom =
      (freeMap accounts (fun pair => (freeMap accounts values).hom pair)).hom ≫
        (writerMonad N).μ.app Y := by
  apply ConcreteCategory.ext_apply
  intro pair
  exact Prod.ext (accounts.map_mul pair.1 pair.2.1) rfl

/-- A map between observation carriers gives an equivariant map between their
trivial actions; it changes no account. -/
def observationMap (keys : K → L) : Action.trivial M K ⟶ Action.trivial M L where
  hom := TypeCat.ofHom keys
  comm := fun _ => by ext value; rfl

/-- Simultaneous account and observation transport on free sliced objects.
The supplied generator triangle licenses observation preservation. -/
def sliceMap (accounts : M →* N) (keys : K → L)
    (source : Over K) (target : Over L)
    (values : source.left ⟶ target.left)
    (observations : values ≫ target.hom = source.hom ≫ TypeCat.ofHom keys) :
    (Over.map (observationMap (M := M) keys)).obj
        ((WriterActionSlice.install M K).obj source) ⟶
      (Over.post (Action.res (Type u) accounts)).obj
        ((WriterActionSlice.install N L).obj target) :=
  Over.homMk (freeMap accounts fun value => values value) (by
    apply Action.Hom.ext
    apply ConcreteCategory.ext_apply
    intro pair
    exact ConcreteCategory.congr_hom observations pair.2)

/-- The sliced map explicitly carries both transported coordinates. -/
theorem sliceMap_apply (accounts : M →* N) (keys : K → L)
    (source : Over K) (target : Over L)
    (values : source.left ⟶ target.left)
    (observations : values ≫ target.hom = source.hom ≫ TypeCat.ofHom keys)
    (pair : M × source.left) :
    (sliceMap accounts keys source target values observations).left.hom pair =
      (accounts pair.1, values pair.2) := rfl

/-- The map retains the source observation through the selected observation
transport, independently of its account homomorphism. -/
theorem sliceMap_observation (accounts : M →* N) (keys : K → L)
    (source : Over K) (target : Over L)
    (values : source.left ⟶ target.left)
    (observations : values ≫ target.hom = source.hom ≫ TypeCat.ofHom keys)
    (pair : M × source.left) :
    target.hom
      ((sliceMap accounts keys source target values observations).left.hom pair).2 =
      keys (source.hom pair.2) :=
  ConcreteCategory.congr_hom observations pair.2

#print axioms freeMap
#print axioms freeMap_id
#print axioms freeMap_resId
#print axioms freeMap_comp
#print axioms freeMap_resComp
#print axioms freeMap_unit
#print axioms freeMap_multiplication
#print axioms sliceMap
#print axioms sliceMap_observation

end Mettapedia.CategoryTheory.WriterActionTransport
