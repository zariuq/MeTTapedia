import Mathlib.CategoryTheory.Opposites
import Mettapedia.GSLT.Core.ContextualLadderBaseCategory

/-!
# The family-valued presheaf of a contextual core

A standard category with families includes a presheaf into the category
`Fam` of indexed families.  `ContextualLadder.Cwf` stores the same data in
its concrete, substitution-oriented form.  This module reconstructs the
actual categorical object:

* an object of `IndexedFamily` is an index type and one fibre over each
  index;
* a morphism maps both indices and their dependent fibres;
* every `Cwf` induces a contravariant functor from contexts and
  substitutions to `IndexedFamily`.

The term component is essential data.  The negative canary at the end gives
two family morphisms with the same index map and different fibre maps, so a
type-only translation cannot masquerade as a morphism of families.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

/-! ## The category of indexed families -/

/-- An indexed family consists of an index type and a type over each index. -/
structure IndexedFamily where
  Index : Type w
  Fibre : Index → Type w'

namespace IndexedFamily

/-- A morphism of indexed families maps indices and every corresponding
fibre. -/
structure Hom (X Y : IndexedFamily.{w, w'}) where
  onIndex : X.Index → Y.Index
  onFibre : ∀ index, X.Fibre index → Y.Fibre (onIndex index)

/-- Extensional equality for family morphisms.  `HEq` states fibrewise
agreement while the index maps are still propositionally, rather than
definitionally, equal. -/
@[ext]
theorem Hom.ext {X Y : IndexedFamily.{w, w'}} {left right : Hom X Y}
    (indexEq : left.onIndex = right.onIndex)
    (fibreEq : ∀ index element,
      HEq (left.onFibre index element) (right.onFibre index element)) :
    left = right := by
  cases left with
  | mk leftIndex leftFibre =>
      cases right with
      | mk rightIndex rightFibre =>
          dsimp at indexEq fibreEq
          cases indexEq
          have fibresEqual : leftFibre = rightFibre := by
            funext index element
            exact eq_of_heq (fibreEq index element)
          cases fibresEqual
          rfl

/-- Indexed families and their dependent maps form a category. -/
instance : Category (IndexedFamily.{w, w'}) where
  Hom := Hom
  id _ :=
    { onIndex := id
      onFibre := fun _ element => element }
  comp left right :=
    { onIndex := right.onIndex ∘ left.onIndex
      onFibre := fun index element =>
        right.onFibre (left.onIndex index) (left.onFibre index element) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp]
theorem id_onIndex (X : IndexedFamily.{w, w'}) :
    (CategoryStruct.id X : Hom X X).onIndex = id := rfl

@[simp]
theorem comp_onIndex {X Y Z : IndexedFamily.{w, w'}}
    (left : X ⟶ Y) (right : Y ⟶ Z) :
    (left ≫ right).onIndex = right.onIndex ∘ left.onIndex := rfl

end IndexedFamily

/-! ## A cwf as a family-valued presheaf -/

/-- The type-and-term family of a contextual core at one context. -/
def Cwf.familyAt (C : Cwf.{u, v, w, w'}) (context : C.base.Context) :
    IndexedFamily.{w, w'} where
  Index := C.Ty context.val
  Fibre := C.Tm context.val

/-- Reindexing types and terms along substitutions is a contravariant
functor into indexed families.  This is the `Fam`-valued presheaf in the
standard definition of a category with families. -/
def Cwf.familyPresheaf (C : Cwf.{u, v, w, w'}) :
    C.base.Contextᵒᵖ ⥤ IndexedFamily.{w, w'} where
  obj context := C.familyAt context.unop
  map substitution :=
    { onIndex := fun A => C.tySub A substitution.unop
      onFibre := fun _ term => C.tmSub term substitution.unop }
  map_id context := by
    apply IndexedFamily.Hom.ext
    · funext A
      exact C.tySub_id A
    · intro A term
      exact (heq_of_eq (C.tmSub_id term)).trans (cast_heq _ term)
  map_comp left right := by
    apply IndexedFamily.Hom.ext
    · funext A
      exact C.tySub_comp A left.unop right.unop
    · intro A term
      exact (heq_of_eq (C.tmSub_comp term left.unop right.unop)).trans
        (cast_heq _ _)

/-- Positive index canary: the presheaf action on indices is exactly type
substitution. -/
@[simp]
theorem Cwf.familyPresheaf_map_index (C : Cwf.{u, v, w, w'})
    {source target : C.base.Contextᵒᵖ} (substitution : source ⟶ target)
    (A : C.Ty source.unop.val) :
    (C.familyPresheaf.map substitution).onIndex A =
      C.tySub A substitution.unop := rfl

/-- Positive fibre canary: the presheaf action on a term is exactly term
substitution over the mapped type. -/
@[simp]
theorem Cwf.familyPresheaf_map_fibre (C : Cwf.{u, v, w, w'})
    {source target : C.base.Contextᵒᵖ} (substitution : source ⟶ target)
    (A : C.Ty source.unop.val) (term : C.Tm source.unop.val A) :
    (C.familyPresheaf.map substitution).onFibre A term =
      C.tmSub term substitution.unop := rfl

/-! ## The fibre action is independent, load-bearing data -/

/-- One indexed family with a single index and a Boolean fibre. -/
def boolFibreFamily : IndexedFamily where
  Index := PUnit
  Fibre := fun _ => Bool

/-- The identity endomorphism of the Boolean fibre. -/
def boolFibreIdentity : boolFibreFamily ⟶ boolFibreFamily where
  onIndex := id
  onFibre := fun _ value => value

/-- An endomorphism with the same index action which negates the fibre. -/
def boolFibreNegation : boolFibreFamily ⟶ boolFibreFamily where
  onIndex := id
  onFibre := fun _ value => !value

/-- The two endomorphisms are indistinguishable on indices. -/
theorem boolFibre_maps_agree_on_indices :
    boolFibreIdentity.onIndex = boolFibreNegation.onIndex := rfl

/-- Negative canary: agreement on type indices does not determine the term
action of a family morphism. -/
theorem boolFibre_maps_differ_on_fibres :
    boolFibreIdentity ≠ boolFibreNegation := by
  intro mapsEqual
  have atTrue := congrArg
    (fun map => map.onFibre PUnit.unit true) mapsEqual
  change true = false at atTrue
  cases atTrue

#print axioms IndexedFamily.Hom.ext
#print axioms Cwf.familyPresheaf
#print axioms Cwf.familyPresheaf_map_index
#print axioms Cwf.familyPresheaf_map_fibre
#print axioms boolFibre_maps_agree_on_indices
#print axioms boolFibre_maps_differ_on_fibres

end Mettapedia.GSLT.Core.ContextualLadder
