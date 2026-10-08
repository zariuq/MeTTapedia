import Mettapedia.GSLT.Topos.PresheafPredicateProjection
import Mettapedia.CategoryTheory.MonoArrowImageAdjunction
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# The based equivalence between presheaf predicates and mono displays

Every predicate is sent to its actual satisfying subfunctor inclusion.
An independently supplied commuting mono square yields precisely the
entailment needed for a predicate morphism. Conversely every mono display
is isomorphic, over its unchanged codomain, to the inclusion of its range.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafPredicateMonoArrowEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.MonoArrowImageAdjunction

universe u
variable {C : Type u} [Category.{u} C]

def displayObject (object : PresheafPredicateTotal C) : Predicate (Cᵒᵖ ⥤ Type u) :=
  ⟨Arrow.mk object.fiber.ι, by
    change Mono (show Subfunctor object.base from object.fiber).ι
    infer_instance⟩

def displayMap {first second : PresheafPredicateTotal C} (arrow : first ⟶ second) :
    displayObject first ⟶ displayObject second := by
  let entails := (predicateTotalHomEquiv first second arrow).property
  let body : first.fiber.toFunctor ⟶ second.fiber.toFunctor :=
    Subfunctor.lift (first.fiber.ι ≫ arrow.base) (by
      rintro world value ⟨input, rfl⟩
      exact entails world input.property)
  exact ObjectProperty.homMk (Arrow.homMk body arrow.base (Subfunctor.lift_ι _ _))

@[simp] theorem displayMap_base {first second : PresheafPredicateTotal C}
    (arrow : first ⟶ second) : (displayMap arrow).hom.right = arrow.base := rfl

def display : PresheafPredicateTotal C ⥤ Predicate (Cᵒᵖ ⥤ Type u) where
  obj := displayObject
  map := displayMap
  map_id _ := by
    apply predicate_hom_ext
    rfl
  map_comp _ _ := by
    apply predicate_hom_ext
    rfl

theorem display_over : display (C := C) ⋙ projection (Cᵒᵖ ⥤ Type u) =
    presheafPredicateProjection C := rfl

instance display_faithful : (display (C := C)).Faithful where
  map_injective {first second} {earlier later} same := by
    apply (predicateTotalHomEquiv first second).injective
    apply Subtype.ext
    exact congrArg (fun square => square.hom.right) same

instance display_full : (display (C := C)).Full where
  map_surjective {first second} square := by
    let entails : (show Subfunctor first.base from first.fiber) ≤
        second.fiber.preimage square.hom.right := by
      intro world value member
      have equation := NatTrans.congr_app (Arrow.w square.hom) world
      have readout := congrArg (fun component => component ⟨value, member⟩) equation
      change ((square.hom.left.app world ⟨value, member⟩).val) =
        square.hom.right.app world value at readout
      change square.hom.right.app world value ∈ second.fiber.obj world
      exact readout ▸ (square.hom.left.app world ⟨value, member⟩).property
    refine ⟨(predicateTotalHomEquiv first second).symm ⟨square.hom.right, entails⟩, ?_⟩
    apply predicate_hom_ext
    rfl

def rangeObject (predicate : Predicate (Cᵒᵖ ⥤ Type u)) : PresheafPredicateTotal C :=
  ⟨predicate.obj.right, Subfunctor.range predicate.obj.hom⟩

def rangeDisplayIso (predicate : Predicate (Cᵒᵖ ⥤ Type u)) :
    display.obj (rangeObject predicate) ≅ predicate :=
  (monomorphismProperty (Cᵒᵖ ⥤ Type u)).isoMk
    (Arrow.isoMk (asIso (Subfunctor.toRange predicate.obj.hom)).symm
      (Iso.refl predicate.obj.right) (by
        change inv (Subfunctor.toRange predicate.obj.hom) ≫ predicate.obj.hom =
          (Subfunctor.range predicate.obj.hom).ι ≫ 𝟙 predicate.obj.right
        rw [Category.comp_id]
        apply (cancel_epi (Subfunctor.toRange predicate.obj.hom)).mp
        simp only [IsIso.hom_inv_id_assoc, Subfunctor.toRange_ι]))

@[simp] theorem rangeDisplayIso_base (predicate : Predicate (Cᵒᵖ ⥤ Type u)) :
    (rangeDisplayIso predicate).hom.hom.right = 𝟙 predicate.obj.right := rfl

instance display_essSurj : (display (C := C)).EssSurj where
  mem_essImage predicate := ⟨rangeObject predicate, ⟨rangeDisplayIso predicate⟩⟩

instance display_isEquivalence : (display (C := C)).IsEquivalence where

def equivalence : PresheafPredicateTotal C ≌ Predicate (Cᵒᵖ ⥤ Type u) :=
  display.asEquivalence

end Mettapedia.GSLT.Topos.PresheafPredicateMonoArrowEquivalence
