import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mettapedia.TypeTheory.CwfTermJointObservation

/-!
# Transport of displayed families along contextual equivalence

A substitution-coherent family displayed over a type-valued functor `base`
is a type-valued functor on the category of elements of `base`.  An
isomorphism of base functors induces an equivalence of their categories of
elements and therefore an equivalence of the corresponding categories of
displayed families.

Applied to jointly separating contextual observations, this upgrades
pointwise dependent-family descent to transport of families together with
their substitution action.  The construction does not by itself transport
context comprehension, dependent products, dependent sums, identity
elimination, conversion, or operational effects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTransport

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.ContextualJointObservation

universe uContext vContext uBase uFibre

variable {Context : Type uContext} [Category.{vContext} Context]

/-- A type-valued family with a coherent action along every contextual
substitution of its base presheaf. -/
abbrev DisplayedFamily
    (base : Face.{uContext, vContext, uBase} Context) :=
  base.Elements ⥤ Type uFibre

/-- A natural observation displays its actual source elements over each
observed value. Its action transports the retained source element along the
source presheaf and uses naturality only to check the observed index. -/
def observationFibreFamily
    {source target : Face.{uContext, vContext, uBase} Context}
    (observation : source ⟶ target) :
    DisplayedFamily.{uContext, vContext, uBase, uBase} target where
  obj value :=
    { candidate : source.obj value.1 //
      observation.app value.1 candidate = value.2 }
  map {first second} substitution := TypeCat.ofHom fun receipt =>
    ⟨source.map substitution.val receipt.val, by
      calc
        observation.app second.1 (source.map substitution.val receipt.val) =
            target.map substitution.val
              (observation.app first.1 receipt.val) := by
                have natural := observation.naturality substitution.val
                exact congrArg (fun map => map receipt.val) natural
        _ = target.map substitution.val first.2 := by rw [receipt.property]
        _ = second.2 := substitution.property⟩
  map_id value := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    simp
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    simp

/-- An isomorphism of contextual bases induces an equivalence between their
categories of elements. -/
noncomputable def elementCategoryEquivalence
    {source target : Face.{uContext, vContext, uBase} Context}
    (isomorphism : source ≅ target) :
    source.Elements ≌ target.Elements :=
  Cat.equivOfIso ((Functor.elementsFunctor).mapIso isomorphism)

/-- Displayed substitution-coherent families transport in both directions
along an isomorphism of their base presheaves. -/
noncomputable def displayedFamilyEquivalence
    {source target : Face.{uContext, vContext, uBase} Context}
    (isomorphism : source ≅ target) :
    DisplayedFamily.{uContext, vContext, uBase, uFibre} source ≌
      DisplayedFamily.{uContext, vContext, uBase, uFibre} target :=
  (elementCategoryEquivalence isomorphism).congrLeft

/-- Transporting a displayed family forward and then backward recovers it
naturally. -/
noncomputable def recoverSourceFamily
    {source target : Face.{uContext, vContext, uBase} Context}
    (isomorphism : source ≅ target)
    (family : DisplayedFamily.{uContext, vContext, uBase, uFibre} source) :
    family ≅
      (displayedFamilyEquivalence isomorphism).inverse.obj
        ((displayedFamilyEquivalence isomorphism).functor.obj family) :=
  (displayedFamilyEquivalence isomorphism).unitIso.app family

/-- Transporting a displayed family backward and then forward recovers it
naturally. -/
noncomputable def recoverTargetFamily
    {source target : Face.{uContext, vContext, uBase} Context}
    (isomorphism : source ≅ target)
    (family : DisplayedFamily.{uContext, vContext, uBase, uFibre} target) :
    (displayedFamilyEquivalence isomorphism).functor.obj
        ((displayedFamilyEquivalence isomorphism).inverse.obj family) ≅
      family :=
  (displayedFamilyEquivalence isomorphism).counitIso.app family

namespace ContextualObservationFamily

variable {source : Face.{uContext, vContext, uBase} Context}
variable (observations :
  ContextualObservationFamily.{uContext, vContext, uBase} source)

/-- Jointly separating natural observations preserve the complete category
of substitution-coherent displayed families over their compatible image. -/
noncomputable def displayedFamiliesEquivalence
    (separates : observations.PointwiseJointlySeparating) :
    DisplayedFamily.{uContext, vContext, uBase, uFibre} source ≌
      DisplayedFamily.{uContext, vContext, uBase, uFibre}
        (_root_.Mettapedia.Computability.ContextualJointObservation.ContextualObservationFamily.compatibleFace
          observations) :=
  displayedFamilyEquivalence
    (_root_.Mettapedia.Computability.ContextualJointObservation.ContextualObservationFamily.compatibleIso
      observations separates)

end ContextualObservationFamily

/-! ## Open-term CwF instance -/

namespace OpenTermCanary

open Mettapedia.TypeTheory.CwfTermJointObservation

/-- The actual open value-and-route term instance transports every displayed
family, including its action under open-term substitution. -/
noncomputable def valueAndRouteDisplayedFamilies :
    DisplayedFamily.{1, 0, 0, 0} valueRouteTerms ≌
      DisplayedFamily.{1, 0, 0, 0}
        (_root_.Mettapedia.Computability.ContextualJointObservation.ContextualObservationFamily.compatibleFace
          valueAndRoute) :=
  ContextualObservationFamily.displayedFamiliesEquivalence valueAndRoute
    valueAndRoute_pointwiseSeparating

/-- A transported displayed family is recoverable on the source side; this
is an isomorphism of functors, not only a pointwise type equivalence. -/
noncomputable def sourceFamilyRoundtrip
    (family : DisplayedFamily.{1, 0, 0, 0} valueRouteTerms) :
    family ≅
      valueAndRouteDisplayedFamilies.inverse.obj
        (valueAndRouteDisplayedFamilies.functor.obj family) :=
  valueAndRouteDisplayedFamilies.unitIso.app family

/-- The open-term instance witnesses an equivalence of whole displayed-family
categories. -/
theorem valueAndRoute_displayed_boundary :
    Nonempty
      (DisplayedFamily.{1, 0, 0, 0} valueRouteTerms ≌
        DisplayedFamily.{1, 0, 0, 0}
          (_root_.Mettapedia.Computability.ContextualJointObservation.ContextualObservationFamily.compatibleFace
            valueAndRoute)) :=
  ⟨valueAndRouteDisplayedFamilies⟩

end OpenTermCanary

#print axioms elementCategoryEquivalence
#print axioms observationFibreFamily
#print axioms displayedFamilyEquivalence
#print axioms recoverSourceFamily
#print axioms recoverTargetFamily
#print axioms ContextualObservationFamily.displayedFamiliesEquivalence
#print axioms OpenTermCanary.valueAndRouteDisplayedFamilies
#print axioms OpenTermCanary.sourceFamilyRoundtrip
#print axioms OpenTermCanary.valueAndRoute_displayed_boundary

end Mettapedia.TypeTheory.DisplayedPresheafTransport
