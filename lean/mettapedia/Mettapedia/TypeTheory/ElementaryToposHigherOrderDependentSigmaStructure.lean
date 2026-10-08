import Mettapedia.CategoryTheory.ElementaryToposGlobalImageAction
import Mettapedia.CategoryTheory.MonomorphismGenericObject
import Mettapedia.TypeTheory.HigherOrderDependentSigmaStructure
import Mettapedia.TypeTheory.ProjectionIndexedElementaryToposComprehension

/-!
# The general dependent structure constructed by an elementary topos

The actual image-comprehension fibred reflection supplies the object of
the general higher-order dependent target. Both comprehension categories
are closed along their display projections, with their selected sums,
products and Beck--Chevalley comparisons. The classifier is the domain
of an actual terminal kind, and truth is an actual generic type object.

Monicity is a property of this logical instance; the general target does
not impose it on arbitrary dependent models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ElementaryToposHigherOrderDependentSigmaStructure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory Mettapedia.CategoryTheory.FibrationTwoCategory
open ElementaryToposImageComprehensionAction

universe u v

local instance raisedKindFibres (topos : ElementaryTopos.{u,v}) :
    HasFibers.{v,max u v} (codomain (ElementaryToposObjectUniverseLift.raised topos)).functor :=
  CodomainComprehension.sliceFibres

def profile (topos : ElementaryTopos.{u,v}) :
    HigherOrderDependentSigmaStructure.Profile.{max u v,v,max u v,max u v,v}
      (globalAmbientAction.obj topos) where
  sameBase := rfl
  leftBase := rfl
  rightBase := rfl
  unitBase := HEq.rfl
  counitBase := HEq.rfl
  rightFull := inferInstanceAs (MonoArrowImageAdjunction.comprehension
    (ElementaryToposObjectUniverseLift.raised topos)).Full
  rightFaithful := inferInstanceAs (MonoArrowImageAdjunction.comprehension
    (ElementaryToposObjectUniverseLift.raised topos)).Faithful
  kindFibres := CodomainComprehension.sliceFibres
  kinds := ProjectionIndexedElementaryToposComprehension.profile topos
  typeFibres := ProjectionIndexedMonomorphismComprehension.fibres
  types := ProjectionIndexedElementaryToposComprehension.typeProfile topos
  typeDisplay := by
    rfl
  kind := ProjectionIndexedElementaryToposComprehension.terminalKind
    (ElementaryToposObjectUniverseLift.raised topos).classifier.Ω
  kindTerminal := (ProjectionIndexedElementaryToposComprehension.genericKind topos).baseTerminal
  generic := MonomorphismGenericObject.generic
    (ElementaryToposObjectUniverseLift.raised topos).classifier
  genericBase := Iso.refl _

theorem type_display_mono (topos : ElementaryTopos.{u,v})
    (predicate : (globalAmbientAction.obj topos).target.Total) :
    Mono (((profile topos).typeComprehension.display.obj predicate).hom) :=
  predicate.property

theorem generic_classifier_readout (topos : ElementaryTopos.{u,v})
    (predicate : (globalAmbientAction.obj topos).target.Total) :
    (profile topos).generic.characteristic predicate =
      (ElementaryToposObjectUniverseLift.raised topos).classifier.χ predicate.obj.hom :=
  MonomorphismGenericObject.characteristic_readout _ predicate

end Mettapedia.TypeTheory.ElementaryToposHigherOrderDependentSigmaStructure
