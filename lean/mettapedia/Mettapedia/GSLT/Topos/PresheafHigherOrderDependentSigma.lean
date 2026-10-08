import Mettapedia.TypeTheory.HigherOrderDependentSigma
import Mettapedia.TypeTheory.CodomainFibrationComprehensionProfile
import Mettapedia.TypeTheory.PresheafCodomainFoundation
import Mettapedia.GSLT.Topos.PresheafPredicateMonoArrowEquivalence
import Mettapedia.GSLT.Topos.PresheafPredicateHigherOrder
import Mettapedia.CategoryTheory.MonomorphismGenericObject
import Mettapedia.TypeTheory.ProjectionIndexedCodomainComprehension
import Mettapedia.TypeTheory.ProjectionIndexedMonomorphismBaseChange
import Mettapedia.TypeTheory.ProjectionIndexedElementaryToposComprehension

/-!
# The presheaf higher-order dependent sum language

The actual image/comprehension adjunction is admitted to the full higher-order
dependent sum object sub-bicategory. Both kinds and reflected types have
the actual projection-indexed closed comprehension structure. Their fibres
are slices and monomorphism slices, and the selected dependent products
and Cartesian lifts earn the complete base-change and strong-sum maps.
Generic truth is based on the classifier displayed by a terminal kind.

Beck--Chevalley readouts retain their actual pullback-square hypothesis and
the complete evaluation and abstraction comparisons. These results concern
one presheaf category; no action on every elementary topos is inferred here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafHigherOrderDependentSigma

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.CategoryTheory.FibrationTwoCategory
open Mettapedia.TypeTheory

universe u
variable (C : Type u) [Category.{u} C]

local instance images : HasImages (Cᵒᵖ ⥤ Type u) :=
  ElementaryToposImages.hasImages (PresheafSliceLogicalAction.baseClassifier (C := C))

local instance strongEpis : StrongEpiCategory (Cᵒᵖ ⥤ Type u) :=
  ElementaryToposImages.strongEpiCategory
    (PresheafSliceLogicalAction.baseClassifier (C := C))

local instance imageMaps : HasImageMaps (Cᵒᵖ ⥤ Type u) := inferInstance

def adjunctionObject : FibrationAdjunctionTwoCategory.{u+1,u} :=
  FibrationAdjunctionTwoCategory.imageObject.{u+1,u}
    (PresheafSliceLogicalAction.baseClassifier (C := C))

def profile : HigherOrderDependentSigma.Profile.{u+1,u,u+1,u+1,u} (adjunctionObject C) where
  sameBase := rfl
  leftBase := rfl
  rightBase := rfl
  unitBase := HEq.rfl
  counitBase := HEq.rfl
  kindFibres := PresheafCodomainFoundation.sliceFibres C
  kinds := ProjectionIndexedCodomainComprehension.closed.{u+1,u}
    (PresheafCodomainFoundation.closedComprehension C)
  typeFibres := ProjectionIndexedMonomorphismComprehension.fibres.{u+1,u}
  types := ProjectionIndexedMonomorphismComprehension.closed.{u+1,u}
    (PresheafCodomainFoundation.closedComprehension C)
  typeDisplay := by rfl
  rightFull := inferInstanceAs (MonoArrowImageAdjunction.comprehension (Cᵒᵖ ⥤ Type u)).Full
  rightFaithful :=
    inferInstanceAs (MonoArrowImageAdjunction.comprehension (Cᵒᵖ ⥤ Type u)).Faithful
  kind := ProjectionIndexedElementaryToposComprehension.terminalKind.{u+1,u}
    (PresheafSliceLogicalAction.baseClassifier (C := C)).Ω
  kindTerminal := by
    change IsTerminal (_root_.CategoryTheory.Limits.terminal (Cᵒᵖ ⥤ Type u))
    exact terminalIsTerminal
  generic := MonomorphismGenericObject.generic.{u+1,u}
    (PresheafSliceLogicalAction.baseClassifier (C := C))
  genericBase := Iso.refl _

def language : HigherOrderDependentSigma.TwoCategory.{u+1,u,u+1,u+1,u} :=
  ⟨adjunctionObject C, ⟨profile C⟩⟩

theorem predicate_comprehension_mono
    (predicate : MonoArrowImageAdjunction.Predicate (Cᵒᵖ ⥤ Type u)) :
    Mono (((profile C).typeComprehension.display.obj predicate).hom) := by
  change Mono predicate.obj.hom
  exact predicate.property

variable {C}
variable {first second third fourth : Cᵒᵖ ⥤ Type u}
variable {top : first ⟶ second} {left : first ⟶ third}
variable {right : second ⟶ fourth} {bottom : third ⟶ fourth}

def productBaseChange (square : IsPullback top left right bottom) :
    (PresheafCodomainFoundation.closedComprehension C).dependentProduct right ⋙
      Over.pullback bottom ≅
    Over.pullback top ⋙
      (PresheafCodomainFoundation.closedComprehension C).dependentProduct left :=
  PresheafCodomainFoundation.productBaseChange square

theorem productBaseChange_evaluation (square : IsPullback top left right bottom)
    (object : Over second) :
    (Over.pullback left ⋙ Over.map top).map ((productBaseChange square).hom.app object) ≫
        (((PresheafCodomainFoundation.closedComprehension C).dependentAdjunction left).comp
          (Over.mapPullbackAdj top)).counit.app object =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
        (((PresheafCodomainFoundation.closedComprehension C).dependentProduct right ⋙
          Over.pullback bottom).obj object) ≫
        ((Over.mapPullbackAdj bottom).comp
          ((PresheafCodomainFoundation.closedComprehension C).dependentAdjunction right)).counit.app
            object :=
  PresheafCodomainFoundation.productBaseChange_evaluation square object

theorem productBaseChange_abstraction (square : IsPullback top left right bottom)
    (argument : Over third) (result : Over second)
    (body : (Over.map bottom ⋙ Over.pullback right).obj argument ⟶ result) :
    ((Over.mapPullbackAdj bottom).comp
        ((PresheafCodomainFoundation.closedComprehension C).dependentAdjunction right)).homEquiv
        argument result body ≫ (productBaseChange square).hom.app result =
      (((PresheafCodomainFoundation.closedComprehension C).dependentAdjunction left).comp
        (Over.mapPullbackAdj top)).homEquiv argument result
          ((SliceBeckChevalley.sigmaBaseChange square.flip).hom.app argument ≫ body) :=
  PresheafCodomainFoundation.productBaseChange_abstraction square argument result body

end Mettapedia.GSLT.Topos.PresheafHigherOrderDependentSigma
