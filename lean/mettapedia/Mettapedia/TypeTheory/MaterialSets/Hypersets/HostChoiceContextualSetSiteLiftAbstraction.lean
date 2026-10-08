import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftProducts

/-!
# Abstraction and application commute with actual material universe growth

Dependent operations on the original member signature induce natural
operations on the larger signature. Their value equation retains the
actual argument and body decoder. The independently defined upper
abstraction is compared with the original abstraction on every complete
future argument, with arbitrary wider consumer values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftAbstraction

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies
open HostChoiceContextualSetSiteLiftProducts
open WiderPresheafDependentFunctions

universe u v h
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))
variable (bodyMap : NaturalHom (HostChoiceContextualHypersetFamilyClosure.comprehension parent)
  (lowerSets (D := D)))
variable {consumer : P.Elements ⥤ Type h}
variable (operation : Hom (over (lowerDomain parent) consumer) (lowerBody parent bodyMap))

/-- Transpose through the two independently constructed full-future adjunctions. -/
noncomputable def raiseOperation : Hom
    (over (upperDomain parent) (ContextualFutureSiteLift.retained P consumer)) (upperBody parent bodyMap) :=
  uncurry ((ContextualFutureSiteLift.retainedHom P (curry operation)).comp (Pi.nativeForward parent bodyMap))

theorem operation_value (point : (ContextualFutureSiteLift.base P).Elements)
    (argument : (raisedDomain parent).obj point)
    (value : consumer.obj ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    (raiseOperation parent bodyMap operation).app ⟨point, domainEquiv parent point argument⟩ value =
      bodyEquiv parent bodyMap ⟨point, argument⟩
        (ULift.up (operation.app ⟨(ContextualFutureSiteLift.elementsDown P).obj point, argument.down⟩ value)) := by
  have result := Pi.native_evaluation parent bodyMap point point ((curry operation).app
    ((ContextualFutureSiteLift.elementsDown P).obj point) value) (𝟙 point) argument
  change (raiseOperation parent bodyMap operation).app ⟨point, domainEquiv parent point argument⟩ value =
    bodyEquiv parent bodyMap ⟨point, argument⟩
      (ULift.up (operation.app ⟨(ContextualFutureSiteLift.elementsDown P).obj point, argument.down⟩
        (consumer.map (𝟙 _) value))) at result
  exact result.trans (congrArg (fun parameter => bodyEquiv parent bodyMap ⟨point, argument⟩
    (ULift.up (operation.app ⟨(ContextualFutureSiteLift.elementsDown P).obj point, argument.down⟩ parameter)))
    (consumer.map_id_apply ((ContextualFutureSiteLift.elementsDown P).obj point) value))

theorem native_abstraction_comparison :
    curry (raiseOperation parent bodyMap operation) =
      (ContextualFutureSiteLift.retainedHom P (curry operation)).comp (Pi.nativeForward parent bodyMap) :=
  curry_uncurry _

theorem abstraction_comparison :
    (ContextualFutureSiteLift.retainedHom P
      (ContextualSmallFamilyNativeAdjunction.smallCurry (lowerDomain parent) (lowerBody parent bodyMap) operation)).comp
        (Pi.forward parent bodyMap) =
      ContextualSmallFamilyNativeAdjunction.smallCurry (upperDomain parent) (upperBody parent bodyMap)
        (raiseOperation parent bodyMap operation) := by
  apply Hom.ext
  intro point value
  change consumer.obj ((ContextualFutureSiteLift.elementsDown P).obj point) at value
  apply (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (upperDomain parent)
    (upperBody parent bodyMap) point).symm.injective
  have square := congrArg (fun map => map.app point
    ((ContextualSmallFamilyNativeAdjunction.smallCurry (lowerDomain parent) (lowerBody parent bodyMap) operation).app
      ((ContextualFutureSiteLift.elementsDown P).obj point) value)) (Pi.small_native_square parent bodyMap)
  have original := congrArg (fun map => map.app ((ContextualFutureSiteLift.elementsDown P).obj point) value)
    (ContextualSmallFamilyNativeAdjunction.smallCurry_native (lowerDomain parent) (lowerBody parent bodyMap) operation)
  have actual := congrArg (fun map => map.app point value)
    (ContextualSmallFamilyNativeAdjunction.smallCurry_native (upperDomain parent) (upperBody parent bodyMap)
      (raiseOperation parent bodyMap operation))
  have originalRead := (congrArg
    ((ContextualSmallFamilyNativeAdjunction.smallToNative (lowerDomain parent) (lowerBody parent bodyMap)).app
      ((ContextualFutureSiteLift.elementsDown P).obj point)) original).symm.trans
    ((ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (lowerDomain parent) (lowerBody parent bodyMap)
      ((ContextualFutureSiteLift.elementsDown P).obj point)).symm_apply_apply
      ((curry operation).app ((ContextualFutureSiteLift.elementsDown P).obj point) value))
  have actualRead := (congrArg
    ((ContextualSmallFamilyNativeAdjunction.smallToNative (upperDomain parent) (upperBody parent bodyMap)).app point) actual).symm.trans
    ((ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (upperDomain parent) (upperBody parent bodyMap) point).symm_apply_apply
      ((curry (raiseOperation parent bodyMap operation)).app point value))
  exact square.trans ((congrArg ((Pi.nativeForward parent bodyMap).app point) originalRead).trans
    ((congrArg (fun map => map.app point value) (native_abstraction_comparison parent bodyMap operation)).symm.trans actualRead.symm))

theorem application_comparison :
    ContextualSmallFamilyNativeAdjunction.smallUncurry (upperDomain parent) (upperBody parent bodyMap)
      ((ContextualFutureSiteLift.retainedHom P
        (ContextualSmallFamilyNativeAdjunction.smallCurry (lowerDomain parent) (lowerBody parent bodyMap) operation)).comp
        (Pi.forward parent bodyMap)) = raiseOperation parent bodyMap operation := by
  exact (congrArg
    (ContextualSmallFamilyNativeAdjunction.smallUncurry (upperDomain parent) (upperBody parent bodyMap))
    (abstraction_comparison parent bodyMap operation)).trans
    (ContextualSmallFamilyNativeAdjunction.small_uncurry_curry _ _ _)

namespace Sigma

variable (eliminate : Hom (lowerBody parent bodyMap) (over (lowerDomain parent) consumer))

/-- The dependent eliminator is formed through the actual upper sum
adjunction and the constructed inverse on both material coordinates. -/
noncomputable def raiseElimination : Hom (upperBody parent bodyMap)
    (over (upperDomain parent) (ContextualFutureSiteLift.retained P consumer)) :=
  ContextualSmallFamilyNativeAdjunction.sigmaCurry (upperDomain parent) (upperBody parent bodyMap)
    ((HostChoiceContextualSetSiteLiftProducts.Sigma.backward parent bodyMap).comp
      (ContextualFutureSiteLift.retainedHom P
        (ContextualSmallFamilyNativeAdjunction.sigmaUncurry
          (lowerDomain parent) (lowerBody parent bodyMap) eliminate)))

theorem elimination_value (point : (ContextualFutureSiteLift.base P).Elements)
    (argument : (raisedDomain parent).obj point)
    (bodyValue : (raisedBody parent bodyMap).obj ⟨point, argument⟩) :
    (raiseElimination parent bodyMap eliminate).app
        ⟨point, domainEquiv parent point argument⟩
        (bodyEquiv parent bodyMap ⟨point, argument⟩ bodyValue) =
      eliminate.app ⟨(ContextualFutureSiteLift.elementsDown P).obj point, argument.down⟩ bodyValue.down := by
  exact congrArg
    ((ContextualSmallFamilyNativeAdjunction.sigmaUncurry
      (lowerDomain parent) (lowerBody parent bodyMap) eliminate).app
      ((ContextualFutureSiteLift.elementsDown P).obj point))
    ((HostChoiceContextualSetSiteLiftProducts.Sigma.equiv parent bodyMap point).symm_apply_apply
      ⟨argument.down, bodyValue.down⟩)

theorem elimination_comparison :
    ContextualSmallFamilyNativeAdjunction.sigmaUncurry (upperDomain parent) (upperBody parent bodyMap)
        (raiseElimination parent bodyMap eliminate) =
      (HostChoiceContextualSetSiteLiftProducts.Sigma.backward parent bodyMap).comp
        (ContextualFutureSiteLift.retainedHom P
          (ContextualSmallFamilyNativeAdjunction.sigmaUncurry
            (lowerDomain parent) (lowerBody parent bodyMap) eliminate)) :=
  ContextualSmallFamilyNativeAdjunction.sigma_uncurry_curry _ _ _

end Sigma

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftAbstraction
