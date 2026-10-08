import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftW
import Mettapedia.TypeTheory.ContextualFutureSiteWAlgebra
import Mettapedia.TypeTheory.WiderContextualWSignatureAlgebra

/-!
# Actual material W algebra comparison through the larger model

The site comparison and the independently formed material-member
signature comparison both act on complete compatible polynomial branches.
Their composite gives an actual upper algebra whose independently defined
fold agrees with the original fold for every natural tree. The consumer
universe is independent of the original and successor tree bounds.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftWAlgebra

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies
open PowerClassPresheafBaseChange

universe u v h
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))
variable (bodyMap : NaturalHom (HostChoiceContextualHypersetFamilyClosure.comprehension parent)
  (lowerSets (D := D)))
variable (point : (ContextualFutureSiteLift.base P).Elements)
variable (target : Future.Objects point.1.down ⥤ Type h)

noncomputable abbrev lowerSignature := ContextualFutureSiteWCones.oldSignature
  (lowerDomain parent) (lowerBody parent bodyMap) point

noncomputable abbrev upperSignature := ContextualSmallFamilyWTypes.signature
  (upperDomain parent) (upperBody parent bodyMap) point

noncomputable def algebra
    (original : WiderContextualWAlgebras.Algebra (lowerSignature parent bodyMap point).1
      (lowerSignature parent bodyMap point).2 target) :
    WiderContextualWAlgebras.Algebra (upperSignature parent bodyMap point).1
      (upperSignature parent bodyMap point).2 (ContextualFutureSiteWAlgebra.upperTarget point target) :=
  WiderContextualWSignatureAlgebra.pullAlgebra
    (ContextualWSignatureEquivalence.inverseSignature
      (ContextualSmallFamilyWSignature.signature (signature parent bodyMap) point))
    (ContextualFutureSiteWAlgebra.upperTarget point target)
    (ContextualFutureSiteWAlgebra.algebra (lowerDomain parent) (lowerBody parent bodyMap) point target original)

theorem fold_comparison
    (original : WiderContextualWAlgebras.Algebra (lowerSignature parent bodyMap point).1
      (lowerSignature parent bodyMap point).2 target)
    (tree : (HostChoiceContextualSetSiteLiftW.lower parent bodyMap).obj
      ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    WiderContextualWAlgebras.fold (upperSignature parent bodyMap point).1
        (upperSignature parent bodyMap point).2 (algebra parent bodyMap point target original)
        ((HostChoiceContextualSetSiteLiftW.forward parent bodyMap).app point tree) =
      WiderContextualWAlgebras.fold (lowerSignature parent bodyMap point).1
        (lowerSignature parent bodyMap point).2 original tree :=
  (WiderContextualWSignatureAlgebra.fold_inverse
    (ContextualSmallFamilyWSignature.signature (signature parent bodyMap) point)
    (ContextualFutureSiteWAlgebra.upperTarget point target)
    (ContextualFutureSiteWAlgebra.algebra (lowerDomain parent) (lowerBody parent bodyMap) point target original)
    ((ContextualFutureSiteWCones.equiv (lowerDomain parent) (lowerBody parent bodyMap) point).symm tree)).trans
      (ContextualFutureSiteWAlgebra.fold_comparison (lowerDomain parent) (lowerBody parent bodyMap) point target original tree)

theorem fold_comparison_upper
    (original : WiderContextualWAlgebras.Algebra (lowerSignature parent bodyMap point).1
      (lowerSignature parent bodyMap point).2 target)
    (tree : (HostChoiceContextualSetSiteLiftW.upper parent bodyMap).obj point) :
    WiderContextualWAlgebras.fold (upperSignature parent bodyMap point).1
        (upperSignature parent bodyMap point).2 (algebra parent bodyMap point target original) tree =
      WiderContextualWAlgebras.fold (lowerSignature parent bodyMap point).1
        (lowerSignature parent bodyMap point).2 original
        ((HostChoiceContextualSetSiteLiftW.backward parent bodyMap).app point tree) := by
  have compared := fold_comparison parent bodyMap point target original
    ((HostChoiceContextualSetSiteLiftW.backward parent bodyMap).app point tree)
  have recovered : (HostChoiceContextualSetSiteLiftW.forward parent bodyMap).app point
      ((HostChoiceContextualSetSiteLiftW.backward parent bodyMap).app point tree) = tree :=
    (HostChoiceContextualSetSiteLiftW.equiv parent bodyMap point).apply_symm_apply tree
  exact (congrArg (WiderContextualWAlgebras.fold (upperSignature parent bodyMap point).1
    (upperSignature parent bodyMap point).2 (algebra parent bodyMap point target original)) recovered).symm.trans compared

namespace Whole

variable (consumer : P.Elements ⥤ Type h)
variable (original : ContextualSmallFamilyWiderAlgebra.Algebra
  (lowerDomain parent) (lowerBody parent bodyMap) (target := consumer))

/-- The value is obtained by evaluating the independently formed upper W
tree using the constructed upper future algebra. -/
noncomputable def value (atPoint : (ContextualFutureSiteLift.base P).Elements)
    (tree : (HostChoiceContextualSetSiteLiftW.upper parent bodyMap).obj atPoint) :
    (ContextualFutureSiteLift.retained P consumer).obj atPoint :=
  ContextualSmallFamilyWiderAlgebra.rootValueEquiv consumer
    ((ContextualFutureSiteLift.elementsDown P).obj atPoint)
    (WiderContextualWAlgebras.fold (upperSignature parent bodyMap atPoint).1
      (upperSignature parent bodyMap atPoint).2
      (algebra parent bodyMap atPoint
        (ContextualSmallFamilyWiderPolynomial.futureTarget consumer
          ((ContextualFutureSiteLift.elementsDown P).obj atPoint))
        (ContextualSmallFamilyWiderAlgebra.localAlgebra
          (lowerDomain parent) (lowerBody parent bodyMap) original
          ((ContextualFutureSiteLift.elementsDown P).obj atPoint))) tree)

theorem value_comparison (atPoint : (ContextualFutureSiteLift.base P).Elements)
    (tree : (HostChoiceContextualSetSiteLiftW.upper parent bodyMap).obj atPoint) :
    value parent bodyMap consumer original atPoint tree =
      ContextualSmallFamilyWiderAlgebra.foldValue (lowerDomain parent) (lowerBody parent bodyMap)
        original ((ContextualFutureSiteLift.elementsDown P).obj atPoint)
        ((HostChoiceContextualSetSiteLiftW.backward parent bodyMap).app atPoint tree) :=
  congrArg (ContextualSmallFamilyWiderAlgebra.rootValueEquiv consumer
    ((ContextualFutureSiteLift.elementsDown P).obj atPoint))
    (fold_comparison_upper parent bodyMap atPoint
      (ContextualSmallFamilyWiderPolynomial.futureTarget consumer
        ((ContextualFutureSiteLift.elementsDown P).obj atPoint))
      (ContextualSmallFamilyWiderAlgebra.localAlgebra
        (lowerDomain parent) (lowerBody parent bodyMap) original
        ((ContextualFutureSiteLift.elementsDown P).obj atPoint)) tree)

theorem value_natural {first second : (ContextualFutureSiteLift.base P).Elements}
    (step : first ⟶ second)
    (tree : (HostChoiceContextualSetSiteLiftW.upper parent bodyMap).obj first) :
    (ContextualFutureSiteLift.retained P consumer).map step
        (value parent bodyMap consumer original first tree) =
      value parent bodyMap consumer original second
        ((HostChoiceContextualSetSiteLiftW.upper parent bodyMap).map step tree) := by
  rw [value_comparison, value_comparison]
  have square := (ContextualSmallFamilyWiderRecursion.foldMap
    (lowerDomain parent) (lowerBody parent bodyMap) original).naturality
    ((ContextualFutureSiteLift.elementsDown P).map step)
    ((HostChoiceContextualSetSiteLiftW.backward parent bodyMap).app first tree)
  exact square.trans (congrArg
    (ContextualSmallFamilyWiderAlgebra.foldValue (lowerDomain parent) (lowerBody parent bodyMap)
      original ((ContextualFutureSiteLift.elementsDown P).obj second))
    ((HostChoiceContextualSetSiteLiftW.backward parent bodyMap).naturality step tree))

/-- These independently evaluated upper cone folds form a whole contextual
consumer; its naturality follows from the proved cone and tree squares. -/
noncomputable def fold : WiderPresheafDependentFunctions.Hom
    (HostChoiceContextualSetSiteLiftW.upper parent bodyMap)
    (ContextualFutureSiteLift.retained P consumer) where
  app := value parent bodyMap consumer original
  naturality step tree := value_natural parent bodyMap consumer original step tree

noncomputable def lowerFold : WiderPresheafDependentFunctions.Hom
    (ContextualFutureSiteLift.retained P (HostChoiceContextualSetSiteLiftW.lower parent bodyMap))
    (ContextualFutureSiteLift.retained P consumer) where
  app atPoint := (ContextualSmallFamilyWiderRecursion.foldMap
    (lowerDomain parent) (lowerBody parent bodyMap) original).app
    ((ContextualFutureSiteLift.elementsDown P).obj atPoint)
  naturality step := (ContextualSmallFamilyWiderRecursion.foldMap
    (lowerDomain parent) (lowerBody parent bodyMap) original).naturality
    ((ContextualFutureSiteLift.elementsDown P).map step)

theorem fold_comparison : fold parent bodyMap consumer original =
    (HostChoiceContextualSetSiteLiftW.backward parent bodyMap).comp
      (lowerFold parent bodyMap consumer original) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro atPoint tree
  exact value_comparison parent bodyMap consumer original atPoint tree

theorem fold_beta_compared (atPoint : (ContextualFutureSiteLift.base P).Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At (lowerDomain parent) (lowerBody parent bodyMap)
      (HostChoiceContextualSetSiteLiftW.lower parent bodyMap)
      ((ContextualFutureSiteLift.elementsDown P).obj atPoint)) :
    (fold parent bodyMap consumer original).app atPoint
        ((HostChoiceContextualSetSiteLiftW.forward parent bodyMap).app atPoint
          (ContextualSmallFamilyWiderAlgebra.constructorValue
            (lowerDomain parent) (lowerBody parent bodyMap)
            ((ContextualFutureSiteLift.elementsDown P).obj atPoint) node)) =
      original.app ((ContextualFutureSiteLift.elementsDown P).obj atPoint)
        (ContextualSmallFamilyWiderAction.mapValue (lowerDomain parent) (lowerBody parent bodyMap)
          (ContextualSmallFamilyWiderRecursion.foldMap
            (lowerDomain parent) (lowerBody parent bodyMap) original)
          ((ContextualFutureSiteLift.elementsDown P).obj atPoint) node) := by
  have compared := value_comparison parent bodyMap consumer original atPoint
    ((HostChoiceContextualSetSiteLiftW.forward parent bodyMap).app atPoint
      (ContextualSmallFamilyWiderAlgebra.constructorValue
        (lowerDomain parent) (lowerBody parent bodyMap)
        ((ContextualFutureSiteLift.elementsDown P).obj atPoint) node))
  exact compared.trans ((congrArg
    (ContextualSmallFamilyWiderAlgebra.foldValue (lowerDomain parent) (lowerBody parent bodyMap)
      original ((ContextualFutureSiteLift.elementsDown P).obj atPoint))
    ((HostChoiceContextualSetSiteLiftW.equiv parent bodyMap atPoint).symm_apply_apply _)).trans
      (ContextualSmallFamilyWiderInitiality.fold_beta (lowerDomain parent) (lowerBody parent bodyMap)
        original ((ContextualFutureSiteLift.elementsDown P).obj atPoint) node))

theorem sections_comparison (term : (HostChoiceContextualSetSiteLiftW.lower parent bodyMap).sections) :
    (fold parent bodyMap consumer original).mapSection
        (HostChoiceContextualSetSiteLiftW.sections parent bodyMap term) =
      (ContextualFutureSiteLift.retainedSections P consumer)
        ((ContextualSmallFamilyWiderRecursion.foldMap
          (lowerDomain parent) (lowerBody parent bodyMap) original).mapSection term) := by
  apply Subtype.ext
  funext atPoint
  exact (value_comparison parent bodyMap consumer original atPoint _).trans
    (congrArg (ContextualSmallFamilyWiderAlgebra.foldValue
      (lowerDomain parent) (lowerBody parent bodyMap) original
      ((ContextualFutureSiteLift.elementsDown P).obj atPoint))
      ((HostChoiceContextualSetSiteLiftW.equiv parent bodyMap atPoint).symm_apply_apply
        (term.val ((ContextualFutureSiteLift.elementsDown P).obj atPoint))))

end Whole

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftWAlgebra
