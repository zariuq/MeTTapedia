import Mettapedia.TypeTheory.ElementaryToposNativeLanguageAction
import Mettapedia.TypeTheory.SliceDependentProductComparisonContract
import Mettapedia.CategoryTheory.SliceFunctorSumComparison
import Mettapedia.CategoryTheory.LogicalClassifierComparison

/-!
# Logical comparisons on the actual global native action

The same geometric base map acts on actual dependent displays, slice
substitution, sums, products and characteristic maps. Sum and substitution
comparisons are isomorphisms. The product and classifier comparisons have
their earned evaluation and classification laws; their invertibility is
not part of the geometric-map contract.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ElementaryToposNativeLogicalComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory

universe u v

abbrev Base (topos : ElementaryTopos.{u,v}) :=
  ElementaryToposObjectUniverseLift.raised topos

def model (topos : ElementaryTopos.{u,v}) :
    CodomainClosedComprehension (Base topos) :=
  ElementaryToposCodomainClosedProfile.closedComprehension.{max u v,v} (Base topos)

variable {source target : ElementaryTopos.{u,v}} (route : source ⟶ target)

abbrev baseMap := (ElementaryToposObjectUniverseLift.map route).functor

def substitutionComparison {X Y : Base source} (f : X ⟶ Y) :
    Over.pullback f ⋙ Over.post (baseMap route) ≅
      Over.post (baseMap route) ⋙ Over.pullback ((baseMap route).map f) :=
  SliceFunctorPullbackComparison.comparison (baseMap route) f

def sumComparison {X Y : Base source} (f : X ⟶ Y) :
    Over.map f ⋙ Over.post (baseMap route) ≅
      Over.post (baseMap route) ⋙ Over.map ((baseMap route).map f) :=
  SliceFunctorSumComparison.comparison (baseMap route) f

def productComparison {X Y : Base source} (f : X ⟶ Y) :
    (model source).dependentProduct f ⋙ Over.post (baseMap route) ⟶
      Over.post (baseMap route) ⋙
        (model target).dependentProduct ((baseMap route).map f) :=
  SliceDependentProductComparison.comparison.{max u v,max u v,v,v}
    (model source) (model target) (baseMap route) f

def classifierComparison : (baseMap route).obj (Base source).classifier.Ω ⟶
    (Base target).classifier.Ω :=
  LogicalClassifierComparison.comparison
    (Base source).classifier (Base target).classifier (baseMap route)

attribute [local irreducible] model

/-- The type endpoint is the actual complete arrow-category action,
including both components of each mapped dependent square. -/
theorem native_type_endpoint :
    (ElementaryToposNativeLanguageAction.action.map route).hom.hom.right.square.left.toFunctor =
      (baseMap route).mapArrow := rfl

theorem sum_retains_complete_domain {X Y : Base source} (f : X ⟶ Y)
    (display : Over X) :
    ((sumComparison route f).hom.app display).left =
      𝟙 ((baseMap route).obj display.left) :=
  SliceFunctorSumComparison.complete_domain (baseMap route) f display

theorem product_evaluation {X Y : Base source} (f : X ⟶ Y) (result : Over X) :
    (Over.pullback ((baseMap route).map f)).map
        ((SliceDependentProductComparison.comparison (model source) (model target)
          (baseMap route) f).app result) ≫
      (model target).evaluation ((baseMap route).map f)
        ((Over.post (baseMap route)).obj result) =
    (SliceFunctorPullbackComparison.comparison (baseMap route) f).inv.app
        (((model source).dependentProduct f).obj result) ≫
      (Over.post (baseMap route)).map ((model source).evaluation f result) :=
  SliceDependentProductComparison.evaluation.{max u v,max u v,v,v}
    (model source) (model target) (baseMap route) f result

/-- Evaluation, abstraction and the full unit square are earned for
this actual comparison. No preservation condition is supplied by the caller. -/
theorem product_compatibility {X Y : Base source} (f : X ⟶ Y) :
    SliceDependentProductComparison.Compatible
      (model source) (model target) (baseMap route) f (productComparison route f) :=
  SliceDependentProductComparison.compatible.{max u v,max u v,v,v}
    (model source) (model target) (baseMap route) f

theorem product_unique {X Y : Base source} (f : X ⟶ Y)
    (candidate : (model source).dependentProduct f ⋙ Over.post (baseMap route) ⟶
      Over.post (baseMap route) ⋙ (model target).dependentProduct ((baseMap route).map f))
    (readout : ∀ result,
      (Over.pullback ((baseMap route).map f)).map (candidate.app result) ≫
          (model target).evaluation ((baseMap route).map f)
            ((Over.post (baseMap route)).obj result) =
        (substitutionComparison route f).inv.app
            (((model source).dependentProduct f).obj result) ≫
          (Over.post (baseMap route)).map ((model source).evaluation f result)) :
    candidate = productComparison route f :=
  SliceDependentProductComparison.unique.{max u v,max u v,v,v}
    (model source) (model target) (baseMap route) f
    candidate readout

theorem classifier_truth_square :
    IsPullback ((baseMap route).map (Base source).classifier.truth)
      ((Base target).classifier.χ₀ ((baseMap route).obj (Base source).classifier.Ω₀))
      (classifierComparison route) (Base target).classifier.truth :=
  LogicalClassifierComparison.truth_square
    (Base source).classifier (Base target).classifier (baseMap route)

theorem classifier_characteristic {selected object : Base source}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    (baseMap route).map ((Base source).classifier.χ inclusion) ≫
        classifierComparison route =
      (Base target).classifier.χ ((baseMap route).map inclusion) :=
  LogicalClassifierComparison.characteristic_preservation
    (Base source).classifier (Base target).classifier (baseMap route) inclusion

end Mettapedia.TypeTheory.ElementaryToposNativeLogicalComparisons
