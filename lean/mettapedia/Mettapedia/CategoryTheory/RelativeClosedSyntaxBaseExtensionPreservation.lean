import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtension
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapClosed
import Mettapedia.CategoryTheory.RelativeClosedBaseClosed
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Preserved base structures in the actual augmented presentation

The comparison presentation maps into the arbitrary authored presentation
with its base diagrams adjoined. Its independently proved finite-limit and
closed preservation transports the local base comparisons to that actual
category. The whole base functor equality supplies the final comparison;
preservation of the augmented base is a derived theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a k

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable (signature : Signature (C := C) (symbols := symbols))

instance extended_base_preservesFiniteLimits :
    PreservesFiniteLimits (GeneratedCategory.baseFunctor (extend signature)) := by
  rw [← comparison_base_recovery signature]
  exact comp_preservesFiniteLimits _ _

section CommonUniverse

private theorem closed_of_equal {X Y : Type k} [Category.{k} X] [Category.{k} Y]
    [CartesianMonoidalCategory X] [CartesianMonoidalCategory Y]
    [MonoidalClosed X] [MonoidalClosed Y] (F G : X ⥤ Y)
    [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    (same : F = G) [MonoidalClosedFunctor F] : MonoidalClosedFunctor G := by
  subst G
  infer_instance

variable {E : Type k} [Category.{k} E] {names : Symbols.{k}}
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable (presentation : Signature (C := E) (symbols := names))

instance extended_base_closed :
    MonoidalClosedFunctor (GeneratedCategory.baseFunctor (extend presentation)) := by
  have : PreservesFiniteLimits
      (GeneratedCategory.baseFunctor (BaseComparisons.signature (C := E)) ⋙
        (comparisonMap presentation).functor) := comp_preservesFiniteLimits _ _
  have : MonoidalClosedFunctor
      (GeneratedCategory.baseFunctor (BaseComparisons.signature (C := E)) ⋙
        (comparisonMap presentation).functor) :=
    CartesianClosedFunctorCoherence.closed_composition _ _
  exact closed_of_equal
    (GeneratedCategory.baseFunctor (BaseComparisons.signature (C := E)) ⋙
      (comparisonMap presentation).functor)
    (GeneratedCategory.baseFunctor (extend presentation))
    (comparison_base_recovery presentation)

end CommonUniverse

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension
