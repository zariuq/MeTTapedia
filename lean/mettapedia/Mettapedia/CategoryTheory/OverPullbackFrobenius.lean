import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Frobenius reciprocity for actual slice pullback

The canonical Frobenius morphism for composition and pullback is the
pullback-pasting isomorphism. Its two projection readouts are retained.
Consequently actual slice pullback preserves exponentials whenever the
source and target slices have cartesian closed structure.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.OverPullbackFrobenius

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {P Q : C} (f : Q ⟶ P)

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable def comparison (A : Over P) :=
  frobeniusMorphism (Over.pullback f) (Over.mapPullbackAdj f) A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem comparison_left (A : Over P) (B : Over Q) :
    ((comparison f A).natTrans.app B).left =
      (pullbackLeftPullbackSndIso A.hom f B.hom).hom := by
  apply pullback.hom_ext
  · simp [comparison, frobeniusMorphism,
      CartesianMonoidalCategory.prodComparisonNatTrans,
      CartesianMonoidalCategory.prodComparison]
  · simp [comparison, frobeniusMorphism,
      CartesianMonoidalCategory.prodComparisonNatTrans,
      CartesianMonoidalCategory.prodComparison]

noncomputable instance comparison_invertible (A : Over P) :
    IsIso (comparison f A).natTrans := by
  have (B : Over Q) : IsIso ((comparison f A).natTrans.app B) := by
    have : IsIso ((Over.forget P).map ((comparison f A).natTrans.app B)) := by
      change IsIso (((comparison f A).natTrans.app B).left)
      rw [comparison_left]
      infer_instance
    exact isIso_of_reflects_iso _ (Over.forget P)
  exact NatIso.isIso_of_isIso_app _

noncomputable instance pullback_closed
    [MonoidalClosed (Over P)] [MonoidalClosed (Over Q)] :
    MonoidalClosedFunctor (Over.pullback f) where
  comparison_iso A := by
    have : IsIso (frobeniusMorphism (Over.pullback f) (Over.mapPullbackAdj f) A).natTrans :=
      comparison_invertible f A
    exact expComparison_iso_of_frobeniusMorphism_iso
      (Over.pullback f) (Over.mapPullbackAdj f) A

end Mettapedia.CategoryTheory.OverPullbackFrobenius
