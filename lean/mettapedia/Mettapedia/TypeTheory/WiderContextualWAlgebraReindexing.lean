import Mettapedia.TypeTheory.WiderContextualWPolynomialReindexing

/-!
# Whole-signature transport of wider W algebras and folds
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderContextualWAlgebraReindexing

open CategoryTheory MaterialSets.Hypersets

universe u h
variable {D : Type u} [Category.{u} D]

abbrev Algebra (signature : WiderContextualWPolynomialReindexing.Signature D) :=
  WiderContextualWAlgebras.Algebra signature.1.1 signature.1.2 signature.2

theorem algebra_ext_heq {first second : WiderContextualWPolynomialReindexing.Signature D} (same : first = second)
    (left : Algebra first) (right : Algebra second)
    (values : ∀ (point : D) (firstLabel : first.1.1.obj point) (secondLabel : second.1.1.obj point),
      HEq firstLabel secondLabel →
      ∀ (firstBranches : WiderContextualWAlgebras.Branches first.1.1 first.1.2 first.2 firstLabel)
        (secondBranches : WiderContextualWAlgebras.Branches second.1.1 second.1.2 second.2 secondLabel),
        HEq firstBranches secondBranches →
        HEq (left.make point firstLabel firstBranches) (right.make point secondLabel secondBranches)) :
    HEq left right := by
  cases same
  apply heq_of_eq
  rcases left with ⟨make, natural⟩
  rcases right with ⟨otherMake, otherNatural⟩
  have functions : make = otherMake := funext fun point => funext fun label => funext fun branches =>
    eq_of_heq (values point label label HEq.rfl branches branches HEq.rfl)
  cases functions
  rfl

theorem node_heq {first second : WiderContextualWPolynomialReindexing.Signature D} (same : first = second)
    (point : D) (firstLabel : first.1.1.obj point) (secondLabel : second.1.1.obj point) (labels : HEq firstLabel secondLabel)
    (firstBranches : WiderContextualWAlgebras.Branches first.1.1 first.1.2 first.2 firstLabel)
    (secondBranches : WiderContextualWAlgebras.Branches second.1.1 second.1.2 second.2 secondLabel)
    (branches : HEq firstBranches secondBranches) :
    HEq (⟨firstLabel, firstBranches⟩ : WiderContextualWPolynomialReindexing.At first point)
      (⟨secondLabel, secondBranches⟩ : WiderContextualWPolynomialReindexing.At second point) := by
  cases same
  cases eq_of_heq labels
  cases eq_of_heq branches
  rfl

theorem fold_heq {first second : WiderContextualWPolynomialReindexing.Signature D} (same : first = second)
    {firstPoint secondPoint : D} (points : firstPoint = secondPoint)
    (leftAlgebra : Algebra first) (rightAlgebra : Algebra second) (algebras : HEq leftAlgebra rightAlgebra)
    (left : ContextualWReindexing.Tree first.1 firstPoint) (right : ContextualWReindexing.Tree second.1 secondPoint)
    (trees : HEq left.val right.val) :
    HEq (WiderContextualWAlgebras.fold first.1.1 first.1.2 leftAlgebra left)
      (WiderContextualWAlgebras.fold second.1.1 second.1.2 rightAlgebra right) := by
  cases same
  cases points
  cases eq_of_heq algebras
  have treeEq : left = right := Subtype.ext (eq_of_heq trees)
  cases treeEq
  rfl


end Mettapedia.TypeTheory.WiderContextualWAlgebraReindexing
