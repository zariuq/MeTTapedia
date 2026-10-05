import Mettapedia.TypeTheory.ContextualSmallFamilyWiderInitiality

/-!
# Fusion for mixed-universe contextual W folds

An actual natural algebra homomorphism commutes with the separately
constructed folds, even when its source and target consumer universes
are independent. The comparison tests complete future branch tables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderFusion

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes ContextualSmallFamilyWiderAlgebra
open ContextualSmallFamilyWiderRecursion ContextualSmallFamilyWiderInitiality

universe u v h k
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable {firstTarget : base.Elements ⥤ Type h} {secondTarget : base.Elements ⥤ Type k}
variable (firstAlgebra : Algebra domain body (target := firstTarget))
variable (secondAlgebra : Algebra domain body (target := secondTarget))
variable (operation : WiderPresheafDependentFunctions.Hom firstTarget secondTarget)

theorem fold_fusion
    (algebraLaw : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWiderPolynomial.At domain body firstTarget point),
      operation.app point (firstAlgebra.app point node) =
        secondAlgebra.app point (ContextualSmallFamilyWiderAction.mapValue domain body operation point node)) :
    (foldMap domain body firstAlgebra).comp operation = foldMap domain body secondAlgebra := by
  apply fold_unique domain body secondAlgebra ((foldMap domain body firstAlgebra).comp operation)
  intro point node
  have first := congrArg (operation.app point) (fold_beta domain body firstAlgebra point node)
  have law := algebraLaw point (ContextualSmallFamilyWiderAction.mapValue domain body
    (foldMap domain body firstAlgebra) point node)
  have branches := congrArg (secondAlgebra.app point)
    (ContextualSmallFamilyWiderAction.mapValue_composition domain body
      (foldMap domain body firstAlgebra) operation point node)
  exact first.trans (law.trans branches.symm)

theorem fold_fusion_value
    (algebraLaw : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWiderPolynomial.At domain body firstTarget point),
      operation.app point (firstAlgebra.app point node) =
        secondAlgebra.app point (ContextualSmallFamilyWiderAction.mapValue domain body operation point node))
    (point : base.Elements) (tree : WAt domain body point) :
    operation.app point (foldValue domain body firstAlgebra point tree) =
      foldValue domain body secondAlgebra point tree :=
  congrArg (fun hom => hom.app point tree)
    (fold_fusion domain body firstAlgebra secondAlgebra operation algebraLaw)

end Mettapedia.TypeTheory.ContextualSmallFamilyWiderFusion
