import Mettapedia.TypeTheory.PresheafPiLimitComparison

/-!
# Evaluation under presheaf dependent-product base change

The family-level right-Kan comparison must preserve evaluation at an
actual dependent argument. The identity question in the pointwise
comma index retains that argument's evidence under natural context
substitution. This module proves the resulting counit comparison;
it does not assert an authored Prime Π computation rule.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafPiEvaluationBaseChange

open CategoryTheory Limits
open Mettapedia.TypeTheory.CategoryOfElementsBaseChange
open Mettapedia.TypeTheory.PresheafPiIndexComparison
open Mettapedia.TypeTheory.PresheafPiLimitComparison

universe u v w wEvidence

variable {Context : Type u} [Category.{v} Context]
variable {source target : Context ⥤ Type w}

/-- Evaluating after the inverse pointwise Π comparison is precisely
evaluation at the same retained dependent argument in the observed
context. -/
theorem pointwisePiLimitIso_inv_evaluation
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence))
    (receipt : (substitution.mapElements ⋙ domain).Elements) :
    (pointwisePiLimitIso substitution domain codomain receipt.1).inv ≫
        ((CategoryOfElements.π
          (substitution.mapElements ⋙ domain)).pointwiseRightKanExtensionCounit
            (mapPrecompElements substitution.mapElements domain ⋙ codomain)).app receipt =
      ((CategoryOfElements.π domain).pointwiseRightKanExtensionCounit
        codomain).app
          ((mapPrecompElements substitution.mapElements domain).obj receipt) := by
  have projection := pointwisePiLimitIso_inv_projection
    substitution domain codomain receipt.1
    (StructuredArrow.mk
      (T := CategoryOfElements.π (substitution.mapElements ⋙ domain))
      (Y := receipt) (𝟙 receipt.1))
  exact projection

/-- The forward family comparison preserves evaluation at each actual
argument receipt. The statement uses the assembled natural family iso,
not just an independently chosen pointwise witness. -/
theorem presheafPiBaseChangeIso_evaluation_app
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence))
    (receipt : (substitution.mapElements ⋙ domain).Elements) :
    (presheafPiBaseChangeIso substitution domain codomain).hom.app receipt.1 ≫
      ((CategoryOfElements.π domain).pointwiseRightKanExtensionCounit
        codomain).app
          ((mapPrecompElements substitution.mapElements domain).obj receipt) =
      ((CategoryOfElements.π
        (substitution.mapElements ⋙ domain)).pointwiseRightKanExtensionCounit
          (mapPrecompElements substitution.mapElements domain ⋙ codomain)).app
            receipt := by
  let comparison := pointwisePiLimitIso substitution domain codomain receipt.1
  have evalInv := pointwisePiLimitIso_inv_evaluation
    substitution domain codomain receipt
  change comparison.hom ≫
      ((CategoryOfElements.π domain).pointwiseRightKanExtensionCounit
        codomain).app
          ((mapPrecompElements substitution.mapElements domain).obj receipt) =
      ((CategoryOfElements.π
        (substitution.mapElements ⋙ domain)).pointwiseRightKanExtensionCounit
          (mapPrecompElements substitution.mapElements domain ⋙ codomain)).app
            receipt
  calc
    _ = comparison.hom ≫
        (comparison.inv ≫
          ((CategoryOfElements.π
            (substitution.mapElements ⋙ domain)).pointwiseRightKanExtensionCounit
              (mapPrecompElements substitution.mapElements domain ⋙ codomain)).app
                receipt) := by rw [evalInv]
    _ = (comparison.hom ≫ comparison.inv) ≫
          ((CategoryOfElements.π
            (substitution.mapElements ⋙ domain)).pointwiseRightKanExtensionCounit
              (mapPrecompElements substitution.mapElements domain ⋙ codomain)).app
                receipt := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [comparison.hom_inv_id]
      exact Category.id_comp _

/-- Beck–Chevalley for the pointwise dependent product commutes with
its evaluation counit as a natural transformation over the full
evidence-bearing comprehension context. -/
theorem presheafPiBaseChangeIso_evaluation
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence)) :
    Functor.whiskerLeft
        (CategoryOfElements.π (substitution.mapElements ⋙ domain))
        (presheafPiBaseChangeIso substitution domain codomain).hom ≫
      Functor.whiskerLeft
        (mapPrecompElements substitution.mapElements domain)
        ((CategoryOfElements.π domain).pointwiseRightKanExtensionCounit
          codomain) =
      (CategoryOfElements.π
        (substitution.mapElements ⋙ domain)).pointwiseRightKanExtensionCounit
          (mapPrecompElements substitution.mapElements domain ⋙ codomain) := by
  apply NatTrans.ext
  funext receipt
  exact presheafPiBaseChangeIso_evaluation_app
    substitution domain codomain receipt

/-- The same evaluation square holds for the chosen right-Kan product
used by the existing indexed-family candidate, not only Mathlib's
pointwise presentation of it. -/
theorem chosenPresheafPiBaseChangeIso_evaluation
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence)) :
    Functor.whiskerLeft
        (CategoryOfElements.π (substitution.mapElements ⋙ domain))
        (chosenPresheafPiBaseChangeIso substitution domain codomain).hom ≫
      Functor.whiskerLeft
        (mapPrecompElements substitution.mapElements domain)
        ((CategoryOfElements.π domain).rightKanExtensionCounit
          codomain) =
      (CategoryOfElements.π
        (substitution.mapElements ⋙ domain)).rightKanExtensionCounit
          (mapPrecompElements substitution.mapElements domain ⋙ codomain) := by
  apply NatTrans.ext
  funext receipt
  let sourceProjection :=
    CategoryOfElements.π (substitution.mapElements ⋙ domain)
  let targetProjection := CategoryOfElements.π domain
  let lifted := mapPrecompElements substitution.mapElements domain
  let sourceBody := lifted ⋙ codomain
  let sourceComparison :=
    chosenRightKanPointwiseIso sourceProjection sourceBody
  let targetComparison :=
    chosenRightKanPointwiseIso targetProjection codomain
  let pointComparison := presheafPiBaseChangeIso substitution domain codomain
  have sourceEval := NatTrans.congr_app
    (chosenRightKanPointwiseIso_counit sourceProjection sourceBody) receipt
  have targetEval := NatTrans.congr_app
    (chosenRightKanPointwiseIso_inv_counit targetProjection codomain)
      (lifted.obj receipt)
  have pointEval := presheafPiBaseChangeIso_evaluation_app
    substitution domain codomain receipt
  change
    sourceComparison.hom.app receipt.1 ≫
      (sourceProjection.pointwiseRightKanExtensionCounit sourceBody).app
        receipt =
    (sourceProjection.rightKanExtensionCounit sourceBody).app receipt
    at sourceEval
  change
    targetComparison.inv.app (substitution.mapElements.obj receipt.1) ≫
      (targetProjection.rightKanExtensionCounit codomain).app
        (lifted.obj receipt) =
    (targetProjection.pointwiseRightKanExtensionCounit codomain).app
      (lifted.obj receipt)
    at targetEval
  change
    (sourceComparison.hom.app receipt.1 ≫
      pointComparison.hom.app receipt.1 ≫
      targetComparison.inv.app (substitution.mapElements.obj receipt.1)) ≫
      (targetProjection.rightKanExtensionCounit codomain).app
        (lifted.obj receipt) =
    (sourceProjection.rightKanExtensionCounit sourceBody).app receipt
  calc
    _ = (sourceComparison.hom.app receipt.1 ≫
        pointComparison.hom.app receipt.1) ≫
        (targetComparison.inv.app (substitution.mapElements.obj receipt.1) ≫
          (targetProjection.rightKanExtensionCounit codomain).app
            (lifted.obj receipt)) := Category.assoc _ _ _
    _ = sourceComparison.hom.app receipt.1 ≫
        (pointComparison.hom.app receipt.1 ≫
          (targetComparison.inv.app (substitution.mapElements.obj receipt.1) ≫
            (targetProjection.rightKanExtensionCounit codomain).app
              (lifted.obj receipt))) := Category.assoc _ _ _
    _ = sourceComparison.hom.app receipt.1 ≫
        (pointComparison.hom.app receipt.1 ≫
          (targetProjection.pointwiseRightKanExtensionCounit codomain).app
            (lifted.obj receipt)) := by rw [targetEval]
    _ = sourceComparison.hom.app receipt.1 ≫
        (sourceProjection.pointwiseRightKanExtensionCounit sourceBody).app
          receipt := by rw [pointEval]
    _ = _ := by exact sourceEval

#print axioms pointwisePiLimitIso_inv_evaluation
#print axioms presheafPiBaseChangeIso_evaluation_app
#print axioms presheafPiBaseChangeIso_evaluation
#print axioms chosenPresheafPiBaseChangeIso_evaluation

end Mettapedia.TypeTheory.PresheafPiEvaluationBaseChange
