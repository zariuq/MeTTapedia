import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorModelEquivalence
import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransportActionLaws

/-!
# Naturality of the coherent functor–model comparison

The independently reconstructed model equivalence commutes with weak target
postcomposition through the actual parser and transport comparisons. These
are natural isomorphisms on the full model and closed-diagram categories.
The interpretation square also respects each supplied ordinary target cell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorModelEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Functor
open GeneratedCategory SemanticModels ClosedModels

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable (headers : HeaderFormation signature)
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {E : Type z} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable (mapping : D ⥤ E) [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

def interpretationComparison : ClosedModels.interpretation ⋙ postcompose mapping ≅
    AssignmentTransportAction.action headers mapping ⋙ ClosedModels.interpretation :=
  NatIso.ofComponents (fun model => ClosedModels.isoOfFunctor
    (AssignmentTransportAction.comparison headers mapping model)) (by
      intro first last input
      change whiskerRight input mapping ≫ (AssignmentTransportAction.comparison headers mapping last).hom =
        (AssignmentTransportAction.comparison headers mapping first).hom ≫
          ((AssignmentTransportAction.comparison headers mapping first).inv ≫
            whiskerRight input mapping ≫ (AssignmentTransportAction.comparison headers mapping last).hom)
      simp only [Iso.hom_inv_id_assoc])

def extractionAt (input : Diagram signature D) :
    ((postcompose mapping ⋙ extract headers).obj input).diagram ≅
      ((extract headers ⋙ AssignmentTransportAction.action headers mapping).obj input).diagram :=
  (comparison headers ((postcompose mapping).obj input)).symm ≪≫
    isoWhiskerRight (comparison headers input) mapping ≪≫
      AssignmentTransportAction.comparison headers mapping (extracted headers input)

def extractionComparison : postcompose mapping ⋙ extract headers ≅
    extract headers ⋙ AssignmentTransportAction.action headers mapping :=
  NatIso.ofComponents (fun input => SemanticModels.isoOfDiagram (extractionAt headers mapping input)) (by
    intro first last input
    apply NatTrans.ext
    funext context
    change ((comparison headers ((postcompose mapping).obj first)).inv.app context ≫
        mapping.map (input.app context) ≫
          (comparison headers ((postcompose mapping).obj last)).hom.app context) ≫
      ((comparison headers ((postcompose mapping).obj last)).inv.app context ≫
        mapping.map ((comparison headers last).hom.app context) ≫
          (AssignmentTransportAction.comparison headers mapping (extracted headers last)).hom.app context) =
      ((comparison headers ((postcompose mapping).obj first)).inv.app context ≫
        mapping.map ((comparison headers first).hom.app context) ≫
          (AssignmentTransportAction.comparison headers mapping (extracted headers first)).hom.app context) ≫
      ((AssignmentTransportAction.comparison headers mapping (extracted headers first)).inv.app context ≫
        mapping.map ((comparison headers first).inv.app context ≫ input.app context ≫
          (comparison headers last).hom.app context) ≫
            (AssignmentTransportAction.comparison headers mapping (extracted headers last)).hom.app context)
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, mapping.map_comp]
    rw [← Category.assoc (mapping.map ((comparison headers first).hom.app context)),
      ← mapping.map_comp, Iso.hom_inv_id_app, mapping.map_id, Category.id_comp])

variable {mapping}
variable {before after : D ⥤ E}
variable [PreservesFiniteLimits before] [MonoidalClosedFunctor before]
variable [PreservesFiniteLimits after] [MonoidalClosedFunctor after]

def postcomposeChange (input : before ⟶ after) : postcompose before ⟶
    postcompose (signature := signature) after where
  app diagram := show diagram.functor ⋙ before ⟶ diagram.functor ⋙ after from
    whiskerLeft diagram.functor input
  naturality {first last} arrow := by
    apply NatTrans.ext
    funext context
    exact input.naturality (arrow.app context)

theorem interpretation_target_cell (input : before ⟶ after) :
    whiskerLeft ClosedModels.interpretation (postcomposeChange (signature := signature) input) ≫
        (interpretationComparison headers after).hom =
      (interpretationComparison headers before).hom ≫
        whiskerRight (AssignmentTransportAction.change headers input) ClosedModels.interpretation := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change input.app (model.diagram.obj context) ≫
      (AssignmentTransportAction.comparison headers after model).hom.app context =
    (AssignmentTransportAction.comparison headers before model).hom.app context ≫
      ((AssignmentTransportAction.comparison headers before model).inv.app context ≫
        input.app (model.diagram.obj context) ≫
          (AssignmentTransportAction.comparison headers after model).hom.app context)
  simp only [Iso.hom_inv_id_app_assoc]

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorModelEquivalence
