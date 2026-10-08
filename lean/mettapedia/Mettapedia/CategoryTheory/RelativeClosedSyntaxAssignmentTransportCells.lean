import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransportAction

/-!
# Ordinary target cells act on transported models

A natural transformation between weak closed functors is whiskered with
each independently derived interpretation and conjugated by its transport
comparisons. Naturality in every model cell, identity and vertical
composition are proved on the complete diagrams.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransportAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Functor
open GeneratedCategory Interpretation SemanticModels

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable (headers : HeaderFormation signature)
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {E : Type z} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable {before after : D ⥤ E}
variable [PreservesFiniteLimits before] [MonoidalClosedFunctor before]
variable [PreservesFiniteLimits after] [MonoidalClosedFunctor after]

def change (input : before ⟶ after) : action headers before ⟶ action headers after where
  app model := show (image headers before model).diagram ⟶ (image headers after model).diagram from
    (comparison headers before model).inv ≫ whiskerLeft model.diagram input ≫
      (comparison headers after model).hom
  naturality {first second} cell := by
    apply NatTrans.ext
    funext context
    change ((comparison headers before first).inv.app context ≫ before.map (cell.app context) ≫
        (comparison headers before second).hom.app context) ≫
        ((comparison headers before second).inv.app context ≫ input.app (second.diagram.obj context) ≫
          (comparison headers after second).hom.app context) =
      ((comparison headers before first).inv.app context ≫ input.app (first.diagram.obj context) ≫
        (comparison headers after first).hom.app context) ≫
        ((comparison headers after first).inv.app context ≫ after.map (cell.app context) ≫
          (comparison headers after second).hom.app context)
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc (before.map (cell.app context)), input.naturality, Category.assoc]

@[simp] theorem change_app_app (input : before ⟶ after) (model : Model signature D)
    (context : Object signature) :
    ((change headers input).app model).app context =
      (comparison headers before model).inv.app context ≫ input.app (model.diagram.obj context) ≫
        (comparison headers after model).hom.app context := rfl

theorem change_identity : change headers (𝟙 before) = 𝟙 (action headers before) := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change (comparison headers before model).inv.app context ≫ 𝟙 (before.obj (model.diagram.obj context)) ≫
    (comparison headers before model).hom.app context = 𝟙 _
  exact (congrArg (fun value => (comparison headers before model).inv.app context ≫ value)
    (Category.id_comp ((comparison headers before model).hom.app context))).trans
      (Iso.inv_hom_id_app (comparison headers before model) context)

variable {last : D ⥤ E} [PreservesFiniteLimits last] [MonoidalClosedFunctor last]

theorem change_compose (first : before ⟶ after) (second : after ⟶ last) :
    change headers (first ≫ second) = change headers first ≫ change headers second := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change (comparison headers before model).inv.app context ≫
      (first.app (model.diagram.obj context) ≫ second.app (model.diagram.obj context)) ≫
        (comparison headers last model).hom.app context =
    ((comparison headers before model).inv.app context ≫ first.app (model.diagram.obj context) ≫
      (comparison headers after model).hom.app context) ≫
    ((comparison headers after model).inv.app context ≫ second.app (model.diagram.obj context) ≫
      (comparison headers last model).hom.app context)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransportAction
