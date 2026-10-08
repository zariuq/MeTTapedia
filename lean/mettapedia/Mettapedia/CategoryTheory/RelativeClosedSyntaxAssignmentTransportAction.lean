import Mettapedia.CategoryTheory.RelativeClosedSyntaxSemanticModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransportIdentity

/-!
# Weak closed functors act on independently realized presentations

Objects use the earned transport of primitive meanings and equations.
Ordinary diagram cells are transported by the genuine target functor and
the complete interpretation comparisons. Identity and vertical composition
are proved from that conjugation. The displayed comparison is natural in
every actual model cell.

The model category uses ordinary natural transformations of the derived
diagrams; it does not assume that arbitrary local primitive maps extend.
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
variable (mapping : D ⥤ E) [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

def image (model : Model signature D) : Model signature E where
  meanings := AssignmentTransport.assignment model.meanings model.realization mapping headers
  realization := AssignmentTransport.locally_realized model.meanings model.realization mapping headers

def comparison (model : Model signature D) : model.diagram ⋙ mapping ≅
    (image headers mapping model).diagram :=
  AssignmentTransport.comparison model.meanings model.realization mapping headers

def cell {first second : Model signature D} (input : first ⟶ second) :
    image headers mapping first ⟶ image headers mapping second :=
  show (image headers mapping first).diagram ⟶ (image headers mapping second).diagram from
    (comparison headers mapping first).inv ≫ whiskerRight input mapping ≫
      (comparison headers mapping second).hom

def action : Model signature D ⥤ Model signature E where
  obj := image headers mapping
  map := cell headers mapping
  map_id model := by
    change (comparison headers mapping model).inv ≫ whiskerRight (𝟙 model.diagram) mapping ≫
      (comparison headers mapping model).hom = 𝟙 (image headers mapping model).diagram
    simp only [whiskerRight_id', Category.id_comp, Iso.inv_hom_id]
  map_comp before after := by
    change (comparison headers mapping _).inv ≫ whiskerRight (before ≫ after) mapping ≫
        (comparison headers mapping _).hom =
      ((comparison headers mapping _).inv ≫ whiskerRight before mapping ≫
        (comparison headers mapping _).hom) ≫
      ((comparison headers mapping _).inv ≫ whiskerRight after mapping ≫
        (comparison headers mapping _).hom)
    simp only [whiskerRight_comp, Category.assoc, Iso.hom_inv_id_assoc]

@[simp] theorem action_obj (model : Model signature D) :
    (action headers mapping).obj model = image headers mapping model := rfl

@[simp] theorem action_map_app {first second : Model signature D} (input : first ⟶ second)
    (context : Object signature) :
    ((action headers mapping).map input).app context =
      (comparison headers mapping first).inv.app context ≫ mapping.map (input.app context) ≫
        (comparison headers mapping second).hom.app context := rfl

def diagramComparison : diagrams (signature := signature) (D := D) ⋙
      (Functor.whiskeringRight (Object signature) D E).obj mapping ≅
    action headers mapping ⋙ diagrams :=
  NatIso.ofComponents (comparison headers mapping) (by
    intro first second input
    change whiskerRight input mapping ≫ (comparison headers mapping second).hom =
      (comparison headers mapping first).hom ≫
        ((comparison headers mapping first).inv ≫ whiskerRight input mapping ≫
          (comparison headers mapping second).hom)
    simp only [Iso.hom_inv_id_assoc])

theorem image_base (model : Model signature D) :
    (image headers mapping model).meanings.base = model.meanings.base ⋙ mapping :=
  AssignmentTransport.assignment_base model.meanings model.realization mapping headers

theorem image_object (model : Model signature D) (origin : symbols.ObjectName) :
    (image headers mapping model).meanings.object origin = mapping.obj (model.meanings.object origin) :=
  AssignmentTransport.assignment_object model.meanings model.realization mapping headers origin

theorem complete_arrow_readout (model : Model signature D) {source target : Object signature}
    (input : RawHom source target) :
    (image headers mapping model).meanings.evaluateArrow input.code =
      some ⟨(image headers mapping model).diagram.obj source,
        (image headers mapping model).diagram.obj target,
        (comparison headers mapping model).inv.app source ≫
          mapping.map (model.diagram.map (classOf input)) ≫
            (comparison headers mapping model).hom.app target⟩ :=
  AssignmentTransport.complete_arrow_readout model.meanings model.realization mapping headers input

end Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransportAction
