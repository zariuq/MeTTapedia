import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransportCells

/-!
# Unit and composition comparisons of the weak model action

The composition comparison retains the actual first and second transported
models. Its components paste the complete interpretation comparisons and
whisker the first comparison through the supplied second functor. Naturality
is proved from real mapped isomorphism cancellation. The unit comparison
retains the independent assignment and the earned identity calibration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransportAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Functor
open GeneratedCategory Interpretation SemanticModels

universe k w z h

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable (headers : HeaderFormation signature)
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

theorem image_identity (model : Model signature D) : image headers (𝟭 D) model = model :=
  Model.ext (AssignmentTransport.assignment_identity model.meanings model.realization headers)

def identityIso : action headers (𝟭 D) ≅ 𝟭 (Model signature D) :=
  NatIso.ofComponents
    (fun model => isoOfDiagram (comparison headers (𝟭 D) model).symm) (by
      intro first second cell
      change ((comparison headers (𝟭 D) first).inv ≫ cell ≫
        (comparison headers (𝟭 D) second).hom) ≫ (comparison headers (𝟭 D) second).inv =
        (comparison headers (𝟭 D) first).inv ≫ cell
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

variable {E : Type z} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable {H : Type h} [Category.{k} H]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable (first : D ⥤ E) [PreservesFiniteLimits first] [MonoidalClosedFunctor first]
variable (second : E ⥤ H) [PreservesFiniteLimits second] [MonoidalClosedFunctor second]

private instance composite_lex : PreservesFiniteLimits (first ⋙ second) :=
  comp_preservesFiniteLimits first second

private instance composite_closed : MonoidalClosedFunctor (first ⋙ second) :=
  CartesianClosedFunctorCoherence.closed_composition first second

def compositionAt (model : Model signature D) :
    (image headers (first ⋙ second) model).diagram ≅
      (image headers second (image headers first model)).diagram :=
  (comparison headers (first ⋙ second) model).symm ≪≫
    isoWhiskerRight (comparison headers first model) second ≪≫
      comparison headers second (image headers first model)

def compositionIso : action headers (first ⋙ second) ≅
    action headers first ⋙ action headers second :=
  NatIso.ofComponents (fun model => isoOfDiagram (compositionAt headers first second model)) (by
    intro before after cell
    apply NatTrans.ext
    funext context
    change ((comparison headers (first ⋙ second) before).inv.app context ≫
        second.map (first.map (cell.app context)) ≫
          (comparison headers (first ⋙ second) after).hom.app context) ≫
        ((comparison headers (first ⋙ second) after).inv.app context ≫
          second.map ((comparison headers first after).hom.app context) ≫
            (comparison headers second (image headers first after)).hom.app context) =
      ((comparison headers (first ⋙ second) before).inv.app context ≫
        second.map ((comparison headers first before).hom.app context) ≫
          (comparison headers second (image headers first before)).hom.app context) ≫
        ((comparison headers second (image headers first before)).inv.app context ≫
          second.map ((comparison headers first before).inv.app context ≫
            first.map (cell.app context) ≫ (comparison headers first after).hom.app context) ≫
              (comparison headers second (image headers first after)).hom.app context)
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, second.map_comp]
    rw [← Category.assoc (second.map ((comparison headers first before).hom.app context)),
      ← second.map_comp, Iso.hom_inv_id_app, second.map_id, Category.id_comp])

@[simp] theorem compositionIso_hom_app_app (model : Model signature D) (context : Object signature) :
    ((compositionIso headers first second).hom.app model).app context =
      (comparison headers (first ⋙ second) model).inv.app context ≫
        second.map ((comparison headers first model).hom.app context) ≫
          (comparison headers second (image headers first model)).hom.app context := rfl

@[simp] theorem compositionIso_inv_app_app (model : Model signature D) (context : Object signature) :
    ((compositionIso headers first second).inv.app model).app context =
          (comparison headers second (image headers first model)).inv.app context ≫
        second.map ((comparison headers first model).inv.app context) ≫
          (comparison headers (first ⋙ second) model).hom.app context := by
  change ((comparison headers second (image headers first model)).inv.app context ≫
      second.map ((comparison headers first model).inv.app context)) ≫
        (comparison headers (first ⋙ second) model).hom.app context = _
  exact Category.assoc _ _ _

theorem composition_arrow_readout (model : Model signature D) {source target : Object signature}
    (input : RawHom source target) :
    (image headers second (image headers first model)).meanings.evaluateArrow input.code =
      some ⟨(image headers second (image headers first model)).diagram.obj source,
        (image headers second (image headers first model)).diagram.obj target,
        (compositionAt headers first second model).inv.app source ≫
          (image headers (first ⋙ second) model).diagram.map (classOf input) ≫
            (compositionAt headers first second model).hom.app target⟩ := by
  let compared := compositionAt headers first second model
  have natural := compared.hom.naturality (classOf input)
  have conjugated := congrArg (fun value => compared.inv.app source ≫ value) natural
  have recovered : (image headers second (image headers first model)).diagram.map (classOf input) =
      compared.inv.app source ≫
        (image headers (first ⋙ second) model).diagram.map (classOf input) ≫ compared.hom.app target := by
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using conjugated.symm
  exact (functor_complete_readout (image headers second (image headers first model)).meanings
    (image headers second (image headers first model)).realization input).trans
      (congrArg (fun value => some (⟨_, _, value⟩ : ArrowValue H)) recovered)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransportAction
