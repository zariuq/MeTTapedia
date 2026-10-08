import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosedModels
import Mathlib.CategoryTheory.Equivalence

/-!
# Coherent universal comparison for a relative closed presentation

The independent evaluator turns each locally realized assignment into a
genuine finite-limit closed diagram. Conversely, the complete constructor
reconstruction extracts independently evaluated primitive meanings from
each weak closed diagram and proves all declared equations. Their actual
parser comparison supplies a category equivalence and its triangle law.

The hom categories use complete ordinary diagram transformations. This is
the universal comparison for a fixed authored presentation, rather than a
free modal-layer construction or extension of arbitrary primitive cells.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorModelEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory SemanticModels ClosedModels FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable (headers : HeaderFormation signature)
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

def extracted (mapping : Diagram signature D) : Model signature D where
  meanings := assignment mapping.functor headers
  realization := reconstruction_realization mapping.functor headers

def comparison (mapping : Diagram signature D) : mapping.functor ≅ (extracted headers mapping).diagram :=
  parserComparison mapping.functor headers

def extract : Diagram signature D ⥤ Model signature D where
  obj := extracted headers
  map {first second} input :=
    show (extracted headers first).diagram ⟶ (extracted headers second).diagram from
      (comparison headers first).inv ≫ input ≫ (comparison headers second).hom
  map_id mapping := by
    change (comparison headers mapping).inv ≫ 𝟙 mapping.functor ≫
      (comparison headers mapping).hom = 𝟙 _
    simp only [Category.id_comp, Iso.inv_hom_id]
  map_comp {first middle last} before after := by
    change (comparison headers first).inv ≫ (before ≫ after) ≫ (comparison headers last).hom =
      ((comparison headers first).inv ≫ before ≫ (comparison headers middle).hom) ≫
        ((comparison headers middle).inv ≫ after ≫ (comparison headers last).hom)
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

def unitIso : 𝟭 (Model signature D) ≅ ClosedModels.interpretation ⋙ extract headers :=
  NatIso.ofComponents
    (fun model => SemanticModels.isoOfDiagram
      (comparison headers (ClosedModels.interpretation.obj model))) (by
        intro first last input
        change input ≫ (comparison headers (ClosedModels.interpretation.obj last)).hom =
          (comparison headers (ClosedModels.interpretation.obj first)).hom ≫
            ((comparison headers (ClosedModels.interpretation.obj first)).inv ≫ input ≫
              (comparison headers (ClosedModels.interpretation.obj last)).hom)
        simp only [Iso.hom_inv_id_assoc]
        rfl)

def counitIso : extract headers ⋙ ClosedModels.interpretation ≅ 𝟭 (Diagram signature D) :=
  NatIso.ofComponents (fun mapping => ClosedModels.isoOfFunctor (comparison headers mapping).symm) (by
    intro first last input
    change ((comparison headers first).inv ≫ input ≫ (comparison headers last).hom) ≫
        (comparison headers last).inv = (comparison headers first).inv ≫ input
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

def equivalence : Model signature D ≌ Diagram signature D where
  functor := ClosedModels.interpretation
  inverse := extract headers
  unitIso := unitIso headers
  counitIso := counitIso headers
  functor_unitIso_comp model :=
    (comparison headers (ClosedModels.interpretation.obj model)).hom_inv_id

theorem primitive_meanings_recovered (model : Model signature D) :
    (extracted headers (ClosedModels.interpretation.obj model)).meanings = model.meanings :=
  InterpretationNormalization.normalized_assignment model.meanings model.realization headers

theorem complete_model_recovered (model : Model signature D) :
    extracted headers (ClosedModels.interpretation.obj model) = model :=
  Model.ext (primitive_meanings_recovered headers model)

theorem primitive_base_readout (mapping : Diagram signature D) :
    (extracted headers mapping).meanings.base = baseFunctor signature ⋙ mapping.functor := rfl

theorem primitive_object_readout (mapping : Diagram signature D) (origin : symbols.ObjectName) :
    (extracted headers mapping).meanings.object origin = mapping.functor.obj (namedObject origin) := rfl

theorem complete_arrow_readout (mapping : Diagram signature D) {source target : Object signature}
    (input : RawHom source target) :
    (extracted headers mapping).meanings.evaluateArrow input.code =
      some ⟨(extracted headers mapping).diagram.obj source,
        (extracted headers mapping).diagram.obj target,
        (comparison headers mapping).inv.app source ≫ mapping.functor.map (classOf input) ≫
          (comparison headers mapping).hom.app target⟩ := by
  have natural := (comparison headers mapping).hom.naturality (classOf input)
  have transported := congrArg (fun value => (comparison headers mapping).inv.app source ≫ value) natural
  have recovered : (extracted headers mapping).diagram.map (classOf input) =
      (comparison headers mapping).inv.app source ≫ mapping.functor.map (classOf input) ≫
        (comparison headers mapping).hom.app target := by
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using transported.symm
  exact (Interpretation.functor_complete_readout (extracted headers mapping).meanings
    (extracted headers mapping).realization input).trans
      (congrArg (fun arrow => some (⟨_, _, arrow⟩ : Interpretation.ArrowValue D)) recovered)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorModelEquivalence
