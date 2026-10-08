import Mettapedia.GSLT.Core.RelativeClosedPositionedModalRelyInputs
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationLimits

/-!
# Independently supplied local models of positioned-modal declarations

An actual weak finite-limit closed base functor, complete logical operation
values and their finite diagrams are supplied independently. Each new modal
value has only its own complete defining square. These data earn the local
declaration realization, the entire equation-quotient interpretation and its
native finite-limit closed augmentation.

The actual original diagram, every original primitive and the selected
environment-only rely expression are recovered after augmentation. Raw
objects remain retained. This fixed-presentation construction does not yet
assemble a varying-theory free/forgetful action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalLocalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open ProgramReductionTheory

universe k w p
variable (source : Theory.{k,k}) {Index : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (D : Type w) [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

structure LocalModel where
  base : source.closed.Obj ⥤ D
  baseFinite : PreservesFiniteLimits base
  baseClosed : MonoidalClosedFunctor base
  predicates : RelativeClosedPredicateLogic.Interpretation.Meaning base
  finiteDiagrams : RelativeClosedPredicateLogic.Interpretation.Admission base predicates
  modalValues : Option Index → RelativeClosedSyntax.Interpretation.ArrowValue D
  modalDiagrams : RelativeClosedPositionedModalRealization.LocalAdmission source selected
    base predicates modalValues

attribute [instance] LocalModel.baseFinite LocalModel.baseClosed

variable {source selected D}

def LocalModel.meanings (model : LocalModel source selected D) :=
  RelativeClosedPositionedModalRealization.assignment source model.base model.predicates model.modalValues

instance LocalModel.meanings_base_finite (model : LocalModel source selected D) :
    PreservesFiniteLimits model.meanings.base := model.baseFinite

instance LocalModel.meanings_base_closed (model : LocalModel source selected D) :
    MonoidalClosedFunctor model.meanings.base := model.baseClosed

theorem LocalModel.realized (model : LocalModel source selected D) :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected) model.meanings :=
  RelativeClosedPositionedModalRealization.realized source selected model.base model.predicates model.modalValues
    model.finiteDiagrams model.modalDiagrams

def LocalModel.model (model : LocalModel source selected D) :
    SemanticModels.Model (RelativeClosedPositionedModalPresentation.signature source selected) D :=
  ⟨model.meanings, model.realized⟩

abbrev LocalModel.diagram (model : LocalModel source selected D) := model.model.diagram

def LocalModel.weakModel (model : LocalModel source selected D) :
    BaseExtension.Models.WeakModel
      (signature := RelativeClosedPositionedModalPresentation.signature source selected) (D := D) where
  model := model.model
  baseFinite := model.baseFinite
  baseClosed := model.baseClosed

def LocalModel.nativeModel (model : LocalModel source selected D) :
    SemanticModels.Model (RelativeClosedPositionedModalPresentation.nativeSignature source selected) D :=
  BaseExtension.Models.extendModel model.weakModel

abbrev LocalModel.nativeDiagram (model : LocalModel source selected D) := model.nativeModel.diagram

def LocalModel.closedInterpretation (model : LocalModel source selected D) :
    LambdaTheoryMap (RelativeClosedPositionedModalPresentation.nativeTheory source selected)
      (LambdaTheory.ofCategory D) where
  functor := model.nativeDiagram
  preservesFiniteLimits := RelativeClosedSyntax.Interpretation.functor_preservesFiniteLimits
    model.nativeModel.meanings model.nativeModel.realization
  preservesExponentials := RelativeClosedSyntax.Interpretation.functor_closed
    model.nativeModel.meanings model.nativeModel.realization

theorem LocalModel.original_diagram_readback (model : LocalModel source selected D) :
    (RelativeClosedPositionedModalPresentation.nativeInclusion source selected).functor ⋙ model.nativeDiagram =
      model.diagram :=
  BaseExtension.WeakExtension.original_diagram_readback model.meanings model.realized

theorem LocalModel.base_readback (model : LocalModel source selected D) :
    (RelativeClosedPositionedModalPresentation.baseMap source selected).functor ⋙ model.nativeDiagram =
      model.base :=
  RelativeClosedSyntax.Interpretation.functor_base model.nativeModel.meanings model.nativeModel.realization

theorem LocalModel.named_read (model : LocalModel source selected D) (origin : Option Index) :
    model.meanings.evaluateArrow
      (RelativeClosedPositionedModalPresentation.namedRaw source selected origin).code =
        some (model.modalValues origin) :=
  (EquationExtension.evaluate_arrow_original
    (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
    (RelativeClosedPositionedModalRealization.arrowAssignment source model.base model.predicates model.modalValues)
    (RelativeClosedPositionedModalPresentation.primitive source selected origin).code).trans rfl

def LocalModel.namedSource (_model : LocalModel source selected D) (origin : Option Index) :=
  RelativeClosedPositionedModalReadout.rawSource source selected origin

def LocalModel.namedTarget (_model : LocalModel source selected D) (origin : Option Index) :=
  RelativeClosedPositionedModalReadout.rawTarget source selected origin

theorem LocalModel.named_endpoints (model : LocalModel source selected D) (origin : Option Index) :
    model.meanings.evaluateObject (model.namedSource origin).code = some (model.modalValues origin).source ∧
    model.meanings.evaluateObject (model.namedTarget origin).code = some (model.modalValues origin).target := by
  obtain ⟨value, first, second, reading⟩ :=
    RelativeClosedSyntax.Interpretation.sound model.meanings model.realized
      (RelativeClosedPositionedModalPresentation.namedRaw source selected origin).admitted.some
  have same := Option.some.inj (reading.symm.trans (model.named_read origin))
  cases same
  exact ⟨first, second⟩

theorem LocalModel.native_original_object (model : LocalModel source selected D)
    (object : Object (RelativeClosedPositionedModalPresentation.signature source selected)) (value : D)
    (read : model.meanings.evaluateObject object.code = some value) :
    model.nativeDiagram.obj
      ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).object object) = value :=
  RelativeClosedSyntax.Interpretation.objectValue_unique model.nativeModel.meanings model.nativeModel.realization
    ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).object object) value
    ((BaseExtension.WeakExtension.original_object_read
      (signature := RelativeClosedPositionedModalPresentation.signature source selected) model.meanings object.code).trans read)

theorem LocalModel.native_original_arrow (model : LocalModel source selected D)
    {first second : Object (RelativeClosedPositionedModalPresentation.signature source selected)}
    (raw : RawHom first second) {before after : D} (arrow : before ⟶ after)
    (read : model.meanings.evaluateArrow raw.code = some ⟨before, after, arrow⟩) :
    HEq (model.nativeDiagram.map
      (classOf ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).rawArrow raw))) arrow :=
  RelativeClosedSyntax.Interpretation.functor_map_heq model.nativeModel.meanings model.nativeModel.realization
    ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).rawArrow raw) arrow
    ((BaseExtension.WeakExtension.original_arrow_read
      (signature := RelativeClosedPositionedModalPresentation.signature source selected) model.meanings raw.code).trans read)

theorem LocalModel.native_named_image (model : LocalModel source selected D) (origin : Option Index) :
    HEq (model.nativeDiagram.map (classOf
      ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).rawArrow
        (RelativeClosedPositionedModalPresentation.namedRaw source selected origin))))
      (model.modalValues origin).arrow :=
  model.native_original_arrow (RelativeClosedPositionedModalPresentation.namedRaw source selected origin)
    (model.modalValues origin).arrow (model.named_read origin)

theorem LocalModel.native_named_source (model : LocalModel source selected D) (origin : Option Index) :
    model.nativeDiagram.obj
      ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).object
        (model.namedSource origin)) = (model.modalValues origin).source :=
  model.native_original_object (model.namedSource origin) (model.modalValues origin).source
    (model.named_endpoints origin).1

theorem LocalModel.native_named_target (model : LocalModel source selected D) (origin : Option Index) :
    model.nativeDiagram.obj
      ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).object
        (model.namedTarget origin)) = (model.modalValues origin).target :=
  model.native_original_object (model.namedTarget origin) (model.modalValues origin).target
    (model.named_endpoints origin).2

def LocalModel.namedImageAt (model : LocalModel source selected D) (origin : Option Index) :
    (model.modalValues origin).source ⟶ (model.modalValues origin).target :=
  eqToHom (model.native_named_source origin).symm ≫
    model.nativeDiagram.map (classOf
      ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).rawArrow
        (RelativeClosedPositionedModalPresentation.namedRaw source selected origin))) ≫
      eqToHom (model.native_named_target origin)

theorem LocalModel.namedImageAt_complete (model : LocalModel source selected D) (origin : Option Index) :
    model.namedImageAt origin = (model.modalValues origin).arrow := by
  have complete := (conj_eqToHom_iff_heq _ _
    (model.native_named_source origin) (model.native_named_target origin)).mpr (model.native_named_image origin)
  simp only [namedImageAt, complete, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

variable (source selected D)

def native (base : source.closed.Obj ⥤ D) [PreservesFiniteLimits base] [MonoidalClosedFunctor base]
    (doctrine : PredicateDoctrine.HigherOrder.{w,k,p} D) : LocalModel source selected D where
  base := base
  baseFinite := inferInstance
  baseClosed := inferInstance
  predicates := RelativeClosedPositionedModalNativeMeaning.meaning doctrine source base
  finiteDiagrams := RelativeClosedPredicateLogic.NativeMeaning.admitted base doctrine
  modalValues := RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base
  modalDiagrams := RelativeClosedPositionedModalNativeMeaning.admitted doctrine source selected base

variable (base : source.closed.Obj ⥤ D) [PreservesFiniteLimits base] [MonoidalClosedFunctor base]
variable (doctrine : PredicateDoctrine.HigherOrder.{w,k,p} D)

theorem native_diagram : (native source selected D base doctrine).diagram =
    RelativeClosedPositionedModalNativeMeaning.diagram doctrine source selected base := rfl

theorem native_environment_image (origin : Index) :
    HEq ((native source selected D base doctrine).nativeDiagram.map (classOf
      ((RelativeClosedPositionedModalPresentation.nativeInclusion source selected).rawArrow
        (RelativeClosedPositionedModalRelyInputs.sourceArrow source selected origin))))
      (RelativeClosedPositionedModalRelyInputs.image source selected base doctrine origin) :=
  (native source selected D base doctrine).native_original_arrow
    (RelativeClosedPositionedModalRelyInputs.sourceArrow source selected origin)
    (RelativeClosedPositionedModalRelyInputs.image source selected base doctrine origin)
    (RelativeClosedPositionedModalRelyInputs.source_arrow_read source selected base doctrine origin)

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalLocalModels
