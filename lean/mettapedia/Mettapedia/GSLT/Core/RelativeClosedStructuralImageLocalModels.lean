import Mettapedia.GSLT.Core.RelativeClosedStructuralImageNativeMeaning
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalLocalModels

/-!
# Weak closed native augmentation of constructor-image models

An independently realized predicate/modal model supplies only its local
declaration data. Independently supplied constructor values and their local
defining squares earn the extended interpretation and its finite-limit
closed native augmentation. Both the complete old modal diagram and weak
base functor are recovered. No global modal theory action or free-extension
adjunction is supplied as model data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageLocalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory

universe k w p
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)
variable (D : Type w) [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

structure LocalModel where
  previous : RelativeClosedPositionedModalLocalModels.LocalModel source selected D
  constructorValues : Origins → RelativeClosedSyntax.Interpretation.ArrowValue D
  constructorDiagrams : RelativeClosedStructuralImageRealization.LocalAdmission source constructors
    previous.base previous.predicates constructorValues

variable {source selected constructors D}

def LocalModel.meanings (model : LocalModel source selected constructors D) :=
  RelativeClosedStructuralImageRealization.assignment source model.previous.base model.previous.predicates
    model.previous.modalValues model.constructorValues

instance LocalModel.meanings_base_finite (model : LocalModel source selected constructors D) :
    PreservesFiniteLimits model.meanings.base := model.previous.baseFinite

instance LocalModel.meanings_base_closed (model : LocalModel source selected constructors D) :
    MonoidalClosedFunctor model.meanings.base := model.previous.baseClosed

theorem LocalModel.realized (model : LocalModel source selected constructors D) :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedStructuralImagePresentation.signature source selected constructors) model.meanings :=
  RelativeClosedStructuralImageRealization.realized source selected constructors model.previous.base model.previous.predicates
    model.previous.modalValues model.constructorValues model.previous.finiteDiagrams model.previous.modalDiagrams
    model.constructorDiagrams

def LocalModel.model (model : LocalModel source selected constructors D) :
    SemanticModels.Model (RelativeClosedStructuralImagePresentation.signature source selected constructors) D :=
  ⟨model.meanings, model.realized⟩

abbrev LocalModel.diagram (model : LocalModel source selected constructors D) := model.model.diagram

def LocalModel.weakModel (model : LocalModel source selected constructors D) : BaseExtension.Models.WeakModel
    (signature := RelativeClosedStructuralImagePresentation.signature source selected constructors) (D := D) where
  model := model.model
  baseFinite := model.previous.baseFinite
  baseClosed := model.previous.baseClosed

def LocalModel.nativeModel (model : LocalModel source selected constructors D) :
    SemanticModels.Model (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) D :=
  BaseExtension.Models.extendModel model.weakModel

abbrev LocalModel.nativeDiagram (model : LocalModel source selected constructors D) := model.nativeModel.diagram

def LocalModel.closedInterpretation (model : LocalModel source selected constructors D) :
    LambdaTheoryMap (RelativeClosedStructuralImagePresentation.nativeTheory source selected constructors)
      (LambdaTheory.ofCategory D) where
  functor := model.nativeDiagram
  preservesFiniteLimits := RelativeClosedSyntax.Interpretation.functor_preservesFiniteLimits
    model.nativeModel.meanings model.nativeModel.realization
  preservesExponentials := RelativeClosedSyntax.Interpretation.functor_closed
    model.nativeModel.meanings model.nativeModel.realization

theorem LocalModel.original_diagram_readback (model : LocalModel source selected constructors D) :
    (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).functor ⋙
      model.nativeDiagram = model.diagram :=
  BaseExtension.WeakExtension.original_diagram_readback model.meanings model.realized

theorem LocalModel.base_readback (model : LocalModel source selected constructors D) :
    (RelativeClosedStructuralImagePresentation.baseMap source selected constructors).functor ⋙
      model.nativeDiagram = model.previous.base :=
  RelativeClosedSyntax.Interpretation.functor_base model.nativeModel.meanings model.nativeModel.realization

theorem LocalModel.previous_diagram_readback (model : LocalModel source selected constructors D) :
    (RelativeClosedStructuralImagePresentation.inclusion source selected constructors).functor ⋙
      model.diagram = model.previous.diagram :=
  RelativeClosedStructuralImageRealization.complete_previous_diagram source selected constructors model.previous.base
    model.previous.predicates model.previous.modalValues model.constructorValues model.previous.finiteDiagrams
    model.previous.modalDiagrams model.constructorDiagrams

theorem LocalModel.native_named_image (model : LocalModel source selected constructors D) (origin : Origins) :
    HEq (model.nativeDiagram.map (classOf
      ((RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).rawArrow
        (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin))))
      (model.constructorValues origin).arrow :=
  RelativeClosedSyntax.Interpretation.functor_map_heq model.nativeModel.meanings model.nativeModel.realization
    ((RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).rawArrow
      (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin))
    (model.constructorValues origin).arrow
    ((BaseExtension.WeakExtension.original_arrow_read
      (signature := RelativeClosedStructuralImagePresentation.signature source selected constructors) model.meanings _).trans
        (RelativeClosedStructuralImageRealization.named_read source selected constructors model.previous.base model.previous.predicates
          model.previous.modalValues model.constructorValues origin))

variable (source selected constructors D)

def native (base : source.closed.Obj ⥤ D) [PreservesFiniteLimits base] [MonoidalClosedFunctor base]
    (doctrine : PredicateDoctrine.HigherOrder.{w,k,p} D) : LocalModel source selected constructors D where
  previous := RelativeClosedPositionedModalLocalModels.native source selected D base doctrine
  constructorValues := RelativeClosedStructuralImageNativeMeaning.added doctrine source constructors base
  constructorDiagrams := RelativeClosedStructuralImageNativeMeaning.admitted doctrine source constructors base

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageLocalModels
