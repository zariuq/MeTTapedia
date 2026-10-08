import Mettapedia.GSLT.Core.RelativeClosedPositionedModalReadout

/-!
# Environment-only rely inputs of an actual positioned modality

The rely function is independently supplied at the chosen position's
environment. An authored raw expression pulls it to the whole assay before
applying the named modality. Its complete source image equals the native
operation that quantifies exactly those environment inputs and retains the
whole outgoing postcondition. The focus is not an extra rely argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalRelyInputs

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open ProgramReductionTheory

universe k w z p
variable (source : Theory.{k,k}) {Index : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)

def environment (origin : Index) := (selected origin).position.environment

def assayProjection (origin : Index) : (selected origin).frame.assay ⟶ environment source selected origin :=
  prod.fst

theorem instance_projection (origin : Index) :
    (selected origin).frame.instantiate ≫ assayProjection source selected origin =
      (selected origin).position.relies := prod.lift_fst _ _

def domain (origin : Index) : Object (RelativeClosedPredicateLogic.signature (C := source.closed.Obj)) :=
  product (RelativeClosedPredicateLogic.power (environment source selected origin))
    (RelativeClosedPredicateLogic.power ((selected origin).frame.assay ⨯ source.program))

def inputRaw (origin : Index) : RawHom (domain source selected origin)
    (RelativeClosedPositionedModalPresentation.domain source selected (some origin)) :=
  RawHom.pair
    ((RawHom.first _ _).compose
      (RelativeClosedPredicateLogic.precompositionRaw (assayProjection source selected origin)))
    (RawHom.second _ _)

def expression (origin : Index) : RawHom (domain source selected origin)
    (RelativeClosedPositionedModalPresentation.codomain source selected (some origin)) :=
  (inputRaw source selected origin).compose
    (RelativeClosedPositionedModalPresentation.expression source selected (some origin))

def mappedInputRaw (origin : Index) :=
  (RelativeClosedPositionedModalPresentation.definingInclusion source selected).rawArrow
    ((RelativeClosedPositionedModalPresentation.arrowInclusion source selected).rawArrow
      (RelativeClosedPredicateLogic.equationInclusion.rawArrow (inputRaw source selected origin)))

def sourceArrow (origin : Index) :=
  (mappedInputRaw source selected origin).compose
    (RelativeClosedPositionedModalPresentation.namedRaw source selected (some origin))

variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : source.closed.Obj ⥤ D)
variable (meaning : RelativeClosedPredicateLogic.Interpretation.Meaning base)

abbrev profiles (origin : Index) :=
  RelativeClosedPredicateLogic.Interpretation.targetPower base meaning (environment source selected origin) ⊗
    RelativeClosedPredicateLogic.Interpretation.targetPower base meaning
      ((selected origin).frame.assay ⨯ source.program)

def inputMap (origin : Index) : profiles source selected base meaning origin ⟶
    RelativeClosedPositionedModal.Interpretation.targetProfiles base meaning
      (assay := (selected origin).frame.assay)
      (outgoing := (selected origin).frame.assay ⨯ source.program) :=
  lift (fst _ _ ≫ InternalPredicateQuantifier.precomposition meaning.predicates
    (base.map (assayProjection source selected origin))) (snd _ _)

theorem input_read (origin : Index) :
    RawInterpretation.Reads (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
      (inputRaw source selected origin) (inputMap source selected base meaning origin) :=
  RawInterpretation.pair _
    (RawInterpretation.compose _
      (RawInterpretation.first _
        (RelativeClosedPredicateLogic.Interpretation.power_read base meaning (environment source selected origin))
        (RelativeClosedPredicateLogic.Interpretation.power_read base meaning
          ((selected origin).frame.assay ⨯ source.program)))
      (RelativeClosedPredicateLogic.Interpretation.precomposition_read base meaning
        (assayProjection source selected origin)))
    (RawInterpretation.second _
      (RelativeClosedPredicateLogic.Interpretation.power_read base meaning (environment source selected origin))
      (RelativeClosedPredicateLogic.Interpretation.power_read base meaning
        ((selected origin).frame.assay ⨯ source.program)))

theorem expression_read (origin : Index) :
    RawInterpretation.Reads (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
      (expression source selected origin)
      (inputMap source selected base meaning origin ≫
        RelativeClosedPositionedModal.Interpretation.modalityOperator base meaning
          (selected origin).frame.forget (selected origin).frame.focus
          (selected origin).frame.instantiate (selected origin).frame.outgoing) :=
  RawInterpretation.compose _ (input_read source selected base meaning origin)
    (RelativeClosedPositionedModal.Interpretation.modality_read base meaning
      (selected origin).frame.forget (selected origin).frame.focus
      (selected origin).frame.instantiate (selected origin).frame.outgoing)

variable (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)

abbrev nativeMeaning := RelativeClosedPositionedModalNativeMeaning.meaning doctrine source base

def image (origin : Index) : profiles source selected base (nativeMeaning source base doctrine) origin ⟶
    PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.carrier) :=
  inputMap source selected base (nativeMeaning source base doctrine) origin ≫
    RelativeClosedPositionedModalReadout.imageAt doctrine source selected base (some origin)

theorem mapped_input_read (origin : Index) :
    (RelativeClosedPositionedModalReadout.meanings doctrine source selected base).evaluateArrow
      (mappedInputRaw source selected origin).code =
        some ⟨profiles source selected base (nativeMeaning source base doctrine) origin,
          RelativeClosedPositionedModal.Interpretation.targetProfiles base (nativeMeaning source base doctrine)
            (assay := (selected origin).frame.assay)
            (outgoing := (selected origin).frame.assay ⨯ source.program),
          inputMap source selected base (nativeMeaning source base doctrine) origin⟩ :=
  (EquationExtension.evaluate_arrow_original
    (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
    (RelativeClosedPositionedModalRealization.arrowAssignment source base (nativeMeaning source base doctrine)
      (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base)) _).trans
    ((ArrowExtension.evaluate_arrow_original
      (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))
      (RelativeClosedPositionedModalPresentation.arrowDeclaration source selected)
      (RelativeClosedPredicateLogic.Interpretation.lawfulAssignment base (nativeMeaning source base doctrine))
      (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base) _).trans
      ((EquationExtension.evaluate_arrow_original
        (RelativeClosedPredicateLogic.signature (C := source.closed.Obj)) RelativeClosedPredicateLogic.declaration
        (RelativeClosedPredicateLogic.Interpretation.assignment base (nativeMeaning source base doctrine)) _).trans
          (input_read source selected base (nativeMeaning source base doctrine) origin)))

theorem source_arrow_read (origin : Index) :
    RawInterpretation.Reads (RelativeClosedPositionedModalReadout.meanings doctrine source selected base)
      (sourceArrow source selected origin) (image source selected base doctrine origin) := by
  have named := RelativeClosedPositionedModalNativeMeaning.named_read doctrine source selected base (some origin)
  have actual := (RelativeClosedPositionedModalReadout.meanings doctrine source selected base).evaluate_compose
    (inputMap source selected base (nativeMeaning source base doctrine) origin)
    (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base (some origin)).arrow
    (mapped_input_read source selected base doctrine origin) named
  exact actual.trans (congrArg (fun arrow => some
    (⟨profiles source selected base (nativeMeaning source base doctrine) origin,
      PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.carrier), arrow⟩ :
        RelativeClosedSyntax.Interpretation.ArrowValue D))
      (congrArg (fun arrow => inputMap source selected base (nativeMeaning source base doctrine) origin ≫ arrow)
        (RelativeClosedPositionedModalReadout.imageAt_complete doctrine source selected base (some origin)).symm))

theorem complete_source_image (origin : Index) :
    HEq ((RelativeClosedPositionedModalNativeMeaning.diagram doctrine source selected base).map
      (classOf (sourceArrow source selected origin))) (image source selected base doctrine origin) :=
  RelativeClosedSyntax.Interpretation.functor_map_heq
    (RelativeClosedPositionedModalReadout.meanings doctrine source selected base)
    (RelativeClosedPositionedModalNativeMeaning.realized doctrine source selected base)
    (sourceArrow source selected origin) (image source selected base doctrine origin)
    (source_arrow_read source selected base doctrine origin)

omit [HasFiniteLimits D] in
theorem inputMap_first (origin : Index) :
    inputMap source selected base (nativeMeaning source base doctrine) origin ≫
        fst (PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.assay))
          (PositionedRewritePredicatePower.power doctrine
            (base.obj ((selected origin).frame.assay ⨯ source.program))) =
      fst (PositionedRewritePredicatePower.power doctrine (base.obj (environment source selected origin)))
          (PositionedRewritePredicatePower.power doctrine
            (base.obj ((selected origin).frame.assay ⨯ source.program))) ≫
        InternalPredicateQuantifier.precomposition
          (HigherOrderInternalPredicateObject.operations doctrine)
          (base.map (assayProjection source selected origin)) :=
  lift_fst _ _

omit [HasFiniteLimits D] in
theorem inputMap_second (origin : Index) :
    inputMap source selected base (nativeMeaning source base doctrine) origin ≫
        snd (PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.assay))
          (PositionedRewritePredicatePower.power doctrine
            (base.obj ((selected origin).frame.assay ⨯ source.program))) =
      snd (PositionedRewritePredicatePower.power doctrine (base.obj (environment source selected origin)))
        (PositionedRewritePredicatePower.power doctrine
          (base.obj ((selected origin).frame.assay ⨯ source.program))) :=
  lift_snd _ _

omit [HasFiniteLimits D] in
theorem rely_input_read (origin : Index) {parameter : D}
    (inputs : parameter ⟶ profiles source selected base (nativeMeaning source base doctrine) origin) :
    PositionedRewritePredicatePower.family doctrine
      ((inputs ≫ inputMap source selected base (nativeMeaning source base doctrine) origin) ≫
        fst (PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.assay))
          (PositionedRewritePredicatePower.power doctrine
            (base.obj ((selected origin).frame.assay ⨯ source.program)))) =
      doctrine.reindex (base.map (assayProjection source selected origin) ▷ parameter)
        (PositionedRewritePredicatePower.family doctrine
          (inputs ≫ fst (PositionedRewritePredicatePower.power doctrine
              (base.obj (environment source selected origin)))
            (PositionedRewritePredicatePower.power doctrine
              (base.obj ((selected origin).frame.assay ⨯ source.program))))) := by
  have supplied := HigherOrderInternalPredicateQuantifier.precomposition_supplied doctrine
    (base.map (assayProjection source selected origin))
    (inputs ≫ fst (PositionedRewritePredicatePower.power doctrine
        (base.obj (environment source selected origin)))
      (PositionedRewritePredicatePower.power doctrine
        (base.obj ((selected origin).frame.assay ⨯ source.program))))
  exact (congrArg (PositionedRewritePredicatePower.family doctrine)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun arrow => inputs ≫ arrow)
        (inputMap_first source selected base doctrine origin)).trans
          (Category.assoc _ _ _).symm))).trans supplied

omit [HasFiniteLimits D] in
theorem post_input_read (origin : Index) {parameter : D}
    (inputs : parameter ⟶ profiles source selected base (nativeMeaning source base doctrine) origin) :
    PositionedRewritePredicatePower.family doctrine
      ((inputs ≫ inputMap source selected base (nativeMeaning source base doctrine) origin) ≫
        snd (PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.assay))
          (PositionedRewritePredicatePower.power doctrine
            (base.obj ((selected origin).frame.assay ⨯ source.program)))) =
        PositionedRewritePredicatePower.family doctrine
          (inputs ≫ snd (PositionedRewritePredicatePower.power doctrine
              (base.obj (environment source selected origin)))
            (PositionedRewritePredicatePower.power doctrine
              (base.obj ((selected origin).frame.assay ⨯ source.program)))) :=
  congrArg (PositionedRewritePredicatePower.family doctrine)
    ((Category.assoc _ _ _).trans
      (congrArg (fun arrow => inputs ≫ arrow)
        (inputMap_second source selected base doctrine origin)))

omit [HasFiniteLimits D] in
theorem condition_read (origin : Index) {parameter : D}
    (inputs : parameter ⟶ profiles source selected base (nativeMeaning source base doctrine) origin) :
    PositionedRewritePredicatePower.conditionAt doctrine
        (base.map (selected origin).frame.instantiate) (base.map (selected origin).frame.outgoing)
        (inputs ≫ inputMap source selected base (nativeMeaning source base doctrine) origin) =
      PositionedRewritePredicatePower.conditionAt doctrine
        (base.map (selected origin).position.relies) (base.map (selected origin).frame.outgoing) inputs := by
  unfold PositionedRewritePredicatePower.conditionAt
  rw [rely_input_read, post_input_read, ← doctrine.reindex_comp, ← comp_whiskerRight]
  have complete : base.map (selected origin).frame.instantiate ≫
      base.map (assayProjection source selected origin) = base.map (selected origin).position.relies :=
    (base.map_comp _ _).symm.trans (congrArg base.map (instance_projection source selected origin))
  rw [complete]
  rfl

theorem supplied_read (origin : Index) {parameter : D}
    (inputs : parameter ⟶ profiles source selected base (nativeMeaning source base doctrine) origin) :
    PositionedRewritePredicatePower.family doctrine (inputs ≫ image source selected base doctrine origin) =
      PositionedRewritePredicatePower.modalAt doctrine
        (base.map (selected origin).frame.forget) (base.map (selected origin).frame.focus)
        (base.map (selected origin).position.relies) (base.map (selected origin).frame.outgoing) inputs := by
  unfold image
  rw [← Category.assoc, RelativeClosedPositionedModalReadout.imageAt_complete]
  change PositionedRewritePredicatePower.family doctrine
    ((inputs ≫ inputMap source selected base (nativeMeaning source base doctrine) origin) ≫
      PositionedRewritePredicatePower.operation doctrine (base.map (selected origin).frame.forget)
        (base.map (selected origin).frame.focus) (base.map (selected origin).frame.instantiate)
        (base.map (selected origin).frame.outgoing)) = _
  rw [PositionedRewritePredicatePower.supplied_evaluation]
  change doctrine.existsAlong _ (doctrine.forallAlong _ _) = doctrine.existsAlong _ (doctrine.forallAlong _ _)
  exact congrArg (fun predicate => doctrine.existsAlong (base.map (selected origin).frame.focus ▷ parameter)
    (doctrine.forallAlong (base.map (selected origin).frame.forget ▷ parameter) predicate))
      (condition_read source selected base doctrine origin inputs)

theorem image_is_environment_operation (origin : Index) :
    image source selected base doctrine origin = PositionedRewritePredicatePower.operation doctrine
      (base.map (selected origin).frame.forget) (base.map (selected origin).frame.focus)
      (base.map (selected origin).position.relies) (base.map (selected origin).frame.outgoing) := by
  apply PositionedRewritePredicatePower.operation_unique doctrine
    (base.map (selected origin).frame.forget) (base.map (selected origin).frame.focus)
    (base.map (selected origin).position.relies) (base.map (selected origin).frame.outgoing)
  exact (congrArg (PositionedRewritePredicatePower.family doctrine) (Category.id_comp _)).symm.trans
    (supplied_read source selected base doctrine origin (𝟙 _))

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalRelyInputs
