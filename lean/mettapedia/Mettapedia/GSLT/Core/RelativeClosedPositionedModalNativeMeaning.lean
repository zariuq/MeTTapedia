import Mettapedia.GSLT.Core.RelativeClosedPositionedModalRealization

/-!
# Native classifier meanings of generated positioned modalities

The native arrows are constructed independently by classifying their complete
predicate families. Their equality with the evaluated authored expressions
earns the local declaration admission, and hence an actual interpretation of
the generated equation category. The empty-context possibility uses the
actual source and target of the supplied event relation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalNativeMeaning

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open ProgramReductionTheory

universe k w z p
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D]
variable (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)

def possibilityOperation {events programs : D} (source target : events ⟶ programs) :
    HigherOrderInternalPredicateQuantifier.power doctrine programs ⟶
      HigherOrderInternalPredicateQuantifier.power doctrine programs :=
  curry (doctrine.generic.characteristic _
    (doctrine.existsAlong (source ▷ HigherOrderInternalPredicateQuantifier.power doctrine programs)
      (doctrine.reindex (target ▷ HigherOrderInternalPredicateQuantifier.power doctrine programs)
        (HigherOrderInternalPredicateObject.family doctrine (𝟙 _)))))

theorem possibilityOperation_family {events programs : D} (source target : events ⟶ programs) :
    HigherOrderInternalPredicateObject.family doctrine (possibilityOperation doctrine source target) =
      doctrine.existsAlong (source ▷ HigherOrderInternalPredicateQuantifier.power doctrine programs)
        (doctrine.reindex (target ▷ HigherOrderInternalPredicateQuantifier.power doctrine programs)
          (HigherOrderInternalPredicateObject.family doctrine (𝟙 _))) := by
  change doctrine.reindex (uncurry (curry (doctrine.generic.characteristic _ _)))
    doctrine.generic.truth = _
  rw [uncurry_curry, doctrine.generic.classifies]

theorem possibilityOperation_complete {events programs : D} (source target : events ⟶ programs) :
    InternalPredicateQuantifier.precomposition (operations doctrine) target ≫
      existsOperation doctrine source = possibilityOperation doctrine source target := by
  apply HigherOrderInternalPredicateObject.family_injective doctrine
  rw [exists_supplied, precomposition_generic, possibilityOperation_family]

variable [HasFiniteLimits D]
variable (source : Theory.{k,k}) {Index : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (base : source.closed.Obj ⥤ D)

abbrev meaning := RelativeClosedPredicateLogic.NativeMeaning.meaning base doctrine

def added : Option Index → RelativeClosedSyntax.Interpretation.ArrowValue D
  | none => ⟨HigherOrderInternalPredicateQuantifier.power doctrine (base.obj source.program),
      HigherOrderInternalPredicateQuantifier.power doctrine (base.obj source.program),
      possibilityOperation doctrine (base.map source.source) (base.map source.target)⟩
  | some origin =>
      ⟨PositionedRewritePredicatePower.profiles doctrine
          (base.obj (selected origin).frame.assay)
          (base.obj ((selected origin).frame.assay ⨯ source.program)),
        PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.carrier),
        PositionedRewritePredicatePower.operation doctrine
          (base.map (selected origin).frame.forget) (base.map (selected origin).frame.focus)
          (base.map (selected origin).frame.instantiate) (base.map (selected origin).frame.outgoing)⟩

omit [HasFiniteLimits D] in
theorem admitted : RelativeClosedPositionedModalRealization.LocalAdmission source selected base
    (meaning doctrine source base) (added doctrine source selected base) := by
  intro origin
  cases origin with
  | none =>
      exact congrArg (fun arrow =>
        (⟨HigherOrderInternalPredicateQuantifier.power doctrine (base.obj source.program),
          HigherOrderInternalPredicateQuantifier.power doctrine (base.obj source.program), arrow⟩ :
          RelativeClosedSyntax.Interpretation.ArrowValue D))
        (possibilityOperation_complete doctrine (base.map source.source) (base.map source.target)).symm
  | some origin =>
      exact congrArg (fun arrow =>
        (⟨PositionedRewritePredicatePower.profiles doctrine
            (base.obj (selected origin).frame.assay)
            (base.obj ((selected origin).frame.assay ⨯ source.program)),
          PositionedRewritePredicatePower.power doctrine (base.obj (selected origin).frame.carrier), arrow⟩ :
          RelativeClosedSyntax.Interpretation.ArrowValue D))
        (RelativeClosedPositionedModal.Interpretation.native_modality_complete base doctrine
          (selected origin).frame.forget (selected origin).frame.focus
          (selected origin).frame.instantiate (selected origin).frame.outgoing).symm

theorem realized : RelativeClosedSyntax.Interpretation.Realization
    (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedPositionedModalRealization.assignment source base (meaning doctrine source base)
      (added doctrine source selected base)) :=
  RelativeClosedPositionedModalRealization.realized source selected base (meaning doctrine source base)
    (added doctrine source selected base) (RelativeClosedPredicateLogic.NativeMeaning.admitted base doctrine)
    (admitted doctrine source selected base)

def diagram := RelativeClosedSyntax.Interpretation.functor
  (RelativeClosedPositionedModalRealization.assignment source base (meaning doctrine source base)
    (added doctrine source selected base)) (realized doctrine source selected base)

theorem named_read (origin : Option Index) :
    (RelativeClosedPositionedModalRealization.assignment source base (meaning doctrine source base)
      (added doctrine source selected base)).evaluateArrow
      (RelativeClosedPositionedModalPresentation.namedRaw source selected origin).code =
        some (added doctrine source selected base origin) :=
  (EquationExtension.evaluate_arrow_original
    (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
    (RelativeClosedPositionedModalRealization.arrowAssignment source base (meaning doctrine source base)
      (added doctrine source selected base)) _).trans rfl

theorem complete_named_image (origin : Option Index) :
    HEq ((diagram doctrine source selected base).map
      (classOf (RelativeClosedPositionedModalPresentation.namedRaw source selected origin)))
      (added doctrine source selected base origin).arrow :=
  RelativeClosedSyntax.Interpretation.functor_map_heq
    (RelativeClosedPositionedModalRealization.assignment source base (meaning doctrine source base)
      (added doctrine source selected base)) (realized doctrine source selected base)
    (RelativeClosedPositionedModalPresentation.namedRaw source selected origin)
    (added doctrine source selected base origin).arrow (named_read doctrine source selected base origin)

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalNativeMeaning
