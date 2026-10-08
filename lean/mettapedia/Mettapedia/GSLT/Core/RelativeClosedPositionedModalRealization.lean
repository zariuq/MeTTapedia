import Mettapedia.GSLT.Core.RelativeClosedPositionedModalPresentation
import Mettapedia.CategoryTheory.RelativeClosedPositionedModalInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowInterpretation

/-!
# Exact local admission of the generated positioned-modal names

The new operator arrows are supplied independently. Their complete values
are compared with the independently evaluated authored expressions, retaining
both function inputs and the actual rule and position maps. These local
squares and the old finite predicate diagrams earn all declaration readings.
Conversely, declaration realization forces those complete local values.

There is no whole-model interpretation or free-extension universal property
field. Raw source objects, names and authored rewrite origins remain retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalRealization

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open ProgramReductionTheory

universe k w z
variable (source : Theory.{k,k}) {Index : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : source.closed.Obj ⥤ D)
variable (meaning : RelativeClosedPredicateLogic.Interpretation.Meaning base)

def expectedValue : Option Index → RelativeClosedSyntax.Interpretation.ArrowValue D
  | none => ⟨RelativeClosedPredicateLogic.Interpretation.targetPower base meaning source.program,
      RelativeClosedPredicateLogic.Interpretation.targetPower base meaning source.program,
      InternalPredicateQuantifier.precomposition meaning.predicates (base.map source.target) ≫
        meaning.existential source.source⟩
  | some origin =>
      ⟨RelativeClosedPositionedModal.Interpretation.targetProfiles base meaning
          (assay := (selected origin).frame.assay)
          (outgoing := (selected origin).frame.assay ⨯ source.program),
        RelativeClosedPredicateLogic.Interpretation.targetPower base meaning (selected origin).frame.carrier,
        RelativeClosedPositionedModal.Interpretation.modalityOperator base meaning
          (selected origin).frame.forget (selected origin).frame.focus
          (selected origin).frame.instantiate (selected origin).frame.outgoing⟩

theorem expected_source_read (origin : Option Index) :
    (RelativeClosedPredicateLogic.Interpretation.assignment base meaning).evaluateObject
        (RelativeClosedPositionedModalPresentation.domain source selected origin).code =
      some (expectedValue source selected base meaning origin).source := by
  cases origin with
  | none => exact RelativeClosedPredicateLogic.Interpretation.power_read base meaning source.program
  | some origin =>
      exact (RelativeClosedPredicateLogic.Interpretation.assignment base meaning).evaluate_product
        (RelativeClosedPredicateLogic.Interpretation.power_read base meaning (selected origin).frame.assay)
        (RelativeClosedPredicateLogic.Interpretation.power_read base meaning
          ((selected origin).frame.assay ⨯ source.program))

theorem expected_target_read (origin : Option Index) :
    (RelativeClosedPredicateLogic.Interpretation.assignment base meaning).evaluateObject
        (RelativeClosedPositionedModalPresentation.codomain source selected origin).code =
      some (expectedValue source selected base meaning origin).target := by
  cases origin with
  | none => exact RelativeClosedPredicateLogic.Interpretation.power_read base meaning source.program
  | some origin => exact RelativeClosedPredicateLogic.Interpretation.power_read base meaning (selected origin).frame.carrier

theorem expected_expression_read (origin : Option Index) :
    (RelativeClosedPredicateLogic.Interpretation.assignment base meaning).evaluateArrow
        (RelativeClosedPositionedModalPresentation.expression source selected origin).code =
      some (expectedValue source selected base meaning origin) := by
  cases origin with
  | none => exact RelativeClosedPositionedModal.Interpretation.possibility_read base meaning source.source source.target
  | some origin =>
      exact RelativeClosedPositionedModal.Interpretation.modality_read base meaning
        (selected origin).frame.forget (selected origin).frame.focus
        (selected origin).frame.instantiate (selected origin).frame.outgoing

variable (added : Option Index → RelativeClosedSyntax.Interpretation.ArrowValue D)

def arrowAssignment := ArrowExtension.extendAssignment
  (RelativeClosedPredicateLogic.Interpretation.lawfulAssignment base meaning) added

def assignment := EquationExtension.extendAssignment (Index := Option Index) (arrowAssignment source base meaning added)

def LocalAdmission : Prop :=
  ∀ origin, added origin = expectedValue source selected base meaning origin

theorem added_headers (admitted : LocalAdmission source selected base meaning added) :
    ArrowExtension.AddedAdmission (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))
      (RelativeClosedPositionedModalPresentation.arrowDeclaration source selected)
      (RelativeClosedPredicateLogic.Interpretation.lawfulAssignment base meaning) added where
  source origin := by
    rw [admitted origin]
    exact (EquationExtension.evaluate_object_original
      (RelativeClosedPredicateLogic.signature (C := source.closed.Obj)) RelativeClosedPredicateLogic.declaration
      (RelativeClosedPredicateLogic.Interpretation.assignment base meaning) _).trans
        (expected_source_read source selected base meaning origin)
  target origin := by
    rw [admitted origin]
    exact (EquationExtension.evaluate_object_original
      (RelativeClosedPredicateLogic.signature (C := source.closed.Obj)) RelativeClosedPredicateLogic.declaration
      (RelativeClosedPredicateLogic.Interpretation.assignment base meaning) _).trans
        (expected_target_read source selected base meaning origin)

theorem arrow_realized
    (old : RelativeClosedPredicateLogic.Interpretation.Admission base meaning)
    (admitted : LocalAdmission source selected base meaning added) :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
      (arrowAssignment source base meaning added) :=
  ArrowExtension.extended_realization (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))
    (RelativeClosedPositionedModalPresentation.arrowDeclaration source selected)
    (RelativeClosedPredicateLogic.Interpretation.lawfulAssignment base meaning) added
    (RelativeClosedPredicateLogic.Interpretation.lawful_realization base meaning old)
    (added_headers source selected base meaning added admitted)

theorem extended_expression_read (origin : Option Index) :
    (arrowAssignment source base meaning added).evaluateArrow
        (RelativeClosedPositionedModalPresentation.definingDeclaration source selected origin).right.code =
      some (expectedValue source selected base meaning origin) :=
  (ArrowExtension.evaluate_arrow_original
    (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))
    (RelativeClosedPositionedModalPresentation.arrowDeclaration source selected)
    (RelativeClosedPredicateLogic.Interpretation.lawfulAssignment base meaning) added _).trans
      ((EquationExtension.evaluate_arrow_original
        (RelativeClosedPredicateLogic.signature (C := source.closed.Obj)) RelativeClosedPredicateLogic.declaration
        (RelativeClosedPredicateLogic.Interpretation.assignment base meaning) _).trans
          (expected_expression_read source selected base meaning origin))

theorem declarations_satisfied
    (old : RelativeClosedPredicateLogic.Interpretation.Admission base meaning)
    (admitted : LocalAdmission source selected base meaning added) :
    EquationExtension.Satisfies (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
      (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
      (arrowAssignment source base meaning added)
      (arrow_realized source selected base meaning added old admitted) := by
  intro origin
  have first := RelativeClosedSyntax.Interpretation.functor_map_heq
    (arrowAssignment source base meaning added)
    (arrow_realized source selected base meaning added old admitted)
    (RelativeClosedPositionedModalPresentation.primitive source selected origin) (added origin).arrow rfl
  have second := RelativeClosedSyntax.Interpretation.functor_map_heq
    (arrowAssignment source base meaning added)
    (arrow_realized source selected base meaning added old admitted)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected origin).right
    (expectedValue source selected base meaning origin).arrow
    (extended_expression_read source selected base meaning added origin)
  exact eq_of_heq (first.trans
    ((RelativeClosedSyntax.Interpretation.ArrowValue.arrows_heq (admitted origin)).trans second.symm))

theorem realized
    (old : RelativeClosedPredicateLogic.Interpretation.Admission base meaning)
    (admitted : LocalAdmission source selected base meaning added) :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected)
      (assignment source base meaning added) :=
  EquationExtension.extended_realization
    (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
    (arrowAssignment source base meaning added)
    (arrow_realized source selected base meaning added old admitted)
    (declarations_satisfied source selected base meaning added old admitted)

theorem necessary_local
    (realized : RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected)
      (assignment source base meaning added)) :
    LocalAdmission source selected base meaning added := by
  intro origin
  obtain ⟨value, _, _, first, second⟩ := realized.equation (Sum.inr origin)
  have leftRead := (EquationExtension.evaluate_arrow_original
    (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
    (arrowAssignment source base meaning added)
    (RelativeClosedPositionedModalPresentation.primitive source selected origin).code).trans
      (show (arrowAssignment source base meaning added).evaluateArrow
        (RelativeClosedPositionedModalPresentation.primitive source selected origin).code = some (added origin) from rfl)
  have rightRead := (EquationExtension.evaluate_arrow_original
    (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
    (arrowAssignment source base meaning added)
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected origin).right.code).trans
      (extended_expression_read source selected base meaning added origin)
  exact Option.some.inj (leftRead.symm.trans (first.trans (second.symm.trans rightRead)))

theorem necessary_old
    (realized : RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected)
      (assignment source base meaning added)) :
    RelativeClosedPredicateLogic.Interpretation.Admission base meaning := by
  have arrowRealized := (RelativeClosedPositionedModalPresentation.definingInclusion source selected).realization_precompose
    (assignment source base meaning added) realized
  have actual : RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
      (arrowAssignment source base meaning added) := by
    have restricted := EquationExtension.restricted_assignment
      (RelativeClosedPositionedModalPresentation.arrowSignature source selected)
      (RelativeClosedPositionedModalPresentation.definingDeclaration source selected)
      (arrowAssignment source base meaning added)
    exact (congrArg (RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.arrowSignature source selected)) restricted).mp arrowRealized
  exact RelativeClosedPredicateLogic.Interpretation.necessary_admission base meaning
    (ArrowExtension.necessary_original (RelativeClosedPredicateLogic.lawfulSignature (C := source.closed.Obj))
      (RelativeClosedPositionedModalPresentation.arrowDeclaration source selected)
      (RelativeClosedPredicateLogic.Interpretation.lawfulAssignment base meaning) added actual)

theorem realization_iff_local :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected)
      (assignment source base meaning added) ↔
    RelativeClosedPredicateLogic.Interpretation.Admission base meaning ∧
      LocalAdmission source selected base meaning added :=
  ⟨fun actual => ⟨necessary_old source selected base meaning added actual,
      necessary_local source selected base meaning added actual⟩,
    fun admitted => realized source selected base meaning added admitted.1 admitted.2⟩

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalRealization
