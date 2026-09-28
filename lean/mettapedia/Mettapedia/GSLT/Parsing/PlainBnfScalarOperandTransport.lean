import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderExecution
import Mettapedia.GSLT.Parsing.PlainBnfInputCarrier

/-!
# Actual scalar-call operands across source and generated syntax

The selected source premise and generated callee are projected from the
original rule and compiled caller, not transcribed as replacement programs.
Their input substitution is simultaneous and preserves arbitrary origin data.
The final execution theorem uses the existing finite ground worker model.
This does not execute the surrounding collection/once wrappers or establish
native admission, source-reader normalization, or whole-caller scheduling.
The checked-input theorem extracts Integer values along the actual declared
constructor path and instantiates the worker theorem at their canonical value
image. It does not identify noncanonical Pattern atoms with native wire bytes.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfScalarOperandTransport

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open PlainBnfGeneratedScalarOrderSyntax
open PlainBnfGeneratedScalarOrderExecution

private theorem source_rows_length : PlainBnfScalarOrderSource.sourceRows.length = 67 := rfl

def sourceCons : Rewrite :=
  PlainBnfScalarOrderSource.sourceRows[35]'(by rw [source_rows_length]; decide)

theorem source_cons_occurrence :
    rawRewriteAt? PlainBnfScalarOrderSource.sourceSyntax 35 = some sourceCons := rfl

private theorem source_cons_body_length : sourceCons.body.length = 5 := rfl

def sourceOrderCall : SExpr := sourceCons.body[1]'(by rw [source_cons_body_length]; decide)

private def inputCall? : SExpr → Option SExpr
  | .list [relation, left, right, origin, _output] =>
      some (.list [relation, left, right, origin])
  | _ => none

private theorem source_inputs_present : (inputCall? sourceOrderCall).isSome = true := rfl

/-- Project the actual input mode 1110, without requiring an output binding. -/
def sourceInputs : SExpr := (inputCall? sourceOrderCall).get source_inputs_present

theorem source_order_call_shape : sourceOrderCall =
    .list [.atom PlainBnfScalarOrderSource.relation, .atom "?head", .atom "?next",
      .atom "?origin", .atom "?orderDiagnostics"] := rfl

theorem source_inputs_shape : sourceInputs =
    .list [.atom PlainBnfScalarOrderSource.relation, .atom "?head", .atom "?next",
      .atom "?origin"] := rfl

private def wrappedCallee? : SExpr → Option SExpr
  | .list [.atom "once", callee] => some callee
  | .list [.atom "superpose", .list [.atom "collapse", callee]] => some callee
  | _ => none

private theorem generated_callee_present (typed : Bool) :
    (wrappedCallee? (callerValue typed)).isSome = true := by cases typed <;> rfl

/-- Syntax projection only; this does not interpret either wrapper. -/
def generatedCallee (typed : Bool) : SExpr :=
  (wrappedCallee? (callerValue typed)).get (generated_callee_present typed)

theorem generated_callee_shape (typed : Bool) : generatedCallee typed =
    .list [.atom (symbol typed), .atom "$head", .atom "$next", .atom "$origin"] := by
  cases typed <;> rfl

theorem source_operand_transport (env : SourceSExprPatternInstantiation.Env)
    (left right : Int) (origin : SExpr)
    (first : SourceSExprPatternInstantiation.instantiate? env (.atom "?head") =
      some (.atom (toString left)))
    (second : SourceSExprPatternInstantiation.instantiate? env (.atom "?next") =
      some (.atom (toString right)))
    (location : SourceSExprPatternInstantiation.instantiate? env (.atom "?origin") = some origin) :
    SourceSExprPatternInstantiation.instantiate? env sourceInputs =
      some (.list [.atom PlainBnfScalarOrderSource.relation,
        .atom (toString left), .atom (toString right), origin]) := by
  rw [source_inputs_shape]
  have ordinary : SourceSExprPatternInstantiation.instantiate? env
      (.atom PlainBnfScalarOrderSource.relation) = some (.atom PlainBnfScalarOrderSource.relation) := by
    simp [SourceSExprPatternInstantiation.instantiate?, PlainBnfScalarOrderSource.relation,
      SourceIntegerProvider.sourceVariableToken]
  change (SExpr.list <$> SourceSExprPatternInstantiation.instantiateList? env _) = _
  simp only [SourceSExprPatternInstantiation.instantiateList?, ordinary, first, second, location]
  rfl

theorem generated_operand_transport (env : Bindings) (typed : Bool)
    (left right : Int) (origin : SExpr)
    (first : GeneratedPeTTaTemplateInstantiation.instantiate? env (.atom "$head") =
      some (.atom (toString left)))
    (second : GeneratedPeTTaTemplateInstantiation.instantiate? env (.atom "$next") =
      some (.atom (toString right)))
    (location : GeneratedPeTTaTemplateInstantiation.instantiate? env (.atom "$origin") = some origin) :
    GeneratedPeTTaTemplateInstantiation.instantiate? env (generatedCallee typed) =
      some (call typed left right origin) := by
  rw [generated_callee_shape]
  have ordinary : GeneratedPeTTaTemplateInstantiation.instantiate? env (.atom (symbol typed)) =
      some (.atom (symbol typed)) := by
    simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, symbol_not_variable]
  simp [GeneratedPeTTaTemplateInstantiation.instantiateList_cons,
    ordinary, first, second, location, call]

/-- A successfully instantiated actual callee executes the independent source
answer list. The operand premises are explicit canonical-value facts, not
claims that arbitrary source token spellings have already been normalized. -/
theorem generated_callee_source_agreement (depth : Nat) (env : Bindings) (typed : Bool)
    (left right : Int) (origin : SExpr)
    (first : GeneratedPeTTaTemplateInstantiation.instantiate? env (.atom "$head") =
      some (.atom (toString left)))
    (second : GeneratedPeTTaTemplateInstantiation.instantiate? env (.atom "$next") =
      some (.atom (toString right)))
    (location : GeneratedPeTTaTemplateInstantiation.instantiate? env (.atom "$origin") = some origin) :
    (GeneratedPeTTaTemplateInstantiation.instantiate? env (generatedCallee typed)).map
      (GeneratedPeTTaGroundExecution.run (depth + 4) program dataHeads) =
    (PlainBnfScalarOrderSource.sourceAnswers? left right origin).map
      (fun answers => GeneratedPeTTaGroundExecution.Outcome.complete (answers.map result)) := by
  rw [generated_operand_transport env typed left right origin first second location]
  exact source_execution_agreement depth typed left right origin

/-- The canonical target value image of native signed integers. This defines
the selected representation relation; it is not a proof of a C printer. -/
def signedValue (value : Int64) : SExpr := .atom (toString value.toInt)

theorem signed_value_source_integer (value : Int64) :
    SourceIntegerProvider.integerValue? (toString value.toInt) = some value.toInt :=
  SourceIntegerProvider.integerValue?_repr value.toInt

theorem signed_worker_source_agreement (depth : Nat) (typed : Bool)
    (left right : Int64) (origin : SExpr) :
    some (GeneratedPeTTaGroundExecution.run (depth + 4) program dataHeads
      (.list [.atom (symbol typed), signedValue left, signedValue right, origin])) =
    (PlainBnfScalarOrderSource.sourceAnswers? left.toInt right.toInt origin).map
      (fun answers => GeneratedPeTTaGroundExecution.Outcome.complete (answers.map result)) :=
  source_execution_agreement depth typed left.toInt right.toInt origin

/-- Every structurally checked selected pair supplies actual Integer values
for the independent source and generated-worker theorem. The origin wire is
an arbitrary shared opaque observation: this statement does not define a
physical codec for the input Pattern or execute the surrounding call path. -/
theorem checked_pair_source_agreement {input left right origin : Pattern}
    {declarationOccurrence scalarPosition : Nat}
    (checked : PlainBnfInputCarrier.Checked input "BnfGrammarInput")
    (selected : PlainBnfInputCarrier.InputScalarPair input
      declarationOccurrence scalarPosition left right origin)
    (originWire : SExpr) :
    ∃ leftToken rightToken leftValue rightValue,
      left = .apply leftToken [] ∧ right = .apply rightToken [] ∧
      leftToken.toInt? = some leftValue ∧ rightToken.toInt? = some rightValue ∧
      PlainBnfInputCarrier.Checked origin "BnfLexicalOrigin" ∧
      SourceIntegerProvider.integerValue? (toString leftValue) = some leftValue ∧
      SourceIntegerProvider.integerValue? (toString rightValue) = some rightValue ∧
      ∀ depth typed,
        some (GeneratedPeTTaGroundExecution.run (depth + 4) program dataHeads
          (call typed leftValue rightValue originWire)) =
        (PlainBnfScalarOrderSource.sourceAnswers? leftValue rightValue originWire).map
          (fun answers => GeneratedPeTTaGroundExecution.Outcome.complete (answers.map result)) := by
  obtain ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed⟩ :=
    PlainBnfInputCarrier.input_pair_integer_values checked selected
  exact ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed,
    (PlainBnfInputCarrier.input_pair_checked checked selected).2.2,
    SourceIntegerProvider.integerValue?_repr leftValue,
    SourceIntegerProvider.integerValue?_repr rightValue,
    fun depth typed => source_execution_agreement depth typed leftValue rightValue originWire⟩

/-- The same extracted values license finite answer-occurrence replacement
at the actual caller schemas. This still assumes completed worker observations;
it is not a theorem interpreting the literal early-stopping wrappers. -/
theorem checked_pair_finite_binding {input left right origin : Pattern}
    {declarationOccurrence scalarPosition : Nat}
    (checked : PlainBnfInputCarrier.Checked input "BnfGrammarInput")
    (selected : PlainBnfInputCarrier.InputScalarPair input
      declarationOccurrence scalarPosition left right origin)
    (originWire : SExpr) :
    ∃ leftToken rightToken leftValue rightValue,
      left = .apply leftToken [] ∧ right = .apply rightToken [] ∧
      leftToken.toInt? = some leftValue ∧ rightToken.toInt? = some rightValue ∧
      ∀ depth rawAnswers typedAnswers,
        GeneratedPeTTaGroundExecution.run (depth + 4) program dataHeads
          (call false leftValue rightValue originWire) = .complete rawAnswers →
        GeneratedPeTTaGroundExecution.run (depth + 4) program dataHeads
          (call true leftValue rightValue originWire) = .complete typedAnswers →
        ∀ (env : Bindings) (continuation : Bindings → List SExpr),
          (GeneratedPeTTaResultBinding.bindAnswers env (callerSchema true)
            (typedAnswers.take 1)).flatMap continuation =
          (GeneratedPeTTaResultBinding.bindAnswers env (callerSchema false)
            rawAnswers).flatMap continuation := by
  obtain ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed⟩ :=
    PlainBnfInputCarrier.input_pair_integer_values checked selected
  exact ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed,
    fun depth rawAnswers typedAnswers rawCompleted typedCompleted env continuation =>
      actual_schema_finite_replacement depth leftValue rightValue originWire
        rawAnswers typedAnswers rawCompleted typedCompleted env continuation⟩

#print axioms source_operand_transport
#print axioms generated_operand_transport
#print axioms generated_callee_source_agreement
#print axioms signed_worker_source_agreement
#print axioms checked_pair_source_agreement
#print axioms checked_pair_finite_binding

end Mettapedia.GSLT.Parsing.PlainBnfScalarOperandTransport
