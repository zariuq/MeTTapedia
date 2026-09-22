import Mettapedia.GSLT.Parsing.PlainBnfScalarOperandTransport

/-!
# Actual scalar caller control under finite ground execution

The raw source literal `superpose(collapse(CALL))` has two alternatives:
the atom `collapse`, and CALL. This is the literal-list branch in PeTTa's
translator, not findall followed by member. The actual inert result tag
rejects the atom. Only after that filtering does it agree with the selected
single-answer worker and its typed once wrapper.

This extends the preceding finite ground observation, not full PeTTa effects,
infinite streams, native scheduling, or the caller's renamed recursive body.
Constraint-first binding is connected by the existing zero-or-one-occurrence
law, never by assuming once commutes with arbitrary result constraints.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarCallerExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaGroundExecution
open GeneratedPeTTaTemplateInstantiation
open GeneratedPeTTaResultBinding (bindResult bindAnswers)
open PlainBnfGeneratedScalarOrderSyntax
open PlainBnfGeneratedScalarOrderExecution
open PlainBnfScalarOperandTransport

theorem raw_wrapper : callerValue false =
    .list [.atom "superpose", .list [.atom "collapse", generatedCallee false]] := by
  rw [raw_caller_value, generated_callee_shape]

theorem typed_wrapper : callerValue true =
    .list [.atom "once", generatedCallee true] := by
  rw [typed_caller_value, generated_callee_shape]

theorem callee_eval (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram) (depth : Nat) (env : Bindings) (typed : Bool)
    (left right : Int) (origin : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 5) targetProgram dataHeads env (generatedCallee typed) =
      .complete [answer left right origin] := by
  rw [generated_callee_shape, eval]
  · simp only [ordinary, dataTemplates, dataTemplate, Bool.and_self,
      Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      instantiateList_cons, instantiateList_nil, first, second, location]
    exact run_exact_in targetProgram inventory depth typed left right origin
  all_goals cases typed <;> simp [symbol]

theorem raw_value (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram)
    (depth : Nat) (env : Bindings) (left right : Int) (origin : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 6) targetProgram dataHeads env (callerValue false) =
      .complete [.atom "collapse", answer left right origin] := by
  rw [raw_wrapper, literal_superpose]
  have atomResult : eval (depth + 5) targetProgram dataHeads env (.atom "collapse") =
      .complete [.atom "collapse"] := by
    apply atom_exact
    simp [instantiate_atom, GeneratedPeTTaResultBinding.variableToken]
  simp [collect, atomResult,
    callee_eval targetProgram inventory depth env false left right origin first second location]

theorem typed_value (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram)
    (depth : Nat) (env : Bindings) (left right : Int) (origin : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 6) targetProgram dataHeads env (callerValue true) =
      .complete [answer left right origin] := by
  rw [typed_wrapper, once_complete (depth + 5) targetProgram dataHeads env _ _
    (by simp)
    (callee_eval targetProgram inventory depth env true left right origin first second location)]
  rfl

theorem result_schema_rejects_atom (env : Bindings) (typed : Bool) (token : String) :
    bindResult env (callerSchema typed) (.atom token) = [] := by
  rw [caller_schema]
  simp [bindResult, GeneratedPeTTaResultBinding.template, SourceSExprPatternCodec.encode,
    matchPattern]

theorem result_schema_filters_atom (env : Bindings) (typed : Bool)
    (token : String) (answers : List SExpr) :
    bindAnswers env (callerSchema typed) (.atom token :: answers) =
      bindAnswers env (callerSchema typed) answers := by
  simp [bindAnswers, result_schema_rejects_atom]

/-- The values differ; it is the actual result-pattern observation that
removes the extra alternative. No output-variable freshness is assumed. -/
theorem bound_values_equal (env : Bindings) (left right : Int) (origin : SExpr) :
    bindAnswers env (callerSchema false) [.atom "collapse", answer left right origin] =
      bindAnswers env (callerSchema true) [answer left right origin] := by
  rw [result_schema_filters_atom, caller_schema, caller_schema]

theorem actual_let_same_continuation_in (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram)
    (noTagEquation : GeneratedPeTTaEquationDispatch.equationsFor tag targetProgram = [])
    (depth : Nat) (env : Bindings)
    (left right : Int) (origin continuation : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 7) targetProgram dataHeads env
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) targetProgram dataHeads env
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) := by
  rw [let_complete (depth + 6) targetProgram dataHeads env _ _ _ _
      (schema_inert_in targetProgram noTagEquation false)
      (raw_value targetProgram inventory depth env left right origin first second location),
    let_complete (depth + 6) targetProgram dataHeads env _ _ _ _
      (schema_inert_in targetProgram noTagEquation true)
      (typed_value targetProgram inventory depth env left right origin first second location),
    bound_values_equal]

theorem actual_let_same_continuation (depth : Nat) (env : Bindings)
    (left right : Int) (origin continuation : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) :=
  actual_let_same_continuation_in program actual_inventory result_tag_not_callable
    depth env left right origin continuation first second location

/-- Moving result constraints before the selected once is justified by
one worker answer occurrence, not by the two-answer raw wrapper. -/
theorem constraint_first_once (env : Bindings) (left right : Int) (origin : SExpr) :
    (bindAnswers env (callerSchema true) [answer left right origin]).take 1 =
      bindAnswers env (callerSchema false) [.atom "collapse", answer left right origin] := by
  rw [← GeneratedPeTTaResultBinding.semidet_binding_once env (callerSchema true)
    [answer left right origin] (by simp)]
  simpa using (bound_values_equal env left right origin).symm

/-- The canonical value image at this selected call site, not a new physical
input codec or an evaluation of the preceding recursive caller. -/
def callerEnv (left right : Int) (origin : SExpr) : Bindings :=
  [("$head", SourceSExprPatternCodec.encode (.atom (toString left))),
   ("$next", SourceSExprPatternCodec.encode (.atom (toString right))),
   ("$origin", SourceSExprPatternCodec.encode origin)]

theorem canonical_caller_execution (depth : Nat) (left right : Int)
    (origin continuation : SExpr) :
    eval (depth + 7) program dataHeads (callerEnv left right origin)
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) program dataHeads (callerEnv left right origin)
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) := by
  apply actual_let_same_continuation depth _ left right origin continuation
  all_goals simp [callerEnv, instantiate_atom, GeneratedPeTTaResultBinding.variableToken]

/-- The actual checked declaration path supplies Integer witnesses for the
literal caller theorem. Source aliases are not assumed to be canonical: the
execution is explicitly at their canonical value image and shared origin wire. -/
theorem checked_pair_caller_execution {input left right origin : Pattern}
    {declarationOccurrence scalarPosition : Nat}
    (checked : PlainBnfInputCarrier.Checked input "BnfGrammarInput")
    (selected : PlainBnfInputCarrier.InputScalarPair input
      declarationOccurrence scalarPosition left right origin)
    (originWire : SExpr) :
    ∃ leftToken rightToken leftValue rightValue,
      left = .apply leftToken [] ∧ right = .apply rightToken [] ∧
      leftToken.toInt? = some leftValue ∧ rightToken.toInt? = some rightValue ∧
      ∀ depth continuation,
        eval (depth + 7) program dataHeads (callerEnv leftValue rightValue originWire)
          (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
        eval (depth + 7) program dataHeads (callerEnv leftValue rightValue originWire)
          (.list [.atom "let", callerSchema true, callerValue true, continuation]) := by
  obtain ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed⟩ :=
    PlainBnfInputCarrier.input_pair_integer_values checked selected
  exact ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed,
    fun depth continuation => canonical_caller_execution depth leftValue rightValue
      originWire continuation⟩

theorem unwrapped_values_differ (left right : Int) (origin : SExpr) :
    ([.atom "collapse", answer left right origin] : List SExpr) ≠
      [answer left right origin] := by
  intro same
  have lengths := congrArg List.length same
  simp at lengths

theorem ignored_schema_does_not_filter (env : Bindings) (value : SExpr) :
    bindAnswers env (.atom "$_") [.atom "collapse", value] ≠
      bindAnswers env (.atom "$_") [value] := by
  simp [bindAnswers, bindResult]

#print axioms raw_value
#print axioms typed_value
#print axioms actual_let_same_continuation
#print axioms actual_let_same_continuation_in
#print axioms constraint_first_once
#print axioms checked_pair_caller_execution

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarCallerExecution
