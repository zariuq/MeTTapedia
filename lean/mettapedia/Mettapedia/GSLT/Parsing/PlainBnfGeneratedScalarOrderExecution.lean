import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderSyntax
import Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderDispatch
import Mettapedia.GSLT.Parsing.PlainBnfScalarOrderSource

/-!
# Executing the two actual scalar-order diagnostic clauses

Both raw and NativeType-selected workers are read from the full generated
definition inventory. Their provider calls execute original Integer bodies;
complementary comparisons select exactly one answer occurrence. The boundary
is the finite ground execution model, not import execution or C adequacy.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult bindAnswers)
open GeneratedPeTTaTemplateInstantiation (instantiate? instantiateList?)
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open PlainBnfGeneratedScalarOrderSyntax

def dataHeads : List String := ["ground-integer-less", "ground-integer-not-less", tag]

def localEnv (left right : Int) (origin : SExpr) : Bindings :=
  [("$right", encode (.atom (toString right))), ("$origin", encode origin),
    ("$left", encode (.atom (toString left)))]

def call (typed : Bool) (left right : Int) (origin : SExpr) : SExpr :=
  .list [.atom (symbol typed), .atom (toString left), .atom (toString right), origin]

def diagnostic (left right : Int) (origin : SExpr) : SExpr :=
  .list [.atom "BNFDiagnosticsConsV1",
    .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom (toString left),
      .atom (toString right), origin], .atom "BNFDiagnosticsNilV1"]

def result (payload : SExpr) : SExpr := .list [.atom tag, payload]

theorem provider_rows (i : Fin 4) :
    equationsFor (GeneratedPeTTaIntegerProviderDispatch.symbol i) program =
      [(823 + 2 * i.val, (GeneratedPeTTaIntegerProviderDispatch.row i).2)] := by
  rw [equationsFor_program]
  fin_cases i <;> rfl

theorem ordinary (typed : Bool) : reserved (symbol typed) = false := by cases typed <;> rfl

theorem symbol_not_variable (typed : Bool) : variableToken (symbol typed) = false := by
  cases typed <;> simp [symbol, variableToken]

theorem match_row (typed : Bool) (i : Fin 2) (left right : Int) (origin : SExpr) :
    matchEquation [] (call typed left right origin) (row typed i).2 = [localEnv left right origin] := by
  have lv : variableToken "$left" = true := by simp [variableToken]
  have rv : variableToken "$right" = true := by simp [variableToken]
  have ov : variableToken "$origin" = true := by simp [variableToken]
  simp [matchEquation, row_equation, bindResult, head_shape, call, symbol_not_variable,
    template, templates, lv, rv, ov, encode, encodeList, matchPattern, matchArgs,
    mergeBindings, List.foldlM, localEnv]

def providerIndex (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

/-- Exact equation occurrences consulted by this scalar kernel. This is a
condition on a target inventory, not an assumption that execution is correct.
Unrelated literal-headed definitions may be present. Result-tag inertness is
a separate caller condition. -/
structure ScalarInventory (targetProgram : List (Nat × SExpr)) : Prop where
  literal : ∀ entry ∈ targetProgram, LiteralEquationHead entry.2
  scalarRows : ∀ typed, equationsFor (symbol typed) targetProgram = rows typed
  integerRows : ∀ i : Fin 2,
    equationsFor (GeneratedPeTTaIntegerProviderDispatch.symbol (providerIndex i)) targetProgram =
      [(823 + 2 * i.val, (GeneratedPeTTaIntegerProviderDispatch.row (providerIndex i)).2)]

theorem actual_inventory : ScalarInventory program where
  literal := literal_heads
  scalarRows := equationsFor_rows
  integerRows i := provider_rows (providerIndex i)

theorem dispatch_exact (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram)
    (typed : Bool) (left right : Int) (origin : SExpr) :
    dispatch [] (call typed left right origin) targetProgram =
      [(row typed 0, localEnv left right origin), (row typed 1, localEnv left right origin)] := by
  unfold call
  rw [dispatch_literal_filter [] _ _ targetProgram inventory.literal]
  rw [inventory.scalarRows]
  change dispatch [] (call typed left right origin) (rows typed) = _
  rw [exact_rows]
  simp [dispatch, match_row]

theorem call_bodies (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram)
    (depth : Nat) (typed : Bool) (left right : Int) (origin : SExpr) :
    run depth targetProgram dataHeads (call typed left right origin) =
      collect (fun i => eval depth targetProgram dataHeads (localEnv left right origin) (body typed i))
        ([0, 1] : List (Fin 2)) := by
  have known : knownFunction targetProgram (symbol typed) = true := by
    unfold knownFunction
    rw [inventory.scalarRows, exact_rows]
    rfl
  have arity : hasArity targetProgram (symbol typed) 3 = true := by
    unfold hasArity
    rw [inventory.scalarRows, exact_rows]
    simp [row_equation, head_shape]
  unfold run runWith
  simp only [call, ordinary, known, arity, List.length_cons, List.length_nil,
    Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  change collect _ (dispatch [] (call typed left right origin) targetProgram) = _
  rw [dispatch_exact targetProgram inventory]
  simp [collect, row_equation]

def truth (i : Fin 2) (left right : Int) : Bool :=
  if i.val = 0 then decide (left < right) else decide (left ≥ right)

theorem provider_result (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram)
    (depth : Nat) (i : Fin 2) (left right : Int) :
    run (depth + 2) targetProgram dataHeads
      (GeneratedPeTTaIntegerProviderDispatch.call (providerIndex i) left right) =
      .complete (if truth i left right then
        [GeneratedPeTTaIntegerProviderDispatch.query (providerIndex i) left right] else []) := by
  rw [GeneratedPeTTaIntegerProviderDispatch.run_body_of_rows (depth + 2) targetProgram dataHeads
    (providerIndex i) left right (823 + 2 * i.val) inventory.literal (inventory.integerRows i)]
  rcases (show i = 0 ∨ i = 1 from by omega) with rfl | rfl
  · have shape : GeneratedPeTTaIntegerProviderDispatch.body (providerIndex 0) =
        .list [.atom "if", .list [.atom "<", .atom "$left", .atom "$right"],
          .list [.atom "quote", .list [.atom "ground-integer-less", .atom "$left", .atom "$right"]],
          .list [.atom "empty"]] := rfl
    rw [shape]
    apply conditional_quote_empty
    · simp [GeneratedPeTTaGroundCondition.condition?, GeneratedPeTTaIntegerProviderBridge.integer_left,
        GeneratedPeTTaIntegerProviderBridge.integer_right, truth]
    · exact GeneratedPeTTaIntegerProviderDispatch.query_template_closes 0 left right
  · have shape : GeneratedPeTTaIntegerProviderDispatch.body (providerIndex 1) =
        .list [.atom "if", .list [.atom ">=", .atom "$left", .atom "$right"],
          .list [.atom "quote", .list [.atom "ground-integer-not-less", .atom "$left", .atom "$right"]],
          .list [.atom "empty"]] := rfl
    rw [shape]
    apply conditional_quote_empty
    · simp [GeneratedPeTTaGroundCondition.condition?, GeneratedPeTTaIntegerProviderBridge.integer_left,
        GeneratedPeTTaIntegerProviderBridge.integer_right, truth]
    · exact GeneratedPeTTaIntegerProviderDispatch.query_template_closes 1 left right

theorem local_left (left right : Int) (origin : SExpr) :
    instantiate? (localEnv left right origin) (.atom "$left") = some (.atom (toString left)) := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable (by simp [variableToken])
  simp [localEnv]

theorem local_right (left right : Int) (origin : SExpr) :
    instantiate? (localEnv left right origin) (.atom "$right") = some (.atom (toString right)) := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable (by simp [variableToken])
  simp [localEnv]

theorem local_origin (left right : Int) (origin : SExpr) :
    instantiate? (localEnv left right origin) (.atom "$origin") = some origin := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable (by simp [variableToken])
  simp [localEnv]

theorem provider_call_in_body (targetProgram : List (Nat × SExpr))
    (depth : Nat) (i : Fin 2) (left right : Int) (origin : SExpr) :
    eval (depth + 3) targetProgram dataHeads (localEnv left right origin)
      (.list [.atom (GeneratedPeTTaIntegerProviderDispatch.symbol (providerIndex i)),
        .list [.atom (GeneratedPeTTaIntegerProviderDispatch.relation (providerIndex i)),
          .atom "$left", .atom "$right"]]) =
      run (depth + 2) targetProgram dataHeads
        (GeneratedPeTTaIntegerProviderDispatch.call (providerIndex i) left right) := by
  have templatesValid : dataTemplates dataHeads
      [.list [.atom (GeneratedPeTTaIntegerProviderDispatch.relation (providerIndex i)),
        .atom "$left", .atom "$right"]] = true := by fin_cases i <;> rfl
  have closed : instantiateList? (localEnv left right origin)
      [.list [.atom (GeneratedPeTTaIntegerProviderDispatch.relation (providerIndex i)),
        .atom "$left", .atom "$right"]] =
      some [GeneratedPeTTaIntegerProviderDispatch.query (providerIndex i) left right] := by
    have relationClosed : instantiate? (localEnv left right origin)
        (.atom (GeneratedPeTTaIntegerProviderDispatch.relation (providerIndex i))) =
        some (.atom (GeneratedPeTTaIntegerProviderDispatch.relation (providerIndex i))) := by
      simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom,
        GeneratedPeTTaIntegerProviderDispatch.relation_not_variable]
    simp [GeneratedPeTTaTemplateInstantiation.instantiateList_cons, relationClosed,
      local_left, local_right, GeneratedPeTTaIntegerProviderDispatch.query]
  have ordinaryProvider := GeneratedPeTTaIntegerProviderDispatch.symbol_ordinary (providerIndex i)
  rcases (show i = 0 ∨ i = 1 from by omega) with rfl | rfl
  all_goals
    rw [eval]
    change (if reserved (GeneratedPeTTaIntegerProviderDispatch.symbol _) ||
        !dataTemplates dataHeads _ then _ else _) = _
    rw [ordinaryProvider, templatesValid]
    simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, closed]
    rfl
  all_goals simp_all [reserved]

def clauseResult (i : Fin 2) (left right : Int) (origin : SExpr) : SExpr :=
  result (if i.val = 0 then .atom "BNFDiagnosticsNilV1" else diagnostic left right origin)

theorem ignored_guard (targetProgram : List (Nat × SExpr))
    (depth : Nat) (env : Bindings) (guard quoted value : SExpr)
    (guardAnswers : List SExpr) (selected : Bool)
    (completed : eval depth targetProgram dataHeads env guard =
      .complete (if selected then guardAnswers else []))
    (oneGuard : guardAnswers.length = 1)
    (quotedResult : eval depth targetProgram dataHeads env (.list [.atom "quote", quoted]) =
      .complete [value]) :
    eval (depth + 1) targetProgram dataHeads env
      (.list [.atom "let", .atom "$_", guard, .list [.atom "quote", quoted]]) =
      .complete (if selected then [value] else []) := by
  rw [let_complete depth targetProgram dataHeads env _ _ _ _ rfl completed]
  obtain ⟨witness, same⟩ := List.length_eq_one_iff.mp oneGuard
  subst guardAnswers
  cases selected <;> simp [bindAnswers, bindResult, quotedResult]

theorem body_result (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram) (depth : Nat) (typed : Bool) (i : Fin 2)
    (left right : Int) (origin : SExpr) :
    eval (depth + 4) targetProgram dataHeads (localEnv left right origin) (body typed i) =
      .complete (if truth i left right then [clauseResult i left right origin] else []) := by
  have provider := (provider_call_in_body targetProgram depth i left right origin).trans
    (provider_result targetProgram inventory depth i left right)
  rcases (show i = 0 ∨ i = 1 from by omega) with rfl | rfl
  · rw [first_body]
    apply ignored_guard targetProgram (depth + 3) _ _ _ _ [_] (truth 0 left right) provider rfl
    apply quote_exact
    simp [GeneratedPeTTaTemplateInstantiation.instantiateList_cons,
      GeneratedPeTTaTemplateInstantiation.instantiate_atom, variableToken,
      clauseResult, result, tag]
  · rw [second_body]
    apply ignored_guard targetProgram (depth + 3) _ _ _ _ [_] (truth 1 left right) provider rfl
    apply quote_exact
    have ordinaryAtom (token : String) (notVariable : variableToken token = false) :
        instantiate? (localEnv left right origin) (.atom token) = some (.atom token) := by
      simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, notVariable]
    simp [GeneratedPeTTaTemplateInstantiation.instantiateList_cons,
      ordinaryAtom tag (by simp [tag, variableToken]),
      ordinaryAtom "BNFDiagnosticsConsV1" (by simp [variableToken]),
      ordinaryAtom "BNFNonIncreasingLexicalScalarsV1" (by simp [variableToken]),
      ordinaryAtom "BNFDiagnosticsNilV1" (by simp [variableToken]), local_left, local_right, local_origin,
      clauseResult, result, diagnostic]

def answer (left right : Int) (origin : SExpr) : SExpr :=
  result (if left < right then .atom "BNFDiagnosticsNilV1" else diagnostic left right origin)

/-- The raw and selected workers each have precisely one completed answer
occurrence. Invalid Unicode values remain Integers here and yield ordering
diagnostics normally; Unicode membership is a different source relation. -/
theorem run_exact_in (targetProgram : List (Nat × SExpr))
    (inventory : ScalarInventory targetProgram)
    (depth : Nat) (typed : Bool) (left right : Int) (origin : SExpr) :
    run (depth + 4) targetProgram dataHeads (call typed left right origin) =
      .complete [answer left right origin] := by
  rw [call_bodies targetProgram inventory]
  simp only [collect, body_result targetProgram inventory]
  by_cases increasing : left < right
  · have notReverse : ¬left ≥ right := by omega
    simp [truth, increasing, notReverse, clauseResult, answer]
  · have reverse : left ≥ right := by omega
    simp [truth, increasing, reverse, clauseResult, answer]

theorem run_exact (depth : Nat) (typed : Bool) (left right : Int) (origin : SExpr) :
    run (depth + 4) program dataHeads (call typed left right origin) =
      .complete [answer left right origin] :=
  run_exact_in program actual_inventory depth typed left right origin

theorem raw_typed_same (depth : Nat) (left right : Int) (origin : SExpr) :
    run (depth + 4) program dataHeads (call true left right origin) =
      run (depth + 4) program dataHeads (call false left right origin) := by
  rw [run_exact, run_exact]

theorem completed_iff (depth : Nat) (typed : Bool) (left right : Int) (origin : SExpr)
    (answers : List SExpr) :
    run (depth + 4) program dataHeads (call typed left right origin) = .complete answers ↔
      answers = [answer left right origin] := by
  simp [run_exact, eq_comm]

/-- Finite binding/continuation replacement, with an arbitrary caller frame
and continuation. This is not early `once` over divergent or effectful calls. -/
theorem finite_caller_replacement (depth : Nat) (left right : Int) (origin : SExpr)
    (answers : List SExpr)
    (completed : run (depth + 4) program dataHeads (call true left right origin) = .complete answers)
    (env : Bindings) (schema : SExpr) (continuation : Bindings → List SExpr) :
    (bindAnswers env schema (answers.take 1)).flatMap continuation =
      (bindAnswers env schema answers).flatMap continuation := by
  have only := (completed_iff depth true left right origin answers).mp completed
  subst answers
  rfl

theorem schema_inert_in (targetProgram : List (Nat × SExpr))
    (noTagEquation : equationsFor tag targetProgram = []) (typed : Bool) :
    inertBinder targetProgram dataHeads (callerSchema typed) = true := by
  rw [caller_schema]
  simp only [inertBinder, knownFunction, noTagEquation]
  simp [inertBinders, inertBinder, dataHeads, reserved, tag]

theorem actual_schema_inert (typed : Bool) :
    inertBinder program dataHeads (callerSchema typed) = true :=
  schema_inert_in program result_tag_not_callable typed

/-- The generated second-let schemas are read from both actual callers.
This compares finite compatible bindings, not literal wrapper execution or
the renamed recursive continuations of the complete caller equations. -/
theorem actual_schema_finite_replacement (depth : Nat) (left right : Int) (origin : SExpr)
    (rawAnswers typedAnswers : List SExpr)
    (rawCompleted : run (depth + 4) program dataHeads (call false left right origin) =
      .complete rawAnswers)
    (typedCompleted : run (depth + 4) program dataHeads (call true left right origin) =
      .complete typedAnswers)
    (env : Bindings) (continuation : Bindings → List SExpr) :
    (bindAnswers env (callerSchema true) (typedAnswers.take 1)).flatMap continuation =
      (bindAnswers env (callerSchema false) rawAnswers).flatMap continuation := by
  have rawOnly := (completed_iff depth false left right origin rawAnswers).mp rawCompleted
  have typedOnly := (completed_iff depth true left right origin typedAnswers).mp typedCompleted
  subst rawAnswers
  subst typedAnswers
  rw [caller_schema, caller_schema]
  rfl

theorem actual_schema_preserves_frame (env next : Bindings) (answers : List SExpr)
    (typed : Bool) (name : String) (before : Pattern)
    (returned : next ∈ bindAnswers env (callerSchema typed) answers)
    (bound : env.find? (·.1 == name) = some (name, before)) :
    next.find? (·.1 == name) = some (name, before) :=
  GeneratedPeTTaResultBinding.bindAnswers_preserves_frame env (callerSchema typed)
    answers next returned name before bound

theorem answer_source_meaning (left right : Int) (origin : SExpr) :
    answer left right origin = result (PlainBnfScalarOrderSource.diagnostic left right origin) := by
  unfold answer PlainBnfScalarOrderSource.diagnostic diagnostic
  split <;> rfl

/-- Independent source-clause execution and actual generated body execution
agree on their whole finite ordered answer lists, including the result tag. -/
theorem source_execution_agreement (depth : Nat) (typed : Bool)
    (left right : Int) (origin : SExpr) :
    some (run (depth + 4) program dataHeads (call typed left right origin)) =
      (PlainBnfScalarOrderSource.sourceAnswers? left right origin).map
        (fun answers => Outcome.complete (answers.map result)) := by
  rw [run_exact, PlainBnfScalarOrderSource.sourceAnswers_eq, answer_source_meaning]
  rfl

theorem completed_source_iff (depth : Nat) (typed : Bool)
    (left right : Int) (origin : SExpr) (answers : List SExpr) :
    run (depth + 4) program dataHeads (call typed left right origin) = .complete answers ↔
      ∃ sourceAnswers, PlainBnfScalarOrderSource.sourceAnswers? left right origin = some sourceAnswers ∧
        answers = sourceAnswers.map result := by
  simp [run_exact, PlainBnfScalarOrderSource.sourceAnswers_eq, answer_source_meaning, eq_comm]

theorem increasing_control (typed : Bool) (origin : SExpr) :
    run 4 program dataHeads (call typed (-3) (-2) origin) =
      .complete [result (.atom "BNFDiagnosticsNilV1")] := by
  rw [show 4 = 0 + 4 from rfl, run_exact]
  simp [answer]

theorem equal_control (typed : Bool) (origin : SExpr) :
    run 4 program dataHeads (call typed 7 7 origin) =
      .complete [result (diagnostic 7 7 origin)] := by
  rw [show 4 = 0 + 4 from rfl, run_exact]
  simp [answer]

theorem equal_is_not_increasing (typed : Bool) :
    run 4 program dataHeads (call typed 7 7 (.atom "origin")) ≠
      .complete [result (.atom "BNFDiagnosticsNilV1")] := by
  rw [equal_control]
  simp [result, diagnostic]

#print axioms run_exact
#print axioms run_exact_in
#print axioms raw_typed_same
#print axioms finite_caller_replacement
#print axioms actual_schema_finite_replacement
#print axioms actual_schema_inert
#print axioms actual_schema_preserves_frame
#print axioms source_execution_agreement
#print axioms completed_source_iff

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderExecution
