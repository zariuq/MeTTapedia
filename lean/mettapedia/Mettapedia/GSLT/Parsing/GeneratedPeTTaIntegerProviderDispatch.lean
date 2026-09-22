import Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderExecution
import Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaDispatch

/-!
# Full-fixture dispatch for the actual generated Integer providers

The four rows are retrieved from the existing generated component fixture.
Their full-arity ground calls select exactly the original equation and fresh
Integer bindings. The existing body-execution theorem then applies to whole
calls. Mathematical integers, the frozen fixture and selected execution model
remain explicit; this is not installed-runtime or machine-overflow adequacy.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderDispatch

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult)
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open GeneratedPeTTaIntegerProviderBridge (targetEnv sourceEnv sourceSides? targetSides?)
open PlainBnfGeneratedPeTTaSyntax (generatedProgram)

def providerRows : List (Nat × SExpr) :=
  generatedProgram.filter (fun row => GeneratedPeTTaIntegerProviderBridge.isIntegerProvider row.2)

theorem providerRows_count : providerRows.length = 4 := rfl

def row (occurrence : Fin 4) : Nat × SExpr :=
  providerRows[occurrence.val]'(by rw [providerRows_count]; exact occurrence.isLt)

private theorem row_is_equation (occurrence : Fin 4) : (equation? (row occurrence).2).isSome = true := by
  fin_cases occurrence <;> rfl

def head (occurrence : Fin 4) : SExpr :=
  ((equation? (row occurrence).2).get (row_is_equation occurrence)).1

def body (occurrence : Fin 4) : SExpr :=
  ((equation? (row occurrence).2).get (row_is_equation occurrence)).2

def symbol (occurrence : Fin 4) : String :=
  (equationSymbol? (row occurrence).2).get (by fin_cases occurrence <;> rfl)

def querySymbol? (source : SExpr) : Option String := do
  let (.list [.atom _, .list (.atom name :: _)], _) ← equation? source | none
  return name

def relation (occurrence : Fin 4) : String :=
  (querySymbol? (row occurrence).2).get (by fin_cases occurrence <;> rfl)

def query (occurrence : Fin 4) (left right : Int) : SExpr :=
  .list [.atom (relation occurrence), .atom (toString left), .atom (toString right)]

def call (occurrence : Fin 4) (left right : Int) : SExpr :=
  .list [.atom (symbol occurrence), query occurrence left right]

theorem row_equation (occurrence : Fin 4) :
    equation? (row occurrence).2 = some (head occurrence, body occurrence) := by
  fin_cases occurrence <;> rfl

theorem target_sides (occurrence : Fin 4) :
    targetSides? occurrence = some (head occurrence, body occurrence) := by
  fin_cases occurrence <;> rfl

theorem head_shape (occurrence : Fin 4) :
    head occurrence = .list [.atom (symbol occurrence),
      .list [.atom (relation occurrence), .atom "$left", .atom "$right"]] := by
  fin_cases occurrence <;> rfl

theorem source_row_lines : providerRows.map Prod.fst = [717, 719, 721, 723] := rfl

private theorem provider_rows_exact (occurrence : Fin 4) :
    equationsFor (symbol occurrence) providerRows = [row occurrence] := by
  fin_cases occurrence <;> rfl

private theorem symbol_prefix (occurrence : Fin 4) :
    ((symbol occurrence).toList.take 20 == "gslt:ground-integer-".toList) = true := by
  fin_cases occurrence <;> rfl

private theorem matching_symbol_is_provider (occurrence : Fin 4) (source : SExpr)
    (same : equationSymbol? source = some (symbol occurrence)) :
    GeneratedPeTTaIntegerProviderBridge.isIntegerProvider source = true := by
  cases parsed : equation? source with
  | none => simp [equationSymbol?, parsed] at same
  | some pair =>
    rcases pair with ⟨lhs, rhs⟩
    have shape := (equation?_eq_some_iff source lhs rhs).mp parsed
    subst source
    cases lhs with
    | atom token => simp [equationSymbol?, equation?] at same
    | list terms =>
      cases terms with
      | nil => simp [equationSymbol?, equation?] at same
      | cons first rest =>
        cases first with
        | list terms => simp [equationSymbol?, equation?] at same
        | atom actual =>
          have equal : actual = symbol occurrence := by simpa [equationSymbol?, equation?] using same
          subst actual
          exact symbol_prefix occurrence

theorem whole_provider_rows (occurrence : Fin 4) :
    equationsFor (symbol occurrence) generatedProgram = [row occurrence] := by
  have retained : equationsFor (symbol occurrence) providerRows =
      equationsFor (symbol occurrence) generatedProgram := by
    unfold equationsFor providerRows
    rw [List.filter_filter]
    apply List.filter_congr
    intro actual _
    by_cases same : equationSymbol? actual.2 = some (symbol occurrence)
    · simp [same, matching_symbol_is_provider occurrence actual.2 same]
    · simp [same]
  exact retained.symm.trans (provider_rows_exact occurrence)

theorem symbol_not_variable (occurrence : Fin 4) : variableToken (symbol occurrence) = false := by
  fin_cases occurrence
  · change variableToken "gslt:ground-integer-less" = false
    simp [variableToken]
  · change variableToken "gslt:ground-integer-not-less" = false
    simp [variableToken]
  · change variableToken "gslt:ground-integer-gap" = false
    simp [variableToken]
  · change variableToken "gslt:ground-integer-no-gap" = false
    simp [variableToken]

theorem relation_not_variable (occurrence : Fin 4) : variableToken (relation occurrence) = false := by
  fin_cases occurrence
  · change variableToken "ground-integer-less" = false
    simp [variableToken]
  · change variableToken "ground-integer-not-less" = false
    simp [variableToken]
  · change variableToken "ground-integer-gap" = false
    simp [variableToken]
  · change variableToken "ground-integer-no-gap" = false
    simp [variableToken]

theorem symbol_ordinary (occurrence : Fin 4) : reserved (symbol occurrence) = false := by
  fin_cases occurrence <;> rfl

theorem symbol_known (occurrence : Fin 4) : knownFunction generatedProgram (symbol occurrence) = true := by
  simp [knownFunction, whole_provider_rows]

/-- One structured relation argument is the provider's full outer arity;
the relation's two operands are checked by ordinary structural matching. -/
theorem symbol_arity (occurrence : Fin 4) (arity : Nat) :
    hasArity generatedProgram (symbol occurrence) arity = (arity == 1) := by
  simp [hasArity, whole_provider_rows, row_equation, head_shape, eq_comm]

theorem dispatch_provider_rows (occurrence : Fin 4) (arguments : List SExpr) :
    dispatch [] (.list (.atom (symbol occurrence) :: arguments)) generatedProgram =
      dispatch [] (.list (.atom (symbol occurrence) :: arguments)) [row occurrence] := by
  rw [PlainBnfGeneratedPeTTaDispatch.generated_dispatch_filter, whole_provider_rows]

theorem match_row (occurrence : Fin 4) (left right : Int) :
    matchEquation [] (call occurrence left right) (row occurrence).2 = [targetEnv left right] := by
  have leftVariable : variableToken "$left" = true := by simp [variableToken]
  have rightVariable : variableToken "$right" = true := by simp [variableToken]
  simp [matchEquation, row_equation, bindResult, head_shape, call, query,
    template, templates, symbol_not_variable, relation_not_variable, leftVariable, rightVariable,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, targetEnv]

theorem dispatch_exact (occurrence : Fin 4) (left right : Int) :
    dispatch [] (call occurrence left right) generatedProgram =
      [(row occurrence, targetEnv left right)] := by
  unfold call
  rw [dispatch_provider_rows]
  change dispatch [] (call occurrence left right) [row occurrence] = _
  simp [dispatch, match_row]

theorem run_body (depth : Nat) (occurrence : Fin 4) (left right : Int) :
    run depth generatedProgram [] (call occurrence left right) =
      eval depth generatedProgram [] (targetEnv left right) (body occurrence) := by
  exact call_single_match depth generatedProgram [] (symbol occurrence) [query occurrence left right]
    (row occurrence) (targetEnv left right) (head occurrence) (body occurrence)
    (symbol_ordinary occurrence) (symbol_known occurrence)
    (by simp [symbol_arity]) (dispatch_exact occurrence left right) (row_equation occurrence)

/-- The exact source empty/singleton answer list is now connected to a whole
call against all original generated equations, not only a supplied body. -/
theorem actual_call_execution (depth : Nat) (occurrence : Fin 4) (left right : Int) :
    some (run (depth + 2) generatedProgram [] (call occurrence left right)) =
      ((sourceSides? occurrence).bind (fun sides =>
        SourceIntegerProvider.evalAnswers? (sourceEnv left right) sides.2)).map Outcome.complete := by
  rw [run_body]
  have executed := GeneratedPeTTaIntegerProviderExecution.actual_body_execution depth occurrence left right
  simpa only [target_sides, Option.map_some] using executed

theorem completed_call_iff (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (answers : List SExpr) :
    run (depth + 2) generatedProgram [] (call occurrence left right) = .complete answers ↔
      ∃ sourceHead sourceBody, sourceSides? occurrence = some (sourceHead, sourceBody) ∧
        SourceIntegerProvider.AnswersEval (sourceEnv left right) sourceBody answers := by
  rw [run_body]
  have equivalent := GeneratedPeTTaIntegerProviderExecution.completed_body_iff depth occurrence left right answers
  simpa only [target_sides, Option.map_some, Option.some.injEq] using equivalent

theorem completed_call_at_most_one (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (answers : List SExpr)
    (completed : run (depth + 2) generatedProgram [] (call occurrence left right) = .complete answers) :
    answers.length ≤ 1 := by
  obtain ⟨_, _, _, sourceExecution⟩ := (completed_call_iff depth occurrence left right answers).mp completed
  exact sourceExecution.at_most_one

theorem duplicate_dispatch (occurrence : Fin 4) (left right : Int) :
    dispatch [] (call occurrence left right) (generatedProgram ++ [row occurrence]) =
      [(row occurrence, targetEnv left right), (row occurrence, targetEnv left right)] := by
  rw [dispatch_append, dispatch_exact]
  simp [dispatch, match_row]

private theorem duplicate_rows (occurrence : Fin 4) :
    equationsFor (symbol occurrence) (generatedProgram ++ [row occurrence]) =
      [row occurrence, row occurrence] := by
  simp only [equationsFor, List.filter_append]
  change equationsFor (symbol occurrence) generatedProgram ++
    equationsFor (symbol occurrence) [row occurrence] = _
  rw [whole_provider_rows]
  simp [equationsFor, equationSymbol?, row_equation, head_shape]

/-- The actual provider bodies contain no ordinary call or binding operation;
their arithmetic condition and quote/empty branches do not consult a program. -/
theorem body_program_independent (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (program : List (Nat × SExpr)) (dataHeads : List String) :
    eval (depth + 2) program dataHeads (targetEnv left right) (body occurrence) =
      eval (depth + 2) generatedProgram [] (targetEnv left right) (body occurrence) := by
  obtain ⟨_, _, _, guard, _, echo, _, targetShape⟩ :=
    GeneratedPeTTaIntegerProviderBridge.actual_body_shapes occurrence
  have exactBody : body occurrence =
      .list [.atom "if", guard, .list [.atom "quote", echo], .list [.atom "empty"]] := by
    exact congrArg Prod.snd (Option.some.inj ((target_sides occurrence).symm.trans targetShape))
  rw [exactBody]
  cases selected : GeneratedPeTTaGroundCondition.condition? (targetEnv left right) guard with
  | none => simp [eval, selected]
  | some truth => cases truth <;> simp [eval, selected]

/-- Duplicating the original equation duplicates its completed answer stream,
even though the copied occurrence computes exactly the same values. -/
theorem duplicate_completed_call (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (answers : List SExpr)
    (completed : run (depth + 2) generatedProgram [] (call occurrence left right) = .complete answers) :
    run (depth + 2) (generatedProgram ++ [row occurrence]) [] (call occurrence left right) =
      .complete (answers ++ answers) := by
  have known : knownFunction (generatedProgram ++ [row occurrence]) (symbol occurrence) = true := by
    simp [knownFunction, duplicate_rows]
  have arity : hasArity (generatedProgram ++ [row occurrence]) (symbol occurrence) 1 = true := by
    simp [hasArity, duplicate_rows, row_equation, head_shape]
  have executed : eval (depth + 2) generatedProgram [] (targetEnv left right) (body occurrence) =
      .complete answers := by simpa only [run_body] using completed
  unfold run runWith
  simp only [call, symbol_ordinary, known, arity, List.length_cons, List.length_nil,
    Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  change collect _ (dispatch [] (call occurrence left right) (generatedProgram ++ [row occurrence])) = _
  rw [duplicate_dispatch]
  simp [collect, row_equation, body_program_independent, executed]

theorem duplicate_success_does_not_license_once (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (value : SExpr)
    (completed : run (depth + 2) generatedProgram [] (call occurrence left right) = .complete [value]) :
    run (depth + 2) (generatedProgram ++ [row occurrence]) [] (call occurrence left right) =
      .complete [value, value] ∧ [value, value] ≠ [value, value].take 1 := by
  constructor
  · simpa using duplicate_completed_call depth occurrence left right [value] completed
  · simp

theorem unsupported_outer_arity (depth : Nat) (occurrence : Fin 4) (arguments : List SExpr)
    (different : arguments.length ≠ 1) :
    run depth generatedProgram [] (.list (.atom (symbol occurrence) :: arguments)) = .outsideFragment := by
  apply unsupported_arity_outside
  simp [symbol_arity, different]

theorem symbols_injective : Function.Injective symbol := by
  apply List.nodup_ofFn.mp
  change (["gslt:ground-integer-less", "gslt:ground-integer-not-less",
    "gslt:ground-integer-gap", "gslt:ground-integer-no-gap"] : List String).Nodup
  decide

theorem other_provider_does_not_match (occurrence other : Fin 4) (different : occurrence ≠ other)
    (left right : Int) : matchEquation [] (call occurrence left right) (row other).2 = [] := by
  apply other_literal_equation_does_not_match [] (symbol occurrence) [query occurrence left right]
  · intro lhs rhs parsed
    have same := Option.some.inj ((row_equation other).symm.trans parsed)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨symbol other, [.list [.atom (relation other), .atom "$left", .atom "$right"]],
      head_shape other, symbol_not_variable other⟩
  · have symbolOf : equationSymbol? (row other).2 = some (symbol other) := by
      simp [equationSymbol?, row_equation, head_shape]
    rw [symbolOf]
    simp only [ne_eq, Option.some.injEq]
    exact fun equal => different (symbols_injective equal).symm

private theorem dispatch_filter_rows (env : Bindings) (queryTerm : SExpr)
    (rows : List (Nat × SExpr)) (keep : (Nat × SExpr) → Bool) :
    dispatch env queryTerm (rows.filter keep) =
      (dispatch env queryTerm rows).filter (fun matched => keep matched.1) := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
    simp only [dispatch] at ih ⊢
    cases kept : keep first <;>
      simp [kept, ih, List.filter_map, Function.comp_def]

/-- A mutation removes the selected physical equation row from the complete
fixture. The original fixture has exactly one row at that source position. -/
def withoutRow (occurrence : Fin 4) : List (Nat × SExpr) :=
  generatedProgram.filter (fun actual => actual.1 != (row occurrence).1)

theorem removed_row_exact (occurrence : Fin 4) :
    generatedProgram.filter (fun actual => actual.1 == (row occurrence).1) = [row occurrence] := by
  fin_cases occurrence <;> rfl

theorem missing_row_dispatch (occurrence : Fin 4) (left right : Int) :
    dispatch [] (call occurrence left right) (withoutRow occurrence) = [] := by
  rw [withoutRow, dispatch_filter_rows, dispatch_exact]
  simp

theorem missing_row_equations (occurrence : Fin 4) :
    equationsFor (symbol occurrence) (withoutRow occurrence) = [] := by
  have commutes : equationsFor (symbol occurrence) (withoutRow occurrence) =
      (equationsFor (symbol occurrence) generatedProgram).filter
        (fun actual => actual.1 != (row occurrence).1) := by
    simp [withoutRow, equationsFor, List.filter_filter, Bool.and_comm]
  rw [commutes, whole_provider_rows]
  simp

/-- Removing the only provider makes that function unknown to the selected
model; it is not misreported as a completed logical rejection. -/
theorem missing_row_outside (depth : Nat) (occurrence : Fin 4) (left right : Int) :
    run depth (withoutRow occurrence) [] (call occurrence left right) = .outsideFragment := by
  simp [run, runWith, call, knownFunction, missing_row_equations]

theorem missing_inner_operand_dispatch (occurrence : Fin 4) (left : SExpr) :
    dispatch [] (.list [.atom (symbol occurrence), .list [.atom (relation occurrence), left]])
      generatedProgram = [] := by
  rw [dispatch_provider_rows]
  have leftVariable : variableToken "$left" = true := by simp [variableToken]
  have rightVariable : variableToken "$right" = true := by simp [variableToken]
  simp [dispatch, matchEquation, row_equation, bindResult, head_shape,
    template, templates, symbol_not_variable, relation_not_variable, leftVariable, rightVariable,
    encode, encodeList, matchPattern, matchArgs]

theorem extra_inner_operand_dispatch (occurrence : Fin 4) (left right extra : SExpr) :
    dispatch [] (.list [.atom (symbol occurrence),
      .list [.atom (relation occurrence), left, right, extra]]) generatedProgram = [] := by
  rw [dispatch_provider_rows]
  have leftVariable : variableToken "$left" = true := by simp [variableToken]
  have rightVariable : variableToken "$right" = true := by simp [variableToken]
  simp [dispatch, matchEquation, row_equation, bindResult, head_shape,
    template, templates, symbol_not_variable, relation_not_variable, leftVariable, rightVariable,
    encode, encodeList, matchPattern, matchArgs]

theorem query_template_closes (occurrence : Fin 4) (left right : Int) :
    GeneratedPeTTaTemplateInstantiation.instantiate? (targetEnv left right)
      (.list [.atom (relation occurrence), .atom "$left", .atom "$right"]) =
        some (query occurrence left right) := by
  have relationClosed : GeneratedPeTTaTemplateInstantiation.instantiate? (targetEnv left right)
      (.atom (relation occurrence)) = some (.atom (relation occurrence)) := by
    simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, relation_not_variable]
  simp [query, GeneratedPeTTaTemplateInstantiation.instantiateList_cons, relationClosed,
    GeneratedPeTTaIntegerProviderBridge.target_left, GeneratedPeTTaIntegerProviderBridge.target_right]

/-- An all-input successful family supplies the positive premise of the
duplicate-answer control; it is not merely a conditional mutation theorem. -/
theorem less_success (depth : Nat) (left right : Int) (less : left < right) :
    run (depth + 2) generatedProgram [] (call 0 left right) = .complete [query 0 left right] := by
  rw [run_body]
  have bodyShape : body 0 = .list [.atom "if", .list [.atom "<", .atom "$left", .atom "$right"],
      .list [.atom "quote", .list [.atom (relation 0), .atom "$left", .atom "$right"]],
      .list [.atom "empty"]] := rfl
  rw [bodyShape]
  apply (conditional_quote_empty depth generatedProgram [] (targetEnv left right) _ _
    (query 0 left right) true ?_ (query_template_closes 0 left right)).trans
  · rfl
  · simp [GeneratedPeTTaGroundCondition.condition?, GeneratedPeTTaIntegerProviderBridge.integer_left,
      GeneratedPeTTaIntegerProviderBridge.integer_right, less]

theorem actual_duplicate_once_counterexample (depth : Nat) :
    run (depth + 2) (generatedProgram ++ [row 0]) [] (call 0 (-3) (-2)) =
      .complete [query 0 (-3) (-2), query 0 (-3) (-2)] ∧
      [query 0 (-3) (-2), query 0 (-3) (-2)] ≠ [query 0 (-3) (-2), query 0 (-3) (-2)].take 1 :=
  duplicate_success_does_not_license_once depth 0 (-3) (-2) _
    (less_success depth (-3) (-2) (by decide))

/-- Transfer to another actual program requires both the original singleton
row and exclusion of broad variable-headed matches. Filter equality alone
would not establish whole-program dispatch. -/
theorem run_body_of_rows (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (occurrence : Fin 4) (left right : Int) (line : Nat)
    (literal : ∀ actual ∈ program, LiteralEquationHead actual.2)
    (rows : equationsFor (symbol occurrence) program = [(line, (row occurrence).2)]) :
    run depth program dataHeads (call occurrence left right) =
      eval depth program dataHeads (targetEnv left right) (body occurrence) := by
  have matched : dispatch [] (call occurrence left right) program =
      [((line, (row occurrence).2), targetEnv left right)] := by
    unfold call
    rw [dispatch_literal_filter [] (symbol occurrence) [query occurrence left right] program literal, rows]
    change dispatch [] (call occurrence left right) [(line, (row occurrence).2)] = _
    simp [dispatch, match_row]
  exact call_single_match depth program dataHeads (symbol occurrence) [query occurrence left right]
    (line, (row occurrence).2) (targetEnv left right) (head occurrence) (body occurrence)
    (symbol_ordinary occurrence) (by simp [knownFunction, rows])
    (by simp [hasArity, rows, row_equation, head_shape]) matched (row_equation occurrence)

theorem actual_call_execution_of_rows (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (occurrence : Fin 4) (left right : Int) (line : Nat)
    (literal : ∀ actual ∈ program, LiteralEquationHead actual.2)
    (rows : equationsFor (symbol occurrence) program = [(line, (row occurrence).2)]) :
    some (run (depth + 2) program dataHeads (call occurrence left right)) =
      ((sourceSides? occurrence).bind (fun sides =>
        SourceIntegerProvider.evalAnswers? (sourceEnv left right) sides.2)).map Outcome.complete := by
  rw [run_body_of_rows (depth + 2) program dataHeads occurrence left right line literal rows,
    body_program_independent]
  exact (congrArg some (run_body (depth + 2) occurrence left right)).symm.trans
    (actual_call_execution depth occurrence left right)

theorem closed_source_call (occurrence : Fin 4) (left right : Int) :
    (sourceSides? occurrence).bind (fun sides =>
      SourceIntegerProvider.closeTerm? (sourceEnv left right) sides.1) =
        some (call occurrence left right) := by
  fin_cases occurrence
  all_goals
    change SourceIntegerProvider.closeTerm? (sourceEnv left right)
      (.list [.atom _, .list [.atom _, .atom "?left", .atom "?right"]]) =
        some (.list [.atom _, .list [.atom _, .atom (toString left), .atom (toString right)]])
    simp [SourceIntegerProvider.closeTerm?, SourceIntegerProvider.closeTerms?,
      SourceIntegerProvider.sourceVariableToken, SourceIntegerProvider.lookup?, sourceEnv]
    exact ⟨rfl, rfl⟩

/-- Whole-call reflection includes the actual source head and occurrence,
not only an independently executable expression with the same body. -/
theorem source_completion_iff (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (answers : List SExpr) :
    run (depth + 2) generatedProgram [] (call occurrence left right) = .complete answers ↔
      SourceIntegerProviderNativeType.source.Evaluates
        ([GeneratedPeTTaIntegerProviderBridge.providerSource], sourceEnv left right)
        ⟨occurrence, call occurrence left right⟩
        ([GeneratedPeTTaIntegerProviderBridge.providerSource], sourceEnv left right) answers := by
  rw [completed_call_iff]
  constructor
  · rintro ⟨lhs, rhs, selected, executed⟩
    refine ⟨rfl, lhs, rhs, ?_, ?_, executed⟩
    · rw [← GeneratedPeTTaIntegerProviderBridge.sourceSides_from_admitted]
      exact selected
    · simpa [selected] using closed_source_call occurrence left right
  · rintro ⟨_, lhs, rhs, selected, _, executed⟩
    refine ⟨lhs, rhs, ?_, executed⟩
    rw [GeneratedPeTTaIntegerProviderBridge.sourceSides_from_admitted]
    exact selected

#print axioms dispatch_exact
#print axioms completed_call_iff
#print axioms source_completion_iff
#print axioms duplicate_completed_call
#print axioms actual_duplicate_once_counterexample
#print axioms missing_row_dispatch
#print axioms actual_call_execution_of_rows

end Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderDispatch
