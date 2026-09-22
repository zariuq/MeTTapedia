import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderSyntax
import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution
import Mettapedia.GSLT.Parsing.PlainBnfLexicalScalarSemantics

/-!
# Execution of the generated Unicode scalar diagnostics

The providers and both diagnostic families are selected from the complete
generated fixture, including their original ordered occurrences. Their actual
nested conditions execute in the existing ground PeTTa model and agree with
the independently defined Unicode scalar predicate on canonical mathematical
Integer inputs. Origin values remain opaque data. This is neither a new
evaluator nor a claim about arbitrary ambient redefinitions or native C.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedUnicodeScalarExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult bindAnswers)
open GeneratedPeTTaTemplateInstantiation (instantiate? instantiateList?)
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open GeneratedPeTTaGroundCondition (integer? condition?)
open PlainBnfGeneratedScalarOrderSyntax (program selectedRows equationsFor_program)
open PlainBnfLexicalScalarSemantics (isUnicodeScalarInt)

def providerSymbol : Bool → String
  | false => "gslt:ground-unicode-scalar"
  | true => "gslt:ground-non-unicode-scalar"

def relation : Bool → String
  | false => "ground-unicode-scalar"
  | true => "ground-non-unicode-scalar"

def providerRows (negative : Bool) := selectedRows (providerSymbol negative)

theorem providerRows_count (negative : Bool) : (providerRows negative).length = 1 := by
  cases negative <;> rfl

def providerRow (negative : Bool) : Nat × SExpr :=
  (providerRows negative)[0]'(by rw [providerRows_count]; decide)

theorem provider_rows (negative : Bool) :
    equationsFor (providerSymbol negative) program = [providerRow negative] := by
  rw [equationsFor_program]
  cases negative <;> rfl

theorem provider_occurrences :
    (providerRow false).1 = 831 ∧ (providerRow true).1 = 833 := by constructor <;> rfl

private theorem provider_is_equation (negative : Bool) :
    (equation? (providerRow negative).2).isSome = true := by cases negative <;> rfl

def providerHead (negative : Bool) : SExpr :=
  ((equation? (providerRow negative).2).get (provider_is_equation negative)).1

def providerBody (negative : Bool) : SExpr :=
  ((equation? (providerRow negative).2).get (provider_is_equation negative)).2

theorem provider_equation (negative : Bool) :
    equation? (providerRow negative).2 = some (providerHead negative, providerBody negative) := by
  cases negative <;> rfl

def queryTemplate (negative : Bool) : SExpr :=
  .list [.atom (relation negative), .atom "$scalar"]

theorem provider_head (negative : Bool) : providerHead negative =
    .list [.atom (providerSymbol negative), queryTemplate negative] := by cases negative <;> rfl

def query (negative : Bool) (scalar : Int) : SExpr :=
  .list [.atom (relation negative), .atom (toString scalar)]

def providerCall (negative : Bool) (scalar : Int) : SExpr :=
  .list [.atom (providerSymbol negative), query negative scalar]

def providerEnv (scalar : Int) : Bindings := [("$scalar", encode (.atom (toString scalar)))]

def truth (negative : Bool) (scalar : Int) : Bool :=
  if negative then !isUnicodeScalarInt scalar else isUnicodeScalarInt scalar

private theorem provider_symbol_variable (negative : Bool) :
    variableToken (providerSymbol negative) = false := by
  cases negative <;> simp [providerSymbol, variableToken]

private theorem relation_variable (negative : Bool) :
    variableToken (relation negative) = false := by cases negative <;> simp [relation, variableToken]

private theorem provider_ordinary (negative : Bool) : reserved (providerSymbol negative) = false := by
  cases negative <;> rfl

theorem provider_match (negative : Bool) (scalar : Int) :
    matchEquation [] (providerCall negative scalar) (providerRow negative).2 =
      [providerEnv scalar] := by
  have sv : variableToken "$scalar" = true := by simp [variableToken]
  simp [matchEquation, provider_equation, bindResult, provider_head, providerCall, query,
    queryTemplate, template, templates, provider_symbol_variable, relation_variable, sv,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, providerEnv]

theorem provider_dispatch (negative : Bool) (scalar : Int) :
    dispatch [] (providerCall negative scalar) program =
      [(providerRow negative, providerEnv scalar)] := by
  unfold providerCall
  rw [PlainBnfGeneratedScalarOrderSyntax.dispatch_filter, provider_rows]
  change dispatch [] (providerCall negative scalar) [providerRow negative] = _
  simp [dispatch, provider_match]

theorem provider_run_body (depth : Nat) (dataHeads : List String) (negative : Bool) (scalar : Int) :
    run depth program dataHeads (providerCall negative scalar) =
      eval depth program dataHeads (providerEnv scalar) (providerBody negative) := by
  apply call_single_match depth program dataHeads (providerSymbol negative) [query negative scalar]
    (providerRow negative) (providerEnv scalar) (providerHead negative) (providerBody negative)
  · exact provider_ordinary negative
  · simp [knownFunction, provider_rows]
  · simp [hasArity, provider_rows, provider_equation, provider_head]
  · exact provider_dispatch negative scalar
  · exact provider_equation negative

private theorem provider_scalar (scalar : Int) :
    instantiate? (providerEnv scalar) (.atom "$scalar") = some (.atom (toString scalar)) := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable
  · simp [variableToken]
  · simp [providerEnv]

private theorem integer_scalar (scalar : Int) :
    integer? (providerEnv scalar) (.atom "$scalar") = some scalar := by
  simp only [integer?, provider_scalar]
  exact SourceIntegerProvider.integerValue?_repr scalar

private theorem query_closed (negative : Bool) (scalar : Int) :
    instantiate? (providerEnv scalar) (queryTemplate negative) = some (query negative scalar) := by
  have name : instantiate? (providerEnv scalar) (.atom (relation negative)) =
      some (.atom (relation negative)) := by
    simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, relation_variable]
  simp [queryTemplate, query, name, provider_scalar]

private def branch (negative selected : Bool) : SExpr :=
  if selected == negative then .list [.atom "empty"]
  else .list [.atom "quote", queryTemplate negative]

theorem provider_body_shape (negative : Bool) : providerBody negative =
    .list [.atom "if", .list [.atom "<", .atom "$scalar", .atom "0"], branch negative false,
      .list [.atom "if", .list [.atom "<", .atom "1114111", .atom "$scalar"], branch negative false,
        .list [.atom "if", .list [.atom "<", .atom "$scalar", .atom "55296"], branch negative true,
          .list [.atom "if", .list [.atom "<", .atom "57343", .atom "$scalar"],
            branch negative true, branch negative false]]]] := by
  cases negative <;> rfl

theorem provider_body_result (depth : Nat) (dataHeads : List String)
    (negative : Bool) (scalar : Int) :
    eval (depth + 5) program dataHeads (providerEnv scalar) (providerBody negative) =
      .complete (if truth negative scalar then [query negative scalar] else []) := by
  rw [provider_body_shape]
  have c0 : integer? (providerEnv scalar) (.atom "0") = some 0 := by
    simp [integer?, GeneratedPeTTaTemplateInstantiation.instantiate_atom, variableToken]
    exact SourceIntegerProvider.integerValue?_repr 0
  have c1 : integer? (providerEnv scalar) (.atom "1114111") = some 1114111 := by
    simp [integer?, GeneratedPeTTaTemplateInstantiation.instantiate_atom, variableToken]
    exact SourceIntegerProvider.integerValue?_repr 1114111
  have c2 : integer? (providerEnv scalar) (.atom "55296") = some 55296 := by
    simp [integer?, GeneratedPeTTaTemplateInstantiation.instantiate_atom, variableToken]
    exact SourceIntegerProvider.integerValue?_repr 55296
  have c3 : integer? (providerEnv scalar) (.atom "57343") = some 57343 := by
    simp [integer?, GeneratedPeTTaTemplateInstantiation.instantiate_atom, variableToken]
    exact SourceIntegerProvider.integerValue?_repr 57343
  cases negative <;>
    by_cases low : scalar < 0 <;>
    by_cases high : 1114111 < scalar <;>
    by_cases below : scalar < 55296 <;>
    by_cases above : 57343 < scalar <;>
    simp [eval, condition?, integer_scalar, c0, c1, c2, c3, branch,
      query_closed, truth, isUnicodeScalarInt, low, high, below, above]

theorem provider_run_exact (depth : Nat) (dataHeads : List String)
    (negative : Bool) (scalar : Int) :
    run (depth + 5) program dataHeads (providerCall negative scalar) =
      .complete (if truth negative scalar then [query negative scalar] else []) := by
  rw [provider_run_body, provider_body_result]

def symbol : Bool → String
  | false => "gslt:mode:BNFScalarDiagnosticV1:110"
  | true => "admitted:gslt:mode:BNFScalarDiagnosticV1:110"

def rows (typed : Bool) := selectedRows (symbol typed)

theorem rows_count (typed : Bool) : (rows typed).length = 2 := by cases typed <;> rfl

def row (typed : Bool) (i : Fin 2) : Nat × SExpr :=
  (rows typed)[i.val]'(by rw [rows_count]; exact i.isLt)

theorem exact_rows (typed : Bool) : rows typed = [row typed 0, row typed 1] := by
  cases typed <;> rfl

theorem worker_occurrences :
    (rows false).map Prod.fst = [952, 957] ∧ (rows true).map Prod.fst = [2348, 2353] := by
  constructor <;> rfl

private theorem row_is_equation (typed : Bool) (i : Fin 2) :
    (equation? (row typed i).2).isSome = true := by cases typed <;> fin_cases i <;> rfl

def head (typed : Bool) (i : Fin 2) : SExpr :=
  ((equation? (row typed i).2).get (row_is_equation typed i)).1

def body (typed : Bool) (i : Fin 2) : SExpr :=
  ((equation? (row typed i).2).get (row_is_equation typed i)).2

theorem row_equation (typed : Bool) (i : Fin 2) :
    equation? (row typed i).2 = some (head typed i, body typed i) := by
  cases typed <;> fin_cases i <;> rfl

theorem head_shape (typed : Bool) (i : Fin 2) :
    head typed i = .list [.atom (symbol typed), .atom "$scalar", .atom "$origin"] := by
  cases typed <;> fin_cases i <;> rfl

theorem bodies_unchanged (i : Fin 2) : body true i = body false i := by fin_cases i <;> rfl

def tag := "gslt:result:BNFScalarDiagnosticV1:110"

def dataHeads := [relation false, relation true, tag]

def localEnv (scalar : Int) (origin : SExpr) : Bindings :=
  [("$origin", encode origin), ("$scalar", encode (.atom (toString scalar)))]

def call (typed : Bool) (scalar : Int) (origin : SExpr) : SExpr :=
  .list [.atom (symbol typed), .atom (toString scalar), origin]

def diagnostic (scalar : Int) (origin : SExpr) : SExpr :=
  .list [.atom "BNFDiagnosticsConsV1",
    .list [.atom "BNFInvalidUnicodeScalarV1", .atom (toString scalar), origin],
    .atom "BNFDiagnosticsNilV1"]

def result (payload : SExpr) : SExpr := .list [.atom tag, payload]

def clauseResult (negative : Bool) (scalar : Int) (origin : SExpr) : SExpr :=
  result (if negative then diagnostic scalar origin else .atom "BNFDiagnosticsNilV1")

def quotedTemplate (negative : Bool) : SExpr :=
  .list [.atom tag, if negative then
    .list [.atom "BNFDiagnosticsConsV1",
      .list [.atom "BNFInvalidUnicodeScalarV1", .atom "$scalar", .atom "$origin"],
      .atom "BNFDiagnosticsNilV1"] else .atom "BNFDiagnosticsNilV1"]

theorem body_shape (typed : Bool) (i : Fin 2) : body typed i =
    .list [.atom "let", .atom "$_",
      .list [.atom (providerSymbol (i.val == 1)), queryTemplate (i.val == 1)],
      .list [.atom "quote", quotedTemplate (i.val == 1)]] := by
  cases typed <;> fin_cases i <;> rfl

private theorem ordinary (typed : Bool) : reserved (symbol typed) = false := by
  cases typed <;> rfl

private theorem symbol_not_variable (typed : Bool) : variableToken (symbol typed) = false := by
  cases typed <;> simp [symbol, variableToken]

theorem match_row (typed : Bool) (i : Fin 2) (scalar : Int) (origin : SExpr) :
    matchEquation [] (call typed scalar origin) (row typed i).2 = [localEnv scalar origin] := by
  have sv : variableToken "$scalar" = true := by simp [variableToken]
  have ov : variableToken "$origin" = true := by simp [variableToken]
  simp [matchEquation, row_equation, bindResult, head_shape, call, symbol_not_variable,
    template, templates, sv, ov, encode, encodeList, matchPattern, matchArgs,
    mergeBindings, List.foldlM, localEnv]

theorem worker_dispatch (typed : Bool) (scalar : Int) (origin : SExpr) :
    dispatch [] (call typed scalar origin) program =
      [(row typed 0, localEnv scalar origin), (row typed 1, localEnv scalar origin)] := by
  unfold call
  rw [PlainBnfGeneratedScalarOrderSyntax.dispatch_filter, equationsFor_program]
  change dispatch [] (call typed scalar origin) (rows typed) = _
  rw [exact_rows]
  simp [dispatch, match_row]

theorem call_bodies (depth : Nat) (typed : Bool) (scalar : Int) (origin : SExpr) :
    run depth program dataHeads (call typed scalar origin) =
      collect (fun i => eval depth program dataHeads (localEnv scalar origin) (body typed i))
        ([0, 1] : List (Fin 2)) := by
  have known : knownFunction program (symbol typed) = true := by
    simp only [knownFunction, equationsFor_program]
    change (!(rows typed).isEmpty) = true
    rw [exact_rows]; rfl
  have arity : hasArity program (symbol typed) 2 = true := by
    simp only [hasArity, equationsFor_program]
    change (rows typed).any _ = true
    rw [exact_rows]
    simp [row_equation, head_shape]
  unfold run runWith
  simp only [call, ordinary, known, arity, List.length_cons, List.length_nil,
    Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  change collect _ (dispatch [] (call typed scalar origin) program) = _
  rw [worker_dispatch]
  simp [collect, row_equation]

private theorem local_scalar (scalar : Int) (origin : SExpr) :
    instantiate? (localEnv scalar origin) (.atom "$scalar") = some (.atom (toString scalar)) := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable
  · simp [variableToken]
  · simp [localEnv]

private theorem local_origin (scalar : Int) (origin : SExpr) :
    instantiate? (localEnv scalar origin) (.atom "$origin") = some origin := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable
  · simp [variableToken]
  · simp [localEnv]

private theorem local_query (negative : Bool) (scalar : Int) (origin : SExpr) :
    instantiateList? (localEnv scalar origin) [queryTemplate negative] =
      some [query negative scalar] := by
  have name : instantiate? (localEnv scalar origin) (.atom (relation negative)) =
      some (.atom (relation negative)) := by
    simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, relation_variable]
  simp [queryTemplate, query, name, local_scalar]

theorem provider_call_in_body (depth : Nat) (negative : Bool) (scalar : Int) (origin : SExpr) :
    eval (depth + 1) program dataHeads (localEnv scalar origin)
      (.list [.atom (providerSymbol negative), queryTemplate negative]) =
      run depth program dataHeads (providerCall negative scalar) := by
  have valid : dataTemplates dataHeads [queryTemplate negative] = true := by
    cases negative <;> rfl
  unfold eval
  cases negative
  all_goals
    change (if reserved (providerSymbol _) || !dataTemplates dataHeads [queryTemplate _]
      then _ else _) = _
    rw [provider_ordinary, valid]
    simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, local_query]
    rfl

private theorem quoted_closed (negative : Bool) (scalar : Int) (origin : SExpr) :
    instantiate? (localEnv scalar origin) (quotedTemplate negative) =
      some (clauseResult negative scalar origin) := by
  cases negative <;>
    simp only [quotedTemplate, clauseResult, Bool.false_eq_true, ↓reduceIte, result, diagnostic,
      GeneratedPeTTaTemplateInstantiation.instantiate_list,
      GeneratedPeTTaTemplateInstantiation.instantiateList_cons,
      GeneratedPeTTaTemplateInstantiation.instantiateList_nil, local_scalar, local_origin] <;>
    simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, tag, variableToken]

theorem body_result (depth : Nat) (typed : Bool) (i : Fin 2) (scalar : Int) (origin : SExpr) :
    eval (depth + 7) program dataHeads (localEnv scalar origin) (body typed i) =
      .complete (if truth (i.val == 1) scalar then [clauseResult (i.val == 1) scalar origin] else []) := by
  rw [body_shape]
  have guard : eval (depth + 6) program dataHeads (localEnv scalar origin)
      (.list [.atom (providerSymbol (i.val == 1)), queryTemplate (i.val == 1)]) =
        .complete (if truth (i.val == 1) scalar then [query (i.val == 1) scalar] else []) := by
    rw [provider_call_in_body, provider_run_exact]
  have quoted : eval (depth + 6) program dataHeads (localEnv scalar origin)
      (.list [.atom "quote", quotedTemplate (i.val == 1)]) =
        .complete [clauseResult (i.val == 1) scalar origin] :=
    quote_exact (depth + 5) program dataHeads (localEnv scalar origin) _ _
      (quoted_closed (i.val == 1) scalar origin)
  rw [let_complete (depth + 6) program dataHeads (localEnv scalar origin) _ _ _ _ rfl guard]
  cases truth (i.val == 1) scalar <;>
    simp [bindAnswers, bindResult, quoted]

/-- The independent specification contains no target equation or branch tree. -/
def answer (scalar : Int) (origin : SExpr) : SExpr :=
  result (if isUnicodeScalarInt scalar then .atom "BNFDiagnosticsNilV1" else diagnostic scalar origin)

/-- Both real clauses execute; exactly one returns its diagnostic. The result
is an ordered singleton, not merely an extensional membership statement. -/
theorem run_exact (depth : Nat) (typed : Bool) (scalar : Int) (origin : SExpr) :
    run (depth + 7) program dataHeads (call typed scalar origin) = .complete [answer scalar origin] := by
  rw [call_bodies]
  simp only [collect, body_result]
  cases valid : isUnicodeScalarInt scalar <;> simp [truth, valid, clauseResult, answer]

theorem completed_iff (depth : Nat) (typed : Bool) (scalar : Int) (origin : SExpr)
    (answers : List SExpr) :
    run (depth + 7) program dataHeads (call typed scalar origin) = .complete answers ↔
      answers = [answer scalar origin] := by
  rw [run_exact]
  simp [eq_comm]

theorem raw_typed_same (depth : Nat) (scalar : Int) (origin : SExpr) :
    run (depth + 7) program dataHeads (call false scalar origin) =
      run (depth + 7) program dataHeads (call true scalar origin) := by rw [run_exact, run_exact]

theorem result_tag_not_callable : equationsFor tag program = [] := by
  rw [equationsFor_program]
  rfl

theorem positive_boundaries (depth : Nat) (typed : Bool) (origin : SExpr) :
    [0, 55295, 57344, 1114111].map (fun scalar : Int =>
      run (depth + 7) program dataHeads (call typed scalar origin)) =
      List.replicate 4 (.complete [result (.atom "BNFDiagnosticsNilV1")]) := by
  simp only [List.map_cons, List.map_nil, run_exact]
  rfl

theorem negative_boundaries (depth : Nat) (typed : Bool) (origin : SExpr) :
    [-1, 55296, 57343, 1114112].map (fun scalar : Int =>
      run (depth + 7) program dataHeads (call typed scalar origin)) =
      [-1, 55296, 57343, 1114112].map (fun scalar : Int =>
        .complete [result (diagnostic scalar origin)]) := by
  simp only [List.map_cons, List.map_nil, run_exact]
  rfl

#print axioms provider_run_exact
#print axioms run_exact
#print axioms completed_iff
#print axioms raw_typed_same

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedUnicodeScalarExecution
