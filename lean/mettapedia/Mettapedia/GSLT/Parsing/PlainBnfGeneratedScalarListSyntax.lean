import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderSyntax
import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution

/-!
# Actual generated scalar-list clauses and their dispatch

Rows and bodies are retrieved from the complete generated fixture. The shape
equations below expose those bodies for the separate execution proof; they do
not supply replacement implementations. Dispatch preserves physical equation
occurrences and the existing matcher's exact ordered bindings. It is proved
for canonical Integer scalar arguments and opaque origin/tail data, including
the empty scalar-list case, not for arbitrary malformed calls.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarListSyntax

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult)
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open PlainBnfGeneratedScalarOrderSyntax (program equationsFor_program)

def symbol : Bool → String
  | false => "gslt:mode:BNFValidateScalarListV1:110"
  | true => "admitted:gslt:mode:BNFValidateScalarListV1:110"

def tag := "gslt:result:BNFValidateScalarListV1:110"

def rows := PlainBnfGeneratedScalarOrderSyntax.callerRows

theorem rows_count (typed : Bool) : (rows typed).length = 2 :=
  PlainBnfGeneratedScalarOrderSyntax.caller_rows_count typed

def row (typed : Bool) (i : Fin 2) : Nat × SExpr :=
  (rows typed)[i.val]'(by rw [rows_count]; exact i.isLt)

theorem exact_rows (typed : Bool) : rows typed = [row typed 0, row typed 1] := by
  cases typed <;> rfl

theorem equationsFor_rows (typed : Bool) : equationsFor (symbol typed) program = rows typed := by
  rw [equationsFor_program]
  cases typed <;> rfl

theorem physical_lines :
    (rows false).map Prod.fst = [972, 977] ∧ (rows true).map Prod.fst = [2368, 2373] := by
  constructor <;> rfl

private theorem row_is_equation (typed : Bool) (i : Fin 2) :
    (equation? (row typed i).2).isSome = true := by cases typed <;> fin_cases i <;> rfl

def lhs (typed : Bool) (i : Fin 2) : SExpr :=
  ((equation? (row typed i).2).get (row_is_equation typed i)).1

def body (typed : Bool) (i : Fin 2) : SExpr :=
  ((equation? (row typed i).2).get (row_is_equation typed i)).2

theorem row_equation (typed : Bool) (i : Fin 2) :
    equation? (row typed i).2 = some (lhs typed i, body typed i) := by
  cases typed <;> fin_cases i <;> rfl

def nil : SExpr := .list [.atom "bnf-v1:scalars-nil"]

def cons (scalar tail : SExpr) : SExpr := .list [.atom "bnf-v1:scalars-cons", scalar, tail]

def scalars : List Int → SExpr
  | [] => nil
  | first :: rest => cons (.atom (toString first)) (scalars rest)

def result (diagnostics : SExpr) : SExpr := .list [.atom tag, diagnostics]

def call (typed : Bool) (listTerm origin : SExpr) : SExpr :=
  .list [.atom (symbol typed), listTerm, origin]

theorem singleton_lhs (typed : Bool) : lhs typed 0 =
    call typed (cons (.atom "$scalar") nil) (.atom "$origin") := by cases typed <;> rfl

theorem cons_lhs (typed : Bool) : lhs typed 1 =
    call typed (cons (.atom "$head") (cons (.atom "$next") (.atom "$tail"))) (.atom "$origin") := by
  cases typed <;> rfl

def scalarSymbol : Bool → String
  | false => "gslt:mode:BNFScalarDiagnosticV1:110"
  | true => "admitted:gslt:mode:BNFScalarDiagnosticV1:110"

def appendSymbol : Bool → String
  | false => "gslt:fn:BNFAppendDiagnosticsV1:110"
  | true => "admitted:gslt:fn:BNFAppendDiagnosticsV1:110"

theorem singleton_body (typed : Bool) : body typed 0 =
    .list [.atom "let",
      .list [.atom "gslt:result:BNFScalarDiagnosticV1:110", .atom "$diagnostics"],
      .list [.atom "superpose", .list [.atom "collapse",
        .list [.atom (scalarSymbol typed), .atom "$scalar", .atom "$origin"]]],
      .list [.atom "quote", result (.atom "$diagnostics")]] := by
  cases typed <;> rfl

/-- This displayed subterm is a source-literal superpose list in the raw
family and once in the admitted family. It is not a collapse round trip. -/
def orderCallTemplate (typed : Bool) : SExpr :=
  let inner := .list [.atom (PlainBnfGeneratedScalarOrderSyntax.symbol typed),
    .atom "$head", .atom "$next", .atom "$origin"]
  if typed then .list [.atom "once", inner]
  else .list [.atom "superpose", .list [.atom "collapse", inner]]

theorem cons_body (typed : Bool) : body typed 1 =
    .list [.atom "let",
      .list [.atom "gslt:result:BNFScalarDiagnosticV1:110", .atom "$headDiagnostics"],
      .list [.atom "superpose", .list [.atom "collapse",
        .list [.atom (scalarSymbol typed), .atom "$head", .atom "$origin"]]],
      .list [.atom "let",
        .list [.atom "gslt:result:BNFScalarOrderDiagnosticV1:1110", .atom "$orderDiagnostics"],
        orderCallTemplate typed,
        .list [.atom "let",
          .list [.atom tag, .atom "$tailDiagnostics"],
          .list [.atom "superpose", .list [.atom "collapse",
            call typed (cons (.atom "$next") (.atom "$tail")) (.atom "$origin")]],
          .list [.atom "let",
            .list [.atom "gslt:result:BNFAppendDiagnosticsV1:110", .atom "$currentDiagnostics"],
            .list [.atom "once", .list [.atom (appendSymbol typed),
              .atom "$headDiagnostics", .atom "$orderDiagnostics"]],
            .list [.atom "let",
              .list [.atom "gslt:result:BNFAppendDiagnosticsV1:110", .atom "$diagnostics"],
              .list [.atom "once", .list [.atom (appendSymbol typed),
                .atom "$currentDiagnostics", .atom "$tailDiagnostics"]],
              .list [.atom "quote", result (.atom "$diagnostics")]]]]]] := by
  cases typed <;> rfl

def singletonEnv (scalar : Int) (origin : SExpr) : Bindings :=
  [("$origin", encode origin), ("$scalar", encode (.atom (toString scalar)))]

def consEnv (first next : Int) (tail origin : SExpr) : Bindings :=
  [("$origin", encode origin), ("$head", encode (.atom (toString first))),
    ("$next", encode (.atom (toString next))), ("$tail", encode tail)]

theorem ordinary (typed : Bool) : reserved (symbol typed) = false := by cases typed <;> rfl

theorem symbol_not_variable (typed : Bool) : variableToken (symbol typed) = false := by
  cases typed <;> simp [symbol, variableToken]

theorem known (typed : Bool) : knownFunction program (symbol typed) = true := by
  simp only [knownFunction, equationsFor_rows]
  rw [exact_rows]
  rfl

theorem arity (typed : Bool) : hasArity program (symbol typed) 2 = true := by
  simp [hasArity, equationsFor_rows, exact_rows, row_equation, singleton_lhs, cons_lhs, call]

theorem match_single (typed : Bool) (scalar : Int) (origin : SExpr) :
    matchEquation [] (call typed (scalars [scalar]) origin) (row typed 0).2 =
      [singletonEnv scalar origin] := by
  cases typed <;> simp [matchEquation, row_equation, bindResult, singleton_lhs, call, scalars, cons, nil,
    template, templates, symbol, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, singletonEnv]

theorem match_single_other (typed : Bool) (scalar : Int) (origin : SExpr) :
    matchEquation [] (call typed (scalars [scalar]) origin) (row typed 1).2 = [] := by
  simp [matchEquation, row_equation, bindResult, cons_lhs, call, scalars, cons, nil,
    template, templates, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem match_cons (typed : Bool) (first next : Int) (tail origin : SExpr) :
    matchEquation [] (call typed (cons (.atom (toString first))
      (cons (.atom (toString next)) tail)) origin) (row typed 1).2 =
        [consEnv first next tail origin] := by
  cases typed <;> simp [matchEquation, row_equation, bindResult, cons_lhs, call, cons,
    template, templates, symbol, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, consEnv]

theorem match_cons_other (typed : Bool) (first next : Int) (tail origin : SExpr) :
    matchEquation [] (call typed (cons (.atom (toString first))
      (cons (.atom (toString next)) tail)) origin) (row typed 0).2 = [] := by
  simp [matchEquation, row_equation, bindResult, singleton_lhs, call, cons, nil,
    template, templates, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem match_nil (typed : Bool) (origin : SExpr) (i : Fin 2) :
    matchEquation [] (call typed nil origin) (row typed i).2 = [] := by
  fin_cases i <;>
    simp [matchEquation, row_equation, bindResult, singleton_lhs, cons_lhs, call, cons, nil,
      template, templates, variableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem dispatch_single (typed : Bool) (scalar : Int) (origin : SExpr) :
    dispatch [] (call typed (scalars [scalar]) origin) program =
      [(row typed 0, singletonEnv scalar origin)] := by
  unfold call
  rw [PlainBnfGeneratedScalarOrderSyntax.dispatch_filter, equationsFor_rows, exact_rows]
  change dispatch [] (call typed (scalars [scalar]) origin) [row typed 0, row typed 1] = _
  simp [dispatch, match_single, match_single_other]

theorem dispatch_cons (typed : Bool) (first next : Int) (tail origin : SExpr) :
    dispatch [] (call typed (cons (.atom (toString first))
      (cons (.atom (toString next)) tail)) origin) program =
        [(row typed 1, consEnv first next tail origin)] := by
  unfold call
  rw [PlainBnfGeneratedScalarOrderSyntax.dispatch_filter, equationsFor_rows, exact_rows]
  change dispatch [] (call typed (cons (.atom (toString first))
    (cons (.atom (toString next)) tail)) origin) [row typed 0, row typed 1] = _
  simp only [dispatch, List.flatMap_cons, List.flatMap_nil]
  rw [match_cons_other, match_cons]
  rfl

theorem dispatch_nil (typed : Bool) (origin : SExpr) :
    dispatch [] (call typed nil origin) program = [] := by
  unfold call
  rw [PlainBnfGeneratedScalarOrderSyntax.dispatch_filter, equationsFor_rows, exact_rows]
  change dispatch [] (call typed nil origin) [row typed 0, row typed 1] = _
  simp [dispatch, match_nil]

theorem run_single (depth : Nat) (dataHeads : List String)
    (typed : Bool) (scalar : Int) (origin : SExpr) :
    run depth program dataHeads (call typed (scalars [scalar]) origin) =
      eval depth program dataHeads (singletonEnv scalar origin) (body typed 0) := by
  apply call_single_match depth program dataHeads (symbol typed) [scalars [scalar], origin]
    (row typed 0) (singletonEnv scalar origin) (lhs typed 0) (body typed 0)
    (ordinary typed) (known typed) (arity typed)
    (dispatch_single typed scalar origin) (row_equation typed 0)

theorem run_cons (depth : Nat) (dataHeads : List String)
    (typed : Bool) (first next : Int) (tail origin : SExpr) :
    run depth program dataHeads (call typed (cons (.atom (toString first))
      (cons (.atom (toString next)) tail)) origin) =
        eval depth program dataHeads (consEnv first next tail origin) (body typed 1) := by
  apply call_single_match depth program dataHeads (symbol typed)
    [cons (.atom (toString first)) (cons (.atom (toString next)) tail), origin]
    (row typed 1) (consEnv first next tail origin) (lhs typed 1) (body typed 1)
    (ordinary typed) (known typed) (arity typed)
    (dispatch_cons typed first next tail origin) (row_equation typed 1)

/-- There is no empty-list clause in this generated worker. This is a
completed absence of worker answers, not a successful validation verdict. -/
theorem run_nil (depth : Nat) (dataHeads : List String) (typed : Bool) (origin : SExpr) :
    run depth program dataHeads (call typed nil origin) = .complete [] := by
  unfold run runWith
  change (if reserved (symbol typed) || !knownFunction program (symbol typed) ||
      !hasArity program (symbol typed) 2 then _ else _) = _
  rw [ordinary, known, arity]
  simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [dispatch_nil]
  rfl

theorem result_tag_not_callable : equationsFor tag program = [] := by
  rw [equationsFor_program]
  rfl

#print axioms dispatch_single
#print axioms dispatch_cons
#print axioms run_single
#print axioms run_cons
#print axioms run_nil

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarListSyntax
