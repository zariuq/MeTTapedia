import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderSyntax
import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataHeadExtension

/-!
# Actual generated diagnostic-list concatenation

The raw and admitted equations are retrieved from the complete generated
candidate. They execute using the existing finite ground model, not an append
provider. Ordered diagnostic payloads are opaque, including repeated values.
This is a dependency of the complete scalar-list caller, not its replacement
by a handwritten algorithm or a claim of native PeTTa adequacy.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedDiagnosticsAppendExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult bindAnswers)
open GeneratedPeTTaTemplateInstantiation
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open PlainBnfGeneratedScalarOrderSyntax (program selectedRows equationsFor_program literal_heads)

def symbol (typed : Bool) : String :=
  if typed then "admitted:gslt:fn:BNFAppendDiagnosticsV1:110"
  else "gslt:fn:BNFAppendDiagnosticsV1:110"

def tag : String := "gslt:result:BNFAppendDiagnosticsV1:110"
def rows (typed : Bool) : List (Nat × SExpr) := selectedRows (symbol typed)

theorem rows_count (typed : Bool) : (rows typed).length = 2 := by cases typed <;> rfl

def row (typed : Bool) (index : Fin 2) : Nat × SExpr :=
  (rows typed)[index.val]'(by rw [rows_count]; exact index.isLt)

theorem exact_rows (typed : Bool) : equationsFor (symbol typed) program =
    [row typed 0, row typed 1] := by
  rw [equationsFor_program]
  cases typed <;> rfl

theorem row_present (typed : Bool) (index : Fin 2) :
    (equation? (row typed index).2).isSome = true := by cases typed <;> fin_cases index <;> rfl

def lhs (typed : Bool) (index : Fin 2) : SExpr :=
  ((equation? (row typed index).2).get (row_present typed index)).1

def body (typed : Bool) (index : Fin 2) : SExpr :=
  ((equation? (row typed index).2).get (row_present typed index)).2

theorem row_equation (typed : Bool) (index : Fin 2) :
    equation? (row typed index).2 = some (lhs typed index, body typed index) := by
  cases typed <;> fin_cases index <;> rfl

def nil : SExpr := .atom "BNFDiagnosticsNilV1"
def cons (head tail : SExpr) : SExpr := .list [.atom "BNFDiagnosticsConsV1", head, tail]
def result (value : SExpr) : SExpr := .list [.atom tag, value]
def call (typed : Bool) (left right : SExpr) : SExpr := .list [.atom (symbol typed), left, right]

def diagnostics : List SExpr → SExpr
  | [] => nil
  | head :: tail => cons head (diagnostics tail)

def prepend (values : List SExpr) (right : SExpr) : SExpr := values.foldr cons right

theorem nil_head (typed : Bool) : lhs typed 0 = call typed nil (.atom "$right") := by
  cases typed <;> rfl

theorem cons_head (typed : Bool) : lhs typed 1 =
    call typed (cons (.atom "$head") (.atom "$tail")) (.atom "$right") := by
  cases typed <;> rfl

theorem nil_body (typed : Bool) : body typed 0 =
    .list [.atom "quote", result (.atom "$right")] := by cases typed <;> rfl

theorem cons_body (typed : Bool) : body typed 1 =
    .list [.atom "let", result (.atom "$after"), call typed (.atom "$tail") (.atom "$right"),
      .list [.atom "quote", result (cons (.atom "$head") (.atom "$after"))]] := by
  cases typed <;> rfl

theorem physical_lines :
    (rows false).map Prod.fst = [866, 870] ∧ (rows true).map Prod.fst = [2262, 2266] :=
  ⟨rfl, rfl⟩

def dataHeads : List String := ["BNFDiagnosticsConsV1", tag]
def nilBindings (right : SExpr) : Bindings := [("$right", encode right)]
def consBindings (head tail right : SExpr) : Bindings :=
  [("$right", encode right), ("$head", encode head), ("$tail", encode tail)]

theorem dispatch_nil (typed : Bool) (right : SExpr) :
    dispatch [] (call typed nil right) program = [(row typed 0, nilBindings right)] := by
  rw [show call typed nil right = .list (.atom (symbol typed) :: [nil, right]) from rfl,
    dispatch_literal_filter [] _ _ program literal_heads, exact_rows]
  cases typed <;> simp [dispatch, matchEquation, row_equation, nil_head, cons_head, call, nil, cons,
    bindResult, template, templates, variableToken, symbol, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, nilBindings]

theorem dispatch_cons (typed : Bool) (head tail right : SExpr) :
    dispatch [] (call typed (cons head tail) right) program =
      [(row typed 1, consBindings head tail right)] := by
  rw [show call typed (cons head tail) right =
      .list (.atom (symbol typed) :: [cons head tail, right]) from rfl,
    dispatch_literal_filter [] _ _ program literal_heads, exact_rows]
  cases typed <;> simp [dispatch, matchEquation, row_equation, nil_head, cons_head, call, nil, cons,
    bindResult, template, templates, variableToken, symbol, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, consBindings]

theorem ordinary (typed : Bool) : reserved (symbol typed) = false := by cases typed <;> rfl

theorem known (typed : Bool) : knownFunction program (symbol typed) = true := by
  rw [knownFunction, exact_rows]
  rfl

theorem arity (typed : Bool) : hasArity program (symbol typed) 2 = true := by
  rw [hasArity, exact_rows]
  simp [row_equation, nil_head, call]

theorem binder_inert : inertBinder program dataHeads (result (.atom "$after")) = true := by
  have absent : equationsFor "gslt:result:BNFAppendDiagnosticsV1:110" program = [] := by
    rw [equationsFor_program]; rfl
  simp [inertBinder, inertBinders, result, reserved, knownFunction, absent, dataHeads, tag]

theorem run_nil (depth : Nat) (typed : Bool) (right : SExpr) :
    run depth program dataHeads (call typed nil right) =
      eval depth program dataHeads (nilBindings right) (body typed 0) :=
  call_single_match depth program dataHeads (symbol typed) _ _ _ _ _
    (ordinary typed) (known typed) (arity typed) (dispatch_nil typed right) (row_equation typed 0)

theorem run_cons (depth : Nat) (typed : Bool) (head tail right : SExpr) :
    run depth program dataHeads (call typed (cons head tail) right) =
      eval depth program dataHeads (consBindings head tail right) (body typed 1) :=
  call_single_match depth program dataHeads (symbol typed) _ _ _ _ _
    (ordinary typed) (known typed) (arity typed) (dispatch_cons typed head tail right)
    (row_equation typed 1)

theorem nil_quote (depth : Nat) (typed : Bool) (right : SExpr) :
    eval (depth + 1) program dataHeads (nilBindings right) (body typed 0) =
      .complete [result right] := by
  rw [nil_body]
  apply quote_exact
  simp [instantiate_atom, variableToken, nilBindings, result, tag]

theorem recursive_call (depth : Nat) (typed : Bool) (head tail right : SExpr) :
    eval (depth + 1) program dataHeads (consBindings head tail right)
      (call typed (.atom "$tail") (.atom "$right")) =
      run depth program dataHeads (call typed tail right) := by
  cases typed <;>
    simp [call, symbol, eval, reserved, dataTemplates, dataTemplate,
      instantiate_atom, variableToken, consBindings, run]

def afterBindings (head tail right value : SExpr) : Bindings :=
  [("$after", encode value), ("$right", encode right),
    ("$head", encode head), ("$tail", encode tail)]

theorem bind_recursive_result (head tail right value : SExpr) :
    bindAnswers (consBindings head tail right) (result (.atom "$after")) [result value] =
      [afterBindings head tail right value] := by
  simp [bindAnswers, bindResult, result, tag, consBindings, afterBindings,
    template, templates, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem after_quote (depth : Nat) (head tail right value : SExpr) :
    eval (depth + 1) program dataHeads (afterBindings head tail right value)
      (.list [.atom "quote", result (cons (.atom "$head") (.atom "$after"))]) =
      .complete [result (cons head value)] := by
  apply quote_exact
  simp [instantiate_atom, variableToken, afterBindings, result, cons, tag]

theorem cons_complete (depth : Nat) (typed : Bool) (head tail right value : SExpr)
    (recursive : run depth program dataHeads (call typed tail right) = .complete [result value]) :
    run (depth + 2) program dataHeads (call typed (cons head tail) right) =
      .complete [result (cons head value)] := by
  rw [run_cons, cons_body]
  rw [let_complete (depth + 1) program dataHeads _ _ _ _ _ binder_inert
    ((recursive_call depth typed head tail right).trans recursive)]
  rw [bind_recursive_result, collect_singleton]
  exact after_quote depth head tail right value

theorem cons_exhausted (depth : Nat) (typed : Bool) (head tail right : SExpr)
    (recursive : run depth program dataHeads (call typed tail right) = .exhausted) :
    run (depth + 2) program dataHeads (call typed (cons head tail) right) = .exhausted := by
  rw [run_cons, cons_body, eval]
  rw [binder_inert]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [recursive_call, recursive]

theorem run_exact (depth : Nat) (typed : Bool) (values : List SExpr) (right : SExpr) :
    run depth program dataHeads (call typed (diagnostics values) right) =
      if 2 * values.length < depth then .complete [result (prepend values right)] else .exhausted := by
  cases depth with
  | zero =>
      cases values <;> simp [diagnostics, run_nil, run_cons, eval]
  | succ depth =>
      cases values with
      | nil => simp [diagnostics, run_nil, nil_quote, prepend]
      | cons head tail =>
          cases depth with
          | zero =>
              simp [diagnostics, run_cons, cons_body, eval, binder_inert]
          | succ depth =>
              have smaller := run_exact depth typed tail right
              change run (depth + 2) program dataHeads
                (call typed (cons head (diagnostics tail)) right) = _
              by_cases enough : 2 * tail.length < depth
              · have completed : run depth program dataHeads (call typed (diagnostics tail) right) =
                    .complete [result (prepend tail right)] := by simpa [enough] using smaller
                rw [cons_complete depth typed head (diagnostics tail) right _ completed]
                simp [prepend]
                omega
              · have incomplete : run depth program dataHeads (call typed (diagnostics tail) right) =
                    .exhausted := by simpa [enough] using smaller
                rw [cons_exhausted depth typed head (diagnostics tail) right incomplete]
                simp
                omega
termination_by depth

theorem completed_iff (typed : Bool) (values : List SExpr) (right : SExpr)
    (answers : List SExpr) :
    (∃ depth, run depth program dataHeads (call typed (diagnostics values) right) =
      .complete answers) ↔ answers = [result (prepend values right)] := by
  constructor
  · rintro ⟨depth, completed⟩
    rw [run_exact] at completed
    split at completed
    · simpa using completed.symm
    · cases completed
  · rintro rfl
    exact ⟨2 * values.length + 1, by simp [run_exact]⟩

theorem prepend_diagnostics (left right : List SExpr) :
    prepend left (diagnostics right) = diagnostics (left ++ right) := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simpa only [prepend, List.foldr_cons, List.cons_append, diagnostics] using congrArg (cons head) ih

theorem raw_typed_same (depth : Nat) (left : List SExpr) (right : SExpr) :
    run depth program dataHeads (call false (diagnostics left) right) =
      run depth program dataHeads (call true (diagnostics left) right) := by
  rw [run_exact, run_exact]

/-- The concrete caller may need additional constructor tags for other
workers. Its larger data inventory does not change this completed append. -/
theorem completed_with_additional_data (additional : List String) (typed : Bool)
    (left right : List SExpr) :
    run (2 * left.length + 1) program (dataHeads ++ additional)
      (call typed (diagnostics left) (diagnostics right)) =
      .complete [result (diagnostics (left ++ right))] := by
  apply GeneratedPeTTaDataHeadExtension.run_completed
    (GeneratedPeTTaDataHeadExtension.extends_append dataHeads additional)
  simp [run_exact, prepend_diagnostics]

theorem duplicate_payloads_retained (typed : Bool) (payload : SExpr) :
    run 5 program dataHeads (call typed (diagnostics [payload, payload]) nil) =
      .complete [result (diagnostics [payload, payload])] := by
  simpa [diagnostics, prepend] using run_exact 5 typed [payload, payload] nil

theorem call_looking_payload_retained (typed : Bool) :
    let payload := call typed (.atom "$tail") (.list [.atom "empty"])
    run 3 program dataHeads (call typed (diagnostics [payload]) nil) =
      .complete [result (diagnostics [payload])] := by
  dsimp only
  rw [run_exact]
  rfl

theorem reordered_result_refused (typed : Bool) :
    ¬ ∃ depth, run depth program dataHeads
      (call typed (diagnostics [.atom "first", .atom "second"]) (diagnostics [.atom "third"])) =
      .complete [result (diagnostics [.atom "second", .atom "first", .atom "third"])] := by
  rw [completed_iff]
  simp [prepend, result, diagnostics, cons]

theorem insufficient_depth_not_empty (depth : Nat) (typed : Bool)
    (left : List SExpr) (right : SExpr) (short : depth ≤ 2 * left.length) :
    run depth program dataHeads (call typed (diagnostics left) right) = .exhausted ∧
      run depth program dataHeads (call typed (diagnostics left) right) ≠ .complete [] := by
  simp [run_exact, Nat.not_lt.mpr short]

#print axioms run_exact
#print axioms completed_iff
#print axioms raw_typed_same
#print axioms completed_with_additional_data
#print axioms duplicate_payloads_retained
#print axioms reordered_result_refused

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedDiagnosticsAppendExecution
