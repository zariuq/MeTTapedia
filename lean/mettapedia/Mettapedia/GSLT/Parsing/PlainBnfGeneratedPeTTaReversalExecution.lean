import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution
import Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaReversalDispatch

/-!
# Execution of the actual generated definition-reversal worker

The program is the whole generated component fixture. Its two reversal bodies
are retrieved from the actual equations, not supplied by a host reversal hook.
The observation is the entire ordered answer list, with explicit exhaustion.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaReversalExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult bindAnswers)
open GeneratedPeTTaTemplateInstantiation
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open PlainBnfGeneratedPeTTaSyntax (generatedProgram)
open PlainBnfGeneratedPeTTaReversalDispatch
open PlainBnfCollectorSourceExecution (definitions)

/-- The call-argument constructor and inert result-pattern constructor in
these two actual bodies. -/
def dataHeads : List String :=
  ["BNFDefinitionsConsV1", "gslt:result:BNFDiscoveryReverseDefinitionsV1:110"]

def result (value : SExpr) : SExpr :=
  .list [.atom "gslt:result:BNFDiscoveryReverseDefinitionsV1:110", value]

def cons (head tail : SExpr) : SExpr := .list [.atom "BNFDefinitionsConsV1", head, tail]

theorem result_binder_inert :
    inertBinder generatedProgram dataHeads (result (.atom "$after")) = true := by
  have absent : equationsFor "gslt:result:BNFDiscoveryReverseDefinitionsV1:110"
      generatedProgram = [] := rfl
  simp [inertBinder, inertBinders, result, reserved, knownFunction, absent, dataHeads]

def reversedInto (values : List SExpr) (accumulator : SExpr) : SExpr :=
  values.foldl (fun tail head => cons head tail) accumulator

theorem worker_ordinary : reserved worker = false := rfl

theorem worker_known : knownFunction generatedProgram worker = true := by
  rw [knownFunction, whole_reversal_rows]
  rfl

theorem worker_arity : hasArity generatedProgram worker 2 = true := by
  rw [hasArity, whole_reversal_rows]
  simp [nil_equation, nil_head_shape]

theorem run_nil (depth : Nat) (accumulator : SExpr) :
    run depth generatedProgram dataHeads (call (.atom "BNFDefinitionsNilV1") accumulator) =
      eval depth generatedProgram dataHeads (nilBindings accumulator) nilBody :=
  call_single_match depth generatedProgram dataHeads worker _ _ _ _ _
    worker_ordinary worker_known worker_arity (dispatch_nil accumulator) nil_equation

theorem run_cons (depth : Nat) (head tail accumulator : SExpr) :
    run depth generatedProgram dataHeads (call (cons head tail) accumulator) =
      eval depth generatedProgram dataHeads (consBindings head tail accumulator) consBody :=
  call_single_match depth generatedProgram dataHeads worker _ _ _ _ _
    worker_ordinary worker_known worker_arity (dispatch_cons head tail accumulator) cons_equation

theorem nil_quote (depth : Nat) (accumulator : SExpr) :
    eval (depth + 1) generatedProgram dataHeads (nilBindings accumulator) nilBody =
      .complete [result accumulator] := by
  rw [nil_body_shape]
  apply quote_exact
  simp [instantiate_atom, variableToken, nilBindings, result]

theorem recursive_arguments (head tail accumulator : SExpr) :
    instantiateList? (consBindings head tail accumulator)
      [.atom "$tail", .list [.atom "BNFDefinitionsConsV1", .atom "$head", .atom "$before"]] =
      some [tail, cons head accumulator] := by
  simp [instantiate_atom, variableToken, consBindings, cons]

theorem recursive_call (depth : Nat) (head tail accumulator : SExpr) :
    eval (depth + 1) generatedProgram dataHeads (consBindings head tail accumulator)
      (call (.atom "$tail") (.list [.atom "BNFDefinitionsConsV1", .atom "$head", .atom "$before"])) =
      run depth generatedProgram dataHeads (call tail (cons head accumulator)) := by
  simp only [call, worker, PlainBnfGeneratedPeTTaSyntax.workerName,
    PlainBnfGeneratedPeTTaSyntax.modeBits, eval]
  change (if reserved "gslt:fn:BNFDiscoveryReverseDefinitionsV1:110" ||
      !dataTemplates dataHeads [.atom "$tail", .list [.atom "BNFDefinitionsConsV1", .atom "$head", .atom "$before"]]
      then _ else _) = _
  simp only [reserved, dataTemplates, dataTemplate, dataHeads, List.contains_cons,
    List.contains_nil, beq_self_eq_true, Bool.true_or, Bool.true_and,
    Bool.not_true]
  rw [recursive_arguments]
  rfl

def afterBindings (head tail accumulator value : SExpr) : Bindings :=
  [("$after", encode value), ("$before", encode accumulator),
    ("$head", encode head), ("$tail", encode tail)]

theorem bind_recursive_result (head tail accumulator value : SExpr) :
    bindAnswers (consBindings head tail accumulator)
      (result (.atom "$after")) [result value] =
      [afterBindings head tail accumulator value] := by
  simp [bindAnswers, bindResult, result, consBindings, afterBindings,
    template, templates, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem after_quote (depth : Nat) (head tail accumulator value : SExpr) :
    eval (depth + 1) generatedProgram dataHeads (afterBindings head tail accumulator value)
      (.list [.atom "quote", result (.atom "$after")]) = .complete [result value] := by
  apply quote_exact
  simp [instantiate_atom, variableToken, afterBindings, result]

theorem cons_complete (depth : Nat) (head tail accumulator value : SExpr)
    (recursive : run depth generatedProgram dataHeads (call tail (cons head accumulator)) =
      .complete [result value]) :
    run (depth + 2) generatedProgram dataHeads (call (cons head tail) accumulator) =
      .complete [result value] := by
  rw [run_cons, cons_body_shape]
  change eval (depth + 2) generatedProgram dataHeads (consBindings head tail accumulator)
    (.list [.atom "let", result (.atom "$after"), _, .list [.atom "quote", result (.atom "$after")]]) = _
  rw [let_complete (depth + 1) generatedProgram dataHeads _ _ _ _ _
    result_binder_inert
    ((recursive_call depth head tail accumulator).trans recursive)]
  rw [bind_recursive_result, collect_singleton]
  exact after_quote depth head tail accumulator value

theorem cons_exhausted (depth : Nat) (head tail accumulator : SExpr)
    (recursive : run depth generatedProgram dataHeads (call tail (cons head accumulator)) =
      .exhausted) :
    run (depth + 2) generatedProgram dataHeads (call (cons head tail) accumulator) =
      .exhausted := by
  rw [run_cons, cons_body_shape]
  rw [eval]
  change (if !inertBinder generatedProgram dataHeads (result (.atom "$after")) then _ else _) = _
  rw [result_binder_inert]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [recursive_call, recursive]

/-- All depth bounds and all ground payloads: the result is either the exact
single answer occurrence or explicit exhaustion, never silent empty success. -/
theorem run_exact (depth : Nat) (values : List SExpr) (accumulator : SExpr) :
    run depth generatedProgram dataHeads (call (definitions values) accumulator) =
      if 2 * values.length < depth then .complete [result (reversedInto values accumulator)]
      else .exhausted := by
  cases depth with
  | zero =>
      cases values with
      | nil => simp [definitions, run_nil, eval]
      | cons head tail =>
          change run 0 generatedProgram dataHeads (call (cons head (definitions tail)) accumulator) = _
          rw [run_cons]
          simp [eval]
  | succ depth =>
      cases values with
      | nil => simp [definitions, run_nil, nil_quote, reversedInto]
      | cons head tail =>
          cases depth with
          | zero =>
              change run 1 generatedProgram dataHeads (call (cons head (definitions tail)) accumulator) = _
              rw [run_cons, cons_body_shape]
              change eval 1 generatedProgram dataHeads _
                (.list [.atom "let", result (.atom "$after"), _, _]) = _
              simp [eval, result_binder_inert]
          | succ depth =>
              have smaller := run_exact depth tail (cons head accumulator)
              change run (depth + 2) generatedProgram dataHeads
                (call (cons head (definitions tail)) accumulator) = _
              by_cases enough : 2 * tail.length < depth
              · have completed : run depth generatedProgram dataHeads
                    (call (definitions tail) (cons head accumulator)) =
                    .complete [result (reversedInto tail (cons head accumulator))] := by
                  simpa [enough] using smaller
                rw [cons_complete depth head (definitions tail) accumulator _ completed]
                simp [reversedInto]
                omega
              · have incomplete : run depth generatedProgram dataHeads
                    (call (definitions tail) (cons head accumulator)) = .exhausted := by
                  simpa [enough] using smaller
                rw [cons_exhausted depth head (definitions tail) accumulator incomplete]
                simp
                omega
termination_by depth

theorem completed_iff (values : List SExpr) (accumulator : SExpr) (answers : List SExpr) :
    (∃ depth, run depth generatedProgram dataHeads (call (definitions values) accumulator) =
      .complete answers) ↔ answers = [result (reversedInto values accumulator)] := by
  constructor
  · rintro ⟨depth, completed⟩
    rw [run_exact] at completed
    split at completed
    · simpa using completed.symm
    · simp at completed
  · rintro rfl
    refine ⟨2 * values.length + 1, ?_⟩
    simp [run_exact]

theorem reversedInto_definitions (values before : List SExpr) :
    reversedInto values (definitions before) = definitions (values.reverse ++ before) := by
  induction values generalizing before with
  | nil => simp [reversedInto]
  | cons head tail ih =>
      change reversedInto tail (definitions (head :: before)) = _
      rw [ih]
      simp

/-- The same ground payloads are observed in the independent authored-source
contextual step and in completed execution in the selected model of the
actual generated program. This is not SWI or C runtime adequacy. -/
theorem source_execution_iff
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (values before : List SExpr) (target : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
        PlainBnfCollectorSourceExecution.reversalLanguage
        (encode (PlainBnfCollectorSourceExecution.reverseCall values before)) target ↔
      ∃ depth payload,
        run depth generatedProgram dataHeads (call (definitions values) (definitions before)) =
          .complete [result payload] ∧ target = encode (.list [payload]) := by
  rw [PlainBnfCollectorSourceExecution.reversal_step_iff]
  constructor
  · intro same
    refine ⟨2 * values.length + 1, definitions (values.reverse ++ before), ?_, ?_⟩
    · simp [run_exact, reversedInto_definitions]
    · exact same
  · rintro ⟨depth, payload, completed, same⟩
    have exactAnswers := (completed_iff values (definitions before) [result payload]).mp
      ⟨depth, completed⟩
    have exactPayload : payload = definitions (values.reverse ++ before) := by
      simpa [result, reversedInto_definitions] using exactAnswers
    simpa only [exactPayload, PlainBnfCollectorSourceExecution.resultTuple] using same

/-- Insufficient depth is never reported as a successful empty answer stream. -/
theorem reversal_never_completed_empty (depth : Nat) (values : List SExpr)
    (accumulator : SExpr) :
    run depth generatedProgram dataHeads (call (definitions values) accumulator) ≠
      .complete [] := by
  rw [run_exact]
  split <;> simp

/-- Duplicate payload occurrences survive; equal values are not a set. -/
theorem duplicate_payloads_retained (value : SExpr) :
    run 5 generatedProgram dataHeads (call (definitions [value, value]) (definitions [])) =
      .complete [result (definitions [value, value])] := by
  simp [run_exact, reversedInto_definitions]

/-- A payload that looks like a call containing a variable is still opaque. -/
theorem call_looking_payload_retained :
    let payload := call (.atom "$tail") (.list [.atom "empty"])
    run 3 generatedProgram dataHeads (call (definitions [payload]) (definitions [])) =
      .complete [result (definitions [payload])] := by
  simp [run_exact, reversedInto_definitions]

/-- Returning the unreversed sequence is not another permitted completion. -/
theorem unreversed_answer_refused :
    ¬ ∃ depth, run depth generatedProgram dataHeads
      (call (definitions [.atom "first", .atom "second"]) (definitions [])) =
        .complete [result (definitions [.atom "first", .atom "second"])] := by
  rw [completed_iff, reversedInto_definitions]
  simp [result, definitions]

#print axioms run_exact
#print axioms completed_iff
#print axioms source_execution_iff
#print axioms reversal_never_completed_empty
#print axioms duplicate_payloads_retained
#print axioms call_looking_payload_retained
#print axioms unreversed_answer_refused

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaReversalExecution
