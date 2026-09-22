import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataHeadExtension

/-!
# More depth preserves completed selected generated execution

The program, data constructors, caller environment, and exact ordered answer
list are fixed. Additional proof-model depth preserves completed evaluation
and calls. This is not an equivalence for exhausted or unsupported outcomes,
nor an extension of the finite semideterministic once profile.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDepthMonotonicity

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaGroundExecution
open GeneratedPeTTaDataHeadExtension (collect_completed runWith_completed)

theorem eval_completed {depth later : Nat} (more : depth ≤ later)
    (program : List (Nat × SExpr)) (dataHeads : List String) (env : Bindings)
    (expression : SExpr) (answers : List SExpr)
    (completed : eval depth program dataHeads env expression = .complete answers) :
    eval later program dataHeads env expression = .complete answers := by
  induction depth generalizing later env expression answers with
  | zero => cases completed
  | succ depth ih =>
      cases later with
      | zero => omega
      | succ later =>
          have depthOrder : depth ≤ later := Nat.le_of_succ_le_succ more
          have preserves := ih depthOrder
          unfold eval at completed ⊢
          split at completed
          all_goals try exact completed
          case h_3 => exact collect_completed _ _ (preserves env) _ _ completed
          case h_4 =>
            rename_i original inner
            cases evaluated : eval depth program dataHeads env inner with
            | exhausted => simp [evaluated] at completed
            | outsideFragment => simp [evaluated] at completed
            | complete values =>
                simpa only [evaluated, preserves env inner values evaluated] using completed
          case h_5 =>
            split at completed
            · exact preserves _ _ _ completed
            · exact preserves _ _ _ completed
            · cases completed
          case h_6 =>
            rename_i original schema value continuation
            split at completed
            · cases completed
            · rename_i permitted
              simp only [permitted]
              cases evaluated : eval depth program dataHeads env value with
              | exhausted => simp [evaluated] at completed
              | outsideFragment => simp [evaluated] at completed
              | complete values =>
                  simp only [evaluated] at completed
                  rw [preserves env value values evaluated]
                  exact collect_completed _ _ (fun next => preserves next continuation) _ _ completed
          case h_7 =>
            split at completed
            · cases completed
            · rename_i permitted
              simp only [permitted]
              split at completed
              · exact runWith_completed _ _ preserves _ _ _ completed
              · cases completed

theorem run_completed {depth later : Nat} (more : depth ≤ later)
    (program : List (Nat × SExpr)) (dataHeads : List String)
    (call : SExpr) (answers : List SExpr)
    (completed : run depth program dataHeads call = .complete answers) :
    run later program dataHeads call = .complete answers :=
  runWith_completed _ _ (eval_completed more program dataHeads) _ _ _ completed

/-- Two completed observations at unrelated depths have identical ordered
answer occurrences; neither observation has to be the least sufficient depth. -/
theorem eval_completed_answers_unique (firstDepth secondDepth : Nat)
    (program : List (Nat × SExpr)) (dataHeads : List String) (env : Bindings)
    (expression : SExpr) (firstAnswers secondAnswers : List SExpr)
    (first : eval firstDepth program dataHeads env expression = .complete firstAnswers)
    (second : eval secondDepth program dataHeads env expression = .complete secondAnswers) :
    firstAnswers = secondAnswers := by
  rcases Nat.le_total firstDepth secondDepth with more | more
  · exact Outcome.complete.inj
      ((eval_completed more program dataHeads env expression firstAnswers first).symm.trans second)
  · exact Outcome.complete.inj
      (first.symm.trans (eval_completed more program dataHeads env expression secondAnswers second))

theorem run_completed_answers_unique (firstDepth secondDepth : Nat)
    (program : List (Nat × SExpr)) (dataHeads : List String)
    (call : SExpr) (firstAnswers secondAnswers : List SExpr)
    (first : run firstDepth program dataHeads call = .complete firstAnswers)
    (second : run secondDepth program dataHeads call = .complete secondAnswers) :
    firstAnswers = secondAnswers := by
  rcases Nat.le_total firstDepth secondDepth with more | more
  · exact Outcome.complete.inj
      ((run_completed more program dataHeads call firstAnswers first).symm.trans second)
  · exact Outcome.complete.inj
      (first.symm.trans (run_completed more program dataHeads call secondAnswers second))

theorem completed_binding_at_larger_depth (later : Nat) (enough : 3 ≤ later) :
    eval later [] ["packet"] [] GeneratedPeTTaDataHeadExtension.packetExample =
      .complete [.atom "payload"] :=
  eval_completed enough _ _ _ _ _ GeneratedPeTTaDataHeadExtension.completed_binding_control

/-- A small control program using actual target calls and result-binding let.
It is a test fixture, not an alternative authority for generated artifacts. -/
def recursiveProgram : List (Nat × SExpr) := [
  (0, .list [.atom "=", .list [.atom "walk", .atom "end"],
    .list [.atom "quote", .atom "done"]]),
  (1, .list [.atom "=", .list [.atom "walk", .list [.atom "more", .atom "$tail"]],
    .list [.atom "let", .atom "$result", .list [.atom "walk", .atom "$tail"],
      .list [.atom "quote", .atom "$result"]]])]

def recursiveCall : SExpr :=
  .list [.atom "walk", .list [.atom "more", .list [.atom "more", .atom "end"]]]

private def recursiveEnv (input : SExpr) : Bindings :=
  [("$tail", SourceSExprPatternCodec.encode input)]

private def recursiveBody : SExpr :=
  .list [.atom "let", .atom "$result", .list [.atom "walk", .atom "$tail"],
    .list [.atom "quote", .atom "$result"]]

private theorem run_recursive_end (depth : Nat) :
    run depth recursiveProgram ["more"] (.list [.atom "walk", .atom "end"]) =
      eval depth recursiveProgram ["more"] [] (.list [.atom "quote", .atom "done"]) := by
  simp [run, runWith, recursiveProgram, reserved, knownFunction, hasArity,
    GeneratedPeTTaEquationDispatch.equationsFor,
    GeneratedPeTTaEquationDispatch.equationSymbol?, GeneratedPeTTaEquationDispatch.equation?,
    GeneratedPeTTaEquationDispatch.dispatch, GeneratedPeTTaEquationDispatch.matchEquation,
    GeneratedPeTTaResultBinding.bindResult,
    GeneratedPeTTaResultBinding.template, GeneratedPeTTaResultBinding.templates,
    GeneratedPeTTaResultBinding.variableToken, SourceSExprPatternCodec.encode, SourceSExprPatternCodec.encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem run_recursive_more (depth : Nat) (input : SExpr) :
    run depth recursiveProgram ["more"] (.list [.atom "walk", .list [.atom "more", input]]) =
      eval depth recursiveProgram ["more"] (recursiveEnv input) recursiveBody := by
  simp [run, runWith, recursiveProgram, recursiveEnv, recursiveBody, reserved, knownFunction, hasArity,
    GeneratedPeTTaEquationDispatch.equationsFor,
    GeneratedPeTTaEquationDispatch.equationSymbol?, GeneratedPeTTaEquationDispatch.equation?,
    GeneratedPeTTaEquationDispatch.dispatch, GeneratedPeTTaEquationDispatch.matchEquation,
    GeneratedPeTTaResultBinding.bindResult,
    GeneratedPeTTaResultBinding.template, GeneratedPeTTaResultBinding.templates,
    GeneratedPeTTaResultBinding.variableToken, SourceSExprPatternCodec.encode, SourceSExprPatternCodec.encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem recursive_value_call (depth : Nat) (input : SExpr) :
    eval (depth + 1) recursiveProgram ["more"] (recursiveEnv input)
      (.list [.atom "walk", .atom "$tail"]) =
      run depth recursiveProgram ["more"] (.list [.atom "walk", input]) := by
  simp [eval, recursiveEnv, reserved, dataTemplates, dataTemplate,
    GeneratedPeTTaTemplateInstantiation.instantiate_atom,
    GeneratedPeTTaResultBinding.variableToken, run]

private theorem recursive_more_complete (depth : Nat) (input value : SExpr)
    (completed : run depth recursiveProgram ["more"] (.list [.atom "walk", input]) =
      .complete [value]) :
    run (depth + 2) recursiveProgram ["more"] (.list [.atom "walk", .list [.atom "more", input]]) =
      .complete [value] := by
  rw [run_recursive_more]
  change eval (depth + 2) recursiveProgram ["more"] (recursiveEnv input)
    (.list [.atom "let", .atom "$result", .list [.atom "walk", .atom "$tail"],
      .list [.atom "quote", .atom "$result"]]) = _
  rw [let_complete (depth + 1) recursiveProgram ["more"] _ _ _ _ _ (by rfl)
    ((recursive_value_call depth input).trans completed)]
  simp [GeneratedPeTTaResultBinding.bindAnswers, GeneratedPeTTaResultBinding.bindResult,
    GeneratedPeTTaResultBinding.template, GeneratedPeTTaResultBinding.variableToken,
    recursiveEnv, matchPattern, mergeBindings, List.foldlM,
    eval, GeneratedPeTTaTemplateInstantiation.instantiate_atom]

private theorem recursive_more_exhausted (depth : Nat) (input : SExpr)
    (exhausted : run depth recursiveProgram ["more"] (.list [.atom "walk", input]) = .exhausted) :
    run (depth + 2) recursiveProgram ["more"] (.list [.atom "walk", .list [.atom "more", input]]) =
      .exhausted := by
  rw [run_recursive_more]
  simp only [recursiveBody]
  rw [eval]
  simp only [inertBinder, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [recursive_value_call depth input, exhausted]

theorem recursive_binding_completed :
    run 5 recursiveProgram ["more"] recursiveCall = .complete [.atom "done"] := by
  apply recursive_more_complete 3
  apply recursive_more_complete 1
  rw [run_recursive_end]
  apply quote_exact
  simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, GeneratedPeTTaResultBinding.variableToken]

theorem recursive_binding_at_larger_depth (later : Nat) (enough : 5 ≤ later) :
    run later recursiveProgram ["more"] recursiveCall = .complete [.atom "done"] :=
  run_completed enough _ _ _ _ recursive_binding_completed

theorem recursive_short_depth_is_not_equivalent :
    run 4 recursiveProgram ["more"] recursiveCall = .exhausted ∧
      run 5 recursiveProgram ["more"] recursiveCall ≠ .exhausted := by
  constructor
  · apply recursive_more_exhausted 2
    apply recursive_more_exhausted 0
    rw [run_recursive_end]
    rfl
  · rw [recursive_binding_completed]
    decide

theorem finite_duplicate_once_still_outside :
    eval 3 [] [] []
      (.list [.atom "once", .list [.atom "superpose", .list [.atom "same", .atom "same"]]]) =
      .outsideFragment := GeneratedPeTTaGroundExecution.duplicated_value_once_outside

#print axioms eval_completed
#print axioms run_completed
#print axioms eval_completed_answers_unique
#print axioms run_completed_answers_unique
#print axioms recursive_binding_completed

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDepthMonotonicity
