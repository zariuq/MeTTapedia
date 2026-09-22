import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution

/-!
# Occurrence-bounded generated result-tag lets

This compares the existing generated literal wrapper with `once` in the actual
selected ground-body evaluator. Both wrappers retain one expression-depth
layer, so their enclosing lets use aligned budgets. The result is equality of
the complete Outcome, including continuation exhaustion and outside-fragment
results, not just equality of successful values.

The callee's occurrence bound is an explicit obligation on actual evaluation.
No answer provider replaces that evaluation. This does not prove a particular
callee meets the obligation, or that native first-answer pruning over an
effectful or infinite generator has these finite-model semantics.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaSemidetLet

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open GeneratedPeTTaGroundExecution
open GeneratedPeTTaResultBinding (bindAnswers bindResult template templates variableToken)
open GeneratedPeTTaTemplateInstantiation (instantiate_atom)
open GeneratedPeTTaEquationDispatch (equationsFor)
open SourceSExprPatternCodec (encode encodeList)
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern matchArgs mergeBindings)

def literal (inner : SExpr) : SExpr :=
  .list [.atom "superpose", .list [.atom "collapse", inner]]

def once (inner : SExpr) : SExpr := .list [.atom "once", inner]

theorem list_binder_rejects_atom (env : Bindings) (schema : List SExpr) (token : String) :
    bindResult env (.list schema) (.atom token) = [] := by
  simp [bindResult, template, SourceSExprPatternCodec.encode,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern]

theorem literal_bindings (env : Bindings) (schema : List SExpr) (answers : List SExpr) :
    bindAnswers env (.list schema) (.atom "collapse" :: answers) =
      bindAnswers env (.list schema) answers := by
  simp only [bindAnswers, List.flatMap_cons, list_binder_rejects_atom, List.nil_append]

/-- Full literal-wrapper outcome, including the zero inner-depth case. -/
theorem literal_outcome (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (inner : SExpr) :
    eval (depth + 1) program dataHeads env (literal inner) =
      match eval depth program dataHeads env inner with
      | .complete answers => .complete (.atom "collapse" :: answers)
      | .exhausted => .exhausted
      | .outsideFragment => .outsideFragment := by
  cases depth with
  | zero => rfl
  | succ depth =>
      rw [literal, literal_superpose]
      have atomDone : eval (depth + 1) program dataHeads env (.atom "collapse") =
          .complete [.atom "collapse"] := by
        apply atom_exact
        simp [instantiate_atom, GeneratedPeTTaResultBinding.variableToken]
      simp only [collect, atomDone]
      cases eval (depth + 1) program dataHeads env inner <;> simp

private theorem take_one_eq {α : Type} (values : List α) (small : values.length ≤ 1) :
    values.take 1 = values := by
  cases values with
  | nil => rfl
  | cons head tail =>
      cases tail with
      | nil => rfl
      | cons next rest => simp at small

/-- A structured result binder rejects the extra literal atom. With at most
one completed worker occurrence, replacing that wrapper by `once` preserves
the entire let outcome, at the same enclosing depth and caller environment.
No occurrence bound is imposed on the continuation's answers. -/
theorem literal_once_let (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (schema : List SExpr)
    (inner continuation : SExpr)
    (semidet : ∀ answers, eval depth program dataHeads env inner = .complete answers →
      answers.length ≤ 1) :
    eval (depth + 2) program dataHeads env
      (.list [.atom "let", .list schema, literal inner, continuation]) =
    eval (depth + 2) program dataHeads env
      (.list [.atom "let", .list schema, once inner, continuation]) := by
  have letLeft := eval.eq_def (depth + 2) program dataHeads env
    (.list [.atom "let", .list schema, literal inner, continuation])
  have letRight := eval.eq_def (depth + 2) program dataHeads env
    (.list [.atom "let", .list schema, once inner, continuation])
  simp only [Nat.add_succ, Nat.add_zero] at letLeft letRight
  rw [letLeft, letRight]
  by_cases inert : inertBinder program dataHeads (.list schema) = true
  · simp only [inert, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [literal_outcome]
    simp only [once, eval]
    cases completed : eval depth program dataHeads env inner with
    | exhausted => rfl
    | outsideFragment => rfl
    | complete answers =>
        have small := semidet answers completed
        simp [small, take_one_eq answers small, literal_bindings]
  · simp [inert] at *

/-- A callee transformation may be composed only when it preserves the actual
Outcome. Source answer-list uniqueness alone does not supply this premise. -/
theorem transported_literal_once_let (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (schema : List SExpr)
    (original optimized continuation : SExpr)
    (same : eval depth program dataHeads env original = eval depth program dataHeads env optimized)
    (semidet : ∀ answers, eval depth program dataHeads env original = .complete answers →
      answers.length ≤ 1) :
    eval (depth + 2) program dataHeads env
      (.list [.atom "let", .list schema, literal original, continuation]) =
    eval (depth + 2) program dataHeads env
      (.list [.atom "let", .list schema, once optimized, continuation]) := by
  rw [literal_once_let depth program dataHeads env schema original continuation semidet]
  simp only [eval, once, same]

private def resultSchema : SExpr := .list [.atom "Result", .atom "$value"]
private def resultValue : SExpr := .list [.atom "Result", .atom "value"]
private def quoted (value : SExpr) : SExpr := .list [.atom "quote", value]
private def letResult (value continuation : SExpr) : SExpr :=
  .list [.atom "let", resultSchema, value, continuation]
private def repeatResult : SExpr :=
  .list [.atom "superpose", .list [quoted resultValue, quoted resultValue]]
private def repeatContinuation : SExpr :=
  .list [.atom "superpose", .list [quoted (.atom "$value"), quoted (.atom "$value")]]

/-- The worker is single-valued, but the continuation deliberately returns
two equal occurrences. Both survive, with the result variable substituted. -/
theorem continuation_multiplicity_preserved :
    eval 6 [] ["Result"] [] (letResult (literal (quoted resultValue)) repeatContinuation) =
      .complete [.atom "value", .atom "value"] ∧
    eval 6 [] ["Result"] [] (letResult (once (quoted resultValue)) repeatContinuation) =
      .complete [.atom "value", .atom "value"] := by
  simp [letResult, literal, once, quoted, resultSchema, resultValue, repeatContinuation, eval,
    collect, SourceSExprPatternCodec.decode, inertBinder, inertBinders, reserved, knownFunction,
    equationsFor, instantiate_atom, variableToken, bindAnswers, bindResult, template, templates,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem completed_failure_preserved :
    eval 4 [] ["Result"] [] (letResult (literal (.list [.atom "empty"])) repeatContinuation) =
      .complete [] ∧
    eval 4 [] ["Result"] [] (letResult (once (.list [.atom "empty"])) repeatContinuation) =
      .complete [] := by
  simp [letResult, literal, once, quoted, resultSchema, repeatContinuation, eval, collect,
    inertBinder, inertBinders, reserved, knownFunction, equationsFor, instantiate_atom,
    variableToken, bindAnswers, bindResult, template, templates, encode, matchPattern,
    mergeBindings]

theorem inner_exhaustion_not_failure :
    eval 2 [] ["Result"] [] (letResult (literal (quoted resultValue)) repeatContinuation) =
      .exhausted ∧
    eval 2 [] ["Result"] [] (letResult (once (quoted resultValue)) repeatContinuation) =
      .exhausted := by
  simp [letResult, literal, once, quoted, resultSchema, resultValue, repeatContinuation, eval,
    collect, inertBinder, inertBinders, reserved, knownFunction, equationsFor]

theorem continuation_outside_not_failure :
    eval 4 [] ["Result"] []
      (letResult (literal (quoted resultValue)) (.list [.atom "unknown-function"])) =
      .outsideFragment ∧
    eval 4 [] ["Result"] []
      (letResult (once (quoted resultValue)) (.list [.atom "unknown-function"])) =
      .outsideFragment := by
  simp [letResult, literal, once, quoted, resultSchema, resultValue, eval, collect, runWith,
    dataTemplates, hasArity, inertBinder, inertBinders, reserved, knownFunction, equationsFor,
    instantiate_atom, variableToken, bindAnswers, bindResult, template, templates, encode,
    encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- Equal worker values are still two occurrences. The selected `once` model
refuses this case; value uniqueness cannot discharge its occurrence premise. -/
theorem duplicate_worker_occurrences_not_licensed :
    eval 6 [] ["Result"] [] (letResult (literal repeatResult) (quoted (.atom "$value"))) =
      .complete [.atom "value", .atom "value"] ∧
    eval 6 [] ["Result"] [] (letResult (once repeatResult) (quoted (.atom "$value"))) =
      .outsideFragment := by
  simp [letResult, literal, once, quoted, resultSchema, resultValue, repeatResult, eval, collect,
    SourceSExprPatternCodec.decode, inertBinder, inertBinders, reserved, knownFunction,
    equationsFor, instantiate_atom, variableToken, bindAnswers, bindResult, template, templates,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- Only one worker answer matches the result tag, but the worker itself has
two answers. A post-binding bound is not the required pre-binding bound. -/
theorem filtering_before_counting_is_insufficient :
    let worker := .list [.atom "superpose",
      .list [quoted (.list [.atom "Other", .atom "value"]), quoted resultValue]]
    eval 6 [] ["Result"] [] (letResult (literal worker) (quoted (.atom "$value"))) =
      .complete [.atom "value"] ∧
    eval 6 [] ["Result"] [] (letResult (once worker) (quoted (.atom "$value"))) =
      .outsideFragment := by
  dsimp only
  simp [letResult, literal, once, quoted, resultSchema, resultValue, eval, collect,
    SourceSExprPatternCodec.decode, inertBinder, inertBinders, reserved, knownFunction,
    equationsFor, instantiate_atom, variableToken, bindAnswers, bindResult, template, templates,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- A root ignored binder also accepts the literal `collapse` atom. The
structured-binder hypothesis is necessary, even for a singleton worker. -/
theorem ignored_binder_is_not_the_same_law :
    eval 4 [] [] [] (.list [.atom "let", .atom "$_", literal (quoted resultValue),
      quoted (.atom "answer")]) = .complete [.atom "answer", .atom "answer"] ∧
    eval 4 [] [] [] (.list [.atom "let", .atom "$_", once (quoted resultValue),
      quoted (.atom "answer")]) = .complete [.atom "answer"] := by
  simp [literal, once, quoted, resultValue, eval, collect, inertBinder, instantiate_atom,
    variableToken, bindAnswers, bindResult]

#print axioms literal_outcome
#print axioms literal_once_let
#print axioms transported_literal_once_let
#print axioms continuation_multiplicity_preserved
#print axioms completed_failure_preserved
#print axioms inner_exhaustion_not_failure
#print axioms continuation_outside_not_failure
#print axioms duplicate_worker_occurrences_not_licensed
#print axioms filtering_before_counting_is_insufficient
#print axioms ignored_binder_is_not_the_same_law

end Mettapedia.GSLT.Parsing.GeneratedPeTTaSemidetLet
