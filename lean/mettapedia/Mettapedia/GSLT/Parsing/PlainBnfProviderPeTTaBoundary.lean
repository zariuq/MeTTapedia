import Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle

/-!
# PeTTa target-semantics boundary for generated BNF providers

The generated integer-provider equations use nested arithmetic/comparisons,
lazy `if`, `quote`, and `(empty)`. The existing binding-threaded PeTTa relation
does not yet express that fragment. These are counterexamples against the
existing relations, not a replacement evaluator or a claimed native refinement.

In particular, absence of a derivation here is a limitation of the formal
interface, not a claim that the corresponding running PeTTa program fails.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfProviderPeTTaBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.PeTTa

/-- Quoting needs an operational constructor, not a user rule in the space. -/
theorem quote_has_no_builtin_derivation (space : PeTTaSpace)
    (noRules : space.rules = []) (value ty : Pattern) (bindings : Bindings)
    (results : EvalResult) :
    ¬ MeTTaEval space (.apply "quote" [value]) ty bindings results := by
  intro evaluation
  generalize expressionEq : (Pattern.apply "quote" [value]) = expression at evaluation
  cases evaluation <;> simp_all [mkError]

/-- The existing binding-threaded relation has no evaluated-condition or
selected-branch evaluation rule. This remains true for a closed condition. -/
theorem if_has_no_builtin_derivation (space : PeTTaSpace)
    (noRules : space.rules = []) (condition yes no ty : Pattern) (bindings : Bindings)
    (results : EvalResult) :
    ¬ MeTTaEval space (.apply "if" [condition, yes, no]) ty bindings results := by
  intro evaluation
  generalize expressionEq : (Pattern.apply "if" [condition, yes, no]) = expression at evaluation
  cases evaluation <;> simp_all [mkError]

theorem addition_has_no_builtin_derivation (space : PeTTaSpace)
    (noRules : space.rules = []) (left right ty : Pattern) (bindings : Bindings)
    (results : EvalResult) :
    ¬ MeTTaEval space (.apply "+" [left, right]) ty bindings results := by
  intro evaluation
  generalize expressionEq : (Pattern.apply "+" [left, right]) = expression at evaluation
  cases evaluation <;> simp_all [mkError]

theorem less_has_no_builtin_derivation (space : PeTTaSpace)
    (noRules : space.rules = []) (left right ty : Pattern) (bindings : Bindings)
    (results : EvalResult) :
    ¬ MeTTaEval space (.apply "<" [left, right]) ty bindings results := by
  intro evaluation
  generalize expressionEq : (Pattern.apply "<" [left, right]) = expression at evaluation
  cases evaluation <;> simp_all [mkError]

/-- An explicit non-example: the present core returns the nullary application
`(empty)` as a value. It does not represent failure with zero answers. -/
theorem empty_passes_through_in_current_core (space : PeTTaSpace) (bindings : Bindings) :
    MeTTaEval space (.apply "empty" []) undefinedType bindings
      [(.apply "empty" [], bindings)] :=
  MeTTaEval.symbolPassThrough "empty" undefinedType bindings isPassThroughType_undefined

theorem empty_has_no_zero_answer_derivation (space : PeTTaSpace)
    (noRules : space.rules = []) (ty : Pattern) (bindings : Bindings) :
    ¬ MeTTaEval space (.apply "empty" []) ty bindings [] := by
  intro evaluation
  generalize expressionEq : (Pattern.apply "empty" []) = expression at evaluation
  generalize resultsEq : ([] : EvalResult) = results at evaluation
  cases evaluation <;> simp_all [mkError]

/-- Positive control: an actual constructor already distinguishes successful
zero-answer completion from a singleton value and threads the caller bindings. -/
theorem empty_superpose_exact (space : PeTTaSpace) (noRules : space.rules = [])
    (ty : Pattern) (bindings : Bindings) (results : EvalResult) :
    MeTTaEval space (.apply "superpose" [.collection .vec [] none]) ty bindings results ↔
      results = [] := by
  constructor
  · intro evaluation
    generalize expressionEq :
      (Pattern.apply "superpose" [.collection .vec [] none]) = expression at evaluation
    cases evaluation <;> simp_all [mkError]
  · rintro rfl
    exact MeTTaEval.superpose [] ty bindings

/-- Grounded argument interpretation recurses through `MeTTaEval`, not through
the grounded relation. A nested addition therefore cannot use the oracle. -/
theorem nested_addition_not_interpretable (space : PeTTaSpace)
    (noRules : space.rules = []) (left right : Pattern) (remaining evaluated : List Pattern)
    (bindings finalBindings : Bindings) :
    ¬ InterpretArgs space bindings (.apply "+" [left, right] :: remaining)
      evaluated finalBindings := by
  intro arguments
  cases arguments with
  | cons _ _ _ ty results _ _ _ _ evaluation _ _ =>
    exact addition_has_no_builtin_derivation space noRules left right ty bindings results evaluation

/-- Consequently even an executable comparison oracle does not repair nested
integer successor in the current grounded evaluator. -/
theorem gap_comparison_has_no_grounded_derivation
    (oracle : GroundedOracle) (space : PeTTaSpace) (noRules : space.rules = [])
    (left one right ty : Pattern) (bindings : Bindings) (results : EvalResult) :
    ¬ MeTTaEvalG oracle space (.apply "<" [.apply "+" [left, one], right])
      ty bindings results := by
  intro evaluation
  cases evaluation with
  | liftPure _ _ _ _ pureEvaluation =>
    exact less_has_no_builtin_derivation space noRules (.apply "+" [left, one]) right
      ty bindings results pureEvaluation
  | groundedCall _ _ _ _ finalBindings evaluated _ _ arguments _ =>
    exact nested_addition_not_interpretable space noRules left one [right]
      evaluated bindings finalBindings arguments
  | groundedNoReduce _ _ _ _ finalBindings evaluated _ arguments _ =>
    exact nested_addition_not_interpretable space noRules left one [right]
      evaluated bindings finalBindings arguments

/-- The abstract oracle layer currently permits two different result lists
from the very same empty primitive call. Its totality contract cannot establish
the exact zero-answer behavior required by a failing BNF provider. -/
theorem empty_oracle_call_has_distinct_evaluations
    (oracle : GroundedOracle) (space : PeTTaSpace) (function : String)
    (raw evaluated : List Pattern) (ty : Pattern) (bindings finalBindings : Bindings)
    (executable : oracle.isExecutable function)
    (arguments : InterpretArgs space bindings raw evaluated finalBindings)
    (emptyCall : oracle.call function evaluated []) :
    MeTTaEvalG oracle space (.apply function raw) ty bindings [] ∧
    MeTTaEvalG oracle space (.apply function raw) ty bindings
      [(.apply function evaluated, finalBindings)] ∧
    ([] : EvalResult) ≠ [(.apply function evaluated, finalBindings)] := by
  refine ⟨?_, ?_, by simp⟩
  · exact MeTTaEvalG.groundedCall function raw ty bindings finalBindings evaluated []
      executable arguments emptyCall
  · exact MeTTaEvalG.groundedNoReduce function raw ty bindings finalBindings evaluated
      executable arguments emptyCall

#print axioms quote_has_no_builtin_derivation
#print axioms if_has_no_builtin_derivation
#print axioms empty_has_no_zero_answer_derivation
#print axioms empty_superpose_exact
#print axioms gap_comparison_has_no_grounded_derivation
#print axioms empty_oracle_call_has_distinct_evaluations

end Mettapedia.GSLT.Parsing.PlainBnfProviderPeTTaBoundary
