import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingObservation

/-!
# Expected-application argument-error chronology regression

The published `interpret_args` recursion stops one result branch as soon as
an evaluated argument changes into `Empty` or `Error`.  The witnesses below
pin the repaired executable behavior: the failing branch is retained
immediately and later arguments are not evaluated on that branch.

The second argument is a query variable, so evaluating it would produce a
public assignment.  Its absence from the earlier error therefore observes
the chronology repair at the binding boundary, not merely through private
fresh-name counter work.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedApplicationErrorChronologyCounterexample

open Metta
open Metta.Minimal

private def firstArgument : Metta.Atom := .sym "first"

private def secondArgument : Metta.Atom := .var "y"

private def firstError : Metta.Atom :=
  .expr [.sym "Error", firstArgument, .sym "FirstFailed"]

private def selected : SelectedFunctionType :=
  { functionType :=
      .expr [.sym "->", .sym "B", .sym "B", .sym "Atom"]
    argumentTypes := [.sym "B", .sym "B"]
    returnType := .sym "Atom"
    typeBindings := [] }

private def evaluateArgument
    (state : St) (bindings : Metta.Bindings) (atom _expected : Metta.Atom) :
    List (Metta.Atom × Metta.Bindings) × St :=
  if atom == firstArgument then
    ([(firstError, bindings)], state)
  else
    ([(.sym "B", [.val "y" (.sym "B")])], state)

private def unusedReducer
    (state : St) (_application : Metta.Atom) :
    List (Metta.Atom × Metta.Bindings) × St :=
  ([], state)

private theorem policies_eq :
    argumentEvaluationPolicies selected 2 =
      [(true, .sym "B"), (true, .sym "B")] := by
  have rangeTwo : List.range 2 = [0, 1] := by
    simp [List.range_succ]
  have bNotAtom : ((.sym "B" : Metta.Atom) != .sym "Atom") = true := rfl
  have bNotVariable :
      ((.sym "B" : Metta.Atom) != .sym "Variable") = true := rfl
  have bNotExpression :
      ((.sym "B" : Metta.Atom) != .sym "Expression") = true := rfl
  unfold argumentEvaluationPolicies
  rw [rangeTwo]
  simp [selected, instantiate_nil, bNotAtom, bNotVariable, bNotExpression]

private theorem retentionScope_eq :
    expectedApplicationRetentionScope [] [firstArgument, secondArgument] =
      ["y"] := by
  simp [expectedApplicationRetentionScope, firstArgument, secondArgument,
    Metta.Atom.vars]

private theorem restrict_empty : restrictBnd ["y"] [] = [] := by
  have resolveEmpty :
      resolveAtom ([] : Metta.Bindings) 1 (.var "y") = .var "y" := by
    simp [resolveAtom, instantiate_nil]
  simp [restrictBnd, restrictBndRaw, resolveEmpty, Metta.Bindings.merge]

/-- The first changed error stops its branch before the later argument can
contribute a binding. -/
theorem first_changed_error_stops_branch :
    evaluateExpectedApplicationFrom evaluateArgument unusedReducer []
      St.init "f" [firstArgument, secondArgument] selected =
        ([(firstError, [])], St.init) := by
  unfold evaluateExpectedApplicationFrom
  rw [retentionScope_eq]
  simp only [List.length_cons, List.length_nil]
  rw [policies_eq]
  have firstMatches : (firstArgument == firstArgument) = true := rfl
  have secondDoesNotMatch : (secondArgument == firstArgument) = false := rfl
  have errorIsError : firstError.isError = true := rfl
  have errorChanged : (firstError != firstArgument) = true := rfl
  simp [evaluateArgument, unusedReducer, firstMatches, secondDoesNotMatch,
    errorIsError, errorChanged, restrict_empty]

/-- Negative canary: the public assignment that the skipped argument would
produce is not attached to the earlier error. -/
theorem later_argument_binding_does_not_reach_earlier_error :
    evaluateExpectedApplicationFrom evaluateArgument unusedReducer []
        St.init "f" [firstArgument, secondArgument] selected ≠
      ([(firstError, [.val "y" (.sym "B")])], St.init) := by
  rw [first_changed_error_stops_branch]
  intro h
  have hlengths := congrArg
    (fun output => output.1.map (fun result => result.2.length)) h
  simp at hlengths

/-- The skipped assignment would have been observable at the worker's
argument scope; the negative canary is therefore semantically meaningful. -/
theorem later_argument_binding_is_public :
    "y" ∈
      expectedApplicationRetentionScope [] [firstArgument, secondArgument] := by
  simp [expectedApplicationRetentionScope, firstArgument, secondArgument,
    Metta.Atom.vars]

end Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedApplicationErrorChronologyCounterexample
