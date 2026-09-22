import Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis

/-!
# Native types observing complete answer lists

An emitted-value type cannot distinguish one answer occurrence from two equal
occurrences, and cannot observe a successful empty completion. This construction
instead observes the first edge of the existing relational evaluation GSLT.

`completesOnly` requires a completion and excludes every completed run violating
the observation. It does not assert termination of every execution or absence
of faults/divergence outside the supplied completion relation. Its universal
future condition is negated diamond of a bad completion, not OSLF's
predecessor-universal right adjoint.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis

open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uState uRequest uAnswer

variable {State : Type uState} {Request : Type uRequest} {Answer : Type uAnswer}

def completedRunSatisfies (source : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop) :
    EvaluationTerm source → Prop
  | .completed initial request final answers => observation initial request final answers
  | _ => False

def completesSatisfying (source : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop) :
    EquationPredicate (evaluationGSLT source) :=
  semanticDiamond (evaluationGSLT source)
    (saturatePredicate (evaluationGSLT source) (completedRunSatisfies source observation))

theorem completesSatisfying_request_iff
    (source : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop)
    (initial : State) (request : Request) :
    completesSatisfying source observation (.request initial request) ↔
      ∃ final answers, source.Evaluates initial request final answers ∧
        observation initial request final answers := by
  change gsltDiamond (evaluationGSLT source)
    (saturatePredicate (evaluationGSLT source)
      (completedRunSatisfies source observation)).1 (.request initial request) ↔ _
  refine (gsltDiamond_spec _ _ _).trans ?_
  constructor
  · rintro ⟨target, step, observed⟩
    have meaning := (saturatePredicate_apply_iff_of_equiv_iff_eq
      (evaluationGSLT source) (fun _ _ => Iff.rfl)
      (completedRunSatisfies source observation) target).1 observed
    cases step with
    | completed evaluation => exact ⟨_, _, evaluation, meaning⟩
  · rintro ⟨final, answers, evaluation, observed⟩
    refine ⟨.completed initial request final answers,
      EvaluationStep.completed evaluation, ?_⟩
    exact (saturatePredicate_apply_iff_of_equiv_iff_eq
      (evaluationGSLT source) (fun _ _ => Iff.rfl)
      (completedRunSatisfies source observation) _).2 observed

/-- Non-vacuous, universal observation of completed runs. `True` here is the
deliberately unrestricted completion observation, not an assumed proof. -/
def completesOnly (source : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop) :
    EquationPredicate (evaluationGSLT source) :=
  ⟨fun term => completesSatisfying source (fun _ _ _ _ => True) term ∧
      ¬ completesSatisfying source (fun initial request final answers =>
        ¬ observation initial request final answers) term,
   by
    intro left right equivalent
    change left = right at equivalent
    cases equivalent
    rfl⟩

theorem completesOnly_request_iff
    (source : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop)
    (initial : State) (request : Request) :
    completesOnly source observation (.request initial request) ↔
      (∃ final answers, source.Evaluates initial request final answers) ∧
      (∀ final answers, source.Evaluates initial request final answers →
        observation initial request final answers) := by
  classical
  change (_ ∧ ¬ _) ↔ _
  rw [completesSatisfying_request_iff, completesSatisfying_request_iff]
  simp only [and_true, not_exists, not_and, not_not]

def completionNativeType (source : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop) :
    GSLTNativeType (evaluationGSLT source) where
  sort := ()
  pred := completesOnly source observation

/-- Refining observations narrows this type, including the entire answer list. -/
theorem completesOnly_mono_observation
    (source : RelationalAnswerSource State Request Answer)
    {stronger weaker : State → Request → State → List Answer → Prop}
    (refines : ∀ initial request final answers,
      stronger initial request final answers → weaker initial request final answers)
    (initial : State) (request : Request)
    (typed : completesOnly source stronger (.request initial request)) :
    completesOnly source weaker (.request initial request) := by
  rw [completesOnly_request_iff] at typed ⊢
  exact ⟨typed.1, fun final answers evaluated =>
    refines initial request final answers (typed.2 final answers evaluated)⟩

/-- Adding possible runs can invalidate a universal completion type. The
comparison therefore requires two-sided equality at the selected request. -/
theorem completesOnly_transport
    (first second : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop)
    (initial : State) (request : Request)
    (same : ∀ final answers,
      first.Evaluates initial request final answers ↔
        second.Evaluates initial request final answers) :
    completesOnly first observation (.request initial request) ↔
      completesOnly second observation (.request initial request) := by
  simp only [completesOnly_request_iff, same]

theorem no_completion_not_typed
    (source : RelationalAnswerSource State Request Answer)
    (observation : State → Request → State → List Answer → Prop)
    (initial : State) (request : Request)
    (none : ∀ final answers, ¬ source.Evaluates initial request final answers) :
    ¬ completesOnly source observation (.request initial request) := by
  rw [completesOnly_request_iff]
  rintro ⟨⟨final, answers, evaluation⟩, _⟩
  exact none final answers evaluation

/-- A finite specimen for the distinction between answer values and occurrences.
State and request are retained; this is not a model of a particular evaluator. -/
def fixedAnswers (answers : List Answer) : RelationalAnswerSource State Request Answer where
  Evaluates initial _ final actual := final = initial ∧ actual = answers

theorem fixedAnswers_completion_iff (answers : List Answer)
    (observation : State → Request → State → List Answer → Prop)
    (initial : State) (request : Request) :
    completesOnly (fixedAnswers answers) observation (.request initial request) ↔
      observation initial request initial answers := by
  rw [completesOnly_request_iff]
  simp [fixedAnswers]

theorem empty_answers_complete (initial : State) (request : Request) :
    completesOnly (fixedAnswers ([] : List Answer))
      (fun before _ after answers => after = before ∧ answers = [])
      (.request initial request) := by
  rw [fixedAnswers_completion_iff]
  exact ⟨rfl, rfl⟩

theorem repeated_value_is_not_single_occurrence
    (initial : State) (request : Request) (answer : Answer) :
    completesOnly (fixedAnswers [answer, answer])
      (fun _ _ _ answers => ∀ value ∈ answers, value = answer)
      (.request initial request) ∧
    ¬ completesOnly (fixedAnswers [answer, answer])
      (fun _ _ _ answers => answers.length ≤ 1) (.request initial request) := by
  simp [fixedAnswers_completion_iff]

#print axioms completesOnly_request_iff
#print axioms completesOnly_transport
#print axioms repeated_value_is_not_single_occurrence

end Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis
