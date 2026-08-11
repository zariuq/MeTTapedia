import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.Languages.MeTTa.MeTTaZero

/-!
# Work closure at the MeTTa Zero boundary

`MeTTaZero.evaluateOne` intentionally exposes an occurrence bag and retains an
unknown subject inertly.  That observation is sufficient for one-step query
and evaluation, but it is not sufficient to drive iteration: the same bag can
mean either "nothing interpreted this subject" or "an interpretation really
produced the subject again".

This module proves that information-loss result, proves that the bare
evaluation GSLT has no composable pair of rewrites, and gives the weakest
status-aware re-entry construction needed for ordinary evaluation chaining.
It does not add the runner to the Zero kernel and it does not choose a
scheduler.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZero

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## The information hidden by the one-step answer bag -/

/-- Whether one evaluation step declined to interpret the subject or produced
at least one semantic result. -/
inductive EvaluationStatus where
  | inert
  | produced
deriving DecidableEq, Repr

/-- A status-preserving one-step evaluation report.  The `produced` payload is
nonempty by construction when obtained from `evaluateReported`; keeping the
carrier proof-free makes the report suitable for ordinary language data. -/
inductive EvaluationReport where
  | inert (subject : Pattern)
  | produced (answers : Multiset Pattern)
deriving DecidableEq

namespace EvaluationReport

/-- The control-relevant classification retained by a report. -/
def status : EvaluationReport → EvaluationStatus
  | .inert _ => .inert
  | .produced _ => .produced

/-- Erase the status and recover the public one-step answer bag. -/
def answers : EvaluationReport → Multiset Pattern
  | .inert subject => {subject}
  | .produced results => results

@[simp] theorem status_inert (subject : Pattern) :
    (inert subject).status = .inert :=
  rfl

@[simp] theorem status_produced (answers : Multiset Pattern) :
    (produced answers).status = .produced :=
  rfl

@[simp] theorem answers_inert (subject : Pattern) :
    (inert subject).answers = {subject} :=
  rfl

@[simp] theorem answers_produced (results : Multiset Pattern) :
    (produced results).answers = results :=
  rfl

end EvaluationReport

/-- The status-preserving form of the canonical one-step evaluator. -/
def evaluateReported (model : Model) (space : model.Space)
    (subject : Pattern) : EvaluationReport :=
  let results := interpretedResults model space subject
  if results = 0 then .inert subject else .produced results

/-- Erasing the report gives exactly the existing Zero answer semantics. -/
@[simp] theorem evaluateReported_answers (model : Model) (space : model.Space)
    (subject : Pattern) :
    (evaluateReported model space subject).answers =
      evaluateOne model space subject := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [evaluateReported, evaluateOne, empty]
  · simp [evaluateReported, evaluateOne, empty]

@[simp] theorem evaluateReported_of_uninterpreted (model : Model)
    (space : model.Space) (subject : Pattern)
    (empty : interpretedResults model space subject = 0) :
    evaluateReported model space subject = .inert subject := by
  simp [evaluateReported, empty]

@[simp] theorem evaluateReported_of_interpreted (model : Model)
    (space : model.Space) (subject : Pattern)
    (nonempty : interpretedResults model space subject ≠ 0) :
    evaluateReported model space subject =
      .produced (interpretedResults model space subject) := by
  simp [evaluateReported, nonempty]

/-- The status is exact: inertness is equivalent to absence of interpreted
results, not equality of the returned value with the input. -/
@[simp] theorem evaluateReported_status_inert_iff (model : Model)
    (space : model.Space) (subject : Pattern) :
    (evaluateReported model space subject).status = .inert ↔
      interpretedResults model space subject = 0 := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [evaluateReported, empty]
  · simp [evaluateReported, empty]

/-- Dually, productive status is exact evidence that at least one interpreted
result exists. -/
@[simp] theorem evaluateReported_status_produced_iff (model : Model)
    (space : model.Space) (subject : Pattern) :
    (evaluateReported model space subject).status = .produced ↔
      interpretedResults model space subject ≠ 0 := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [evaluateReported, empty]
  · simp [evaluateReported, empty]

/-- The proof-free `produced` constructor cannot contain an empty bag when it
was obtained from the canonical reporter. -/
theorem evaluateReported_produced_nonempty (model : Model)
    (space : model.Space) (subject : Pattern) (answers : Multiset Pattern)
    (reported : evaluateReported model space subject = .produced answers) :
    answers ≠ 0 := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [evaluateReported, empty] at reported
  · rw [evaluateReported_of_interpreted model space subject empty] at reported
    cases reported
    exact empty

/-- The subject used by the status-erasure canary. -/
def statusCanarySubject : Pattern := .apply "zero-status-canary" []

/-- A model that declines the canary subject. -/
def inertStatusCanaryModel : Model :=
  structuralModel fun _ => 0

/-- A model that genuinely produces the canary subject itself. -/
def productiveStatusCanaryModel : Model :=
  structuralModel fun subject => {subject}

/-- Two evaluations selected solely to expose the nontrivial observation
fibre. -/
inductive StatusCanary where
  | inert
  | productive
deriving DecidableEq, Repr

/-- The rich report on either side of the canary fibre. -/
def statusCanaryReport : StatusCanary → EvaluationReport
  | .inert =>
      evaluateReported inertStatusCanaryModel
        (0 : Multiset Pattern) statusCanarySubject
  | .productive =>
      evaluateReported productiveStatusCanaryModel
        (0 : Multiset Pattern) statusCanarySubject

/-- What the existing one-step Zero surface observes. -/
def statusCanaryAnswers (canary : StatusCanary) : Multiset Pattern :=
  (statusCanaryReport canary).answers

/-- The distinction a correct iterative runner needs. -/
def statusCanaryStatus (canary : StatusCanary) : EvaluationStatus :=
  (statusCanaryReport canary).status

@[simp] theorem statusCanaryReport_inert :
    statusCanaryReport .inert = .inert statusCanarySubject := by
  simp [statusCanaryReport, evaluateReported, inertStatusCanaryModel,
    structuralModel, interpretedResults, equationResults, queryAll, query]

@[simp] theorem statusCanaryReport_productive :
    statusCanaryReport .productive =
      .produced ({statusCanarySubject} : Multiset Pattern) := by
  simp [statusCanaryReport, evaluateReported, productiveStatusCanaryModel,
    structuralModel, interpretedResults, equationResults, queryAll, query]

/-- The public bag identifies an inert answer with a genuine productive
self-loop, while their control-relevant statuses differ. -/
theorem same_answers_different_evaluation_status :
    statusCanaryAnswers .inert = statusCanaryAnswers .productive ∧
      statusCanaryStatus .inert ≠ statusCanaryStatus .productive := by
  simp [statusCanaryAnswers, statusCanaryStatus]

private def evaluationStatusFiber :
    NonTrivialFiber statusCanaryAnswers statusCanaryStatus where
  left := .inert
  right := .productive
  sameShadow := same_answers_different_evaluation_status.1
  differentValue := same_answers_different_evaluation_status.2

/-- **Status-erasure obstruction.**  No function of the one-step answer bag
can determine, for all Zero evaluations, whether the evaluator declined or
genuinely produced answers.  Consequently naive iteration of `evaluateOne`
cannot both stop on unknown terms and retain genuine self-loops. -/
theorem evaluationStatus_not_factors_through_answers :
    ¬ Factors statusCanaryAnswers statusCanaryStatus :=
  evaluationStatusFiber.not_factors

/-! ## Bare Zero has no internal re-entry -/

/-- A transition system has internal re-entry when some result of a step can
itself take another step. -/
def HasComposableSteps (theory : GSLT) : Prop :=
  ∃ source middle target,
    theory.Step source middle ∧ theory.Step middle target

/-- Every answer term of the bare one-step evaluation GSLT is quiescent. -/
theorem evaluationAnswer_isNormalForm (model : Model) (space : model.Space)
    (subject : Pattern) (occurrence : Nat) (answer : Pattern) :
    (evaluationGSLT model).IsNormalForm
      (.answer space subject occurrence answer) := by
  rintro ⟨target, step⟩
  cases step

/-- Every bare evaluation step ends at a quiescent answer term. -/
theorem evaluationStep_target_isNormalForm (model : Model)
    {source target : (evaluationGSLT model).Term}
    (step : (evaluationGSLT model).Step source target) :
    (evaluationGSLT model).IsNormalForm target := by
  cases step
  exact evaluationAnswer_isNormalForm model _ _ _ _

/-- **Bare-Zero work-closure obstruction.**  The canonical evaluation GSLT
has no composable pair of steps, for any model or space. -/
theorem bareZero_has_no_composable_steps (model : Model) :
    ¬ HasComposableSteps (evaluationGSLT model) := by
  rintro ⟨source, middle, target, first, second⟩
  exact (evaluationStep_target_isNormalForm model first) <| by
    exact Exists.intro target second

/-! ## The weakest status-aware re-entry runner -/

/-- Language-visible states for uniform iterative evaluation.  This is the
minimal re-entry runner, not the more expressive templated continuation layer:
every genuinely produced answer becomes the next subject, while an
uninterpreted subject completes. -/
inductive IterativeTerm (model : Model) where
  | pending (space : model.Space) (subject : Pattern)
      (occurrenceTrace : List Nat)
  | completed (space : model.Space) (answer : Pattern)
      (occurrenceTrace : List Nat)

/-- One status-aware runner transition.  Productive evaluation re-enters with
one answer occurrence; inert evaluation completes instead of looping. -/
inductive IterativeStep (model : Model) :
    IterativeTerm model -> IterativeTerm model -> Prop where
  | produced {space subject answers answer occurrence}
      {occurrenceTrace : List Nat}
      (reported : evaluateReported model space subject = .produced answers)
      (copy : occurrence < Multiset.count answer answers) :
      IterativeStep model (.pending space subject occurrenceTrace)
        (.pending space answer (occurrence :: occurrenceTrace))
  | inert {space subject occurrenceTrace}
      (reported : evaluateReported model space subject = .inert subject) :
      IterativeStep model (.pending space subject occurrenceTrace)
        (.completed space subject occurrenceTrace)

/-- The uniform, status-aware iterative evaluator as a GSLT. -/
def iterativeGSLT (model : Model) : GSLT where
  Term := IterativeTerm model
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := IterativeStep model
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact Exists.intro target <| And.intro step rfl
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Every productive runner transition is an answer of the canonical
one-step Zero evaluator before it is re-entered as work. -/
theorem iterative_produced_mem_evaluateOne (model : Model)
    {space : model.Space} {subject answer : Pattern}
    {answers : Multiset Pattern} {occurrence : Nat}
    (reported : evaluateReported model space subject = .produced answers)
    (copy : occurrence < Multiset.count answer answers) :
    answer ∈ evaluateOne model space subject := by
  have erased := congrArg EvaluationReport.answers reported
  simp only [evaluateReported_answers, EvaluationReport.answers_produced] at erased
  rw [erased]
  exact Multiset.count_pos.mp (Nat.zero_lt_of_lt copy)

/-- Unknown input completes in one runner step. -/
theorem inert_canary_runner_completes :
    (iterativeGSLT inertStatusCanaryModel).Step
      (.pending (0 : Multiset Pattern) statusCanarySubject [])
      (.completed (0 : Multiset Pattern) statusCanarySubject []) := by
  exact IterativeStep.inert statusCanaryReport_inert

/-- A genuine productive self-loop re-enters as work instead of being falsely
reported complete. -/
theorem productive_canary_runner_reenters :
    (iterativeGSLT productiveStatusCanaryModel).Step
      (.pending (0 : Multiset Pattern) statusCanarySubject [])
      (.pending (0 : Multiset Pattern) statusCanarySubject [0]) := by
  apply IterativeStep.produced (answers := {statusCanarySubject})
      (occurrence := 0)
  · exact statusCanaryReport_productive
  · simp

/-- The productive self-loop cannot take the inert completion edge. -/
theorem productive_canary_runner_does_not_complete :
    ¬ (iterativeGSLT productiveStatusCanaryModel).Step
      (.pending (0 : Multiset Pattern) statusCanarySubject [])
      (.completed (0 : Multiset Pattern) statusCanarySubject []) := by
  intro step
  cases step with
  | inert reported =>
      have productive :
          evaluateReported productiveStatusCanaryModel
              (0 : Multiset Pattern) statusCanarySubject =
            .produced ({statusCanarySubject} : Multiset Pattern) := by
        simpa [statusCanaryReport] using statusCanaryReport_productive
      rw [productive] at reported
      cases reported

/-- A model with two indistinguishable produced occurrences. -/
def duplicateRunnerCanaryModel : Model :=
  structuralModel fun _ =>
    ({statusCanarySubject, statusCanarySubject} : Multiset Pattern)

/-- Occurrence traces keep duplicate productive rows as distinct runner
configurations without imposing an enumeration order on their values. -/
theorem iterative_runner_retains_duplicate_occurrences :
    (iterativeGSLT duplicateRunnerCanaryModel).Step
        (.pending (0 : Multiset Pattern) statusCanarySubject [])
        (.pending (0 : Multiset Pattern) statusCanarySubject [0]) ∧
      (iterativeGSLT duplicateRunnerCanaryModel).Step
        (.pending (0 : Multiset Pattern) statusCanarySubject [])
        (.pending (0 : Multiset Pattern) statusCanarySubject [1]) ∧
      (IterativeTerm.pending (model := duplicateRunnerCanaryModel)
          (0 : Multiset Pattern) statusCanarySubject [0]) ≠
        .pending (0 : Multiset Pattern) statusCanarySubject [1] := by
  constructor
  · apply IterativeStep.produced
      (answers := {statusCanarySubject, statusCanarySubject}) (occurrence := 0)
    · simp [evaluateReported, duplicateRunnerCanaryModel, structuralModel,
        interpretedResults, equationResults, queryAll, query]
    · simp
  · constructor
    · apply IterativeStep.produced
        (answers := {statusCanarySubject, statusCanarySubject}) (occurrence := 1)
      · simp [evaluateReported, duplicateRunnerCanaryModel, structuralModel,
          interpretedResults, equationResults, queryAll, query]
      · simp
    · intro equal
      cases equal

/-! ## A concrete two-link evaluation chain -/

def chainA : Pattern := .apply "zero-chain-a" []
def chainB : Pattern := .apply "zero-chain-b" []
def chainC : Pattern := .apply "zero-chain-c" []

def chainAB : Pattern := .apply "=" [chainA, chainB]
def chainBC : Pattern := .apply "=" [chainB, chainC]

def chainSpace : Multiset Pattern := {chainAB, chainBC}
def chainModel : Model := structuralModel fun _ => 0

@[simp] theorem chain_interpretedResults_a :
    interpretedResults chainModel chainSpace chainA = {chainB} := by
  simp [chainModel, chainSpace, chainAB, chainBC, chainA, chainB, chainC,
    structuralModel, interpretedResults, equationResults, queryAll, query,
    viewEquation?, matchPattern, matchArgs, applyBindings]

@[simp] theorem chain_interpretedResults_b :
    interpretedResults chainModel chainSpace chainB = {chainC} := by
  simp [chainModel, chainSpace, chainAB, chainBC, chainA, chainB, chainC,
    structuralModel, interpretedResults, equationResults, queryAll, query,
    viewEquation?, matchPattern, matchArgs, applyBindings]

@[simp] theorem chain_interpretedResults_c :
    interpretedResults chainModel chainSpace chainC = 0 := by
  simp [chainModel, chainSpace, chainAB, chainBC, chainA, chainB, chainC,
    structuralModel, interpretedResults, equationResults, queryAll, query,
    viewEquation?, matchPattern, applyBindings]

/-- Bare Zero exposes only the first link of the chain. -/
@[simp] theorem chain_evaluateOne_a :
    evaluateOne chainModel chainSpace chainA = {chainB} := by
  rw [evaluateOne_of_interpreted]
  · exact chain_interpretedResults_a
  · simp

/-- In particular, the second-link result is not a direct one-step answer. -/
theorem chain_c_not_mem_evaluateOne_a :
    chainC ∉ evaluateOne chainModel chainSpace chainA := by
  rw [chain_evaluateOne_a]
  simp [chainB, chainC]

/-- The status-aware runner follows both productive links and then completes
exactly when the terminal subject is uninterpreted. -/
theorem iterative_chain_reaches_completion :
    (iterativeGSLT chainModel).MultiStep
      (.pending chainSpace chainA []) (.completed chainSpace chainC [0, 0]) := by
  have stepAB :
      (iterativeGSLT chainModel).Step
        (.pending chainSpace chainA []) (.pending chainSpace chainB [0]) := by
    apply IterativeStep.produced (answers := {chainB}) (occurrence := 0)
    · simp [evaluateReported]
    · simp
  have stepBC :
      (iterativeGSLT chainModel).Step
        (.pending chainSpace chainB [0]) (.pending chainSpace chainC [0, 0]) := by
    apply IterativeStep.produced (answers := {chainC}) (occurrence := 0)
    · simp [evaluateReported]
    · simp
  have completeC :
      (iterativeGSLT chainModel).Step
        (.pending chainSpace chainC [0, 0])
        (.completed chainSpace chainC [0, 0]) :=
    IterativeStep.inert <| by simp [evaluateReported]
  exact .step stepAB (.step stepBC (.step completeC (.refl _)))

/-- Adding only status-aware re-entry is sufficient to create a composable
pair of evaluation steps.  Templated continuations are a stronger ergonomic
and programming feature, not a prerequisite for this particular chain. -/
theorem iterativeZero_has_composable_steps :
    HasComposableSteps (iterativeGSLT chainModel) := by
  refine Exists.intro (.pending chainSpace chainA []) ?_
  refine Exists.intro (.pending chainSpace chainB [0]) ?_
  refine Exists.intro (.pending chainSpace chainC [0, 0]) ?_
  constructor
  · apply IterativeStep.produced (answers := {chainB}) (occurrence := 0)
    · simp [evaluateReported]
    · simp
  · apply IterativeStep.produced (answers := {chainC}) (occurrence := 0)
    · simp [evaluateReported]
    · simp

end Mettapedia.Languages.MeTTa.MeTTaZero
