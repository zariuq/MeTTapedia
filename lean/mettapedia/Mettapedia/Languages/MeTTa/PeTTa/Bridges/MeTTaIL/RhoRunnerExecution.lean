import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramResumptionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoLexCanonicalExecution
import Mettapedia.OSLF.MeTTaIL.GeneralRhoTotality
import Mettapedia.Machines.OwnedPullDriver
import Mettapedia.Machines.ValidatedCommit
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
import Mettapedia.GSLT.Dynamics.QueryRevision

/-!
# Running closed rho processes through the PeTTa driver

`gslt_rho_runner.metta` runs a closed rho process step by step. One step puts the state in
lexicographic canonical form, runs the depth-one COMM plan on it through the program driver, and
reads the driver's publication: the first released receipt is the next state; a complete, empty
publication means the state is quiescent; otherwise the budget was not enough.

The model below is that step. Its theorems:

- `step_sound`: a reported step is a depth-one rho step from the canonical form, which is
  structurally congruent to the process;
- `step_quiescent`: a reported quiescence means the process has no rho step at all, at any depth;
- `step_saturated`, `step_complete`: with a budget covering every job's search, a step is never
  left unsaturated, so it finds a rho step whenever the process has one;
- `run_chain`, `run_quiescent`: the run's trace is a reduction sequence modulo structural
  congruence, and it ends in quiescence only at a state with no rho step;
- `resume_search_returns`, `resume_search_completed_iff`: the authored retained-search operation
  advances the same pending program frames and prints the full updated observation;
- `Retained.commit_licenses`, `Retained.advance_add`, `Retained.two_communications`: a whole
  process keeps that search, commits the selected receipt, and resumes the successor search;
- `Retained.Reached.sound`, `Retained.Reached.chain`, `Retained.Reached.done_quiescent`: every
  execution reached by any sequence of retained operations has a chronological history of
  committed depth-one COMMs from the canonical start, its live search runs at that history's
  endpoint, and a done phase there is exact quiescence;
- `Retained.owned_publication`: under the common owned host, committed COMMs reach the world
  exactly once, copies of used tickets are refused, and the delivered history is that
  chronological COMM sequence;
- `Retained.disjoint_retained_diamond`: two disjoint closed COMMs run in either
  order through actual retained searches, retaining their receipts and a common endpoint;
- `Retained.LocatedComm.retained_realization`: occurrence-cell transactions correspond
  to the same runner, with concrete read validation, causal history interchange,
  irreversible consumption, cancellation and exactly-once owned publication;
- `cancel_returns`: the authored cancel operation returns `Retained.Execution.cancel`;
- `append_commit_returns`: chronological receipt append keeps the whole receipt;
- `begin_returns`: an empty history and a live search at matcher budget zero;
- `resume_process_returns`: a live search continues, and a finished phase stays;
- `commit_returns`: a valid completed receipt commits one canonical reduction, and a
  pending, done, or cancelled phase stays;
- `advance_returns`: quoted COMM fuel follows `Retained.Execution.advance`;
- `commit_candidate_returns`: quoted `rho:run:commit-candidate` follows
  `Retained.Execution.commitCandidate`, accepting only whole-wire receipt equality.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoRunnerExecution

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (ProcWellSorted)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (StructuralCongruence)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep RhoStepAt
  rhoStepAt_preserves_closed)
open GeneralProgramResumptionExecution (JobRun ProgramRun)
open GeneralProgramDriverExecution (Invocation LicensedRequest invocations receipts)

/-! ## The model -/

/-- The depth-one rho plan: COMM at the root of the parallel bag. -/
abbrev plan : GeneralExecutionAdmission.Plan := GeneralRho.DepthOne.plan

/-- The depth-one rho plan reads no dynamic provider relations. -/
theorem finiteProvider : plan.snapshot.provider.dynamicRelations = [] := rfl

/-- The driver's run of the depth-one plan on a state, with one budget for every job. -/
def programOf (state : Pattern) (budget : Nat) : ProgramRun :=
  ProgramRun.ofInvocations (invocations plan [] (.base "Proc") state fun _ => budget)

/-- What one runner step reports. -/
inductive Outcome where
  | quiescent (state : Pattern)
  | stepped (state next : Pattern)
  | unsaturated (state : Pattern) (status : ProgramRun.Status)

/-- What the publication of a run on a canonical state reports: its first released receipt, or
quiescence when every job is complete and nothing is released. -/
def outcomeOf (state : Pattern) (program : ProgramRun) : Outcome :=
  match program.publication with
  | receipt :: _ => .stepped state receipt.target
  | [] => if program.status = .complete then .quiescent state else .unsaturated state program.status

/-- One runner step: canonicalize, run the driver, read the publication. -/
def step (process : Pattern) (budget : Nat) : Outcome :=
  outcomeOf (lexCanon process) (programOf (lexCanon process) budget)

/-- How a run ends. -/
inductive Ending where
  | quiescent
  | fuelSpent
  | unsaturated (status : ProgramRun.Status)

/-- At most `fuel` steps; the trace lists the canonical states in order. -/
def run : Nat → Pattern → Nat → List Pattern × Ending
  | 0, process, _ => ([lexCanon process], .fuelSpent)
  | fuel + 1, process, budget =>
      match step process budget with
      | .quiescent state => ([state], .quiescent)
      | .stepped state next => (state :: (run fuel next budget).1, (run fuel next budget).2)
      | .unsaturated state status => ([state], .unsaturated status)

/-! ## Published receipts are valid -/

theorem mem_aggregate_of_mem_publication {program : ProgramRun} {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ program.publication) : receipt ∈ program.aggregate := by
  induction program with
  | nil => simp [ProgramRun.publication] at member
  | cons job rest ih =>
    simp only [ProgramRun.aggregate, List.flatMap_cons, List.mem_append] at ih ⊢
    simp only [ProgramRun.publication] at member
    split at member
    · rcases List.mem_append.mp member with here | later
      · exact .inl here
      · exact .inr (ih later)
    · exact .inl member

/-- Every receipt the driver reads out on a state is a valid receipt of the depth-one plan there. -/
theorem valid_of_mem_receipts {state : Pattern} {budget : GeneralRuleJobs.Job → Nat}
    {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (invocations plan [] (.base "Proc") state budget).flatMap receipts) :
    receipt.Valid plan [] (.base "Proc") state := by
  obtain ⟨invocation, present, found⟩ := List.mem_flatMap.mp member
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  obtain ⟨answer, _, rfl⟩ := List.mem_map.mp found
  exact answer.property

theorem valid_of_mem_publication {state : Pattern} {budget : Nat} {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (programOf state budget).publication) :
    receipt.Valid plan [] (.base "Proc") state := by
  have aggregated := mem_aggregate_of_mem_publication member
  rw [programOf, ProgramRun.ofInvocations_aggregate] at aggregated
  exact valid_of_mem_receipts aggregated

/-! ## A complete job has read out everything -/

theorem settled_receipts (request : LicensedRequest) (budget extra : Nat)
    (settled : (JobRun.begin request budget).state.agenda = []) :
    receipts (request, budget + extra) = receipts (request, budget) := by
  have same := JobRun.resume_settled (JobRun.begin request budget) settled extra
  rw [JobRun.begin_resume] at same
  exact congrArg JobRun.receipts same

/-- When every job of the run is complete, its readout is the whole completed readout. -/
theorem aggregate_eq_completed {state : Pattern} {budget : Nat}
    (complete : ∀ job ∈ programOf state budget, job.complete = true) :
    (programOf state budget).aggregate =
      GeneralRuleJobExecution.completedReceipts plan [] (.base "Proc") state := by
  let cost : GeneralRuleJobs.Job → Nat := fun job =>
    (GeneralPremise.Execution.treeStart (GeneralPlanEnvironment.environment plan)
      (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost
  rw [← GeneralProgramDriverExecution.saturated_receipts_eq_completed plan [] (.base "Proc") state
    (fun job => budget + cost job) (fun job _ => Nat.le_add_left _ _)]
  rw [programOf, ProgramRun.ofInvocations_aggregate]
  unfold invocations
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro item member
  symm
  apply settled_receipts
  apply JobRun.settled_of_complete
  apply complete
  exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨item, member, rfl⟩, rfl⟩

/-! ## One step -/

theorem step_sound {process : Pattern} {budget : Nat} {state next : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true)
    (stepped : step process budget = .stepped state next) :
    state = lexCanon process ∧ StructuralCongruence process state ∧ RhoStepAt 1 state next := by
  unfold step outcomeOf at stepped
  split at stepped
  · rename_i receipt rest published
    simp only [Outcome.stepped.injEq] at stepped
    obtain ⟨rfl, rfl⟩ := stepped
    have member : receipt ∈ (programOf (lexCanon process) budget).publication := by
      rw [published]
      exact List.mem_cons_self
    obtain ⟨lexTyped, _⟩ := closed_lexCanon typed sealed
    exact ⟨rfl, lexCanon_sound process, GeneralRho.DepthOne.receipt_step lexTyped (valid_of_mem_publication member)⟩
  · split at stepped <;> cases stepped

/-- A complete, empty publication leaves no depth-one step on the canonical form. -/
theorem no_depth_one_step {process : Pattern} {budget : Nat}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true)
    (published : (programOf (lexCanon process) budget).publication = [])
    (complete : (programOf (lexCanon process) budget).status = .complete) :
    ∀ target, ¬ RhoStepAt 1 (lexCanon process) target := by
  intro target depthOne
  obtain ⟨lexTyped, lexSealed⟩ := closed_lexCanon typed sealed
  obtain ⟨receipt, valid, _⟩ :=
    GeneralRho.DepthOne.step_receipt lexTyped lexSealed (lexCanon_channelsDecided process) depthOne
  have completed := (GeneralRuleJobExecution.mem_completedReceipts_iff plan [] (.base "Proc")
    (lexCanon process) GeneralRho.DepthOne.stratified receipt).mpr valid
  have allComplete := (ProgramRun.status_complete_iff _).mp complete
  rw [← aggregate_eq_completed allComplete, ← ProgramRun.publication_complete _ allComplete,
    published] at completed
  cases completed

/-- **Quiescence is exact.** A reported quiescence means that neither the process nor its
canonical form has a rho step, at any depth. -/
theorem step_quiescent {process : Pattern} {budget : Nat} {state : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true)
    (quiet : step process budget = .quiescent state) :
    state = lexCanon process ∧ (∀ target, ¬ RhoStep process target) ∧ ∀ target, ¬ RhoStep state target := by
  unfold step outcomeOf at quiet
  split at quiet
  · cases quiet
  · rename_i published
    split at quiet
    · rename_i complete
      cases quiet
      have none := no_depth_one_step typed sealed published complete
      obtain ⟨lexTyped, lexSealed⟩ := closed_lexCanon typed sealed
      refine ⟨rfl, fun target reduction => ?_, fun target reduction => ?_⟩
      · obtain ⟨target', depthOne, _⟩ := lexStep_complete typed reduction
        exact none target' depthOne
      · obtain ⟨target', depthOne, _⟩ := lexStep_complete lexTyped reduction
        rw [lexCanon_idempotent] at depthOne
        exact none target' depthOne
    · cases quiet

/-! ## Enough budget -/

/-- The cost of a job's whole search. -/
def jobCost (job : GeneralRuleJobs.Job) : Nat :=
  (GeneralPremise.Execution.treeStart (GeneralPlanEnvironment.environment plan)
    (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost

/-- A budget saturates a state when it covers the whole search of every job there. -/
def Saturates (budget : Nat) (state : Pattern) : Prop :=
  ∀ job ∈ GeneralRuleJobs.jobs plan [] (.base "Proc") state, jobCost job ≤ budget

theorem begin_state_eq (request : LicensedRequest) (budget : Nat)
    (saturated : (GeneralPremise.Execution.treeStart request.val.environment request.val.goal).cost ≤ budget) :
    (JobRun.begin request budget).state = GeneralPremise.Execution.finish request.val.environment request.val.goal :=
  GeneralPremise.Execution.run_eq_finish_of_cost_le _ _ _ saturated

/-- Under a saturating budget every job on a closed process is complete: its search is drained and
COMM leaves no obligation unresolved. -/
theorem complete_of_saturates {state : Pattern} {budget : Nat}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] state)
    (saturates : Saturates budget state) :
    ∀ job ∈ programOf state budget, job.complete = true := by
  intro job member
  obtain ⟨invocation, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  have licensed := (GeneralRuleJobs.jobs_spec plan [] (.base "Proc") state item.val).mp item.property
  obtain ⟨_, ordinal, site⟩ := GeneralRho.DepthOne.job_root licensed
  have drained := begin_state_eq ⟨⟨plan, [], .base "Proc", state, item.val⟩, licensed⟩ budget
    (saturates item.val item.property)
  simp only [JobRun.complete, Bool.and_eq_true, List.isEmpty_iff]
  rw [drained]
  refine ⟨GeneralPremise.Execution.finish_settled _ _, ?_⟩
  change (GeneralPremise.Execution.finish (GeneralPlanEnvironment.environment plan)
    (.root item.val.site.focusBound item.val.site.focusType item.val.site.focus item.val.ordinal)).unresolved = []
  rw [site, ordinal, GeneralRho.DepthOne.environment_eq]
  exact GeneralRho.comm_root_resolved
    ((GeneralPlanEnvironment.typing_iff GeneralRho.plan [] (.base "Proc") state).mpr
      (GeneralRho.derived_process_open typed))

/-- **Enough budget never leaves a step unsaturated:** the step reports a rho step or quiescence. -/
theorem step_saturated {process : Pattern} {budget : Nat}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true)
    (saturates : Saturates budget (lexCanon process)) :
    (∃ next, step process budget = .stepped (lexCanon process) next) ∨
      step process budget = .quiescent (lexCanon process) := by
  have complete := (ProgramRun.status_complete_iff _).mpr
    (complete_of_saturates (closed_lexCanon typed sealed).1 saturates)
  unfold step outcomeOf
  split
  · rename_i receipt rest _
    exact .inl ⟨receipt.target, rfl⟩
  · exact .inr (by rw [if_pos complete])

/-- **With enough budget the runner finds a step whenever the process has one.** -/
theorem step_complete {process target : Pattern} {budget : Nat}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true)
    (saturates : Saturates budget (lexCanon process))
    (reduction : RhoStep process target) :
    ∃ next, step process budget = .stepped (lexCanon process) next := by
  rcases step_saturated typed sealed saturates with found | quiet
  · exact found
  · exact absurd reduction ((step_quiescent typed sealed quiet).2.1 target)

/-! ## Runs -/

/-- One link of a trace: the next state is the canonical form of a depth-one rho step of the state. -/
def Link (state next : Pattern) : Prop := ∃ target, RhoStepAt 1 state target ∧ next = lexCanon target

/-- **The trace is a reduction sequence modulo structural congruence.** It starts at the canonical
form of the process, and each state reaches the next by a depth-one rho step followed by the
canonical form, which is structurally congruent to the step's target. -/
theorem run_chain (fuel : Nat) {process : Pattern} (budget : Nat)
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true) :
    (run fuel process budget).1.head? = some (lexCanon process) ∧ (run fuel process budget).1.IsChain Link := by
  induction fuel generalizing process with
  | zero => exact ⟨rfl, List.isChain_singleton _⟩
  | succ fuel ih =>
    simp only [run]
    split
    · rename_i state quiet
      obtain ⟨rfl, _⟩ := step_quiescent typed sealed quiet
      exact ⟨rfl, List.isChain_singleton _⟩
    · rename_i state next stepped
      obtain ⟨rfl, _, depthOne⟩ := step_sound typed sealed stepped
      obtain ⟨lexTyped, lexSealed⟩ := closed_lexCanon typed sealed
      obtain ⟨nextTyped, nextSealed⟩ := rhoStepAt_preserves_closed lexTyped lexSealed depthOne
      obtain ⟨first, chain⟩ := ih nextTyped nextSealed
      refine ⟨rfl, List.isChain_cons.mpr ⟨?_, chain⟩⟩
      intro later found
      rw [first, Option.mem_some_iff] at found
      exact ⟨next, depthOne, found.symm⟩
    · rename_i state status _
      have state_eq : state = lexCanon process := by
        unfold step outcomeOf at *
        split at *
        · contradiction
        · split at * <;> simp_all
      exact ⟨by rw [state_eq]; rfl, List.isChain_singleton _⟩

/-- **A run ends in quiescence only where no rho step is left.** -/
theorem run_quiescent (fuel : Nat) {process : Pattern} (budget : Nat)
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true)
    (ended : (run fuel process budget).2 = .quiescent) :
    ∀ last ∈ (run fuel process budget).1.getLast?, ∀ target, ¬ RhoStep last target := by
  induction fuel generalizing process with
  | zero => cases ended
  | succ fuel ih =>
    simp only [run] at ended ⊢
    split at ended
    · rename_i state quiet
      obtain ⟨_, _, none⟩ := step_quiescent typed sealed quiet
      intro last found
      rw [List.getLast?_singleton, Option.mem_some_iff] at found
      exact found ▸ none
    · rename_i state next stepped
      obtain ⟨rfl, _, depthOne⟩ := step_sound typed sealed stepped
      obtain ⟨lexTyped, lexSealed⟩ := closed_lexCanon typed sealed
      obtain ⟨nextTyped, nextSealed⟩ := rhoStepAt_preserves_closed lexTyped lexSealed depthOne
      obtain ⟨first, _⟩ := run_chain fuel budget nextTyped nextSealed
      have nonempty : (run fuel next budget).1 ≠ [] := by
        intro empty
        rw [empty] at first
        cases first
      intro last found
      rw [List.getLast?_cons, List.getLast?_eq_some_getLast nonempty] at found
      apply ih nextTyped nextSealed ended last
      rw [List.getLast?_eq_some_getLast nonempty]
      simpa using found
    · cases ended

/-! ## Retained COMM search

The whole-run convenience function reports an unsaturated state. Continuing
one COMM search instead retains its program observation, so budget is added
to the pending matcher/premise frames rather than restarting them.
-/

structure Search where
  process : Pattern
  program : ProgramRun

namespace Search

def begin (process : Pattern) : Search :=
  ⟨lexCanon process, programOf (lexCanon process) 0⟩

def resume (search : Search) (extra : Nat) : Search :=
  ⟨search.process, search.program.resume extra⟩

def outcome (search : Search) : Outcome := outcomeOf search.process search.program

/-- The canonical process and the actually retained program share the same
source. The budget witness is work per job, not the number of COMM steps. -/
def Valid (search : Search) : Prop :=
  lexCanon search.process = search.process ∧
    ∃ budget, search.program = programOf search.process budget

theorem begin_valid (process : Pattern) : (begin process).Valid :=
  ⟨lexCanon_idempotent process, 0, rfl⟩

theorem reachable (search : Search) (valid : search.Valid) :
    ∀ job ∈ search.program, job.Reachable := by
  obtain ⟨_, budget, program⟩ := valid
  rw [program]
  exact ProgramRun.ofInvocations_reachable _

/-- Every job of a valid search reads no dynamic provider relations. -/
theorem finite (search : Search) (valid : search.Valid) :
    ∀ job ∈ search.program, job.request.val.environment.provider.dynamicRelations = [] := by
  obtain ⟨_, budget, program⟩ := valid
  rw [program]
  intro job member
  obtain ⟨invocation, present, rfl⟩ := List.mem_map.mp member
  exact GeneralProgramDriverExecution.invocations_finiteProvider plan finiteProvider [] (.base "Proc") _ _ invocation present

/-- An empty prefix is not a quiescence certificate while jobs remain pending
or blocked. Completion and emptiness are both required. -/
theorem outcome_quiescent_iff (search : Search) :
    search.outcome = .quiescent search.process ↔
      search.program.publication = [] ∧ search.program.status = .complete := by
  unfold outcome outcomeOf
  cases published : search.program.publication with
  | nil => cases search.program.status <;> simp
  | cons receipt rest => simp

theorem outcome_not_quiescent_of_incomplete (search : Search)
    (incomplete : search.program.status ≠ .complete) :
    search.outcome ≠ .quiescent search.process := by
  intro quiet
  exact incomplete ((outcome_quiescent_iff search).mp quiet).2

theorem resume_add (search : Search) (first extra : Nat) :
    (search.resume first).resume extra = search.resume (first + extra) := by
  simp only [resume, ProgramRun.resume_add]

theorem programOf_resume (process : Pattern) (first extra : Nat) :
    (programOf process first).resume extra = programOf process (first + extra) := by
  unfold programOf
  rw [ProgramRun.ofInvocations_resume]
  congr 1
  simp only [invocations, List.map_map, Function.comp_def]

theorem resume_valid (search : Search) (valid : search.Valid) (extra : Nat) :
    (search.resume extra).Valid := by
  obtain ⟨canonical, budget, exactProgram⟩ := valid
  refine ⟨canonical, budget + extra, ?_⟩
  simpa only [resume, exactProgram] using programOf_resume search.process budget extra

def trajectory (search : Search) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory
      (fun fuel current => current.resume fuel) search :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical _ search
    (by
      intro current
      have zero : current.program.resume 0 = current.program :=
        (current.program.trajectory.observation_eq_run 0).symm.trans current.program.trajectory.at_zero
      cases current
      simpa only [resume] using congrArg (Search.mk _) zero)
    (fun first extra current => (resume_add current first extra).symm)

theorem trajectory_publication_prefix (search : Search) (first extra : Nat) :
    ((search.trajectory).observation first).program.publication <+:
      ((search.trajectory).observation (first + extra)).program.publication :=
  search.trajectory.observer_prefix_after_resume (fun current => current.program.publication)
    (fun fuel current => ProgramRun.publication_prefix current.program fuel) first extra

/-- The retained search has exactly the old step's observation at its
accumulated budget. Its operational state was resumed, not reconstructed. -/
theorem outcome_eq_step (search : Search) (budget : Nat)
    (canonical : lexCanon search.process = search.process)
    (program : search.program = programOf search.process budget) :
    search.outcome = step search.process budget := by
  simp only [outcome, step, canonical, program]

theorem outcome_sound (search : Search) (valid : search.Valid)
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] search.process)
    (sealed : binderSafeAt "NQuote" 0 search.process = true) {state next : Pattern}
    (stepped : search.outcome = .stepped state next) :
    state = search.process ∧ RhoStepAt 1 state next := by
  obtain ⟨canonical, budget, program⟩ := valid
  rw [outcome_eq_step search budget canonical program] at stepped
  obtain ⟨same, _, reduction⟩ := step_sound typed sealed stepped
  exact ⟨same.trans canonical, reduction⟩

/-- Settlement remains a semantic quiescence claim only with the existing
typed/closed COMM adequacy. Zero allowance alone cannot establish it. -/
theorem outcome_quiescent (search : Search) (valid : search.Valid)
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] search.process)
    (sealed : binderSafeAt "NQuote" 0 search.process = true) {state : Pattern}
    (quiet : search.outcome = .quiescent state) :
    state = search.process ∧ ∀ target, ¬ RhoStep search.process target := by
  obtain ⟨canonical, budget, program⟩ := valid
  rw [outcome_eq_step search budget canonical program] at quiet
  obtain ⟨same, none, _⟩ := step_quiescent typed sealed quiet
  exact ⟨same.trans canonical, none⟩

end Search

/-! ## Retained whole-process execution

Matcher budget stays on `Search.resume`. `advance` counts committed COMM steps.
`commit` selects the first receipt of the retained search once that search is
complete; it does not compare an externally supplied candidate. A candidate
commit uses `receiptWireEq`, the constructive `Term.decEq` test of the whole
receipt wire, so job, matcher trace, captured and completed assignments, query
history, local target and target all have to agree. Bag agreement of two
publications is not a commuting-effects theorem. The execution value itself
grants no authority: a saved copy is a fork, and committing one binding leaves
the saved binding on its search, which can commit the same receipt itself.
Exclusive authority is the common owned host's epoch ticket (`owned_publication`
below): it serves one holder, refuses copies of used tickets and delivers each
committed COMM once. `commitPublished` admits another published occurrence as an
explicit selection policy. The occurrence-cell adapter below validates local
candidates after world changes; it never relabels an old whole-process search.
Native atomicity and crash recovery remain implementation obligations.
-/

namespace Retained

/-- One committed communication. The receipt is the publication object, so its
binding and query provenance are part of the history. -/
structure Commit where
  before : Pattern
  receipt : GeneralRuleJobs.Receipt
  after : Pattern

inductive Phase where
  | live (search : Search)
  | done (process : Pattern)
  | cancelled

structure Execution where
  history : List Commit
  phase : Phase

/-- Whole-wire equality of two receipts. `Term.decEq` is the constructed
decidable equality of the carrier; this definition does not use
`Classical.choice`. -/
def receiptWireEq (left right : GeneralRuleJobs.Receipt) : Bool :=
  match Mettapedia.GSLT.LanguageDef.CettaWire.Term.decEq
      (ScopedRuleJobReadoutExecution.receiptTerm left)
      (ScopedRuleJobReadoutExecution.receiptTerm right) with
  | .isTrue _ => true
  | .isFalse _ => false

theorem receiptWireEq_eq_decide (left right : GeneralRuleJobs.Receipt) :
    receiptWireEq left right =
      decide (ScopedRuleJobReadoutExecution.receiptTerm left =
        ScopedRuleJobReadoutExecution.receiptTerm right) := by
  unfold receiptWireEq
  cases Mettapedia.GSLT.LanguageDef.CettaWire.Term.decEq
      (ScopedRuleJobReadoutExecution.receiptTerm left)
      (ScopedRuleJobReadoutExecution.receiptTerm right) with
  | isTrue same => simp [same]
  | isFalse different =>
    simp [decide_eq_false_iff_not.mpr different]

theorem receiptWireEq_iff (left right : GeneralRuleJobs.Receipt) :
    receiptWireEq left right = true ↔ left = right := by
  rw [receiptWireEq_eq_decide, decide_eq_true_iff]
  exact ScopedRuleJobReadoutExecution.receiptTerm_injective.eq_iff

theorem receiptWireEq_iff_fields (left right : GeneralRuleJobs.Receipt) :
    receiptWireEq left right = true ↔
      left.job = right.job ∧ left.matcherTrace = right.matcherTrace ∧
      left.captured = right.captured ∧ left.completed = right.completed ∧
      left.premiseHistory = right.premiseHistory ∧
      left.localTarget = right.localTarget ∧ left.target = right.target := by
  rw [receiptWireEq_iff]
  constructor
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro ⟨job, trace, captured, completed, history, localTarget, target⟩
    cases left
    cases right
    cases job
    cases trace
    cases captured
    cases completed
    cases history
    cases localTarget
    cases target
    rfl

theorem equal_targets_do_not_identify_receipts
    (left right : GeneralRuleJobs.Receipt)
    (_sameTarget : left.target = right.target)
    (differentHistory : left.premiseHistory ≠ right.premiseHistory) :
    receiptWireEq left right = false ∧ left ≠ right := by
  refine ⟨?_, fun same => differentHistory (congrArg (·.premiseHistory) same)⟩
  cases flag : receiptWireEq left right with
  | false => rfl
  | true =>
    exact absurd (congrArg (·.premiseHistory) ((receiptWireEq_iff left right).mp flag))
      differentHistory

def begin (process : Pattern) : Execution where
  history := []
  phase := .live (Search.begin process)

namespace Execution

def resumeSearch (execution : Execution) (extra : Nat) : Execution :=
  match execution.phase with
  | .live search => { execution with phase := .live (search.resume extra) }
  | .done _ | .cancelled => execution

/-- Commit the first published receipt of the retained search. The receipt is
that publication entry, not a value rebuilt from its target. -/
def commit (execution : Execution) : Execution :=
  match execution.phase with
  | .live search =>
    match search.program.publication, search.program.status with
    | [], .complete => { execution with phase := .done search.process }
    | receipt :: _, .complete =>
      let after := lexCanon receipt.target
      { history := execution.history ++ [⟨search.process, receipt, after⟩],
        phase := .live (Search.begin after) }
    | _, _ => execution
  | .done _ | .cancelled => execution

/-- An external candidate is accepted only when its whole wire equals the
selected receipt of this retained search. -/
def commitCandidate (execution : Execution) (candidate : GeneralRuleJobs.Receipt) : Execution :=
  match execution.phase with
  | .live search =>
    match search.program.publication, search.program.status with
    | receipt :: _, .complete =>
      if receiptWireEq candidate receipt then commit execution else execution
    | _, _ => execution
  | .done _ | .cancelled => execution

def cancel (execution : Execution) : Execution :=
  { history := execution.history, phase := .cancelled }

/-- COMM fuel. Zero leaves the execution unchanged. A positive count applies
`commit` once and continues on that result with one less fuel. When `commit`
fixes the execution, the remaining fuel is still spent applying that same
fixed `commit`. This walk leaves the matcher budget unchanged. -/
def advance : Nat → Execution → Execution
  | 0, execution => execution
  | fuel + 1, execution => advance fuel (commit execution)

def quiescent (execution : Execution) : Prop :=
  match execution.phase with
  | .done _ => True
  | .live search => search.program.publication = [] ∧ search.program.status = .complete
  | .cancelled => False

end Execution

open Execution

theorem begin_canonical (process : Pattern) (canonical : lexCanon process = process) :
    (Search.begin process).process = process ∧
      (Search.begin process).program = programOf process 0 := by
  simp [Search.begin, canonical]

theorem begun_resume (process : Pattern) (budget : Nat) (canonical : lexCanon process = process) :
    (Search.begin process).resume budget = ⟨process, programOf process budget⟩ := by
  simp [Search.begin, Search.resume, canonical, Search.programOf_resume]

theorem resumeSearch_continues (execution : Execution) (search : Search) (extra : Nat)
    (live : execution.phase = .live search) :
    (execution.resumeSearch extra).history = execution.history ∧
      (execution.resumeSearch extra).phase = .live (search.resume extra) ∧
      (search.resume extra).program = search.program.resume extra := by
  cases execution
  cases live
  simp [resumeSearch, Search.resume]

theorem resumeSearch_valid (execution : Execution) (search : Search) (extra : Nat)
    (live : execution.phase = .live search) (valid : search.Valid) :
    ((execution.resumeSearch extra).phase = .live (search.resume extra)) ∧
      (search.resume extra).Valid :=
  ⟨(resumeSearch_continues execution search extra live).2.1, Search.resume_valid search valid extra⟩

theorem resumeSearch_appends_nothing (execution : Execution) (extra : Nat) :
    (execution.resumeSearch extra).history = execution.history := by
  cases execution with
  | mk history phase =>
    cases phase <;> simp [resumeSearch]

theorem live_quiescent_iff (execution : Execution) (search : Search)
    (live : execution.phase = .live search) :
    execution.quiescent ↔
      search.program.publication = [] ∧ search.program.status = .complete := by
  cases execution
  cases live
  simp [quiescent]

theorem pending_not_quiescent (execution : Execution) (search : Search)
    (live : execution.phase = .live search)
    (pending : search.program.status ≠ .complete) :
    ¬ execution.quiescent := by
  intro quiet
  exact pending ((live_quiescent_iff execution search live).mp quiet).2

theorem zero_prefix_not_quiescent (process : Pattern)
    (pending : (Search.begin process).program.status ≠ .complete) :
    ¬ (begin process).quiescent :=
  pending_not_quiescent (begin process) (Search.begin process) rfl pending

theorem partial_prefix_not_quiescent (process : Pattern) (budget : Nat)
    (pending : ((Search.begin process).resume budget).program.status ≠ .complete) :
    ¬ ((begin process).resumeSearch budget).quiescent :=
  pending_not_quiescent ((begin process).resumeSearch budget)
    ((Search.begin process).resume budget) (by simp [begin, resumeSearch]) pending

theorem commit_pending (execution : Execution) (search : Search)
    (live : execution.phase = .live search)
    (pending : search.program.status ≠ .complete) :
    commit execution = execution := by
  cases execution
  cases live
  cases status : search.program.status with
  | complete => exact absurd status pending
  | blocked =>
    cases publication : search.program.publication <;> simp [commit, status, publication]
  | pending =>
    cases publication : search.program.publication <;> simp [commit, status, publication]

theorem commit_done (execution : Execution) (process : Pattern)
    (done : execution.phase = .done process) :
    commit execution = execution := by
  cases execution
  cases done
  simp [commit]

theorem commit_cancelled (execution : Execution) (cancelled : execution.phase = .cancelled) :
    commit execution = execution := by
  cases execution
  cases cancelled
  simp [commit]

theorem commit_history_prefix (execution : Execution) :
    execution.history <+: (commit execution).history := by
  cases execution with
  | mk history phase =>
    cases phase with
    | done process => simp [commit]
    | cancelled => simp [commit]
    | live search =>
      cases status : search.program.status <;>
        cases publication : search.program.publication <;>
          simp [commit, status, publication, List.prefix_append]

theorem commit_licenses (execution : Execution) (search : Search)
    (receipt : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (live : execution.phase = .live search) (valid : search.Valid)
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] search.process)
    (published : search.program.publication = receipt :: rest)
    (complete : search.program.status = .complete) :
    receipt.Valid plan [] (.base "Proc") search.process ∧
      RhoStepAt 1 search.process receipt.target ∧
      (commit execution).history =
        execution.history ++ [⟨search.process, receipt, lexCanon receipt.target⟩] ∧
      (commit execution).phase = .live (Search.begin (lexCanon receipt.target)) ∧
      ((commit execution).history.getLast?).map (·.receipt) = some receipt := by
  obtain ⟨canonical, budget, program⟩ := valid
  have member : receipt ∈ (programOf search.process budget).publication := by
    rw [← program, published]
    exact List.mem_cons_self
  refine ⟨valid_of_mem_publication member,
    GeneralRho.DepthOne.receipt_step typed (valid_of_mem_publication member), ?_, ?_, ?_⟩
  · cases execution
    cases live
    simp [commit, published, complete]
  · cases execution
    cases live
    simp [commit, published, complete]
  · cases execution
    cases live
    simp [commit, published, complete]

theorem commit_agrees_at_completed_boundary (history : List Commit) (process : Pattern)
    (budget budget' : Nat) (publication : (programOf process budget).publication =
      (programOf process budget').publication)
    (complete : (programOf process budget).status = .complete)
    (complete' : (programOf process budget').status = .complete) :
    commit ⟨history, .live ⟨process, programOf process budget⟩⟩ =
      commit ⟨history, .live ⟨process, programOf process budget'⟩⟩ := by
  cases published : (programOf process budget).publication with
  | nil =>
    have published' : (programOf process budget').publication = [] := by
      rw [← publication, published]
    simp [commit, published, published', complete, complete']
  | cons receipt rest =>
    have published' : (programOf process budget').publication = receipt :: rest := by
      rw [← publication, published]
    simp [commit, published, published', complete, complete']

theorem unselected_alternative_not_committed (execution : Execution) (search : Search)
    (selected alternative : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (live : execution.phase = .live search)
    (published : search.program.publication = selected :: alternative :: rest)
    (complete : search.program.status = .complete)
    (different : alternative ≠ selected) :
    ∀ entry ∈ (commit execution).history, entry.receipt = alternative → entry ∈ execution.history := by
  intro entry member same
  cases execution
  cases live
  simp [commit, published, complete, List.mem_append] at member
  cases member with
  | inl earlier => exact earlier
  | inr here =>
    cases here
    exact absurd same different.symm

theorem commitCandidate_refused_while_pending (execution : Execution) (search : Search)
    (candidate : GeneralRuleJobs.Receipt) (live : execution.phase = .live search)
    (pending : search.program.status ≠ .complete) :
    commitCandidate execution candidate = execution := by
  cases execution
  cases live
  cases status : search.program.status with
  | complete => exact absurd status pending
  | blocked =>
    cases publication : search.program.publication <;>
      simp [commitCandidate, status, publication]
  | pending =>
    cases publication : search.program.publication <;>
      simp [commitCandidate, status, publication]

theorem commitCandidate_accepts_selected_receipt (execution : Execution) (search : Search)
    (receipt : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (live : execution.phase = .live search)
    (published : search.program.publication = receipt :: rest)
    (complete : search.program.status = .complete) :
    commitCandidate execution receipt = commit execution := by
  have accepted : receiptWireEq receipt receipt = true :=
    (receiptWireEq_iff receipt receipt).mpr rfl
  cases execution
  cases live
  simp [commitCandidate, published, complete, accepted]

theorem foreign_candidate_refused (execution : Execution) (search : Search)
    (selected foreign : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (live : execution.phase = .live search)
    (published : search.program.publication = selected :: rest)
    (complete : search.program.status = .complete)
    (different : foreign ≠ selected) :
    commitCandidate execution foreign = execution := by
  have refused : receiptWireEq foreign selected = false := by
    cases flag : receiptWireEq foreign selected with
    | false => rfl
    | true => exact absurd ((receiptWireEq_iff foreign selected).mp flag) different
  cases execution
  cases live
  simp [commitCandidate, published, complete, refused]

theorem stale_candidate_refused (execution : Execution) (search : Search)
    (receipt : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (candidate : GeneralRuleJobs.Receipt) (live : execution.phase = .live search)
    (published : search.program.publication = receipt :: rest)
    (complete : search.program.status = .complete)
    (pending : (Search.begin (lexCanon receipt.target)).program.status ≠ .complete) :
    commitCandidate (commit execution) candidate = commit execution := by
  have stepped : (commit execution).phase = .live (Search.begin (lexCanon receipt.target)) := by
    cases execution
    cases live
    simp [commit, published, complete]
  exact commitCandidate_refused_while_pending (commit execution)
    (Search.begin (lexCanon receipt.target)) candidate stepped pending

theorem advance_zero (execution : Execution) : advance 0 execution = execution := rfl

theorem advance_add (first extra : Nat) (execution : Execution) :
    advance (first + extra) execution = advance extra (advance first execution) := by
  induction first generalizing execution with
  | zero =>
    rw [Nat.zero_add]
    simp only [advance]
  | succ first ih =>
    rw [Nat.succ_add]
    simp only [advance]
    exact ih (commit execution)

theorem advance_of_commit_fixed (execution : Execution) (fuel : Nat)
    (fixed : commit execution = execution) :
    advance fuel execution = execution := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [advance, fixed, ih]

theorem advance_pending_keeps_search (execution : Execution) (search : Search) (fuel : Nat)
    (live : execution.phase = .live search)
    (pending : search.program.status ≠ .complete) :
    advance fuel execution = execution :=
  advance_of_commit_fixed execution fuel (commit_pending execution search live pending)

theorem advance_done (execution : Execution) (process : Pattern) (fuel : Nat)
    (done : execution.phase = .done process) :
    advance fuel execution = execution :=
  advance_of_commit_fixed execution fuel (commit_done execution process done)

theorem advance_cancelled (execution : Execution) (fuel : Nat)
    (cancelled : execution.phase = .cancelled) :
    advance fuel execution = execution :=
  advance_of_commit_fixed execution fuel (commit_cancelled execution cancelled)

theorem advance_history_prefix (execution : Execution) (fuel : Nat) :
    execution.history <+: (advance fuel execution).history := by
  induction fuel generalizing execution with
  | zero => exact List.prefix_refl execution.history
  | succ fuel ih =>
    exact (commit_history_prefix execution).trans (by simpa [advance] using ih (commit execution))

def trajectory (execution : Execution) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory advance execution :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical advance execution
    (fun _ => rfl) advance_add

theorem trajectory_observation (execution : Execution) (fuel : Nat) :
    (trajectory execution).observation fuel = advance fuel execution := rfl

theorem trajectory_residual_after_settlement (execution : Execution) (first extra : Nat)
    (settled : commit ((trajectory execution).observation first) =
      (trajectory execution).observation first) :
    (trajectory execution).observation (first + extra) =
      (trajectory execution).observation first :=
  (trajectory execution).observation_constant_after_settlement
    (fun current => commit current = current)
    (fun current fixed fuel => advance_of_commit_fixed current fuel fixed)
    first extra settled

/-- Cancellation keeps the committed receipts and drops this execution's phase.
It is a local flag. It does not establish native one-shot resources or
world-update validation. -/
theorem cancel_is_local (execution : Execution) :
    (cancel execution).history = execution.history ∧
      (cancel execution).phase = .cancelled ∧
      (∀ search, (cancel execution).phase ≠ .live search) := by
  refine ⟨rfl, rfl, ?_⟩
  intro search same
  cases same

theorem cancel_keeps_committed_history (execution : Execution) (fuel : Nat) :
    (advance fuel (cancel execution)).history = execution.history ∧
      (cancel execution).phase = .cancelled := by
  refine ⟨?_, rfl⟩
  rw [advance_cancelled (cancel execution) fuel rfl]
  simp [cancel]

/-- Saving this execution and committing another binding are independent.
The saved value stays on the original live search. Its history is not the
committed history. Applying `commitCandidate` to the saved value, with the
selected receipt, produces that committed successor. External one-shot
authority is not a consequence of this copy. -/
theorem copied_state_is_a_fork (execution : Execution) (search : Search)
    (receipt : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (live : execution.phase = .live search)
    (published : search.program.publication = receipt :: rest)
    (complete : search.program.status = .complete) :
    execution.phase = .live search ∧
      execution.history ≠ (commit execution).history ∧
      (commit execution).phase = .live (Search.begin (lexCanon receipt.target)) ∧
      commitCandidate execution receipt = commit execution ∧
      (commitCandidate execution receipt).history =
        execution.history ++ [⟨search.process, receipt, lexCanon receipt.target⟩] := by
  have grown : (commit execution).history =
      execution.history ++ [⟨search.process, receipt, lexCanon receipt.target⟩] := by
    cases execution
    cases live
    simp [commit, published, complete]
  have moved : (commit execution).phase = .live (Search.begin (lexCanon receipt.target)) := by
    cases execution
    cases live
    simp [commit, published, complete]
  have accepted :=
    commitCandidate_accepts_selected_receipt execution search receipt rest live published complete
  refine ⟨live, ?_, moved, accepted, ?_⟩
  · intro same
    rw [grown] at same
    have lengths := congrArg List.length same
    simp only [List.length_append, List.length_cons, List.length_nil] at lengths
    omega
  · simpa [accepted] using grown

/-- The saved execution remains the original live search after another binding
commits. That saved execution can itself commit the selected receipt, and the
resulting history is the one-step extension. -/
theorem fork_remains_after_commit (execution : Execution) (search : Search)
    (receipt : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (live : execution.phase = .live search)
    (published : search.program.publication = receipt :: rest)
    (complete : search.program.status = .complete) :
    execution.phase = .live search ∧
      commitCandidate execution receipt = commit execution ∧
      (commit execution).history =
        execution.history ++ [⟨search.process, receipt, lexCanon receipt.target⟩] ∧
      (commit execution).phase = .live (Search.begin (lexCanon receipt.target)) := by
  refine ⟨live,
    commitCandidate_accepts_selected_receipt execution search receipt rest live published complete,
    ?_, ?_⟩
  · cases execution
    cases live
    simp [commit, published, complete]
  · cases execution
    cases live
    simp [commit, published, complete]

theorem two_communications (process next final : Pattern)
    (first second : GeneralRuleJobs.Receipt)
    (firstRest secondRest : List GeneralRuleJobs.Receipt)
    (partialBudget full nextBudget : Nat)
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (canonical : lexCanon process = process)
    (pausedPending : ((Search.begin process).resume partialBudget).program.status ≠ .complete)
    (readyPublished : ((Search.begin process).resume full).program.publication =
      first :: firstRest)
    (readyComplete : ((Search.begin process).resume full).program.status = .complete)
    (firstCanonical : lexCanon first.target = next)
    (typedNext : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] next)
    (nextPending : (Search.begin next).program.status ≠ .complete)
    (secondPublished : ((Search.begin next).resume nextBudget).program.publication =
      second :: secondRest)
    (secondComplete : ((Search.begin next).resume nextBudget).program.status = .complete)
    (secondCanonical : lexCanon second.target = final) :
    let started := begin process
    let paused := started.resumeSearch partialBudget
    let ready := started.resumeSearch full
    let afterFirst := ready.commit
    let resumedNext := afterFirst.resumeSearch nextBudget
    let afterSecond := resumedNext.commit
    paused.history = [] ∧ ¬ paused.quiescent ∧
      paused.phase = .live ((Search.begin process).resume partialBudget) ∧
      afterFirst.history = [⟨process, first, next⟩] ∧
      afterFirst.phase = .live (Search.begin next) ∧
      (∀ fuel, advance fuel afterFirst = afterFirst) ∧
      commitCandidate afterFirst first = afterFirst ∧
      afterSecond.history = [⟨process, first, next⟩, ⟨next, second, final⟩] ∧
      RhoStepAt 1 process first.target ∧ RhoStepAt 1 next second.target ∧
      (process = next ∧ next = final ∧ first ≠ second →
        (⟨process, first, next⟩ : Commit) ≠ ⟨next, second, final⟩) := by
  have pausedPhase : ((begin process).resumeSearch partialBudget).phase =
      .live ((Search.begin process).resume partialBudget) := by
    simp [begin, resumeSearch]
  have readySearch : (Search.begin process).resume full = ⟨process, programOf process full⟩ :=
    begun_resume process full canonical
  have nextCanonical : lexCanon next = next := by
    simpa [firstCanonical] using lexCanon_idempotent first.target
  have readyProcess : ((Search.begin process).resume full).process = process := by
    simp only [Search.resume]
    exact (begin_canonical process canonical).1
  have nextProcess : ((Search.begin next).resume nextBudget).process = next := by
    simp only [Search.resume]
    exact (begin_canonical next nextCanonical).1
  have readyHistory : ((begin process).resumeSearch full).history = [] := by
    rw [resumeSearch_appends_nothing (begin process) full]
    simp only [begin]
  have firstStep := commit_licenses ((begin process).resumeSearch full)
    ((Search.begin process).resume full) first firstRest
    (by simp [begin, resumeSearch]) (by
      simpa [readySearch] using Search.resume_valid (Search.begin process) (Search.begin_valid process) full)
    (by simpa [begun_resume process full canonical] using typed) readyPublished readyComplete
  have secondLive : (((begin process).resumeSearch full).commit).phase =
      .live (Search.begin next) := by
    simpa [firstCanonical] using firstStep.2.2.2.1
  have secondHistory : (((begin process).resumeSearch full).commit).history =
      [⟨process, first, next⟩] := by
    rw [firstStep.2.2.1, readyHistory, List.nil_append, readyProcess, firstCanonical]
  have resumedPhase :
      ((((begin process).resumeSearch full).commit).resumeSearch nextBudget).phase =
        .live ((Search.begin next).resume nextBudget) :=
    (resumeSearch_continues (((begin process).resumeSearch full).commit)
      (Search.begin next) nextBudget secondLive).2.1
  have secondStep := commit_licenses
    ((((begin process).resumeSearch full).commit).resumeSearch nextBudget)
    ((Search.begin next).resume nextBudget) second secondRest
    resumedPhase
    (Search.resume_valid (Search.begin next) (Search.begin_valid next) nextBudget)
    (nextProcess.symm ▸ typedNext)
    secondPublished secondComplete
  refine ⟨?_, ?_, pausedPhase, secondHistory, secondLive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [begin, resumeSearch]
  · exact partial_prefix_not_quiescent process partialBudget pausedPending
  · intro fuel
    exact advance_of_commit_fixed _ fuel
      (commit_pending (((begin process).resumeSearch full).commit) (Search.begin next)
        secondLive nextPending)
  · exact stale_candidate_refused ((begin process).resumeSearch full)
      ((Search.begin process).resume full) first firstRest first
      (by simp [begin, resumeSearch]) readyPublished readyComplete
      (by simpa [firstCanonical] using nextPending)
  · rw [secondStep.2.2.1,
      resumeSearch_appends_nothing (((begin process).resumeSearch full).commit) nextBudget,
      secondHistory, nextProcess, secondCanonical, List.singleton_append]
  · rw [← readyProcess]
    exact firstStep.2.1
  · rw [← nextProcess]
    exact secondStep.2.1
  · intro ⟨_, _, different⟩ same
    exact different (congrArg (·.receipt) same)

/-! ## Reached histories

A retained execution is reached from a process by the operations of this
module: beginning, resuming the live search, committing, committing a
candidate and cancelling. Every reached execution carries a chronological
history: each commit is a valid receipt of the depth-one plan at the state
where it was committed, licenses a depth-one COMM from that state, and its
canonical result is the state of the next commit. A live search runs on the
history's endpoint; a done phase is that endpoint with a complete, empty
publication; a cancelled phase keeps the history and has no search.
-/

/-- Commit a specified occurrence from the completed publication. Whole-wire
membership retains its matcher path and binding provenance. The successor
process retains the unconsumed components; a new search is started there,
since the old search's jobs were licensed at a different whole process. -/
def Execution.commitPublished (execution : Execution) (candidate : GeneralRuleJobs.Receipt) : Execution :=
  match execution.phase with
  | .live search =>
    if search.program.status = .complete ∧
        search.program.publication.any (receiptWireEq candidate) = true then
      ⟨execution.history ++ [⟨search.process, candidate, lexCanon candidate.target⟩],
        .live (Search.begin (lexCanon candidate.target))⟩
    else execution
  | .done _ | .cancelled => execution

theorem published_wire_member (candidate : GeneralRuleJobs.Receipt)
    (publication : List GeneralRuleJobs.Receipt) :
    publication.any (receiptWireEq candidate) = true ↔ candidate ∈ publication := by
  simp only [List.any_eq_true, receiptWireEq_iff]
  exact ⟨fun ⟨receipt, member, same⟩ => same ▸ member,
    fun member => ⟨candidate, member, rfl⟩⟩

theorem commitPublished_accepts (history : List Commit) (search : Search)
    (candidate : GeneralRuleJobs.Receipt) (complete : search.program.status = .complete)
    (member : candidate ∈ search.program.publication) :
    (Execution.commitPublished ⟨history, .live search⟩ candidate) =
      ⟨history ++ [⟨search.process, candidate, lexCanon candidate.target⟩],
        .live (Search.begin (lexCanon candidate.target))⟩ := by
  simp [Execution.commitPublished, complete, (published_wire_member _ _).mpr member]

theorem commitPublished_refuses (history : List Commit) (search : Search)
    (candidate : GeneralRuleJobs.Receipt) (absent : candidate ∉ search.program.publication) :
    (Execution.commitPublished ⟨history, .live search⟩ candidate) = ⟨history, .live search⟩ := by
  simp only [Execution.commitPublished]
  exact if_neg (fun h => absent ((published_wire_member _ _).mp h.2))

theorem commitPublished_history_prefix (execution : Execution) (candidate : GeneralRuleJobs.Receipt) :
    execution.history <+: (execution.commitPublished candidate).history := by
  cases execution with
  | mk history phase =>
    cases phase with
    | live search =>
      simp only [Execution.commitPublished]
      split <;> simp [List.prefix_append]
    | done process => exact List.prefix_refl _
    | cancelled => exact List.prefix_refl _

theorem commitPublished_head (execution : Execution) (search : Search)
    (candidate : GeneralRuleJobs.Receipt) (rest : List GeneralRuleJobs.Receipt)
    (live : execution.phase = .live search) (complete : search.program.status = .complete)
    (published : search.program.publication = candidate :: rest) :
    execution.commitPublished candidate = execution.commitCandidate candidate := by
  rw [commitCandidate_accepts_selected_receipt execution search candidate rest live published complete]
  cases execution
  cases live
  rw [commitPublished_accepts _ _ _ complete (by simp [published])]
  simp [Execution.commit, published, complete]


/-- A chronological COMM history from a state. -/
inductive Chronicle : Pattern → List Commit → Prop where
  | nil (state : Pattern) : Chronicle state []
  | cons {state : Pattern} {receipt : GeneralRuleJobs.Receipt} {rest : List Commit}
      (valid : receipt.Valid plan [] (.base "Proc") state)
      (step : RhoStepAt 1 state receipt.target)
      (tail : Chronicle (lexCanon receipt.target) rest) :
      Chronicle state (⟨state, receipt, lexCanon receipt.target⟩ :: rest)

/-- The state reached by a history from a state. -/
def endpoint (state : Pattern) : List Commit → Pattern
  | [] => state
  | commit :: rest => endpoint commit.after rest

@[simp] theorem endpoint_nil (state : Pattern) : endpoint state [] = state := rfl

@[simp] theorem endpoint_cons (state : Pattern) (commit : Commit) (rest : List Commit) :
    endpoint state (commit :: rest) = endpoint commit.after rest := rfl

theorem endpoint_append_single (state : Pattern) (history : List Commit) (commit : Commit) :
    endpoint state (history ++ [commit]) = commit.after := by
  induction history generalizing state with
  | nil => rfl
  | cons first rest ih => exact ih first.after

/-- Appending one commit at the endpoint keeps a chronicle. -/
theorem Chronicle.append {state : Pattern} {history : List Commit}
    (chronicle : Chronicle state history) {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan [] (.base "Proc") (endpoint state history))
    (step : RhoStepAt 1 (endpoint state history) receipt.target) :
    Chronicle state
      (history ++ [⟨endpoint state history, receipt, lexCanon receipt.target⟩]) := by
  induction chronicle with
  | nil state => exact .cons valid step (.nil _)
  | cons valid' step' _ ih => exact .cons valid' step' (ih valid step)

/-- A chronicle is a chain of canonical depth-one links. -/
theorem Chronicle.chain {state : Pattern} {history : List Commit}
    (chronicle : Chronicle state history) :
    (state :: history.map (·.after)).IsChain Link := by
  induction chronicle with
  | nil state => exact List.isChain_singleton _
  | @cons state receipt rest valid step tail ih =>
    refine List.isChain_cons_cons.mpr ⟨⟨receipt.target, step, rfl⟩, ?_⟩
    simpa using ih

/-- Each commit starts exactly where the previous one ended. -/
theorem Chronicle.before_eq {state : Pattern} {history : List Commit}
    (chronicle : Chronicle state history) :
    history.map (·.before) = (state :: history.map (·.after)).dropLast := by
  induction chronicle with
  | nil state => rfl
  | @cons state receipt rest valid step tail ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simp only [List.map_cons, List.dropLast_cons_cons] at ih ⊢
      rw [ih]

/-- Every committed receipt licenses a depth-one COMM from the state where it
was committed. -/
theorem Chronicle.receipts_valid {state : Pattern} {history : List Commit}
    (chronicle : Chronicle state history) :
    ∀ commit ∈ history, commit.receipt.Valid plan [] (.base "Proc") commit.before ∧
      RhoStepAt 1 commit.before commit.receipt.target ∧
      commit.after = lexCanon commit.receipt.target := by
  induction chronicle with
  | nil state => intro commit member; cases member
  | @cons state receipt rest valid step tail ih =>
    intro commit member
    rcases List.mem_cons.mp member with here | later
    · subst here
      exact ⟨valid, step, rfl⟩
    · exact ih commit later

/-- The endpoint of a chronicle is reachable by canonical links. -/
theorem Chronicle.reaches {state : Pattern} {history : List Commit}
    (chronicle : Chronicle state history) :
    Relation.ReflTransGen Link state (endpoint state history) := by
  induction chronicle with
  | nil state => exact .refl
  | @cons state receipt rest valid step tail ih =>
    exact Relation.ReflTransGen.head ⟨receipt.target, step, rfl⟩ ih

/-- The phase agrees with the endpoint of the history. -/
inductive PhaseSound (state : Pattern) : Phase → Prop where
  | live {search : Search} (process : search.process = state) (valid : search.Valid) :
      PhaseSound state (.live search)
  | done {process : Pattern} (at_ : process = state)
      (quiet : ∃ budget, (programOf state budget).publication = [] ∧
        (programOf state budget).status = .complete) :
      PhaseSound state (.done process)
  | cancelled : PhaseSound state .cancelled

/-- What every reached execution satisfies. -/
structure Sound (start : Pattern) (execution : Execution) : Prop where
  chronicle : Chronicle (lexCanon start) execution.history
  phase : PhaseSound (endpoint (lexCanon start) execution.history) execution.phase
  typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) []
    (endpoint (lexCanon start) execution.history)
  sealed : binderSafeAt "NQuote" 0 (endpoint (lexCanon start) execution.history) = true

/-- The executions reached from a process by the retained operations. -/
inductive Reached (start : Pattern) : Execution → Prop where
  | begin : Reached start (begin start)
  | resumeSearch {execution : Execution} (extra : Nat) :
      Reached start execution → Reached start (execution.resumeSearch extra)
  | commit {execution : Execution} : Reached start execution → Reached start execution.commit
  | commitCandidate {execution : Execution} (candidate : GeneralRuleJobs.Receipt) :
      Reached start execution → Reached start (execution.commitCandidate candidate)
  | commitPublished {execution : Execution} (candidate : GeneralRuleJobs.Receipt) :
      Reached start execution → Reached start (execution.commitPublished candidate)
  | cancel {execution : Execution} : Reached start execution → Reached start execution.cancel

theorem Reached.advance {start : Pattern} {execution : Execution}
    (reached : Reached start execution) (fuel : Nat) :
    Reached start (Execution.advance fuel execution) := by
  induction fuel generalizing execution with
  | zero => exact reached
  | succ fuel ih => exact ih reached.commit

theorem begin_sound {start : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] start)
    (sealed : binderSafeAt "NQuote" 0 start = true) :
    Sound start (begin start) := by
  obtain ⟨lexTyped, lexSealed⟩ := closed_lexCanon typed sealed
  exact ⟨.nil _, .live rfl (Search.begin_valid start), lexTyped, lexSealed⟩

theorem Sound.resumeSearch {start : Pattern} {execution : Execution}
    (sound : Sound start execution) (extra : Nat) :
    Sound start (execution.resumeSearch extra) := by
  obtain ⟨chronicle, phase, typed, sealed⟩ := sound
  cases execution with
  | mk history current =>
    cases phase with
    | live process valid =>
      exact ⟨chronicle, .live process (Search.resume_valid _ valid extra), typed, sealed⟩
    | done at_ quiet => exact ⟨chronicle, .done at_ quiet, typed, sealed⟩
    | cancelled => exact ⟨chronicle, .cancelled, typed, sealed⟩

theorem Sound.cancel {start : Pattern} {execution : Execution}
    (sound : Sound start execution) : Sound start execution.cancel :=
  ⟨sound.chronicle, .cancelled, sound.typed, sound.sealed⟩

theorem Sound.commit {start : Pattern} {execution : Execution}
    (sound : Sound start execution) : Sound start execution.commit := by
  obtain ⟨chronicle, phase, typed, sealed⟩ := sound
  cases execution with
  | mk history current =>
    cases phase with
    | @live search process valid =>
      obtain ⟨canonical, budget, program⟩ := valid
      cases published : search.program.publication with
      | nil =>
        cases status : search.program.status with
        | complete =>
          have quiet : ∃ budget, (programOf (endpoint (lexCanon start) history) budget).publication = [] ∧
              (programOf (endpoint (lexCanon start) history) budget).status = .complete :=
            ⟨budget, by rw [← process, ← program]; exact ⟨published, status⟩⟩
          have moved : (Execution.commit ⟨history, .live search⟩) =
              ⟨history, .done search.process⟩ := by
            simp [Execution.commit, published, status]
          rw [moved]
          exact ⟨chronicle, .done process quiet, typed, sealed⟩
        | pending =>
          have same : (Execution.commit ⟨history, .live search⟩) = ⟨history, .live search⟩ := by
            simp [Execution.commit, published, status]
          rw [same]
          exact ⟨chronicle, .live process ⟨canonical, budget, program⟩, typed, sealed⟩
        | blocked =>
          have same : (Execution.commit ⟨history, .live search⟩) = ⟨history, .live search⟩ := by
            simp [Execution.commit, published, status]
          rw [same]
          exact ⟨chronicle, .live process ⟨canonical, budget, program⟩, typed, sealed⟩
      | cons receipt rest =>
        cases status : search.program.status with
        | complete =>
          have member : receipt ∈ (programOf search.process budget).publication := by
            rw [← program, published]
            exact List.mem_cons_self
          have validReceipt := valid_of_mem_publication member
          rw [process] at validReceipt
          have step := GeneralRho.DepthOne.receipt_step typed validReceipt
          obtain ⟨targetTyped, targetSealed⟩ := rhoStepAt_preserves_closed typed sealed step
          obtain ⟨afterTyped, afterSealed⟩ := closed_lexCanon targetTyped targetSealed
          have moved : (Execution.commit ⟨history, .live search⟩) =
              ⟨history ++ [⟨search.process, receipt, lexCanon receipt.target⟩],
                .live (Search.begin (lexCanon receipt.target))⟩ := by
            simp [Execution.commit, published, status]
          rw [moved]
          have ending : endpoint (lexCanon start)
              (history ++ [⟨search.process, receipt, lexCanon receipt.target⟩]) =
                lexCanon receipt.target := endpoint_append_single _ _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [process]
            exact chronicle.append validReceipt step
          · simp only [ending]
            refine .live ?_ (Search.begin_valid _)
            simp [Search.begin, lexCanon_idempotent]
          · simpa only [ending] using afterTyped
          · simpa only [ending] using afterSealed
        | pending =>
          have same : (Execution.commit ⟨history, .live search⟩) = ⟨history, .live search⟩ := by
            simp [Execution.commit, published, status]
          rw [same]
          exact ⟨chronicle, .live process ⟨canonical, budget, program⟩, typed, sealed⟩
        | blocked =>
          have same : (Execution.commit ⟨history, .live search⟩) = ⟨history, .live search⟩ := by
            simp [Execution.commit, published, status]
          rw [same]
          exact ⟨chronicle, .live process ⟨canonical, budget, program⟩, typed, sealed⟩
    | @done process at_ quiet =>
      have same : (Execution.commit ⟨history, .done process⟩) = ⟨history, .done process⟩ := by
        simp [Execution.commit]
      rw [same]
      exact ⟨chronicle, .done at_ quiet, typed, sealed⟩
    | cancelled =>
      have same : (Execution.commit ⟨history, .cancelled⟩) = ⟨history, .cancelled⟩ := by
        simp [Execution.commit]
      rw [same]
      exact ⟨chronicle, .cancelled, typed, sealed⟩

theorem Sound.commitCandidate {start : Pattern} {execution : Execution}
    (sound : Sound start execution) (candidate : GeneralRuleJobs.Receipt) :
    Sound start (execution.commitCandidate candidate) := by
  cases execution with
  | mk history current =>
    cases current with
    | live search =>
      cases published : search.program.publication with
      | nil =>
        have same : Execution.commitCandidate ⟨history, .live search⟩ candidate =
            ⟨history, .live search⟩ := by
          simp [Execution.commitCandidate, published]
        rw [same]
        exact sound
      | cons receipt rest =>
        cases status : search.program.status with
        | complete =>
          by_cases accepted : receiptWireEq candidate receipt = true
          · have same : Execution.commitCandidate ⟨history, .live search⟩ candidate =
                Execution.commit ⟨history, .live search⟩ := by
              simp [Execution.commitCandidate, published, status, accepted]
            rw [same]
            exact sound.commit
          · have same : Execution.commitCandidate ⟨history, .live search⟩ candidate =
                ⟨history, .live search⟩ := by
              simp [Execution.commitCandidate, published, status, accepted]
            rw [same]
            exact sound
        | pending =>
          have same : Execution.commitCandidate ⟨history, .live search⟩ candidate =
              ⟨history, .live search⟩ := by
            simp [Execution.commitCandidate, published, status]
          rw [same]
          exact sound
        | blocked =>
          have same : Execution.commitCandidate ⟨history, .live search⟩ candidate =
              ⟨history, .live search⟩ := by
            simp [Execution.commitCandidate, published, status]
          rw [same]
          exact sound
    | done process =>
      have same : Execution.commitCandidate ⟨history, .done process⟩ candidate =
          ⟨history, .done process⟩ := by
        simp [Execution.commitCandidate]
      rw [same]
      exact sound
    | cancelled =>
      have same : Execution.commitCandidate ⟨history, .cancelled⟩ candidate =
          ⟨history, .cancelled⟩ := by
        simp [Execution.commitCandidate]
      rw [same]
      exact sound

theorem Sound.commitPublished {start : Pattern} {execution : Execution}
    (sound : Sound start execution) (candidate : GeneralRuleJobs.Receipt) :
    Sound start (execution.commitPublished candidate) := by
  obtain ⟨chronicle, phase, typed, sealed⟩ := sound
  cases execution with
  | mk history current =>
    cases phase with
    | @live search process valid =>
      simp only [Execution.commitPublished]
      split
      · rename_i accepted
        have member := (published_wire_member _ _).mp accepted.2
        obtain ⟨_, budget, program⟩ := valid
        rw [program] at member
        have receiptValid := valid_of_mem_publication member
        rw [process] at receiptValid
        have step := GeneralRho.DepthOne.receipt_step typed receiptValid
        obtain ⟨nextTyped, nextSealed⟩ := rhoStepAt_preserves_closed typed sealed step
        obtain ⟨afterTyped, afterSealed⟩ := closed_lexCanon nextTyped nextSealed
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [process]; exact chronicle.append receiptValid step
        · rw [endpoint_append_single]
          exact .live (lexCanon_idempotent _) (Search.begin_valid _)
        · simpa only [endpoint_append_single] using afterTyped
        · simpa only [endpoint_append_single] using afterSealed
      · exact ⟨chronicle, .live process valid, typed, sealed⟩
    | done at_ quiet => exact ⟨chronicle, .done at_ quiet, typed, sealed⟩
    | cancelled => exact ⟨chronicle, .cancelled, typed, sealed⟩
/-- **Every reached execution is sound.** Its history is a chronological
sequence of committed depth-one COMMs from the canonical start, and its phase
sits at the history's endpoint. -/
theorem Reached.sound {start : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] start)
    (sealed : binderSafeAt "NQuote" 0 start = true) {execution : Execution}
    (reached : Reached start execution) : Sound start execution := by
  induction reached with
  | begin => exact begin_sound typed sealed
  | resumeSearch extra _ ih => exact ih.resumeSearch extra
  | commit _ ih => exact ih.commit
  | commitCandidate candidate _ ih => exact ih.commitCandidate candidate
  | commitPublished candidate _ ih => exact ih.commitPublished candidate
  | cancel _ ih => exact ih.cancel

/-- The endpoint of a chronicle from a canonical state is canonical. -/
theorem Chronicle.endpoint_canonical {state : Pattern} {history : List Commit}
    (chronicle : Chronicle state history) (canonical : lexCanon state = state) :
    lexCanon (endpoint state history) = endpoint state history := by
  induction chronicle with
  | nil state => exact canonical
  | @cons state receipt rest valid step tail ih => exact ih (lexCanon_idempotent _)

/-- A reached history is a chain of canonical depth-one links from the
canonical start: a finite rho reduction sequence modulo structural congruence. -/
theorem Reached.chain {start : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] start)
    (sealed : binderSafeAt "NQuote" 0 start = true) {execution : Execution}
    (reached : Reached start execution) :
    (lexCanon start :: execution.history.map (·.after)).IsChain Link ∧
      Relation.ReflTransGen Link (lexCanon start) (endpoint (lexCanon start) execution.history) ∧
      StructuralCongruence start (lexCanon start) :=
  by
  have sound := reached.sound typed sealed
  exact ⟨sound.chronicle.chain, sound.chronicle.reaches, lexCanon_sound start⟩

/-- Every committed receipt of a reached execution licenses its COMM. -/
theorem Reached.receipts {start : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] start)
    (sealed : binderSafeAt "NQuote" 0 start = true) {execution : Execution}
    (reached : Reached start execution) :
    ∀ commit ∈ execution.history, commit.receipt.Valid plan [] (.base "Proc") commit.before ∧
      RhoStepAt 1 commit.before commit.receipt.target ∧
      commit.after = lexCanon commit.receipt.target :=
  (reached.sound typed sealed).chronicle.receipts_valid

/-- **A reached done phase is exact quiescence** at the history's endpoint. -/
theorem Reached.done_quiescent {start : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] start)
    (sealed : binderSafeAt "NQuote" 0 start = true) {execution : Execution}
    (reached : Reached start execution) {process : Pattern}
    (done : execution.phase = .done process) :
    process = endpoint (lexCanon start) execution.history ∧ ∀ target, ¬ RhoStep process target := by
  obtain ⟨chronicle, phase, endTyped, endSealed⟩ := reached.sound typed sealed
  rw [done] at phase
  cases phase with
  | done at_ quiet =>
    obtain ⟨budget, published, complete⟩ := quiet
    have canonical := chronicle.endpoint_canonical (lexCanon_idempotent start)
    have quiet : step (endpoint (lexCanon start) execution.history) budget =
        .quiescent (endpoint (lexCanon start) execution.history) := by
      simp [step, outcomeOf, canonical, published, complete]
    exact ⟨at_, by rw [at_]; exact (step_quiescent endTyped endSealed quiet).2.1⟩

/-- A reached live search reports only COMMs from the history's endpoint. -/
theorem Reached.live_outcome {start : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] start)
    (sealed : binderSafeAt "NQuote" 0 start = true) {execution : Execution}
    (reached : Reached start execution) {search : Search}
    (live : execution.phase = .live search) {state next : Pattern}
    (stepped : search.outcome = .stepped state next) :
    state = endpoint (lexCanon start) execution.history ∧
      RhoStepAt 1 (endpoint (lexCanon start) execution.history) next := by
  obtain ⟨_, phase, endTyped, endSealed⟩ := reached.sound typed sealed
  rw [live] at phase
  cases phase with
  | live process valid =>
    rw [← process] at endTyped endSealed ⊢
    obtain ⟨same, depthOne⟩ := Search.outcome_sound search valid endTyped endSealed stepped
    subst same
    exact ⟨rfl, depthOne⟩

/-- An ill-linked record is not a chronicle: a commit must start where the
history stands. -/
theorem misplaced_commit_not_chronicle (state other : Pattern) (receipt : GeneralRuleJobs.Receipt)
    (after : Pattern) (rest : List Commit) (different : other ≠ state) :
    ¬ Chronicle state (⟨other, receipt, after⟩ :: rest) := by
  intro chronicle
  cases chronicle
  exact different rfl

/-- A commit whose recorded result is not the canonical form of its receipt's
target is not a chronicle entry. -/
theorem wrong_result_not_chronicle (state : Pattern) (receipt : GeneralRuleJobs.Receipt)
    (after : Pattern) (rest : List Commit) (different : after ≠ lexCanon receipt.target) :
    ¬ Chronicle state (⟨state, receipt, after⟩ :: rest) := by
  intro chronicle
  cases chronicle
  exact different rfl

/-! ## Exclusive authority over a retained execution

Committed COMMs are the effects of a retained execution. Under the common
owned host, a ticket holder submits retained operations; copies of used
tickets are refused, and every committed COMM reaches the world exactly once.
Combined with the reached-history invariant, the delivered history is a
chronological COMM sequence from the canonical start.
-/

/-- The retained operations available to a ticket holder. -/
inductive Operation where
  | resumeSearch (extra : Nat)
  | commit
  | commitCandidate (candidate : GeneralRuleJobs.Receipt)
  | commitPublished (candidate : GeneralRuleJobs.Receipt)

def Operation.apply : Operation → Execution → Execution
  | .resumeSearch extra, execution => execution.resumeSearch extra
  | .commit, execution => execution.commit
  | .commitCandidate candidate, execution => execution.commitCandidate candidate
  | .commitPublished candidate, execution => execution.commitPublished candidate

theorem Operation.history_prefix (operation : Operation) (execution : Execution) :
    execution.history.IsPrefix (operation.apply execution).history := by
  cases operation with
  | resumeSearch extra =>
    rw [Operation.apply, resumeSearch_appends_nothing]
  | commit => exact commit_history_prefix execution
  | commitPublished candidate => exact commitPublished_history_prefix execution candidate
  | commitCandidate candidate =>
    cases execution with
    | mk history phase =>
      cases phase with
      | live search =>
        cases published : search.program.publication with
        | nil => simp [Operation.apply, Execution.commitCandidate, published]
        | cons receipt rest =>
          cases status : search.program.status with
          | complete =>
            by_cases accepted : receiptWireEq candidate receipt = true
            · simp only [Operation.apply, Execution.commitCandidate, published, status, accepted, if_true]
              exact commit_history_prefix ⟨history, .live search⟩
            · simp [Operation.apply, Execution.commitCandidate, published, status, accepted]
          | pending => simp [Operation.apply, Execution.commitCandidate, published, status]
          | blocked => simp [Operation.apply, Execution.commitCandidate, published, status]
      | done process => simp [Operation.apply, Execution.commitCandidate]
      | cancelled => simp [Operation.apply, Execution.commitCandidate]

/-- A retained whole-process execution as a retained computation whose
committed effects are its COMM commits. -/
def owned : Mettapedia.Machines.OwnedPullDriver.Owned.Retained Execution Operation Commit where
  apply := Operation.apply
  committed := Execution.history
  grows := Operation.history_prefix

theorem Operation.reached {start : Pattern} {execution : Execution}
    (reached : Reached start execution) (operation : Operation) :
    Reached start (operation.apply execution) := by
  cases operation with
  | resumeSearch extra => exact reached.resumeSearch extra
  | commit => exact reached.commit
  | commitCandidate candidate => exact reached.commitCandidate candidate
  | commitPublished candidate => exact reached.commitPublished candidate

theorem derived_reached {start : Pattern} {execution : Execution}
    (derived : Mettapedia.Machines.OwnedPullDriver.Owned.Host.Derived owned (begin start) execution) :
    Reached start execution := by
  induction derived with
  | refl => exact .begin
  | tail _ step ih =>
    obtain ⟨operation, rfl⟩ := step
    exact Operation.reached ih operation

/-- **Owned COMM publication.** Take authority over a process's retained
execution and serve arbitrary requests. The world is the origin with the
delivered commits interpreted exactly once, the delivered history is the
retained execution's history, and that history is a chronological sequence
of depth-one COMMs from the canonical start. -/
theorem owned_publication {World : Type} (act : Commit → World → World) (origin : World)
    {start : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] start)
    (sealed : binderSafeAt "NQuote" 0 start = true)
    {host : Mettapedia.Machines.OwnedPullDriver.Owned.Host Execution Commit World}
    (reached : Mettapedia.Machines.OwnedPullDriver.Owned.Host.Reached owned act origin (begin start) host) :
    host.world = Mettapedia.Machines.OwnedPullDriver.interpret act host.delivered origin ∧
      ∀ execution, host.retained = some execution →
        host.delivered = execution.history ∧ Reached start execution ∧
          Chronicle (lexCanon start) host.delivered := by
  have accounts := reached.accounts
  refine ⟨accounts.world, fun execution retained => ?_⟩
  have delivered := accounts.delivered execution retained
  have derived := reached.retained execution retained
  have reachedExecution : Reached start execution := derived_reached derived
  refine ⟨delivered, reachedExecution, ?_⟩
  rw [delivered]
  exact (reachedExecution.sound typed sealed).chronicle

end Retained


/-! ## Independent retained communications and validated occurrence cells -/

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (ProcWellSorted)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep RhoStepAt)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem (rhoClosedTermWellSorted_process_iff)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open GeneralProgramResumptionExecution (ProgramRun)

/-- A finite budget that completes every depth-one COMM search job. -/
def saturationBudget (state : Pattern) : Nat :=
  (GeneralRuleJobs.jobs plan [] (.base "Proc") state).foldr (fun job cost => max (jobCost job) cost) 0

theorem saturationBudget_saturates (state : Pattern) : Saturates (saturationBudget state) state := by
  unfold Saturates saturationBudget
  generalize GeneralRuleJobs.jobs plan [] (.base "Proc") state = jobs
  intro job member
  induction jobs with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- Every semantically valid receipt is actually published by a completed
retained search; this uses the job enumerator's proved completeness. -/
theorem receipt_published {state : Pattern} (receipt : GeneralRuleJobs.Receipt)
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] state)
    (valid : receipt.Valid plan [] (.base "Proc") state) :
    receipt ∈ (programOf state (saturationBudget state)).publication ∧
      (programOf state (saturationBudget state)).status = .complete := by
  have allComplete := complete_of_saturates typed (saturationBudget_saturates state)
  have member := (GeneralRuleJobExecution.mem_completedReceipts_iff plan [] (.base "Proc") state
    GeneralRho.DepthOne.stratified receipt).mpr valid
  rw [← aggregate_eq_completed allComplete,
    ← ProgramRun.publication_complete _ allComplete] at member
  exact ⟨member, (ProgramRun.status_complete_iff _).mpr allComplete⟩

/-- The actual public rho relation is realized by a receipt on the retained
runner's lexicographic representation, with the same canonical endpoint. -/
theorem public_step_receipt {source target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step source target) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid plan [] (.base "Proc") (lexCanon source.1) ∧
      lexCanon receipt.target = lexCanon target.1 := by
  obtain ⟨redex, contractum, sourceEq, reduction, targetEq⟩ := step
  have redexClosed := (rhoClosedTermWellSorted_process_iff _).mp redex.2
  obtain ⟨next, actual, same⟩ := lexStep_complete redexClosed.1 reduction
  have sourceLex : lexCanon source.1 = lexCanon redex.1 := (lexCanon_eq_iff _ _).mpr sourceEq
  rw [← sourceLex] at actual
  have closed := (rhoClosedTermWellSorted_process_iff _).mp source.2
  have lexClosed := closed_lexCanon closed.1 closed.2
  obtain ⟨receipt, valid, target⟩ := GeneralRho.DepthOne.step_receipt lexClosed.1 lexClosed.2
    (lexCanon_channelsDecided _) actual
  exact ⟨receipt, valid, (lexCanon_eq_iff _ _).mpr (by rw [target]; exact same.trans targetEq)⟩

namespace Retained
/-- A real completed search followed by selecting one validated occurrence. -/
def Execution.realize (execution : Execution) (candidate : GeneralRuleJobs.Receipt) : Execution :=
  match execution.phase with
  | .live search => (execution.resumeSearch (saturationBudget search.process)).commitPublished candidate
  | .done _ | .cancelled => execution

/-- Budgeting and choosing are existing retained operations, so realization
inherits the chronological-history and owned-publication invariants. -/
theorem Reached.realize {start : Pattern} {execution : Execution}
    (reached : Reached start execution) (candidate : GeneralRuleJobs.Receipt) :
    Reached start (execution.realize candidate) := by
  cases execution with
  | mk history phase =>
    cases phase with
    | live search => exact (reached.resumeSearch (saturationBudget search.process)).commitPublished candidate
    | done process => exact reached
    | cancelled => exact reached

/-- Pruning an owner drops future search, while retaining the complete past.
No saved candidate can append a commit to a cancelled execution. -/
theorem cancelled_commitPublished (execution : Execution) (candidate : GeneralRuleJobs.Receipt) :
    execution.cancel.commitPublished candidate = execution.cancel := rfl

theorem cancelled_realize (execution : Execution) (candidate : GeneralRuleJobs.Receipt) :
    execution.cancel.realize candidate = execution.cancel := rfl

/-- Choosing one result records one occurrence. Equal-valued alternatives
are not silently delivered as effects. -/
theorem commitPublished_one_occurrence (history : List Commit) (search : Search)
    (candidate : GeneralRuleJobs.Receipt) (complete : search.program.status = .complete)
    (member : candidate ∈ search.program.publication) :
    (Execution.commitPublished ⟨history, .live search⟩ candidate).history.length = history.length + 1 := by
  rw [commitPublished_accepts _ _ _ complete member]
  simp

/-- An independent reaction can run through the existing retained states. -/
theorem realizes_public_step {source target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step source target) (history : List Commit) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid plan [] (.base "Proc") (lexCanon source.1) ∧
      lexCanon receipt.target = lexCanon target.1 ∧
      Execution.realize ⟨history, .live (Search.begin source.1)⟩ receipt =
        ⟨history ++ [⟨lexCanon source.1, receipt, lexCanon target.1⟩],
          .live (Search.begin target.1)⟩ := by
  obtain ⟨receipt, valid, same⟩ := public_step_receipt step
  have closed := (rhoClosedTermWellSorted_process_iff _).mp source.2
  obtain ⟨member, complete⟩ := receipt_published receipt (closed_lexCanon closed.1 closed.2).1 valid
  refine ⟨receipt, valid, same, ?_⟩
  have searchEq : (Search.begin source.1).resume (saturationBudget (lexCanon source.1)) =
      ⟨lexCanon source.1, programOf (lexCanon source.1) (saturationBudget (lexCanon source.1))⟩ := by
    simp [Search.begin, Search.resume, Search.programOf_resume]
  simp only [Execution.realize, Search.begin, Execution.resumeSearch]
  change (Execution.commitPublished
    ⟨history, .live ((Search.begin source.1).resume (saturationBudget (lexCanon source.1)))⟩ receipt) = _
  rw [searchEq, commitPublished_accepts _ _ _ complete member]
  simp only [same, Search.begin, lexCanon_idempotent]

/-- Two redexes occupy separate summands, even when their atoms have equal
values. All four source reactions and residuals are constructed from COMM. -/
theorem independent_reactions (first second : GroundComm) (frame : Bag) :
    Reaction (append first.redex (append second.redex frame))
      (append first.reactum (append second.redex frame)) ∧
    Reaction (append first.redex (append second.redex frame))
      (append first.redex (append second.reactum frame)) ∧
    Reaction (append first.reactum (append second.redex frame))
      (append first.reactum (append second.reactum frame)) ∧
    Reaction (append first.redex (append second.reactum frame))
      (append first.reactum (append second.reactum frame)) := by
  have rotate (left right tail : Bag) : append left (append right tail) = append right (append left tail) := by
    rw [← append_assoc, append_comm left right, append_assoc]
  refine ⟨⟨first, append second.redex frame, rfl, rfl⟩,
    ⟨second, append first.redex frame, rotate _ _ _, rotate _ _ _⟩,
    ⟨second, append first.reactum frame, rotate _ _ _, rotate _ _ _⟩,
    ⟨first, append second.reactum frame, rfl, rfl⟩⟩

/-- Both orders of two disjoint concrete COMMs run through actual retained
searches and reach the same process. Four full receipts remain available:
the second receipt is transported to the residual source, never relabelled. -/
theorem disjoint_retained_diamond (first second : GroundComm) (frame : Bag)
    (history : List Commit) :
    let source := toProcess (append first.redex (append second.redex frame))
    let afterFirst := toProcess (append first.reactum (append second.redex frame))
    let afterSecond := toProcess (append first.redex (append second.reactum frame))
    let target := toProcess (append first.reactum (append second.reactum frame))
    ∃ a b bAfter aAfter : GeneralRuleJobs.Receipt,
      a.Valid plan [] (.base "Proc") (lexCanon source.1) ∧
      b.Valid plan [] (.base "Proc") (lexCanon source.1) ∧
      bAfter.Valid plan [] (.base "Proc") (lexCanon afterFirst.1) ∧
      aAfter.Valid plan [] (.base "Proc") (lexCanon afterSecond.1) ∧
      Execution.realize (Execution.realize ⟨history, .live (Search.begin source.1)⟩ a) bAfter =
        ⟨history ++ [⟨lexCanon source.1, a, lexCanon afterFirst.1⟩,
          ⟨lexCanon afterFirst.1, bAfter, lexCanon target.1⟩], .live (Search.begin target.1)⟩ ∧
      Execution.realize (Execution.realize ⟨history, .live (Search.begin source.1)⟩ b) aAfter =
        ⟨history ++ [⟨lexCanon source.1, b, lexCanon afterSecond.1⟩,
          ⟨lexCanon afterSecond.1, aAfter, lexCanon target.1⟩], .live (Search.begin target.1)⟩ := by
  intro source afterFirst afterSecond target
  obtain ⟨one, two, twoAfter, oneAfter⟩ := independent_reactions first second frame
  obtain ⟨a, aValid, _, aRun⟩ := realizes_public_step (reaction_public one) history
  obtain ⟨b, bValid, _, bRun⟩ := realizes_public_step (reaction_public two) history
  obtain ⟨bAfter, bAfterValid, _, bAfterRun⟩ := realizes_public_step (reaction_public twoAfter)
    (history ++ [⟨lexCanon source.1, a, lexCanon afterFirst.1⟩])
  obtain ⟨aAfter, aAfterValid, _, aAfterRun⟩ := realizes_public_step (reaction_public oneAfter)
    (history ++ [⟨lexCanon source.1, b, lexCanon afterSecond.1⟩])
  refine ⟨a, b, bAfter, aAfter, aValid, bValid, bAfterValid, aAfterValid, ?_, ?_⟩
  · rw [aRun]
    simpa [List.append_assoc] using bAfterRun
  · rw [bRun]
    simpa [List.append_assoc] using aAfterRun
end Retained

namespace Retained
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Machines
open ValidatedCommit ReadOnlyQuery

local instance : DecidableEq Bag := by
  unfold Bag
  infer_instance

/-- Unallocated and consumed cells differ, so occurrence identifiers cannot
be recycled by a later COMM. -/
inductive Cell where
  | fresh
  | live (contents : Bag)
  | spent
  deriving DecidableEq

/-- A COMM candidate names two stable source occurrences and a distinct,
unoccupied result cell. A cell can contain a whole canonical residual bag;
equal bags at different keys remain different resources. -/
structure LocatedComm where
  rule : GroundComm
  inputKey : Nat
  outputKey : Nat
  resultKey : Nat
  input_output : inputKey ≠ outputKey
  input_result : inputKey ≠ resultKey
  output_result : outputKey ≠ resultKey

namespace LocatedComm

def inputBag (candidate : LocatedComm) : Bag :=
  ⟨{input candidate.rule.inputChannel candidate.rule.body},
    fun pattern member => by
      have equal := Multiset.mem_singleton.mp member
      subst pattern
      exact candidate.rule.inputPrime⟩

def outputBag (candidate : LocatedComm) : Bag :=
  ⟨{output candidate.rule.outputChannel candidate.rule.payload},
    fun pattern member => by
      have equal := Multiset.mem_singleton.mp member
      subst pattern
      exact candidate.rule.outputPrime⟩

theorem redex (candidate : LocatedComm) :
    append candidate.inputBag candidate.outputBag = candidate.rule.redex := by
  apply Subtype.ext
  rfl

def keys (candidate : LocatedComm) : List Nat :=
  [candidate.inputKey, candidate.outputKey, candidate.resultKey]

/-- The absent allocation cell is a real read dependency. -/
def proposal (candidate : LocatedComm) : Proposal Nat (Cell) where
  reads := [(candidate.inputKey, .live candidate.inputBag),
    (candidate.outputKey, .live candidate.outputBag), (candidate.resultKey, .fresh)]
  writes := [(candidate.inputKey, .spent), (candidate.outputKey, .spent),
    (candidate.resultKey, .live candidate.rule.reactum)]

def Ready (candidate : LocatedComm) (store : Nat → Cell) : Prop :=
  store candidate.inputKey = .live candidate.inputBag ∧
    store candidate.outputKey = .live candidate.outputBag ∧ store candidate.resultKey = .fresh

theorem ready_iff_agrees (candidate : LocatedComm) (store : Nat → Cell) :
    candidate.Ready store ↔ Agrees store candidate.proposal.reads := by
  simp [Ready, proposal, Agrees]

/-- The executable query reads both endpoints and the allocation cell. A
failed match has no writes, but its reads still survive in the certificate. -/
def transaction (candidate : LocatedComm) : Transaction Nat (Cell) :=
  .read candidate.inputKey fun incoming =>
  .read candidate.outputKey fun outgoing =>
  .read candidate.resultKey fun available =>
  .pure (if incoming = .live candidate.inputBag ∧ outgoing = .live candidate.outputBag ∧ available = .fresh
    then candidate.proposal.writes else [])

theorem proposal_from_reads (candidate : LocatedComm) (store : Nat → Cell)
    (ready : candidate.Ready store) : propose store candidate.transaction = candidate.proposal := by
  obtain ⟨incoming, outgoing, available⟩ := ready
  simp [propose, transaction, ReadOnlyQuery.run, incoming, outgoing, available, proposal]

theorem commit_iff_ready (candidate : LocatedComm) (store : Nat → Cell) :
    commit store candidate.proposal = some (write store candidate.proposal.writes) ↔
      candidate.Ready store := by
  unfold commit
  split
  · rename_i checked
    simp [((ready_iff_agrees candidate store).mpr ((checkReads_iff _ _).mp checked))]
  · rename_i unchecked
    have notReady : ¬ candidate.Ready store := by
      intro ready
      exact unchecked ((checkReads_iff _ _).mpr ((ready_iff_agrees _ _).mp ready))
    simp [notReady]

theorem write_input (candidate : LocatedComm) (store : Nat → Cell) :
    write store candidate.proposal.writes candidate.inputKey = .spent := by
  simp [write, proposal, candidate.input_output, candidate.input_result]

theorem write_output (candidate : LocatedComm) (store : Nat → Cell) :
    write store candidate.proposal.writes candidate.outputKey = .spent := by
  simp [write, proposal, candidate.output_result]

theorem write_result (candidate : LocatedComm) (store : Nat → Cell) :
    write store candidate.proposal.writes candidate.resultKey = .live candidate.rule.reactum := by
  simp [write, proposal]

/-- Reusing a consumed occurrence is rejected even with a fresh host ticket. -/
theorem replay_refused (candidate : LocatedComm) (store : Nat → Cell) :
    commit (write store candidate.proposal.writes) candidate.proposal = none := by
  apply commit_rejects_changed_read _ _ (read := (candidate.inputKey, .live candidate.inputBag))
  · simp [proposal]
  · rw [write_input]; intro impossible; cases impossible

theorem read_key (candidate : LocatedComm) (read : Nat × Cell)
    (member : read ∈ candidate.proposal.reads) : read.1 ∈ candidate.keys := by
  simp only [proposal, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [keys]

theorem write_key (candidate : LocatedComm) (entry : Nat × Cell)
    (member : entry ∈ candidate.proposal.writes) : entry.1 ∈ candidate.keys := by
  simp only [proposal, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [keys]

/-- Disjoint source/allocation identities establish all read/write
independence obligations, even when the two rules have identical syntax. -/
theorem independent {first second : LocatedComm} (disjoint : first.keys.Disjoint second.keys) :
    first.proposal.Independent second.proposal := by
  have neq : ∀ left ∈ first.keys, ∀ right ∈ second.keys, left ≠ right := by
    intro left hl right hr equal
    subst right
    exact List.disjoint_left.mp disjoint hl hr
  exact ⟨fun left hl right hr => neq _ (first.write_key left hl) _ (second.write_key right hr),
    fun right hr read hl => (neq _ (first.read_key read hl) _ (second.write_key right hr)).symm,
    fun left hl read hr => neq _ (first.write_key left hl) _ (second.read_key read hr)⟩

/-- The candidate computed before an independent update is still valid:
there is no matcher replay and no relabelling of a whole-source search. -/
theorem ready_after_independent {first second : LocatedComm}
    (disjoint : first.keys.Disjoint second.keys) (store : Nat → Cell)
    (ready : second.Ready store) : second.Ready (write store first.proposal.writes) := by
  rw [ready_iff_agrees] at ready ⊢
  exact write_preserves_reads _ _ _ ready (independent disjoint).secondReads

/-- Each allocation cell is validated too; another producer filling it makes
the entire old proposal stale. -/
theorem allocated_result_refused (candidate : LocatedComm) (store : Nat → Cell)
    (occupied : store candidate.resultKey ≠ .fresh) : commit store candidate.proposal = none := by
  exact commit_rejects_changed_read _ _ (read := (candidate.resultKey, .fresh)) (by simp [proposal]) occupied

/-- Forget stable cell positions only at the declared process observer. -/
def inventory (store : Nat → Cell) : List Nat → Bag
  | [] => empty
  | key :: rest => match store key with
    | .fresh | .spent => inventory store rest
    | .live contents => append contents (inventory store rest)

theorem inventory_congr (first second : Nat → Cell) (keys : List Nat)
    (agrees : ∀ key ∈ keys, first key = second key) : inventory first keys = inventory second keys := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [inventory, agrees key (by simp)]
    rw [ih (fun next member => agrees next (by simp [member]))]

theorem inventory_source (candidate : LocatedComm) (store : Nat → Cell) (rest : List Nat)
    (ready : candidate.Ready store) :
    inventory store (candidate.keys ++ rest) = append candidate.rule.redex (inventory store rest) := by
  obtain ⟨incoming, outgoing, available⟩ := ready
  simp only [keys, List.cons_append, List.nil_append, inventory, incoming, outgoing, available]
  rw [← append_assoc, redex]

theorem inventory_target (candidate : LocatedComm) (store : Nat → Cell) (rest : List Nat)
    (untouched : candidate.keys.Disjoint rest) :
    inventory (write store candidate.proposal.writes) (candidate.keys ++ rest) =
      append candidate.rule.reactum (inventory store rest) := by
  simp only [keys, List.cons_append, List.nil_append, inventory, write_input, write_output, write_result]
  congr 1
  apply inventory_congr
  intro key member
  apply write_untouched
  intro entry present equal
  exact List.disjoint_left.mp untouched (candidate.write_key entry present)
    (equal ▸ member)

/-- A successful occurrence transaction is the actual rho COMM reaction on
its complete visible inventory, with the unchanged frame retained. -/
theorem commit_reaction (candidate : LocatedComm) (store : Nat → Cell) (rest : List Nat)
    (ready : candidate.Ready store) (untouched : candidate.keys.Disjoint rest) :
    Reaction (inventory store (candidate.keys ++ rest))
      (inventory (write store candidate.proposal.writes) (candidate.keys ++ rest)) := by
  rw [candidate.inventory_source store rest ready, candidate.inventory_target store rest untouched]
  exact ⟨candidate.rule, inventory store rest, rfl, rfl⟩

/-- Both actual COMMs commit, retaining two complete occurrence-indexed write
records. Independent schedules agree at the store observer, not as lists. -/
theorem ledger_diamond (first second : LocatedComm) (state : Ledger Nat (Cell))
    (disjoint : first.keys.Disjoint second.keys)
    (firstReady : first.Ready state.store) (secondReady : second.Ready state.store) :
    (Ledger.submit second.proposal (Ledger.submit first.proposal state)).store =
      (Ledger.submit first.proposal (Ledger.submit second.proposal state)).store ∧
    (Ledger.submit second.proposal (Ledger.submit first.proposal state)).history =
      state.history ++ [first.proposal.writes, second.proposal.writes] ∧
    (Ledger.submit first.proposal (Ledger.submit second.proposal state)).history =
      state.history ++ [second.proposal.writes, first.proposal.writes] :=
  Ledger.independent_diamond _ _ _ (independent disjoint)
    ((ready_iff_agrees _ _).mp firstReady) ((ready_iff_agrees _ _).mp secondReady)
end LocatedComm
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical
open Mettapedia.Machines
open ValidatedCommit ReadOnlyQuery
open Mettapedia.GSLT.Distinction.CausalGluing
open Mettapedia.GSLT.Dynamics.QueryRevision

namespace LocatedComm

/-- Actual acceptance exposes the checked source cells and the exact writes. -/
theorem accepted {candidate : LocatedComm} {store next : Nat → Cell}
    (step : commit store candidate.proposal = some next) :
    candidate.Ready store ∧ next = write store candidate.proposal.writes := by
  unfold commit at step
  split at step
  · rename_i checked
    exact ⟨(ready_iff_agrees _ _).mpr ((checkReads_iff _ _).mp checked),
      (Option.some.inj step).symm⟩
  · cases step

/-- Consumption is irreversible in this occurrence store. The result cell
must be fresh, so a later COMM cannot recycle a consumed identity. -/
theorem spent_preserved (candidate : LocatedComm) (store : Nat → Cell)
    (ready : candidate.Ready store) (key : Nat) (spent : store key = .spent) :
    write store candidate.proposal.writes key = .spent := by
  by_cases isInput : key = candidate.inputKey
  · rw [isInput, write_input]
  by_cases isOutput : key = candidate.outputKey
  · rw [isOutput, write_output]
  by_cases isResult : key = candidate.resultKey
  · have fresh := ready.2.2
    rw [← isResult, spent] at fresh
    cases fresh
  rw [write_untouched store candidate.proposal.writes key]
  · exact spent
  · intro entry member
    have inKeys := candidate.write_key entry member
    simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at inKeys
    rcases inKeys with equal | equal | equal
    · exact fun same => isInput (same.symm.trans equal)
    · exact fun same => isOutput (same.symm.trans equal)
    · exact fun same => isResult (same.symm.trans equal)

/-- The existing query/revision interface carries the actual validated COMM
transitions. Its observer can inspect any stable occurrence cell. -/
def revisionTheory : Theory where
  World := Nat → Cell
  Revision := LocatedComm
  Query := Nat
  Observation := Cell
  Step candidate store next := commit store candidate.proposal = some next
  query store key := store key

/-- A whole accepted interaction history cannot revive a consumed key. -/
theorem history_preserves_spent {events : List LocatedComm} {initial final : Nat → Cell}
    (history : revisionTheory.HistoryStep events initial final) {key : Nat}
    (spent : initial key = .spent) : final key = .spent := by
  exact Theory.HistoryStep.rec (theory := revisionTheory)
    (motive := fun _ source target _ => source key = .spent → target key = .spent)
    (fun _ h => h)
    (fun {candidate} {_} {source} {_} {_} step _ ih h => by
      obtain ⟨ready, rfl⟩ := accepted step
      exact ih (candidate.spent_preserved source ready key h)) history spent

/-- Reusing a saved candidate remains refused after any subsequent accepted
history, even if all stored result values happen to repeat. -/
theorem replay_after_history_refused (candidate : LocatedComm) (store final : Nat → Cell)
    (events : List LocatedComm)
    (history : revisionTheory.HistoryStep events (write store candidate.proposal.writes) final) :
    commit final candidate.proposal = none := by
  have spent := history_preserves_spent history (candidate.write_input store)
  apply commit_rejects_changed_read _ _ (read := (candidate.inputKey, .live candidate.inputBag))
  · simp [proposal]
  · rw [spent]; intro impossible; cases impossible

/-- Reuse the existing causal trace relation. Only swaps justified by
nonoverlapping occurrence/allocation keys are admitted; chronology is retained
in the original histories, and no enumeration order is imposed on MeTTa. -/
theorem causal_history_iff {first second : List LocatedComm}
    (equivalent : TraceEquiv (fun a b : LocatedComm => a.keys.Disjoint b.keys) first second)
    (source target : Nat → Cell) :
    revisionTheory.HistoryStep first source target ↔ revisionTheory.HistoryStep second source target := by
  apply Theory.HistoryStep.traceEquiv_iff (theory := revisionTheory)
    (fun a b : LocatedComm => a.keys.Disjoint b.keys) (fun h => h.symm) _ equivalent source target
  intro first second source middle target independent firstStep secondStep
  exact commit_swap_actual (LocatedComm.independent independent) firstStep secondStep

theorem independent_trace (first second : LocatedComm) (disjoint : first.keys.Disjoint second.keys) :
    TraceEquiv (fun a b : LocatedComm => a.keys.Disjoint b.keys) [first, second] [second, first] :=
  .rel _ _ (.swap [] [] disjoint)

/-- A validated local transaction has a corresponding completed-search
transition of the actual retained rho runner. The old local candidate can
survive independent updates; the whole-source search itself is not relabelled. -/
theorem retained_realization (candidate : LocatedComm) (store : Nat → Cell) (rest : List Nat)
    (ready : candidate.Ready store) (untouched : candidate.keys.Disjoint rest) (history : List Commit) :
    let source := toProcess (inventory store (candidate.keys ++ rest))
    let target := toProcess (inventory (write store candidate.proposal.writes) (candidate.keys ++ rest))
    commit store candidate.proposal = some (write store candidate.proposal.writes) ∧
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid plan [] (.base "Proc") (lexCanon source.1) ∧
      lexCanon receipt.target = lexCanon target.1 ∧
      Execution.realize ⟨history, .live (Search.begin source.1)⟩ receipt =
        ⟨history ++ [⟨lexCanon source.1, receipt, lexCanon target.1⟩],
          .live (Search.begin target.1)⟩ := by
  exact ⟨(commit_iff_ready _ _).mpr ready,
    realizes_public_step (reaction_public (candidate.commit_reaction store rest ready untouched)) history⟩

/-- Canceling the authority holder retires this publication channel. Neither
a saved candidate nor a different ticket can publish through it afterward. -/
theorem cancelled_cannot_publish {World : Type} (act : Writes Nat Cell → World → World)
    (host : OwnedPullDriver.Owned.Host (Ledger Nat Cell) (Writes Nat Cell) World)
    (state : Ledger Nat Cell) (retained : host.retained = some state)
    (ticket : Nat) (candidate : LocatedComm) :
    let cancelled := OwnedPullDriver.Owned.Host.cancel host.epoch host
    OwnedPullDriver.Owned.Host.submit ledger act ticket candidate.proposal cancelled = cancelled ∧
      cancelled.world = host.world ∧ cancelled.delivered = host.delivered ∧ cancelled.retained = none :=
  OwnedPullDriver.Owned.Host.cancelled_refuses ledger act retained ticket candidate.proposal

/-- A current host ticket does not override dependency rejection: no write is
published and the retained ledger stays unchanged. Only the ticket is spent. -/
theorem refused_no_publication {World : Type} (act : Writes Nat Cell → World → World)
    (host : OwnedPullDriver.Owned.Host (Ledger Nat Cell) (Writes Nat Cell) World)
    (state : Ledger Nat Cell) (retained : host.retained = some state)
    (candidate : LocatedComm) (refused : commit state.store candidate.proposal = none) :
    OwnedPullDriver.Owned.Host.submit ledger act host.epoch candidate.proposal host =
      { host with epoch := host.epoch + 1 } := by
  rw [OwnedPullDriver.Owned.Host.submit_current ledger act candidate.proposal retained]
  simp only [ledger, Ledger.submit, refused, List.drop_length, OwnedPullDriver.interpret_nil,
    List.append_nil]
  cases host
  simp_all

/-- Occurrence-indexed writes inherit the existing owned publication account.
Committed effects are interpreted exactly once, with their full identities. -/
theorem owned_publication {World : Type} (act : Writes Nat Cell → World → World) (origin : World)
    {start state : Ledger Nat Cell}
    {host : OwnedPullDriver.Owned.Host (Ledger Nat Cell) (Writes Nat Cell) World}
    (reached : OwnedPullDriver.Owned.Host.Reached ledger act origin start host)
    (retained : host.retained = some state) :
    host.delivered = state.history ∧ host.world = OwnedPullDriver.interpret act state.history origin :=
  ledger_published_once act origin reached retained

namespace Controls

def first (rule : GroundComm) : LocatedComm := ⟨rule, 0, 1, 2, by decide, by decide, by decide⟩
def second (rule : GroundComm) : LocatedComm := ⟨rule, 3, 4, 5, by decide, by decide, by decide⟩
def competing (rule : GroundComm) : LocatedComm := ⟨rule, 0, 4, 5, by decide, by decide, by decide⟩

def initial (rule : GroundComm) : Nat → Cell := fun key =>
  if key = 0 ∨ key = 3 then .live (first rule).inputBag
  else if key = 1 ∨ key = 4 then .live (first rule).outputBag else .fresh

theorem distinct_occurrences (rule : GroundComm) :
    (first rule).rule = (second rule).rule ∧ (first rule).proposal ≠ (second rule).proposal := by
  refine ⟨rfl, ?_⟩
  intro same
  have heads := congrArg (fun p : Proposal Nat Cell => p.reads.head?.map (·.1)) same
  change some 0 = some 3 at heads
  cases heads

theorem disjoint (rule : GroundComm) : (first rule).keys.Disjoint (second rule).keys := by
  change [0, 1, 2].Disjoint [3, 4, 5]
  simp [List.disjoint_left]

theorem both_ready (rule : GroundComm) :
    (first rule).Ready (initial rule) ∧ (second rule).Ready (initial rule) := by
  simp [Ready, initial, first, second, inputBag, outputBag]

/-- Duplicate-valued redexes produce two retained commits in both orders. -/
theorem two_commits (rule : GroundComm) :
    let start : Ledger Nat Cell := ⟨initial rule, []⟩
    let forward := Ledger.submit (second rule).proposal (Ledger.submit (first rule).proposal start)
    let backward := Ledger.submit (first rule).proposal (Ledger.submit (second rule).proposal start)
    forward.store = backward.store ∧ forward.history.length = 2 ∧ backward.history.length = 2 := by
  obtain ⟨same, forwards, backwards⟩ := ledger_diamond (first rule) (second rule)
    ⟨initial rule, []⟩ (disjoint rule) (both_ready rule).1 (both_ready rule).2
  exact ⟨same, by simp [forwards], by simp [backwards]⟩

/-- The causal observer can identify these schedules, but the chronological
receipt observer still distinguishes them. -/
theorem independent_chronology_differs (rule : GroundComm) :
    [(first rule).proposal.writes, (second rule).proposal.writes] ≠
      [(second rule).proposal.writes, (first rule).proposal.writes] := by
  intro same
  have keys := congrArg (fun rows : List (Writes Nat Cell) => rows.map (fun row => row.map (·.1))) same
  change [[0, 1, 2], [3, 4, 5]] = [[3, 4, 5], [0, 1, 2]] at keys
  simp at keys

/-- A second receiver competing for the first occurrence is refused. -/
theorem competition_refused (rule : GroundComm) :
    commit (write (initial rule) (first rule).proposal.writes) (competing rule).proposal = none := by
  apply commit_rejects_changed_read _ _ (read := (0, .live (competing rule).inputBag))
  · simp [proposal, competing]
  · change write (initial rule) (first rule).proposal.writes (first rule).inputKey ≠ _
    rw [write_input]
    intro impossible
    cases impossible

/-- Allocation cannot silently recycle a consumed occurrence identity. -/
theorem spent_allocation_refused (rule : GroundComm) :
    commit (fun _ => Cell.spent) (first rule).proposal = none :=
  allocated_result_refused _ _ (by intro impossible; cases impossible)

end Controls
end LocatedComm
end Retained

namespace Retained
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Machines ValidatedCommit ReadOnlyQuery
local instance : DecidableEq Bag := by unfold Bag; infer_instance

/-- A finite wire store is newest first; absent keys are genuinely fresh. -/
abbrev CellStore := List (Nat × Cell)
namespace CellStore

def read : CellStore → Nat → Cell
  | [], _ => .fresh
  | (key, value) :: rest, wanted => if wanted = key then value else read rest wanted

theorem read_cons (store : CellStore) (key : Nat) (value : Cell) :
    read ((key, value) :: store) = Function.update (read store) key value := by
  funext wanted
  simp only [read, Function.update_apply]

def write (store : CellStore) (writes : Writes Nat Cell) : CellStore :=
  writes.foldl (fun current entry => entry :: current) store

/-- A shadowing wire row implements the ordinary store update. -/
theorem read_write (store : CellStore) (writes : Writes Nat Cell) :
    read (write store writes) = ValidatedCommit.write (read store) writes := by
  induction writes generalizing store with
  | nil => rfl
  | cons entry rest ih =>
    simp only [write, List.foldl_cons, ValidatedCommit.write]
    exact (ih (entry :: store)).trans (by rw [read_cons]; rfl)

def commit (store : CellStore) (proposal : Proposal Nat Cell) : Option CellStore :=
  if checkReads (read store) proposal.reads then some (write store proposal.writes) else none

/-- The executable finite carrier refines the existing validated ledger. -/
theorem commit_refines (store : CellStore) (proposal : Proposal Nat Cell) :
    (commit store proposal).map read = ValidatedCommit.commit (read store) proposal := by
  simp only [commit, ValidatedCommit.commit]
  split <;> simp [read_write]

end CellStore

def Cell.term : Cell → Term
  | .fresh => .symbol "RhoFresh"
  | .spent => .symbol "RhoSpent"
  | .live contents => .application "RhoLiveCell"
      [encodeList InferenceCettaWire.encodePattern (ordered contents.1)]

theorem Cell.term_injective : Function.Injective Cell.term := by
  intro left right same
  cases left <;> cases right <;> simp only [Cell.term, Term.symbol.injEq,
    Term.application.injEq, List.cons.injEq, and_true, true_and] at same
  all_goals first
    | contradiction
    | rfl
    | (rename_i first second
       have listSame := encodeList_injective InferenceCettaWire.encodePattern
         InferenceCettaWire.encodePattern_injective same
       have bagSame : first = second := by
         apply Subtype.ext
         simpa only [ordered_multiset] using congrArg (fun values : List Pattern => (values : Multiset Pattern)) listSame
       cases bagSame
       rfl)

namespace CellStore

def entryTerm (entry : Nat × Cell) : Term :=
  .application "RhoCell" [.natural entry.1, entry.2.term]

def term (store : CellStore) : Term := encodeList entryTerm store

def proposalTerm (proposal : Proposal Nat Cell) : Term :=
  .application "RhoProposal" [term proposal.reads, term proposal.writes]

def resultTerm (store : CellStore) : Option CellStore → Term
  | some next => .application "RhoCellsAccepted" [term next]
  | none => .application "RhoCellsRefused" [term store]

/-- A finite-carrier candidate is admitted exactly when its actual COMM
occurrences and unused allocation cell still agree with the recorded reads. -/
theorem commit_located_iff (store : CellStore) (candidate : LocatedComm) :
    commit store candidate.proposal = some (write store candidate.proposal.writes) ↔
      candidate.Ready (read store) := by
  simp [commit, ← candidate.ready_iff_agrees, checkReads_iff]
end CellStore
end Retained

/-! ## The authored runner -/

section Authored

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open scoped ProgramQuotation

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_rho_runner.metta"
    sha256 "7c64ac925e7443eb3e137f8a82d8572491c494f1a4346a5de3995fc216ab9c21"

/-- The driver with its resumption, then the canonicalizer, then the runner. -/
def runtime : Program :=
  GeneralProgramResumptionExecution.runtime.append (RhoLexCanonicalExecution.runtime.append source.program)

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)

/-! ### The code beneath the runner -/

private def localHeads : List String :=
  ["rho:lex:name-ser", "rho:lex:append", "rho:lex:length", "rho:lex:ser", "rho:lex:ser-list", "rho:lex:le",
   "rho:lex:insert", "rho:lex:sort", "rho:lex:non-zero", "rho:lex:contents", "rho:lex:collapse",
   "rho:lex:quote", "rho:lex:canonical", "rho:lex:canonical-list", "rho:run:step", "rho:run",
   "rho:run:resume-search", "rho:run:append-commit", "rho:run:begin", "rho:run:resume-process",
   "rho:run:commit", "rho:run:commit-candidate", "rho:run:cancel", "rho:run:advance",
   "rho:run:after-receipt", "rho:run:contains-receipt", "rho:run:commit-published",
   "rho:run:cell-read", "rho:run:validate-reads", "rho:run:apply-writes", "rho:run:commit-cells"]

/-- Every head except the canonicalizer's and the runner's own. -/
private def resumptionHeads (head : String) : Bool := !localHeads.contains head

private theorem resumption_closed : ProgramClosed resumptionHeads GeneralProgramResumptionExecution.runtime := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : GeneralProgramResumptionExecution.runtime.equations.all (fun equation =>
        !resumptionHeads equation.head || codeWithin resumptionHeads equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

private theorem resumption_agreement :
    ProgramAgreementOn resumptionHeads GeneralProgramResumptionExecution.runtime runtime := by
  apply appended_program_agreement
  · intro equation member
    have checked : (RhoLexCanonicalExecution.runtime.append source.program).equations.all
        (fun equation => !resumptionHeads equation.head) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases supported : resumptionHeads equation.head with
    | false => rfl
    | true => simp [supported] at row
  · intro name types member
    have checked : (RhoLexCanonicalExecution.runtime.append source.program).declarations.all (fun declaration =>
        match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !resumptionHeads head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases supported : resumptionHeads name with
    | false => rfl
    | true => simp [supported] at row

/-- The driver and the resumption run unchanged beneath the runner. -/
private theorem resumption_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin resumptionHeads code = true)
    (returned : PureReturns GeneralProgramResumptionExecution.runtime caller before code after answer) :
    PureReturns runtime caller before code after answer :=
  path_of_closed_agreement resumption_closed resumption_agreement ⟨supported, rfl⟩ returned

private def lexVocabulary : List String :=
  ["rho:lex:name-ser", "rho:lex:append", "rho:lex:length", "rho:lex:ser", "rho:lex:ser-list", "rho:lex:le",
   "rho:lex:insert", "rho:lex:sort", "rho:lex:non-zero", "rho:lex:contents", "rho:lex:collapse",
   "rho:lex:quote", "rho:lex:canonical", "rho:lex:canonical-list",
   "let", "let*", "case", "if", "==", "<", "+", "LCons", "LNil", "Var", "PApp", "PLam", "PCollection",
   "UnknownRhoConstructor"]

/-- The canonicalizer's heads, with the operations and constructors its code uses. -/
private def lexHeads (head : String) : Bool := lexVocabulary.contains head

private theorem lex_closed : ProgramClosed lexHeads RhoLexCanonicalExecution.runtime := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RhoLexCanonicalExecution.runtime.equations.all (fun equation =>
        !lexHeads equation.head || codeWithin lexHeads equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

private theorem lex_agreement : ProgramAgreementOn lexHeads RhoLexCanonicalExecution.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · have below : GeneralProgramResumptionExecution.runtime.equations.filter
        (fun equation => lexHeads equation.head) = [] := by
      rw [List.filter_eq_nil_iff]
      intro equation member
      have checked : GeneralProgramResumptionExecution.runtime.equations.all
          (fun equation => !lexHeads equation.head) = true := by decide +kernel
      simpa using List.all_eq_true.mp checked equation member
    have above : source.program.equations.filter (fun equation => lexHeads equation.head) = [] := by
      rw [List.filter_eq_nil_iff]
      intro equation member
      have checked : source.program.equations.all (fun equation => !lexHeads equation.head) = true := by
        decide +kernel
      simpa using List.all_eq_true.mp checked equation member
    simp only [runtime, SpaceSemantics.Program.append, List.filter_append, below, above, List.nil_append,
      List.append_nil]
  · have below : GeneralProgramResumptionExecution.runtime.declarations.filter
        (retainedCallDeclaration lexHeads) = [] := by
      rw [List.filter_eq_nil_iff]
      intro declaration member
      have checked : GeneralProgramResumptionExecution.runtime.declarations.all
          (fun declaration => !retainedCallDeclaration lexHeads declaration) = true := by decide +kernel
      simpa using List.all_eq_true.mp checked declaration member
    have above : source.program.declarations.filter (retainedCallDeclaration lexHeads) = [] := by
      rw [List.filter_eq_nil_iff]
      intro declaration member
      have checked : source.program.declarations.all
          (fun declaration => !retainedCallDeclaration lexHeads declaration) = true := by decide +kernel
      simpa using List.all_eq_true.mp checked declaration member
    simp only [runtime, SpaceSemantics.Program.append, List.filter_append, below, above, List.nil_append,
      List.append_nil]

/-- The canonicalizer runs unchanged beneath the runner. -/
private theorem lex_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin lexHeads code = true)
    (returned : PureReturns RhoLexCanonicalExecution.runtime caller before code after answer) :
    PureReturns runtime caller before code after answer :=
  path_of_closed_agreement lex_closed lex_agreement ⟨supported, rfl⟩ returned

private theorem closed_arguments (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value
    exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

private theorem canonical_captured (caller : Subst) (state : State) {process : Pattern} (shaped : RhoShaped process)
    (captured : applySubst caller (v "process") = patternValue process) :
    PureReturns runtime caller state (a "rho:lex:canonical" [v "process"]) state (patternValue (lexCanon process)) := by
  apply lex_returns (by decide)
  apply PureData.raw_capture_returns RhoLexCanonicalExecution.runtime [] caller state state "rho:lex:canonical"
    [patternValue process] [v "process"] _ (by decide +kernel) _ (by decide)
  · simp [captured]
  · exact RhoLexCanonicalExecution.canonical_returns state process shaped
  · intro index bounded
    have zero : index = 0 := by simpa using bounded
    subst zero
    decide +kernel

private def executeNames : List String :=
  ["environment", "permissions", "bound", "expected", "canonical", "rules", "budget"]

private theorem execute_captured (caller : Subst) (state : State) (canonical : Pattern) (budget : Nat)
    (captured : (executeNames.map v).map (applySubst caller) =
      (GeneralProgramDriverExecution.executeArguments plan [] (.base "Proc") canonical budget).map encoded) :
    PureReturns runtime caller state (a "gslt:program:execute" (executeNames.map v)) state
      (encoded (GeneralProgramDriverExecution.programObservationTerm
        (invocations plan [] (.base "Proc") canonical fun _ => budget))) := by
  apply resumption_returns (by decide)
  apply GeneralProgramResumptionExecution.driver_returns (by decide)
  apply PureData.raw_capture_returns GeneralProgramDriverExecution.runtime [] caller state state
    "gslt:program:execute" ((GeneralProgramDriverExecution.executeArguments plan [] (.base "Proc") canonical
      budget).map encoded) (executeNames.map v) _ (by decide +kernel) _ (by decide)
  · rw [closed_arguments, captured]
  · exact GeneralProgramDriverExecution.execute_returns state plan finiteProvider [] (.base "Proc") canonical budget
  · intro index bounded
    have checked : (List.range 7).all
        (fun index => argumentIsRaw GeneralProgramDriverExecution.runtime "gslt:program:execute" index) = true := by
      decide +kernel
    apply List.all_eq_true.mp checked index
    simp only [GeneralProgramDriverExecution.executeArguments, List.length_map, List.length_cons,
      List.length_nil] at bounded
    exact List.mem_range.mpr bounded

private theorem publication_captured (caller : Subst) (state : State) (program : ProgramRun)
    (captured : applySubst caller (v "observation") = encoded program.term) :
    PureReturns runtime caller state (a "gslt:program:publication" [v "observation"]) state
      (encoded program.publicationTerm) := by
  apply resumption_returns (by decide)
  apply PureData.raw_capture_returns GeneralProgramResumptionExecution.runtime [] caller state state
    "gslt:program:publication" [encoded program.term] [v "observation"] _ (by decide +kernel) _ (by decide)
  · simp [captured]
  · exact GeneralProgramResumptionExecution.publication_returns state program
  · intro index bounded
    have zero : index = 0 := by simpa using bounded
    subst zero
    decide +kernel

/-! ### The runner's equations -/

private inductive Helper where
  | step | run | resumeSearch
  | appendCommit | begin | resumeProcess | commit | commitCandidate | cancel | advance
  | afterReceipt | containsReceipt | commitPublished | cellRead | validateReads | applyWrites | commitCells

private def Helper.head : Helper → String
  | .step => "rho:run:step"
  | .run => "rho:run"
  | .resumeSearch => "rho:run:resume-search"
  | .appendCommit => "rho:run:append-commit"
  | .begin => "rho:run:begin"
  | .resumeProcess => "rho:run:resume-process"
  | .commit => "rho:run:commit"
  | .commitCandidate => "rho:run:commit-candidate"
  | .cancel => "rho:run:cancel"
  | .advance => "rho:run:advance"
  | .afterReceipt => "rho:run:after-receipt"
  | .containsReceipt => "rho:run:contains-receipt"
  | .commitPublished => "rho:run:commit-published"
  | .cellRead => "rho:run:cell-read"
  | .validateReads => "rho:run:validate-reads"
  | .applyWrites => "rho:run:apply-writes"
  | .commitCells => "rho:run:commit-cells"

private def Helper.names : Helper → List String
  | .step => ["plan", "process", "budget"]
  | .run => ["plan", "process", "fuel", "budget"]
  | .resumeSearch => ["search", "extra"]
  | .appendCommit => ["history", "commit"]
  | .begin => ["plan", "process"]
  | .resumeProcess => ["execution", "extra"]
  | .commit => ["plan", "execution"]
  | .commitCandidate => ["plan", "execution", "candidate"]
  | .cancel => ["execution"]
  | .advance => ["plan", "execution", "fuel"]
  | .afterReceipt => ["plan", "history", "process", "receipt"]
  | .containsReceipt => ["candidate", "receipts"]
  | .commitPublished => ["plan", "execution", "candidate"]
  | .cellRead => ["cells", "key"]
  | .validateReads => ["cells", "reads"]
  | .applyWrites => ["cells", "writes"]
  | .commitCells => ["cells", "proposal"]

private def runnerHeads : List String :=
  ["rho:run:step", "rho:run", "rho:run:resume-search", "rho:run:append-commit", "rho:run:begin",
   "rho:run:resume-process", "rho:run:commit", "rho:run:commit-candidate", "rho:run:cancel",
   "rho:run:advance", "rho:run:after-receipt", "rho:run:contains-receipt",
   "rho:run:commit-published", "rho:run:cell-read", "rho:run:validate-reads",
   "rho:run:apply-writes", "rho:run:commit-cells"]

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (source.program.equations.filter (fun equation => equation.head == helper.head))[0]'(by
    cases helper <;> decide +kernel)

private def bindings (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

/-- Only the runner's source defines its heads. -/
private theorem runner_equations (helper : Helper) :
    runtime.equations.filter (fun row => row.head == helper.head) = [equation helper] := by
  have owned : localHeads.contains helper.head = true := by cases helper <;> decide
  have below : GeneralProgramResumptionExecution.runtime.equations.filter
      (fun row => row.head == helper.head) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row member same
    have checked : GeneralProgramResumptionExecution.runtime.equations.all
        (fun row => !localHeads.contains row.head) = true := by decide +kernel
    have fresh := List.all_eq_true.mp checked row member
    rw [beq_iff_eq.mp same, owned] at fresh
    cases fresh
  have beside : RhoLexCanonicalExecution.runtime.equations.filter (fun row => row.head == helper.head) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row member same
    have checked : RhoLexCanonicalExecution.runtime.equations.all
        (fun row => !runnerHeads.contains row.head) = true := by decide +kernel
    have fresh := List.all_eq_true.mp checked row member
    rw [beq_iff_eq.mp same] at fresh
    cases helper <;> simp [Helper.head, runnerHeads] at fresh
  have own : source.program.equations.filter (fun row => row.head == helper.head) = [equation helper] := by
    cases helper <;> rfl
  simp only [runtime, SpaceSemantics.Program.append, List.filter_append, below, beside, own, List.nil_append]

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (bindings helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (runner_equations helper) (by cases helper <;> rfl) (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw runtime helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (bindings helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (bindings helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
  · cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
  · cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · cases helper <;> decide
  · rw [closed_arguments]
    exact captured.symm
  · exact returned

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private theorem named_let_returns (caller : Subst) (state : State)
    (name : String) (expression value body answer : Atom)
    (fresh : caller.lookup name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed
  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]
  · exact continued

private def pairsAtom (pairs : List (Atom × Atom)) : Atom :=
  .expression (pairs.map fun pair => .expression [pair.1, pair.2])

private theorem bind_fresh {caller final : Subst} {state : State} {name : String} {expression value : Atom}
    {rest : List (Atom × Atom)}
    (fresh : caller.lookup name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureData.BindingsReturn runtime ((name, value) :: caller) state rest final state) :
    PureData.BindingsReturn runtime caller state ((v name, expression) :: rest) final state :=
  .cons computed (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]) continued

private theorem let_star_bindings {caller final : Subst} {state : State} {pairs : List (Atom × Atom)}
    {body answer : Atom}
    (computed : PureData.BindingsReturn runtime caller state pairs final state)
    (returned : PureReturns runtime final state body state answer) :
    PureReturns runtime caller state (a "let*" [pairsAtom pairs, body]) state answer :=
  PureData.let_bindings_return computed state body answer returned

private theorem template_constructor (head : String) (arguments : List Atom)
    (constructor : head ∈ ["LCons", "RhoQuiescent", "RhoStepped", "RhoUnsaturated", "RhoTrace", "RhoSearch",
      "RhoProcess", "RhoLive", "RhoDone", "RhoCommit"])
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
  rcases constructor with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact PureData.Template.constructor _ _ (by decide +kernel) (by decide) children

local macro "runner_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.symbol _
  | (apply template_constructor _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

/-! ### The plan and the printed outcomes -/

/-- The depth-one plan as the runner receives it. -/
def planTerm : Term :=
  .application "RhoPlan"
    [GeneralProgramDriverExecution.environmentTerm plan (.apply "PZero" []),
     InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
     encodeList InferenceCettaWire.AuthoredRule.typeTerm [],
     InferenceCettaWire.AuthoredRule.typeTerm (.base "Proc"),
     encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules]

/-- The driver's environment term depends on a source only through its free variables. -/
theorem environmentTerm_closed {state : Pattern} (closed : state.freeFvarNames = []) :
    GeneralProgramDriverExecution.environmentTerm plan state =
      GeneralProgramDriverExecution.environmentTerm plan (.apply "PZero" []) := by
  simp only [GeneralProgramDriverExecution.environmentTerm, closed, Pattern.freeFvarNames, List.flatMap_nil]

def outcomeTerm : Outcome → Term
  | .quiescent state => .application "RhoQuiescent" [InferenceCettaWire.encodePattern state]
  | .stepped state next =>
      .application "RhoStepped" [InferenceCettaWire.encodePattern state, InferenceCettaWire.encodePattern next]
  | .unsaturated state status =>
      .application "RhoUnsaturated" [InferenceCettaWire.encodePattern state, ProgramRun.statusTerm status]

def endingTerm : Ending → Term
  | .quiescent => .symbol "RhoQuiescent"
  | .fuelSpent => .symbol "RhoFuelSpent"
  | .unsaturated status => .application "RhoUnsaturated" [ProgramRun.statusTerm status]

def traceTerm (trace : List Pattern × Ending) : Term :=
  .application "RhoTrace" [encodeList InferenceCettaWire.encodePattern trace.1, endingTerm trace.2]

/-! ### Retaining one COMM search -/

/-- The wire value includes the complete program observation, including its
pending job frames. It is not only the current publication. -/
def Search.term (search : Search) : Term :=
  .application "RhoSearch" [InferenceCettaWire.encodePattern search.process, search.program.term]

def resumeSearchQuery (search : Search) (extra : Nat) : Atom :=
  a "rho:run:resume-search" [encoded search.term, number extra]

private def resumeSearchBody : Atom :=
  a "let" [v "resumed", a "gslt:program:resume" [v "observation", v "extra"],
    a "RhoSearch" [v "process", v "resumed"]]

private def resumeSearchCases : SpaceSemantics.Cases :=
  [(a "RhoSearch" [v "process", v "observation"], resumeSearchBody)]

private theorem resumeSearch_shape : (equation .resumeSearch).body =
    a "case" [v "search", .expression (resumeSearchCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem resume_captured (caller : Subst) (state : State) (program : ProgramRun)
    (finite : ∀ job ∈ program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ job ∈ program, job.Reachable) (extra : Nat)
    (captured : [v "observation", v "extra"].map (applySubst caller) =
      [encoded program.term, number extra]) :
    PureReturns runtime caller state (a "gslt:program:resume" [v "observation", v "extra"]) state
      (encoded (program.resume extra).term) := by
  apply resumption_returns (by decide)
  apply PureData.raw_capture_returns GeneralProgramResumptionExecution.runtime [] caller state state
    "gslt:program:resume" [encoded program.term, number extra] [v "observation", v "extra"] _
    (by decide +kernel) _ (by decide)
  · rw [closed_arguments, captured]
  · exact GeneralProgramResumptionExecution.resume_returns state program finite reachable extra
  · intro index bounded
    have checked : (List.range 2).all
        (fun index => argumentIsRaw GeneralProgramResumptionExecution.runtime "gslt:program:resume" index) = true := by
      decide +kernel
    exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

/-- The authored operation resumes the retained jobs and returns the full
updated search, preserving its canonical process. The ambient state and effect
queues are unchanged. -/
theorem resume_search_returns (state : State) (search : Search)
    (finite : ∀ job ∈ search.program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ job ∈ search.program, job.Reachable) (extra : Nat) :
    PureReturns runtime [] state (resumeSearchQuery search extra) state
      (encoded (search.resume extra).term) := by
  let caller := bindings .resumeSearch [encoded search.term, number extra]
  let selected := [("observation", encoded search.program.term),
    ("process", patternValue search.process)] ++ caller
  let final := ("resumed", encoded (search.program.resume extra).term) :: selected
  apply helper_call .resumeSearch [] state _ [encoded search.term, number extra] _ rfl
    (closed_arguments _)
  rw [resumeSearch_shape]
  apply branch_returns caller selected state _ (encoded search.term) resumeSearchCases resumeSearchBody _
  · exact variable_returns runtime caller state "search"
  · simp [resumeSearchCases, selected, caller, bindings, Helper.names, Search.term,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold resumeSearchBody
    apply named_let_returns selected state "resumed" _ (encoded (search.program.resume extra).term)
    · simp [selected, caller, bindings, Helper.names, Subst.lookup]
    · exact resume_captured selected state search.program finite reachable extra
        (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
    · have template : PureData.Template runtime (a "RhoSearch" [v "process", v "resumed"]) := by
        runner_template
      simpa [final, selected, Search.term, Search.resume, applySubst, applySubst.applySubstList,
        Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime final state _ template

/-- Exact evaluator completion, including the preserved state and empty effect
queues; no successful completion has a different search result. -/
theorem resume_search_completed_iff (state after : State) (search : Search)
    (finite : ∀ job ∈ search.program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ job ∈ search.program, job.Reachable) (extra : Nat) (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run runtime evaluatorFuel
      {state, control := .evaluate [] (resumeSearchQuery search extra)} = .complete after answers input output) ↔
      after = state ∧ answers = [encoded (search.resume extra).term] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _
    (resume_search_returns state search finite reachable extra) after answers input output

/-- Valid searches remain valid through the actual authored resume operation,
whose publication is an ordered prefix extension of the previous publication.
This concerns one search, before any COMM receipt is committed. -/
theorem authored_resume_search (state : State) (search : Search)
    (valid : search.Valid) (extra : Nat) :
    PureReturns runtime [] state (resumeSearchQuery search extra) state
      (encoded (search.resume extra).term) ∧
    (search.resume extra).Valid ∧
    search.program.publication <+: (search.resume extra).program.publication :=
  ⟨resume_search_returns state search (Search.finite search valid) (Search.reachable search valid) extra,
    Search.resume_valid search valid extra, ProgramRun.publication_prefix search.program extra⟩

/-! ### One step -/

private def stepPairs : List (Atom × Atom) :=
  [(v "canonical", a "rho:lex:canonical" [v "process"]),
   (v "observation", a "gslt:program:execute" (executeNames.map v)),
   (v "published", a "gslt:program:publication" [v "observation"])]

private def receiptPattern : Atom :=
  a "RuleJobReceipt" [v "job", v "trace", v "captured", v "completed", v "history", v "local", v "target"]

private def publishedCases : SpaceSemantics.Cases :=
  [(a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationComplete"], a "RhoQuiescent" [v "canonical"]),
   (a "ProgramPublication" [a "LCons" [receiptPattern, v "others"], v "status"],
    a "RhoStepped" [v "canonical", v "target"]),
   (a "ProgramPublication" [v "released", v "status"], a "RhoUnsaturated" [v "canonical", v "status"])]

private def stepBody : Atom :=
  a "let*" [pairsAtom stepPairs,
    a "case" [v "published", .expression (publishedCases.map fun row => .expression [row.1, row.2])]]

private def planCases : SpaceSemantics.Cases :=
  [(a "RhoPlan" [v "environment", v "permissions", v "bound", v "expected", v "rules"], stepBody)]

private theorem step_shape : (equation .step).body =
    a "case" [v "plan", .expression (planCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def planBindings : Subst :=
  [("rules", encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules)),
   ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm (.base "Proc"))),
   ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm [])),
   ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites)),
   ("environment", encoded (GeneralProgramDriverExecution.environmentTerm plan (.apply "PZero" [])))]

private def stepCaller (process : Pattern) (budget : Nat) : Subst :=
  bindings .step [encoded planTerm, patternValue process, number budget]

private def finalBindings (canonical process : Pattern) (program : ProgramRun) (budget : Nat) : Subst :=
  [("published", encoded program.publicationTerm), ("observation", encoded program.term),
   ("canonical", patternValue canonical)] ++ planBindings ++ stepCaller process budget

private theorem published_returns (state : State) (canonical process : Pattern) (program : ProgramRun)
    (budget : Nat) :
    PureReturns runtime (finalBindings canonical process program budget) state
      (a "case" [v "published", .expression (publishedCases.map fun row => .expression [row.1, row.2])]) state
      (encoded (outcomeTerm (outcomeOf canonical program))) := by
  let final := finalBindings canonical process program budget
  have printed : PureReturns runtime final state (v "published") state (encoded program.publicationTerm) := by
    simpa [final, finalBindings, applySubst, Subst.lookup] using variable_returns runtime final state "published"
  unfold outcomeOf
  cases published : program.publication with
  | nil =>
    cases status : program.status with
    | complete =>
      apply branch_returns final final state _ _ publishedCases (a "RhoQuiescent" [v "canonical"]) _ printed
      · simp [publishedCases, ProgramRun.publicationTerm, published, status, ProgramRun.statusTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom]
      · have template : PureData.Template runtime (a "RhoQuiescent" [v "canonical"]) := by runner_template
        simpa [final, finalBindings, outcomeTerm, applySubst, applySubst.applySubstList, Subst.lookup,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using PureData.template_return runtime final state _ template
    | blocked | pending =>
      let selected := [("status", encoded (ProgramRun.statusTerm program.status)),
        ("released", .symbol "LNil")] ++ final
      apply branch_returns final selected state _ _ publishedCases (a "RhoUnsaturated" [v "canonical", v "status"]) _
        printed
      · simp [publishedCases, selected, final, finalBindings, planBindings, stepCaller, bindings, Helper.names,
          ProgramRun.publicationTerm, published, status, ProgramRun.statusTerm, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · have template : PureData.Template runtime (a "RhoUnsaturated" [v "canonical", v "status"]) := by
          runner_template
        simpa [selected, final, finalBindings, outcomeTerm, status, applySubst, applySubst.applySubstList,
          Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return runtime selected state _ template
  | cons receipt rest =>
    have shape : ∃ job trace captured completed history localTarget : Term,
        ScopedRuleJobReadoutExecution.receiptTerm receipt =
          .application "RuleJobReceipt" [job, trace, captured, completed, history, localTarget,
            InferenceCettaWire.encodePattern receipt.target] := ⟨_, _, _, _, _, _, rfl⟩
    obtain ⟨job, trace, captured, completed, history, localTarget, receiptShape⟩ := shape
    let selected := [("status", encoded (ProgramRun.statusTerm program.status)),
      ("others", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm rest)),
      ("target", patternValue receipt.target), ("local", encoded localTarget), ("history", encoded history),
      ("completed", encoded completed), ("captured", encoded captured), ("trace", encoded trace),
      ("job", encoded job)] ++ final
    have template : PureData.Template runtime (a "RhoStepped" [v "canonical", v "target"]) := by runner_template
    have stepped : PureReturns runtime selected state (a "RhoStepped" [v "canonical", v "target"]) state
        (encoded (outcomeTerm (.stepped canonical receipt.target))) := by
      simpa [selected, final, finalBindings, outcomeTerm, applySubst, applySubst.applySubstList, Subst.lookup,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using PureData.template_return runtime selected state _ template
    apply branch_returns final selected state _ _ publishedCases (a "RhoStepped" [v "canonical", v "target"]) _
      printed _ stepped
    cases status : program.status <;>
      simp [publishedCases, receiptPattern, selected, final, finalBindings, planBindings, stepCaller, bindings,
        Helper.names, ProgramRun.publicationTerm, published, status, ProgramRun.statusTerm, encodeList,
        receiptShape, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup]

/-- **One step of the authored runner** is the model's step. -/
theorem step_returns (state : State) {process : Pattern} (shaped : RhoShaped process) (budget : Nat) :
    PureReturns runtime [] state (a "rho:run:step" [encoded planTerm, patternValue process, number budget]) state
      (encoded (outcomeTerm (step process budget))) := by
  have closed := rhoShaped_freeFvarNames (lexCanon_rhoShaped shaped)
  let caller := stepCaller process budget
  let selected := planBindings ++ caller
  let withCanonical := ("canonical", patternValue (lexCanon process)) :: selected
  let program := programOf (lexCanon process) budget
  let withObservation := ("observation", encoded program.term) :: withCanonical
  apply helper_call .step [] state _ [encoded planTerm, patternValue process, number budget] _ rfl
    (closed_arguments _)
  rw [step_shape]
  apply branch_returns caller selected state _ (encoded planTerm) planCases stepBody _
  · exact variable_returns runtime caller state "plan"
  · simp [planCases, selected, caller, stepCaller, planBindings, bindings, Helper.names, planTerm,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold stepBody
    apply let_star_bindings (final := finalBindings (lexCanon process) process program budget)
    · apply bind_fresh (by simp [selected, caller, stepCaller, planBindings, bindings, Helper.names, Subst.lookup])
        (canonical_captured selected state shaped (by
          simp [selected, caller, stepCaller, planBindings, bindings, Helper.names, applySubst, Subst.lookup]))
      apply bind_fresh
        (by simp [selected, caller, stepCaller, planBindings, bindings, Helper.names, Subst.lookup])
        (by
          have observed := execute_captured withCanonical state (lexCanon process) budget (by
            simp [executeNames, withCanonical, selected, caller, stepCaller, planBindings, bindings, Helper.names,
              applySubst, Subst.lookup, GeneralProgramDriverExecution.executeArguments, environmentTerm_closed closed])
          rwa [← ProgramRun.ofInvocations_term] at observed)
      apply bind_fresh
        (by simp [withObservation, withCanonical, selected, caller, stepCaller, planBindings, bindings, Helper.names,
          Subst.lookup])
        (publication_captured withObservation state program (by simp [withObservation, applySubst, Subst.lookup]))
      exact .nil _ _
    · exact published_returns state (lexCanon process) process program budget

/-! ### Runs -/

private def runPairs : List (Atom × Atom) :=
  [(v "remaining", a "-" [v "fuel", number 1]),
   (v "rest", a "rho:run" [v "plan", v "next", v "remaining", v "budget"])]

private def restCases : SpaceSemantics.Cases :=
  [(a "RhoTrace" [v "states", v "end"], a "RhoTrace" [a "LCons" [v "state", v "states"], v "end"])]

private def resultCases : SpaceSemantics.Cases :=
  [(a "RhoQuiescent" [v "state"], a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], .symbol "RhoQuiescent"]),
   (a "RhoStepped" [v "state", v "next"],
    a "let*" [pairsAtom runPairs,
      a "case" [v "rest", .expression (restCases.map fun row => .expression [row.1, row.2])]]),
   (a "RhoUnsaturated" [v "state", v "status"],
    a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], a "RhoUnsaturated" [v "status"]])]

private def runBody : Atom :=
  a "if" [a "==" [v "fuel", number 0],
    a "let" [v "state", a "rho:lex:canonical" [v "process"],
      a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], .symbol "RhoFuelSpent"]],
    a "let" [v "result", a "rho:run:step" [v "plan", v "process", v "budget"],
      a "case" [v "result", .expression (resultCases.map fun row => .expression [row.1, row.2])]]]

private theorem run_shape : (equation .run).body = runBody := by
  decide +kernel

private theorem fuel_test_returns (caller : Subst) (state : State) (fuel : Nat)
    (captured : applySubst caller (v "fuel") = number fuel) :
    PureReturns runtime caller state (a "==" [v "fuel", number 0]) state
      (Effects.boolean (decide (fuel = 0))) := by
  have tested := CettaWireAtom.equality_evaluated_returns runtime caller state (.natural fuel) (.natural 0)
    (v "fuel") (number 0) (by decide +kernel) (by decide +kernel)
    (by simpa only [captured] using variable_returns runtime caller state "fuel")
    (grounded_returns runtime caller state (.int 0))
  simpa only [Term.natural.injEq] using tested

private theorem predecessor_returns (caller : Subst) (state : State) (fuel : Nat)
    (captured : applySubst caller (v "fuel") = number (fuel + 1)) :
    PureReturns runtime caller state (a "-" [v "fuel", number 1]) state (number fuel) := by
  apply native_binary_call_returns runtime caller state state state state "-"
    (v "fuel") (number 1) (number (fuel + 1)) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns runtime caller state "fuel"
  · exact grounded_returns runtime caller state (.int 1)
  · have casts : ((fuel + 1 : Nat) : Int) - 1 = (fuel : Int) := by omega
    simpa only [number, encoded, CettaWireAtom.encode, casts, Int.natCast_one] using
      StdLib.integer_subtraction state ((fuel + 1 : Nat) : Int) 1

private def runCaller (process : Pattern) (fuel budget : Nat) : Subst :=
  bindings .run [encoded planTerm, patternValue process, number fuel, number budget]

/-- **The authored run** is the model's run: at most `fuel` steps, each on the canonical form. -/
theorem run_returns (state : State) (fuel : Nat) : ∀ {process : Pattern} (budget : Nat),
    ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process →
    binderSafeAt "NQuote" 0 process = true →
    PureReturns runtime [] state
      (a "rho:run" [encoded planTerm, patternValue process, number fuel, number budget]) state
      (encoded (traceTerm (run fuel process budget))) := by
  induction fuel with
  | zero =>
    intro process budget typed _
    let caller := runCaller process 0 budget
    let final := ("state", patternValue (lexCanon process)) :: caller
    apply helper_call .run [] state _ [encoded planTerm, patternValue process, number 0, number budget] _ rfl
      (closed_arguments _)
    rw [run_shape]
    unfold runBody
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns runtime caller state _ true
    · simpa using fuel_test_returns caller state 0
        (by simp [caller, runCaller, bindings, Helper.names, applySubst, Subst.lookup])
    · simp only [↓reduceIte]
      apply named_let_returns caller state "state" _ (patternValue (lexCanon process))
      · simp [caller, runCaller, bindings, Helper.names, Subst.lookup]
      · exact canonical_captured caller state (proc_rhoShaped typed)
          (by simp [caller, runCaller, bindings, Helper.names, applySubst, Subst.lookup])
      · have template : PureData.Template runtime
            (a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], .symbol "RhoFuelSpent"]) := by runner_template
        simpa [final, run, traceTerm, endingTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return runtime final state _ template
  | succ fuel ih =>
    intro process budget typed sealed
    let caller := runCaller process (fuel + 1) budget
    apply helper_call .run [] state _ [encoded planTerm, patternValue process, number (fuel + 1), number budget] _
      rfl (closed_arguments _)
    rw [run_shape]
    unfold runBody
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns runtime caller state _ false
    · simpa using fuel_test_returns caller state (fuel + 1)
        (by simp [caller, runCaller, bindings, Helper.names, applySubst, Subst.lookup])
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply named_let_returns caller state "result" _ (encoded (outcomeTerm (step process budget)))
      · simp [caller, runCaller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture .step caller state [v "plan", v "process", v "budget"]
          [encoded planTerm, patternValue process, number budget] _ rfl
          (by simp [caller, runCaller, bindings, Helper.names, applySubst, Subst.lookup])
          (step_returns state (proc_rhoShaped typed) budget)
      · cases outcome : step process budget with
        | quiescent canonical =>
          let withResult := ("result", encoded (outcomeTerm (.quiescent canonical))) :: caller
          have printed : PureReturns runtime withResult state (v "result") state
              (encoded (outcomeTerm (.quiescent canonical))) := by
            simpa [withResult, applySubst, Subst.lookup] using variable_returns runtime withResult state "result"
          let selected := ("state", patternValue canonical) :: withResult
          apply branch_returns withResult selected state _ _ resultCases
            (a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], .symbol "RhoQuiescent"]) _ printed
          · simp [resultCases, selected, withResult, outcomeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              Subst.lookup, caller, runCaller, bindings, Helper.names]
          · have template : PureData.Template runtime
                (a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], .symbol "RhoQuiescent"]) := by runner_template
            simpa [selected, run, outcome, traceTerm, endingTerm, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return runtime selected state _ template
        | stepped canonical next =>
          obtain ⟨rfl, _, depthOne⟩ := step_sound typed sealed outcome
          let withResult := ("result", encoded (outcomeTerm (.stepped (lexCanon process) next))) :: caller
          have printed : PureReturns runtime withResult state (v "result") state
              (encoded (outcomeTerm (.stepped (lexCanon process) next))) := by
            simpa [withResult, applySubst, Subst.lookup] using variable_returns runtime withResult state "result"
          obtain ⟨lexTyped, lexSealed⟩ := closed_lexCanon typed sealed
          obtain ⟨nextTyped, nextSealed⟩ := rhoStepAt_preserves_closed lexTyped lexSealed depthOne
          let selected := [("next", patternValue next), ("state", patternValue (lexCanon process))] ++ withResult
          let withRemaining := ("remaining", number fuel) :: selected
          let restValue := encoded (traceTerm (run fuel next budget))
          let withRest := ("rest", restValue) :: withRemaining
          let finished := [("end", encoded (endingTerm (run fuel next budget).2)),
            ("states", encoded (encodeList InferenceCettaWire.encodePattern (run fuel next budget).1))] ++ withRest
          apply branch_returns withResult selected state _ _ resultCases
            (a "let*" [pairsAtom runPairs,
              a "case" [v "rest", .expression (restCases.map fun row => .expression [row.1, row.2])]]) _ printed
          · simp [resultCases, selected, withResult, outcomeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              Subst.lookup, caller, runCaller, bindings, Helper.names]
          · apply let_star_bindings (final := withRest)
            · apply bind_fresh (by simp [selected, withResult, caller, runCaller, bindings, Helper.names, Subst.lookup])
                (predecessor_returns selected state fuel
                  (by simp [selected, withResult, caller, runCaller, bindings, Helper.names, applySubst,
                    Subst.lookup]))
              apply bind_fresh
                (by simp [withRemaining, selected, withResult, caller, runCaller, bindings, Helper.names,
                  Subst.lookup])
                (helper_capture .run withRemaining state [v "plan", v "next", v "remaining", v "budget"]
                  [encoded planTerm, patternValue next, number fuel, number budget] _ rfl
                  (by simp [withRemaining, selected, withResult, caller, runCaller, bindings, Helper.names,
                    applySubst, Subst.lookup])
                  (ih budget nextTyped nextSealed))
              exact .nil _ _
            · apply branch_returns withRest finished state _ restValue restCases
                (a "RhoTrace" [a "LCons" [v "state", v "states"], v "end"]) _
              · simpa [withRest, applySubst, Subst.lookup] using variable_returns runtime withRest state "rest"
              · simp [restCases, finished, withRest, restValue, withRemaining, selected, withResult, caller,
                  runCaller, bindings, Helper.names, traceTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup]
              · have template : PureData.Template runtime
                    (a "RhoTrace" [a "LCons" [v "state", v "states"], v "end"]) := by runner_template
                simpa [finished, withRest, withRemaining, selected, run, outcome, traceTerm, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
                  Subst.lookup] using PureData.template_return runtime finished state _ template
        | unsaturated canonical status =>
          let withResult := ("result", encoded (outcomeTerm (.unsaturated canonical status))) :: caller
          have printed : PureReturns runtime withResult state (v "result") state
              (encoded (outcomeTerm (.unsaturated canonical status))) := by
            simpa [withResult, applySubst, Subst.lookup] using variable_returns runtime withResult state "result"
          let selected := [("status", encoded (ProgramRun.statusTerm status)), ("state", patternValue canonical)] ++
            withResult
          apply branch_returns withResult selected state _ _ resultCases
            (a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], a "RhoUnsaturated" [v "status"]]) _ printed
          · simp [resultCases, selected, withResult, outcomeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              Subst.lookup, caller, runCaller, bindings, Helper.names]
          · have template : PureData.Template runtime
                (a "RhoTrace" [a "LCons" [v "state", .symbol "LNil"], a "RhoUnsaturated" [v "status"]]) := by
              runner_template
            simpa [selected, run, outcome, traceTerm, endingTerm, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return runtime selected state _ template

/-- **Rho runs on PeTTa.** For a closed, quotation-sealed process, the actual PeTTa run of
`rho:run` prints a trace that starts at the process's canonical form; each state reaches the next
by a depth-one rho step followed by the canonical form, which is structurally congruent to the
step's target; and the run reports quiescence only at a state with no rho step at any depth. -/
theorem authored_run_reduces (state : State) (fuel budget : Nat) {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : binderSafeAt "NQuote" 0 process = true) :
    ∃ trace : List Pattern × Ending,
      PureReturns runtime [] state
        (a "rho:run" [encoded planTerm, patternValue process, number fuel, number budget]) state
        (encoded (traceTerm trace)) ∧
      StructuralCongruence process (lexCanon process) ∧ trace.1.head? = some (lexCanon process) ∧
      trace.1.IsChain Link ∧ (trace.2 = .quiescent → ∀ last ∈ trace.1.getLast?, ∀ target, ¬ RhoStep last target) :=
  ⟨run fuel process budget, run_returns state fuel budget typed sealed, lexCanon_sound process,
    (run_chain fuel budget typed sealed).1, (run_chain fuel budget typed sealed).2,
    run_quiescent fuel budget typed sealed⟩

/-! ### Retained whole-process wire

External one-shot authority, native one-shot resources, and world-update validation
stay outside this owner. Matcher budget stays on `rho:run:resume-process`.
`rho:run:advance` counts commits. Bag agreement is not a commuting-effects theorem.
-/

def Retained.Commit.term (commit : Retained.Commit) : Term :=
  .application "RhoCommit"
    [InferenceCettaWire.encodePattern commit.before,
     ScopedRuleJobReadoutExecution.receiptTerm commit.receipt,
     InferenceCettaWire.encodePattern commit.after]

def Retained.Phase.term : Retained.Phase → Term
  | .live search => .application "RhoLive" [Search.term search]
  | .done process => .application "RhoDone" [InferenceCettaWire.encodePattern process]
  | .cancelled => .symbol "RhoCancelled"

def Retained.Execution.term (execution : Retained.Execution) : Term :=
  .application "RhoProcess"
    [encodeList Retained.Commit.term execution.history, Retained.Phase.term execution.phase]

private def cancelCases : SpaceSemantics.Cases :=
  [(a "RhoProcess" [v "history", a "RhoLive" [v "search"]],
     a "RhoProcess" [v "history", .symbol "RhoCancelled"]),
   (a "RhoProcess" [v "history", a "RhoDone" [v "process"]],
     a "RhoProcess" [v "history", .symbol "RhoCancelled"]),
   (a "RhoProcess" [v "history", .symbol "RhoCancelled"],
     a "RhoProcess" [v "history", .symbol "RhoCancelled"])]

private def cancelBody : Atom :=
  a "case" [v "execution", .expression (cancelCases.map fun row => .expression [row.1, row.2])]

private theorem cancel_shape : (equation .cancel).body = cancelBody := by
  decide +kernel

private def cancelResult : Atom :=
  a "RhoProcess" [v "history", .symbol "RhoCancelled"]

private theorem cancelled_process_returns (caller : Subst) (state : State)
    (history : List Retained.Commit)
    (bound : (caller.lookup "history").getD (v "history") =
      encoded (encodeList Retained.Commit.term history)) :
    PureReturns runtime caller state cancelResult state
      (encoded (Retained.Execution.term ⟨history, .cancelled⟩)) := by
  have template : PureData.Template runtime cancelResult := by
    runner_template
  have returned := PureData.template_return runtime caller state _ template
  simp only [cancelResult, applySubst, applySubst.applySubstList] at returned
  rw [bound] at returned
  simpa [cancelResult, Retained.Execution.term, Retained.Phase.term, CettaWireAtom.encode,
    CettaWireAtom.encodeMany] using returned

/-- The authored cancel operation returns `Retained.Execution.cancel`: the same
receipt history, with this execution's phase set to cancelled. -/
theorem cancel_returns (state : State) (execution : Retained.Execution) :
    PureReturns runtime [] state (a "rho:run:cancel" [encoded execution.term]) state
      (encoded (execution.cancel).term) := by
  let caller := bindings .cancel [encoded execution.term]
  apply helper_call .cancel [] state _ [encoded execution.term] _ rfl (closed_arguments _)
  rw [cancel_shape]
  unfold cancelBody
  cases execution with
  | mk history phase =>
    cases phase with
    | live search =>
      let selected := [("search", encoded search.term),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller selected state _ (encoded (Retained.Execution.term
        ⟨history, .live search⟩)) cancelCases cancelResult _
      · exact variable_returns runtime caller state "execution"
      · simp [cancelCases, cancelResult, selected, caller, bindings, Helper.names, Retained.Execution.term,
          Retained.Phase.term, Search.term, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · apply cancelled_process_returns selected state history
        simp [selected, Subst.lookup]
    | done process =>
      let selected := [("process", patternValue process),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller selected state _ (encoded (Retained.Execution.term
        ⟨history, .done process⟩)) cancelCases cancelResult _
      · exact variable_returns runtime caller state "execution"
      · simp [cancelCases, cancelResult, selected, caller, bindings, Helper.names, Retained.Execution.term,
          Retained.Phase.term, patternValue, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · apply cancelled_process_returns selected state history
        simp [selected, Subst.lookup]
    | cancelled =>
      let selected := [("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller selected state _ (encoded (Retained.Execution.term
        ⟨history, .cancelled⟩)) cancelCases cancelResult _
      · exact variable_returns runtime caller state "execution"
      · simp [cancelCases, cancelResult, selected, caller, bindings, Helper.names, Retained.Execution.term,
          Retained.Phase.term, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · apply cancelled_process_returns selected state history
        simp [selected, Subst.lookup]

/-- Cancel on the quoted runner is the local cancellation law: history stays,
and the phase is cancelled. -/
theorem authored_cancel_agrees (state : State) (execution : Retained.Execution) :
    PureReturns runtime [] state (a "rho:run:cancel" [encoded execution.term]) state
      (encoded (execution.cancel).term) ∧
      (execution.cancel).history = execution.history ∧
      (execution.cancel).phase = .cancelled :=
  ⟨cancel_returns state execution, (Retained.cancel_is_local execution).1,
    (Retained.cancel_is_local execution).2.1⟩

private def appendCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "LCons" [v "commit", .symbol "LNil"]),
   (a "LCons" [v "head", v "tail"],
     a "let" [v "rest", a "rho:run:append-commit" [v "tail", v "commit"],
       a "LCons" [v "head", v "rest"]])]

private def appendBody : Atom :=
  a "case" [v "history", .expression (appendCases.map fun row => .expression [row.1, row.2])]

private def appendNilBody : Atom := a "LCons" [v "commit", .symbol "LNil"]

private def appendConsBody : Atom :=
  a "let" [v "rest", a "rho:run:append-commit" [v "tail", v "commit"], a "LCons" [v "head", v "rest"]]

private theorem append_shape : (equation .appendCommit).body = appendBody := by
  decide +kernel

private theorem append_nil_returns (caller : Subst) (state : State) (commit : Retained.Commit)
    (bound : (caller.lookup "commit").getD (v "commit") = encoded commit.term) :
    PureReturns runtime caller state appendNilBody state
      (encoded (encodeList Retained.Commit.term [commit])) := by
  have template : PureData.Template runtime appendNilBody := by runner_template
  have returned := PureData.template_return runtime caller state _ template
  simp only [appendNilBody, applySubst, applySubst.applySubstList] at returned
  rw [bound] at returned
  simpa [appendNilBody, CettaWireAtom.encode_list_cons, CettaWireAtom.encode_list_nil,
    CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned

/-- Appending one commit prints the chronological receipt history. The receipt
argument is the whole wire value, so its binding and query provenance stay. -/
theorem append_commit_returns (state : State) (history : List Retained.Commit)
    (commit : Retained.Commit) :
    PureReturns runtime [] state
      (a "rho:run:append-commit" [encoded (encodeList Retained.Commit.term history),
        encoded commit.term]) state
      (encoded (encodeList Retained.Commit.term (history ++ [commit]))) := by
  induction history with
  | nil =>
    let caller := bindings .appendCommit
      [encoded (encodeList Retained.Commit.term []), encoded commit.term]
    apply helper_call .appendCommit [] state _
      [encoded (encodeList Retained.Commit.term []), encoded commit.term] _ rfl (closed_arguments _)
    rw [append_shape]
    unfold appendBody
    apply branch_returns caller caller state _ (.symbol "LNil") appendCases appendNilBody _
    · exact variable_returns runtime caller state "history"
    · simp [appendCases, appendNilBody, caller, bindings, Helper.names, CettaWireAtom.encode_list_nil,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · apply append_nil_returns caller state commit
      simp [caller, bindings, Helper.names, Subst.lookup]
  | cons head tail ih =>
    let caller := bindings .appendCommit
      [encoded (encodeList Retained.Commit.term (head :: tail)), encoded commit.term]
    let selected := [("tail", encoded (encodeList Retained.Commit.term tail)),
      ("head", encoded head.term)] ++ caller
    let extended := encoded (encodeList Retained.Commit.term (tail ++ [commit]))
    apply helper_call .appendCommit [] state _
      [encoded (encodeList Retained.Commit.term (head :: tail)), encoded commit.term] _ rfl
      (closed_arguments _)
    rw [append_shape]
    unfold appendBody
    apply branch_returns caller selected state _
      (encoded (encodeList Retained.Commit.term (head :: tail))) appendCases appendConsBody _
    · exact variable_returns runtime caller state "history"
    · simp [appendCases, appendConsBody, selected, caller, bindings, Helper.names,
        CettaWireAtom.encode_list_cons, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · apply named_let_returns selected state "rest" _ extended (a "LCons" [v "head", v "rest"])
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture .appendCommit selected state [v "tail", v "commit"]
          [encoded (encodeList Retained.Commit.term tail), encoded commit.term] _ rfl
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih
      · have template : PureData.Template runtime (a "LCons" [v "head", v "rest"]) := by
          runner_template
        simpa [extended, selected, caller, bindings, Helper.names, applySubst,
          applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode_list_cons,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, List.cons_append] using
          PureData.template_return runtime (("rest", extended) :: selected) state _ template

private def beginExecuteCode : List Atom :=
  [v "environment", v "permissions", v "bound", v "expected", v "canonical", v "rules", number 0]

/-- The successor search starts at matcher budget zero. The budget is a literal,
not a captured variable, so the step's variable-budget bridge does not apply. -/
private theorem begin_execute_returns (caller : Subst) (state : State) (canonical : Pattern)
    (captured : beginExecuteCode.map (applySubst caller) =
      (GeneralProgramDriverExecution.executeArguments plan [] (.base "Proc") canonical 0).map encoded) :
    PureReturns runtime caller state (a "gslt:program:execute" beginExecuteCode) state
      (encoded (programOf canonical 0).term) := by
  have observed : PureReturns runtime caller state (a "gslt:program:execute" beginExecuteCode) state
      (encoded (GeneralProgramDriverExecution.programObservationTerm
        (invocations plan [] (.base "Proc") canonical fun _ => 0))) := by
    apply resumption_returns (by decide)
    apply GeneralProgramResumptionExecution.driver_returns (by decide)
    apply PureData.raw_capture_returns GeneralProgramDriverExecution.runtime [] caller state state
      "gslt:program:execute"
      ((GeneralProgramDriverExecution.executeArguments plan [] (.base "Proc") canonical 0).map encoded)
      beginExecuteCode _ (by decide +kernel) _ (by decide)
    · rw [closed_arguments, captured]
    · exact GeneralProgramDriverExecution.execute_returns state plan finiteProvider [] (.base "Proc") canonical 0
    · intro index bounded
      have checked : (List.range 7).all
          (fun index => argumentIsRaw GeneralProgramDriverExecution.runtime "gslt:program:execute" index) = true := by
        decide +kernel
      apply List.all_eq_true.mp checked index
      simp only [GeneralProgramDriverExecution.executeArguments, List.length_map, List.length_cons,
        List.length_nil] at bounded
      exact List.mem_range.mpr bounded
  rwa [← ProgramRun.ofInvocations_term] at observed

private def beginPairs : List (Atom × Atom) :=
  [(v "canonical", a "rho:lex:canonical" [v "process"]),
   (v "observation", a "gslt:program:execute" beginExecuteCode)]

private def beginResult : Atom :=
  a "RhoProcess" [.symbol "LNil", a "RhoLive" [a "RhoSearch" [v "canonical", v "observation"]]]

private def beginInner : Atom :=
  a "let*" [pairsAtom beginPairs, beginResult]

private def beginCases : SpaceSemantics.Cases :=
  [(a "RhoPlan" [v "environment", v "permissions", v "bound", v "expected", v "rules"], beginInner)]

private def beginBody : Atom :=
  a "case" [v "plan", .expression (beginCases.map fun row => .expression [row.1, row.2])]

private theorem begin_shape : (equation .begin).body = beginBody := by
  decide +kernel

/-- The authored begin operation returns `Retained.begin`: an empty receipt
history and a live search of the canonical process at matcher budget zero. -/
theorem begin_returns (state : State) {process : Pattern} (shaped : RhoShaped process) :
    PureReturns runtime [] state
      (a "rho:run:begin" [encoded planTerm, patternValue process]) state
      (encoded (Retained.begin process).term) := by
  have closed := rhoShaped_freeFvarNames (lexCanon_rhoShaped shaped)
  let caller := bindings .begin [encoded planTerm, patternValue process]
  let selected := planBindings ++ caller
  let canonical := lexCanon process
  let withCanonical := ("canonical", patternValue canonical) :: selected
  let program := programOf canonical 0
  let withObservation := ("observation", encoded program.term) :: withCanonical
  apply helper_call .begin [] state _ [encoded planTerm, patternValue process] _ rfl
    (closed_arguments _)
  rw [begin_shape]
  unfold beginBody
  apply branch_returns caller selected state _ (encoded planTerm) beginCases beginInner _
  · exact variable_returns runtime caller state "plan"
  · simp [beginCases, beginInner, selected, caller, planBindings, bindings, Helper.names, planTerm,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold beginInner
    apply let_star_bindings (final := withObservation)
    · apply bind_fresh
        (by simp [selected, caller, planBindings, bindings, Helper.names, Subst.lookup])
        (canonical_captured selected state shaped (by
          simp [selected, caller, planBindings, bindings, Helper.names, applySubst, Subst.lookup]))
      apply bind_fresh
        (by simp [withCanonical, selected, caller, planBindings, bindings, Helper.names, Subst.lookup])
        (begin_execute_returns withCanonical state canonical (by
          simp [beginExecuteCode, canonical, withCanonical, selected, caller, planBindings, bindings,
            Helper.names, applySubst, Subst.lookup, GeneralProgramDriverExecution.executeArguments,
            environmentTerm_closed closed]))
      exact .nil _ _
    · have template : PureData.Template runtime beginResult := by
        runner_template
      simpa [beginResult, withObservation, withCanonical, selected, caller, planBindings, bindings,
        Helper.names, canonical, program, Retained.begin, Retained.Execution.term, Retained.Phase.term,
        Search.term, Search.begin, applySubst, applySubst.applySubstList, Subst.lookup,
        CettaWireAtom.encode_list_nil, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime withObservation state _ template

/-- Beginning a process on the quoted runner is the empty-history live search. -/
theorem authored_begin_agrees (state : State) {process : Pattern} (shaped : RhoShaped process) :
    PureReturns runtime [] state
      (a "rho:run:begin" [encoded planTerm, patternValue process]) state
      (encoded (Retained.begin process).term) ∧
      (Retained.begin process).history = [] ∧
      (Retained.begin process).phase = .live (Search.begin process) :=
  ⟨begin_returns state shaped, rfl, rfl⟩

private def resumeProcessLiveBody : Atom :=
  a "let" [v "resumed", a "rho:run:resume-search" [v "search", v "extra"],
    a "RhoProcess" [v "history", a "RhoLive" [v "resumed"]]]

private def resumeProcessDoneBody : Atom :=
  a "RhoProcess" [v "history", a "RhoDone" [v "process"]]

private def resumeProcessCancelledBody : Atom :=
  a "RhoProcess" [v "history", .symbol "RhoCancelled"]

private def resumeProcessCases : SpaceSemantics.Cases :=
  [(a "RhoProcess" [v "history", a "RhoLive" [v "search"]], resumeProcessLiveBody),
   (a "RhoProcess" [v "history", a "RhoDone" [v "process"]], resumeProcessDoneBody),
   (a "RhoProcess" [v "history", .symbol "RhoCancelled"], resumeProcessCancelledBody)]

private def resumeProcessBody : Atom :=
  a "case" [v "execution",
    .expression (resumeProcessCases.map fun row => .expression [row.1, row.2])]

private theorem resume_process_shape : (equation .resumeProcess).body = resumeProcessBody := by
  decide +kernel

/-- The authored resume operation returns `Retained.Execution.resumeSearch`.
A live search continues its retained program; a finished phase is unchanged.
Matcher budget is this `extra`, not a committed COMM step. -/
theorem resume_process_returns (state : State) (execution : Retained.Execution) (extra : Nat)
    (finite : ∀ search, execution.phase = .live search →
      ∀ job ∈ search.program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ search, execution.phase = .live search → ∀ job ∈ search.program, job.Reachable) :
    PureReturns runtime [] state
      (a "rho:run:resume-process" [encoded execution.term, number extra]) state
      (encoded (execution.resumeSearch extra).term) := by
  let caller := bindings .resumeProcess [encoded execution.term, number extra]
  apply helper_call .resumeProcess [] state _ [encoded execution.term, number extra] _ rfl
    (closed_arguments _)
  rw [resume_process_shape]
  unfold resumeProcessBody
  cases execution with
  | mk history phase =>
    cases phase with
    | live search =>
      have jobs : ∀ job ∈ search.program, job.Reachable := reachable search rfl
      have finiteJobs := finite search rfl
      let selected := [("search", encoded search.term),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      let resumed := encoded (search.resume extra).term
      apply branch_returns caller selected state _
        (encoded (Retained.Execution.term ⟨history, .live search⟩)) resumeProcessCases
        resumeProcessLiveBody _
      · exact variable_returns runtime caller state "execution"
      · simp [resumeProcessCases, resumeProcessLiveBody, selected, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, Search.term, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply named_let_returns selected state "resumed" _ resumed
          (a "RhoProcess" [v "history", a "RhoLive" [v "resumed"]])
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .resumeSearch selected state [v "search", v "extra"]
            [encoded search.term, number extra] _ rfl
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (resume_search_returns state search finiteJobs jobs extra)
        · have template : PureData.Template runtime
              (a "RhoProcess" [v "history", a "RhoLive" [v "resumed"]]) := by
            runner_template
          simpa [resumed, selected, caller, bindings, Helper.names, Retained.Execution.term,
            Retained.Phase.term, Search.term, Search.resume, Retained.Execution.resumeSearch,
            applySubst,
            applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
            CettaWireAtom.encodeMany] using
            PureData.template_return runtime (("resumed", resumed) :: selected) state _ template
    | done process =>
      let selected := [("process", patternValue process),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller selected state _
        (encoded (Retained.Execution.term ⟨history, .done process⟩)) resumeProcessCases
        resumeProcessDoneBody _
      · exact variable_returns runtime caller state "execution"
      · simp [resumeProcessCases, resumeProcessDoneBody, selected, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, patternValue, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · have template : PureData.Template runtime resumeProcessDoneBody := by
          runner_template
        simpa [resumeProcessDoneBody, selected, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, patternValue, Retained.Execution.resumeSearch,
          applySubst,
          applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return runtime selected state _ template
    | cancelled =>
      let selected := [("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller selected state _
        (encoded (Retained.Execution.term ⟨history, .cancelled⟩)) resumeProcessCases
        resumeProcessCancelledBody _
      · exact variable_returns runtime caller state "execution"
      · simp [resumeProcessCases, resumeProcessCancelledBody, selected, caller, bindings,
          Helper.names, Retained.Execution.term, Retained.Phase.term, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · have template : PureData.Template runtime resumeProcessCancelledBody := by
          runner_template
        simpa [resumeProcessCancelledBody, selected, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, Retained.Execution.resumeSearch, applySubst,
          applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return runtime selected state _ template

/-- Resuming on the quoted runner keeps the committed history. A live phase
continues that search; finished phases do not start another one. -/
theorem authored_resume_process_agrees (state : State) (execution : Retained.Execution)
    (extra : Nat)
    (finite : ∀ search, execution.phase = .live search →
      ∀ job ∈ search.program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ search, execution.phase = .live search → ∀ job ∈ search.program, job.Reachable) :
    PureReturns runtime [] state
      (a "rho:run:resume-process" [encoded execution.term, number extra]) state
      (encoded (execution.resumeSearch extra).term) ∧
      (execution.resumeSearch extra).history = execution.history ∧
      ∀ search, execution.phase = .live search →
        (execution.resumeSearch extra).phase = .live (search.resume extra) :=
  ⟨resume_process_returns state execution extra finite reachable,
    Retained.resumeSearch_appends_nothing execution extra,
    fun search live => (Retained.resumeSearch_continues execution search extra live).2.1⟩

private def commitSuccessorCode : List Atom :=
  [v "environment", v "permissions", v "bound", v "expected", v "after", v "rules", number 0]

private theorem commit_successor_returns (caller : Subst) (state : State) (canonical : Pattern)
    (captured : commitSuccessorCode.map (applySubst caller) =
      (GeneralProgramDriverExecution.executeArguments plan [] (.base "Proc") canonical 0).map encoded) :
    PureReturns runtime caller state (a "gslt:program:execute" commitSuccessorCode) state
      (encoded (programOf canonical 0).term) := by
  have observed : PureReturns runtime caller state (a "gslt:program:execute" commitSuccessorCode) state
      (encoded (GeneralProgramDriverExecution.programObservationTerm
        (invocations plan [] (.base "Proc") canonical fun _ => 0))) := by
    apply resumption_returns (by decide)
    apply GeneralProgramResumptionExecution.driver_returns (by decide)
    apply PureData.raw_capture_returns GeneralProgramDriverExecution.runtime [] caller state state
      "gslt:program:execute"
      ((GeneralProgramDriverExecution.executeArguments plan [] (.base "Proc") canonical 0).map encoded)
      commitSuccessorCode _ (by decide +kernel) _ (by decide)
    · rw [closed_arguments, captured]
    · exact GeneralProgramDriverExecution.execute_returns state plan finiteProvider [] (.base "Proc") canonical 0
    · intro index bounded
      have checked : (List.range 7).all
          (fun index => argumentIsRaw GeneralProgramDriverExecution.runtime "gslt:program:execute" index) = true := by
        decide +kernel
      apply List.all_eq_true.mp checked index
      simp only [GeneralProgramDriverExecution.executeArguments, List.length_map, List.length_cons,
        List.length_nil] at bounded
      exact List.mem_range.mpr bounded
  rwa [← ProgramRun.ofInvocations_term] at observed

private theorem canonical_target_returns (caller : Subst) (state : State) {target : Pattern}
    (shaped : RhoShaped target)
    (captured : applySubst caller (v "target") = patternValue target) :
    PureReturns runtime caller state (a "rho:lex:canonical" [v "target"]) state
      (patternValue (lexCanon target)) := by
  apply lex_returns (by decide)
  apply PureData.raw_capture_returns RhoLexCanonicalExecution.runtime [] caller state state
    "rho:lex:canonical" [patternValue target] [v "target"] _ (by decide +kernel) _ (by decide)
  · simp [captured]
  · exact RhoLexCanonicalExecution.canonical_returns state target shaped
  · intro index bounded
    have zero : index = 0 := by simpa using bounded
    subst zero
    decide +kernel

private def commitReceiptPattern : Atom :=
  a "RuleJobReceipt" [v "job", v "trace", v "captured", v "completed", v "events", v "local", v "target"]

private def commitStepPairs : List (Atom × Atom) :=
  [(v "after", a "rho:lex:canonical" [v "target"]),
   (v "successor", a "gslt:program:execute" commitSuccessorCode),
   (v "committed", a "rho:run:append-commit" [v "history",
     a "RhoCommit" [v "process", v "receipt", v "after"]])]

private def commitStepResult : Atom :=
  a "RhoProcess" [v "committed", a "RhoLive" [a "RhoSearch" [v "after", v "successor"]]]

private def commitReceiptBody : Atom :=
  a "let*" [pairsAtom commitStepPairs, commitStepResult]

private def commitReceiptCases : SpaceSemantics.Cases :=
  [(commitReceiptPattern, commitReceiptBody)]

private def commitQuiescentBody : Atom :=
  a "RhoProcess" [v "history", a "RhoDone" [v "process"]]

private def commitConsBody : Atom :=
  a "rho:run:after-receipt" [v "plan", v "history", v "process", v "receipt"]

private def commitCatchBody : Atom :=
  a "RhoProcess" [v "history", a "RhoLive" [a "RhoSearch" [v "process", v "observation"]]]

private def commitPublicationCases : SpaceSemantics.Cases :=
  [(a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationComplete"], commitQuiescentBody),
   (a "ProgramPublication" [a "LCons" [v "receipt", v "others"], .symbol "ProgramPublicationComplete"],
     commitConsBody),
   (a "ProgramPublication" [v "released", v "status"], commitCatchBody)]

private def commitLiveBody : Atom :=
  a "let" [v "published", a "gslt:program:publication" [v "observation"],
    a "case" [v "published", .expression (commitPublicationCases.map fun row => .expression [row.1, row.2])]]

private def commitDoneBody : Atom := commitQuiescentBody

private def commitCancelledBody : Atom :=
  a "RhoProcess" [v "history", .symbol "RhoCancelled"]

private def commitExecutionCases : SpaceSemantics.Cases :=
  [(a "RhoProcess" [v "history", a "RhoLive" [a "RhoSearch" [v "process", v "observation"]]],
     commitLiveBody),
   (a "RhoProcess" [v "history", a "RhoDone" [v "process"]], commitDoneBody),
   (a "RhoProcess" [v "history", .symbol "RhoCancelled"], commitCancelledBody)]

private def commitPlanBody : Atom :=
  a "case" [v "execution", .expression (commitExecutionCases.map fun row => .expression [row.1, row.2])]

private def commitCases : SpaceSemantics.Cases :=
  [(a "RhoPlan" [v "environment", v "permissions", v "bound", v "expected", v "rules"], commitPlanBody)]

private def commitBody : Atom :=
  a "case" [v "plan", .expression (commitCases.map fun row => .expression [row.1, row.2])]

private theorem commit_shape : (equation .commit).body = commitBody := by
  decide +kernel

private theorem commit_kept_live (caller : Subst) (state : State) (history : List Retained.Commit)
    (process : Pattern) (program : ProgramRun)
    (historyBound : (Subst.lookup caller "history").getD (v "history") =
      encoded (encodeList Retained.Commit.term history))
    (processBound : (Subst.lookup caller "process").getD (v "process") = patternValue process)
    (observationBound : (Subst.lookup caller "observation").getD (v "observation") =
      encoded program.term) :
    PureReturns runtime caller state commitCatchBody state
      (encoded (Retained.Execution.term ⟨history, .live ⟨process, program⟩⟩)) := by
  have template : PureData.Template runtime commitCatchBody := by
    runner_template
  have returned := PureData.template_return runtime caller state _ template
  simp only [commitCatchBody, applySubst, applySubst.applySubstList] at returned
  rw [historyBound, processBound, observationBound] at returned
  simpa [commitCatchBody, Retained.Execution.term, Retained.Phase.term, Search.term,
    CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned

private theorem commit_kept_done (caller : Subst) (state : State) (history : List Retained.Commit)
    (process : Pattern)
    (historyBound : (Subst.lookup caller "history").getD (v "history") =
      encoded (encodeList Retained.Commit.term history))
    (processBound : (Subst.lookup caller "process").getD (v "process") = patternValue process) :
    PureReturns runtime caller state commitQuiescentBody state
      (encoded (Retained.Execution.term ⟨history, .done process⟩)) := by
  have template : PureData.Template runtime commitQuiescentBody := by
    runner_template
  have returned := PureData.template_return runtime caller state _ template
  simp only [commitQuiescentBody, applySubst, applySubst.applySubstList] at returned
  rw [historyBound, processBound] at returned
  simpa [commitQuiescentBody, Retained.Execution.term, Retained.Phase.term, patternValue,
    CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned

private def afterReceiptCases : SpaceSemantics.Cases :=
  [(a "RhoPlan" [v "environment", v "permissions", v "bound", v "expected", v "rules"],
    a "case" [v "receipt", .expression (commitReceiptCases.map fun row => .expression [row.1, row.2])])]

private def afterReceiptBody : Atom :=
  a "case" [v "plan", .expression (afterReceiptCases.map fun row => .expression [row.1, row.2])]

private theorem after_receipt_shape : (equation .afterReceipt).body = afterReceiptBody := by
  decide +kernel

/-- Constructing a successor keeps the full supplied receipt. Admission is
proved separately by the publication and dependency checks. -/
theorem after_receipt_returns (state : State) (history : List Retained.Commit)
    (process : Pattern) (receipt : GeneralRuleJobs.Receipt) (shaped : RhoShaped receipt.target) :
    PureReturns runtime [] state
      (a "rho:run:after-receipt" [encoded planTerm,
        encoded (encodeList Retained.Commit.term history), patternValue process,
        encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt)]) state
      (encoded (Retained.Execution.term
        ⟨history ++ [⟨process, receipt, lexCanon receipt.target⟩],
          .live (Search.begin (lexCanon receipt.target))⟩)) := by
  let caller := bindings .afterReceipt [encoded planTerm,
    encoded (encodeList Retained.Commit.term history), patternValue process,
    encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt)]
  let selected := planBindings ++ caller
  apply helper_call .afterReceipt [] state _ _ _ rfl (closed_arguments _)
  rw [after_receipt_shape]
  unfold afterReceiptBody
  apply branch_returns caller selected state _ (encoded planTerm) afterReceiptCases
    (a "case" [v "receipt", .expression (commitReceiptCases.map fun row => .expression [row.1, row.2])]) _
  · exact variable_returns runtime caller state "plan"
  · simp [afterReceiptCases, selected, caller, planBindings, bindings, Helper.names, planTerm,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · have receiptShape : ∃ job trace captured completed events localTarget : Term,
        ScopedRuleJobReadoutExecution.receiptTerm receipt =
          .application "RuleJobReceipt" [job, trace, captured, completed, events,
            localTarget, InferenceCettaWire.encodePattern receipt.target] := ⟨_, _, _, _, _, _, rfl⟩
    obtain ⟨job, trace, captured, completed, events, localTarget, receiptShape⟩ := receiptShape
    let fieldCaller := [("target", patternValue receipt.target),
      ("local", encoded localTarget), ("events", encoded events),
      ("completed", encoded completed), ("captured", encoded captured),
      ("trace", encoded trace), ("job", encoded job)] ++ selected
    apply branch_returns selected fieldCaller state _
      (encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt)) commitReceiptCases
      commitReceiptBody _
    · exact variable_returns runtime selected state "receipt"
    · simp [commitReceiptCases, commitReceiptBody, commitReceiptPattern, fieldCaller,
        selected, caller, planBindings, bindings, Helper.names, receiptShape,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold commitReceiptBody
      let after := lexCanon receipt.target
      let successorProgram := programOf after 0
      let record : Retained.Commit := ⟨process, receipt, after⟩
      let appended := encoded (encodeList Retained.Commit.term (history ++ [record]))
      let withAfter := ("after", patternValue after) :: fieldCaller
      let withSuccessor := ("successor", encoded successorProgram.term) :: withAfter
      let withCommitted := ("committed", appended) :: withSuccessor
      apply let_star_bindings (final := withCommitted)
      · apply bind_fresh
          (by simp [fieldCaller, selected, caller,
            planBindings, bindings, Helper.names, Subst.lookup])
          (canonical_target_returns fieldCaller state shaped
            (by simp [fieldCaller, selected, applySubst, Subst.lookup]))
        apply bind_fresh
          (by simp [withAfter, fieldCaller, selected,
            caller, planBindings, bindings, Helper.names, Subst.lookup])
          (commit_successor_returns withAfter state after
            (by simp [commitSuccessorCode, after, withAfter, fieldCaller, selected,
              caller, planBindings, bindings,
              Helper.names, applySubst, Subst.lookup,
              GeneralProgramDriverExecution.executeArguments,
              environmentTerm_closed (rhoShaped_freeFvarNames
                (lexCanon_rhoShaped shaped))]))
        apply bind_fresh
          (by simp [withSuccessor, withAfter, fieldCaller, selected,
            caller, planBindings, bindings, Helper.names, Subst.lookup])
          (helper_capture .appendCommit withSuccessor state
            [v "history", a "RhoCommit" [v "process", v "receipt", v "after"]]
            [encoded (encodeList Retained.Commit.term history), encoded record.term] _
            rfl
            (by simp [record, withSuccessor, withAfter, fieldCaller, selected,
              caller, planBindings, bindings,
              Helper.names, Retained.Commit.term, patternValue, applySubst,
              applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
              CettaWireAtom.encodeMany])
            (append_commit_returns state history record))
        exact .nil _ _
      · have idem : lexCanon (lexCanon receipt.target) = lexCanon receipt.target :=
          lexCanon_idempotent receipt.target
        have begun : Search.begin (lexCanon receipt.target) =
            ⟨lexCanon receipt.target, programOf (lexCanon receipt.target) 0⟩ := by
          simp [Search.begin, idem]
        have template : PureData.Template runtime commitStepResult := by
          runner_template
        simpa [commitStepResult, withCommitted, withSuccessor, withAfter, appended, record,
          after, successorProgram, begun,
          Retained.Execution.term, Retained.Phase.term, Search.term, applySubst,
          applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
          CettaWireAtom.encodeMany] using
          PureData.template_return runtime withCommitted state _ template

/-- The authored commit operation returns `Retained.Execution.commit`. A completed
selected receipt is appended and the successor search starts at matcher budget
zero. Any other phase returns the same execution. The selected target is
`RhoShaped` only on that committing branch. -/
theorem commit_returns (state : State) (execution : Retained.Execution)
    (targetShaped : ∀ search receipt rest, execution.phase = .live search →
      search.program.publication = receipt :: rest → search.program.status = .complete →
      RhoShaped receipt.target) :
    PureReturns runtime [] state
      (a "rho:run:commit" [encoded planTerm, encoded execution.term]) state
      (encoded execution.commit.term) := by
  let caller := bindings .commit [encoded planTerm, encoded execution.term]
  let selected := planBindings ++ caller
  apply helper_call .commit [] state _ [encoded planTerm, encoded execution.term] _ rfl
    (closed_arguments _)
  rw [commit_shape]
  unfold commitBody
  apply branch_returns caller selected state _ (encoded planTerm) commitCases commitPlanBody _
  · exact variable_returns runtime caller state "plan"
  · simp [commitCases, commitPlanBody, selected, caller, planBindings, bindings, Helper.names, planTerm,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold commitPlanBody
    cases execution with
    | mk history phase =>
      cases phase with
      | live search =>
        let observed := [("observation", encoded search.program.term),
          ("process", patternValue search.process),
          ("history", encoded (encodeList Retained.Commit.term history))] ++ selected
        apply branch_returns selected observed state _
          (encoded (Retained.Execution.term ⟨history, .live search⟩)) commitExecutionCases
          commitLiveBody _
        · exact variable_returns runtime selected state "execution"
        · simp [commitExecutionCases, commitLiveBody, observed, selected, caller, planBindings, bindings,
            Helper.names, Retained.Execution.term, Retained.Phase.term, Search.term, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · let publishedCaller := ("published", encoded search.program.publicationTerm) :: observed
          apply named_let_returns observed state "published" _
            (encoded search.program.publicationTerm)
            (a "case" [v "published",
              .expression (commitPublicationCases.map fun row => .expression [row.1, row.2])])
          · simp [observed, selected, caller, planBindings, bindings, Helper.names, Subst.lookup]
          · exact publication_captured observed state search.program
              (by simp [observed, selected, caller, planBindings, bindings, Helper.names, applySubst,
                Subst.lookup])
          · cases published : search.program.publication with
            | nil =>
              cases status : search.program.status with
              | complete =>
                apply branch_returns publishedCaller publishedCaller state _
                  (encoded search.program.publicationTerm) commitPublicationCases commitQuiescentBody _
                · simpa [publishedCaller, applySubst, Subst.lookup] using
                    variable_returns runtime publishedCaller state "published"
                · simp [commitPublicationCases, commitQuiescentBody, publishedCaller, observed, selected,
                    caller, planBindings, bindings, Helper.names, ProgramRun.publicationTerm, published,
                    status, ProgramRun.statusTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom]
                · have same : Retained.Execution.commit ⟨history, .live search⟩ =
                      ⟨history, .done search.process⟩ := by
                    simp [Retained.Execution.commit, published, status]
                  simpa [same] using commit_kept_done publishedCaller state history search.process
                    (by simp [publishedCaller, observed, Subst.lookup])
                    (by simp [publishedCaller, observed, Subst.lookup])
              | blocked | pending =>
                let caught := [("status", encoded (ProgramRun.statusTerm search.program.status)),
                  ("released", .symbol "LNil")] ++ publishedCaller
                apply branch_returns publishedCaller caught state _
                  (encoded search.program.publicationTerm) commitPublicationCases commitCatchBody _
                · simpa [publishedCaller, applySubst, Subst.lookup] using
                    variable_returns runtime publishedCaller state "published"
                · simp [commitPublicationCases, commitCatchBody, caught, publishedCaller, observed,
                    selected, caller, planBindings, bindings, Helper.names, ProgramRun.publicationTerm,
                    published, status, ProgramRun.statusTerm, encodeList, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
                · have same : Retained.Execution.commit ⟨history, .live search⟩ =
                      ⟨history, .live search⟩ := by
                    simp [Retained.Execution.commit, published, status]
                  simpa [same] using commit_kept_live caught state history search.process search.program
                    (by simp [caught, publishedCaller, observed, Subst.lookup])
                    (by simp [caught, publishedCaller, observed, Subst.lookup])
                    (by simp [caught, publishedCaller, observed, Subst.lookup])
            | cons receipt rest =>
              cases status : search.program.status with
              | blocked | pending =>
                let caught := [("status", encoded (ProgramRun.statusTerm search.program.status)),
                  ("released", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
                    (receipt :: rest)))] ++ publishedCaller
                apply branch_returns publishedCaller caught state _
                  (encoded search.program.publicationTerm) commitPublicationCases commitCatchBody _
                · simpa [publishedCaller, applySubst, Subst.lookup] using
                    variable_returns runtime publishedCaller state "published"
                · simp [commitPublicationCases, commitCatchBody, caught, publishedCaller, observed,
                    selected, caller, planBindings, bindings, Helper.names, ProgramRun.publicationTerm,
                    published, status, ProgramRun.statusTerm, encodeList, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
                · have same : Retained.Execution.commit ⟨history, .live search⟩ =
                      ⟨history, .live search⟩ := by
                    simp [Retained.Execution.commit, published, status]
                  simpa [same] using commit_kept_live caught state history search.process search.program
                    (by simp [caught, publishedCaller, observed, Subst.lookup])
                    (by simp [caught, publishedCaller, observed, Subst.lookup])
                    (by simp [caught, publishedCaller, observed, Subst.lookup])
              | complete =>
                have shaped : RhoShaped receipt.target :=
                  targetShaped search receipt rest rfl published status
                let receiptCaller := [("others", encoded (encodeList
                    ScopedRuleJobReadoutExecution.receiptTerm rest)),
                  ("receipt", encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt))] ++
                  publishedCaller
                apply branch_returns publishedCaller receiptCaller state _
                  (encoded search.program.publicationTerm) commitPublicationCases commitConsBody _
                · simpa [publishedCaller, applySubst, Subst.lookup] using
                    variable_returns runtime publishedCaller state "published"
                · simp [commitPublicationCases, commitConsBody, receiptCaller, publishedCaller, observed,
                    selected, caller, planBindings, bindings, Helper.names, ProgramRun.publicationTerm,
                    published, status, ProgramRun.statusTerm, encodeList, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
                · have same : Retained.Execution.commit ⟨history, .live search⟩ =
                      ⟨history ++ [⟨search.process, receipt, lexCanon receipt.target⟩],
                        .live (Search.begin (lexCanon receipt.target))⟩ := by
                    simp [Retained.Execution.commit, published, status]
                  rw [same]
                  unfold commitConsBody
                  exact helper_capture .afterReceipt receiptCaller state
                    [v "plan", v "history", v "process", v "receipt"]
                    [encoded planTerm, encoded (encodeList Retained.Commit.term history),
                      patternValue search.process, encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt)]
                    _ rfl
                    (by simp [receiptCaller, publishedCaller, observed, selected, caller, planBindings,
                      bindings, Helper.names, applySubst, Subst.lookup])
                    (after_receipt_returns state history search.process receipt shaped)
      | done process =>
        let finished := [("process", patternValue process),
          ("history", encoded (encodeList Retained.Commit.term history))] ++ selected
        apply branch_returns selected finished state _
          (encoded (Retained.Execution.term ⟨history, .done process⟩)) commitExecutionCases
          commitDoneBody _
        · exact variable_returns runtime selected state "execution"
        · simp [commitExecutionCases, commitDoneBody, finished, selected, caller, planBindings, bindings,
            Helper.names, Retained.Execution.term, Retained.Phase.term, patternValue, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · have same : Retained.Execution.commit ⟨history, .done process⟩ =
              ⟨history, .done process⟩ := by
            simp [Retained.Execution.commit]
          simpa [commitDoneBody, same] using commit_kept_done finished state history process
            (by simp [finished, Subst.lookup]) (by simp [finished, Subst.lookup])
      | cancelled =>
        let finished := [("history", encoded (encodeList Retained.Commit.term history))] ++ selected
        apply branch_returns selected finished state _
          (encoded (Retained.Execution.term ⟨history, .cancelled⟩)) commitExecutionCases
          commitCancelledBody _
        · exact variable_returns runtime selected state "execution"
        · simp [commitExecutionCases, commitCancelledBody, finished, selected, caller, planBindings,
            bindings, Helper.names, Retained.Execution.term, Retained.Phase.term, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · have template : PureData.Template runtime commitCancelledBody := by
            runner_template
          have same : Retained.Execution.commit ⟨history, .cancelled⟩ =
              ⟨history, .cancelled⟩ := by
            simp [Retained.Execution.commit]
          simpa [commitCancelledBody, same, finished, selected, caller, planBindings, bindings,
            Helper.names, Retained.Execution.term, Retained.Phase.term, applySubst,
            applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return runtime finished state _ template

/-- Commit on the quoted runner is the model commit. Earlier receipts stay a
prefix of the later history, and a finished phase does not commit again. -/
theorem authored_commit_agrees (state : State) (execution : Retained.Execution)
    (targetShaped : ∀ search receipt rest, execution.phase = .live search →
      search.program.publication = receipt :: rest → search.program.status = .complete →
      RhoShaped receipt.target) :
    PureReturns runtime [] state
      (a "rho:run:commit" [encoded planTerm, encoded execution.term]) state
      (encoded execution.commit.term) ∧
      execution.history <+: execution.commit.history ∧
      (∀ process, execution.phase = .done process → execution.commit = execution) ∧
      (execution.phase = .cancelled → execution.commit = execution) :=
  ⟨commit_returns state execution targetShaped,
    Retained.commit_history_prefix execution,
    fun process done => Retained.commit_done execution process done,
    fun cancelled => Retained.commit_cancelled execution cancelled⟩

/-- Fuel zero needs no shape. Each later step needs `RhoShaped` on the selected
receipt's target only when that step's publication is a completed cons, and the
successor carries the same obligation for the remaining fuel. -/
def advanceShaped : Nat → Retained.Execution → Prop
  | 0, _ => True
  | fuel + 1, execution =>
      (∀ search receipt rest, execution.phase = .live search →
        search.program.publication = receipt :: rest →
        search.program.status = .complete →
        RhoShaped receipt.target) ∧
      advanceShaped fuel execution.commit

private def advanceCaller (execution : Retained.Execution) (fuel : Nat) : Subst :=
  bindings .advance [encoded planTerm, encoded execution.term, number fuel]

private def advancePairs : List (Atom × Atom) :=
  [(v "stepped", a "rho:run:commit" [v "plan", v "execution"]),
   (v "remaining", a "-" [v "fuel", number 1])]

private def advanceBody : Atom :=
  a "if" [a "==" [v "fuel", number 0],
    v "execution",
    a "let*" [pairsAtom advancePairs,
      a "rho:run:advance" [v "plan", v "stepped", v "remaining"]]]

private theorem advance_shape : (equation .advance).body = advanceBody := by
  decide +kernel

/-- Quoted `rho:run:advance` returns `Retained.Execution.advance`. Zero fuel
returns the execution. Each later fuel evaluates one commit and continues on
that successor. -/
theorem advance_returns (state : State) (fuel : Nat) :
    ∀ (execution : Retained.Execution), advanceShaped fuel execution →
      PureReturns runtime [] state
        (a "rho:run:advance" [encoded planTerm, encoded execution.term, number fuel]) state
        (encoded (Retained.Execution.advance fuel execution).term) := by
  induction fuel with
  | zero =>
    intro execution _
    let caller := advanceCaller execution 0
    apply helper_call .advance [] state _
      [encoded planTerm, encoded execution.term, number 0] _ rfl (closed_arguments _)
    rw [advance_shape]
    unfold advanceBody
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
      runtime caller state _ true
    · simpa using fuel_test_returns caller state 0
        (by simp [caller, advanceCaller, bindings, Helper.names, applySubst, Subst.lookup])
    · simp only [↓reduceIte]
      simpa [caller, advanceCaller, bindings, Helper.names, applySubst, Subst.lookup,
        Retained.Execution.advance] using
        variable_returns runtime caller state "execution"
  | succ fuel ih =>
    intro execution shaped
    let caller := advanceCaller execution (fuel + 1)
    apply helper_call .advance [] state _
      [encoded planTerm, encoded execution.term, number (fuel + 1)] _ rfl (closed_arguments _)
    rw [advance_shape]
    unfold advanceBody
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
      runtime caller state _ false
    · simpa using fuel_test_returns caller state (fuel + 1)
        (by simp [caller, advanceCaller, bindings, Helper.names, applySubst, Subst.lookup])
    · simp only [Bool.false_eq_true, ↓reduceIte, Retained.Execution.advance]
      let steppedValue := encoded execution.commit.term
      let withStepped := ("stepped", steppedValue) :: caller
      let withRemaining := ("remaining", number fuel) :: withStepped
      apply let_star_bindings (final := withRemaining)
      · apply bind_fresh
          (by simp [caller, advanceCaller, bindings, Helper.names, Subst.lookup])
          (helper_capture .commit caller state [v "plan", v "execution"]
            [encoded planTerm, encoded execution.term] steppedValue rfl
            (by simp [caller, advanceCaller, bindings, Helper.names, applySubst, Subst.lookup])
            (commit_returns state execution shaped.1))
        apply bind_fresh
          (by simp [withStepped, caller, advanceCaller, bindings, Helper.names, Subst.lookup])
          (predecessor_returns withStepped state fuel
            (by simp [withStepped, caller, advanceCaller, bindings, Helper.names, applySubst,
              Subst.lookup]))
        exact .nil _ _
      · exact helper_capture .advance withRemaining state
          [v "plan", v "stepped", v "remaining"]
          [encoded planTerm, steppedValue, number fuel]
          (encoded (Retained.Execution.advance fuel execution.commit).term) rfl
          (by simp [withRemaining, withStepped, steppedValue, caller, advanceCaller, bindings,
            Helper.names, applySubst, Subst.lookup])
          (ih execution.commit shaped.2)

/-- The quoted advance is the model advance, and that function is the one
already shown to split as `first + extra`. -/
theorem authored_advance_agrees (state : State) (fuel : Nat)
    (execution : Retained.Execution) (shaped : advanceShaped fuel execution) :
    PureReturns runtime [] state
      (a "rho:run:advance" [encoded planTerm, encoded execution.term, number fuel]) state
      (encoded (Retained.Execution.advance fuel execution).term) ∧
      ∀ first extra, Retained.Execution.advance (first + extra) execution =
        Retained.Execution.advance extra (Retained.Execution.advance first execution) :=
  ⟨advance_returns state fuel execution shaped,
    fun first extra => Retained.advance_add first extra execution⟩

private def candidateIfBody : Atom :=
  a "if" [a "==" [v "candidate", v "receipt"],
    a "rho:run:commit" [v "plan", v "execution"],
    v "execution"]

private def candidatePublicationCases : SpaceSemantics.Cases :=
  [(a "ProgramPublication" [a "LCons" [v "receipt", v "others"], .symbol "ProgramPublicationComplete"],
     candidateIfBody),
   (a "ProgramPublication" [v "released", v "status"], v "execution")]

private def candidateLiveBody : Atom :=
  a "let" [v "published", a "gslt:program:publication" [v "observation"],
    a "case" [v "published",
      .expression (candidatePublicationCases.map fun row => .expression [row.1, row.2])]]

private def candidateExecutionCases : SpaceSemantics.Cases :=
  [(a "RhoProcess" [v "history", a "RhoLive" [a "RhoSearch" [v "process", v "observation"]]],
     candidateLiveBody),
   (a "RhoProcess" [v "history", a "RhoDone" [v "process"]], v "execution"),
   (a "RhoProcess" [v "history", .symbol "RhoCancelled"], v "execution")]

private def candidateBody : Atom :=
  a "case" [v "execution",
    .expression (candidateExecutionCases.map fun row => .expression [row.1, row.2])]

private theorem candidate_shape : (equation .commitCandidate).body = candidateBody := by
  decide +kernel

/-- Quoted `rho:run:commit-candidate` returns `Retained.Execution.commitCandidate`.
The comparison is `receiptWireEq` on the whole receipt wire. A completed selected
receipt whose wire matches commits; every other phase returns the same execution.
`RhoShaped` is required only on the accepting branch. -/
theorem commit_candidate_returns (state : State) (execution : Retained.Execution)
    (candidate : GeneralRuleJobs.Receipt)
    (targetShaped : ∀ search receipt rest, execution.phase = .live search →
      search.program.publication = receipt :: rest → search.program.status = .complete →
      Retained.receiptWireEq candidate receipt = true →
      RhoShaped receipt.target) :
    PureReturns runtime [] state
      (a "rho:run:commit-candidate" [encoded planTerm, encoded execution.term,
        encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)]) state
      (encoded (execution.commitCandidate candidate).term) := by
  let caller := bindings .commitCandidate [encoded planTerm, encoded execution.term,
    encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)]
  apply helper_call .commitCandidate [] state _
    [encoded planTerm, encoded execution.term,
      encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)] _ rfl
    (closed_arguments _)
  rw [candidate_shape]
  unfold candidateBody
  cases execution with
  | mk history phase =>
    cases phase with
    | live search =>
      let observed := [("observation", encoded search.program.term),
        ("process", patternValue search.process),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller observed state _
        (encoded (Retained.Execution.term ⟨history, .live search⟩)) candidateExecutionCases
        candidateLiveBody _
      · exact variable_returns runtime caller state "execution"
      · simp [candidateExecutionCases, candidateLiveBody, observed, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, Search.term, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · let publishedCaller := ("published", encoded search.program.publicationTerm) :: observed
        apply named_let_returns observed state "published" _
          (encoded search.program.publicationTerm)
          (a "case" [v "published",
            .expression (candidatePublicationCases.map fun row => .expression [row.1, row.2])])
        · simp [observed, caller, bindings, Helper.names, Subst.lookup]
        · exact publication_captured observed state search.program
            (by simp [observed, caller, bindings, Helper.names, applySubst, Subst.lookup])
        · cases published : search.program.publication with
          | nil =>
            cases status : search.program.status
            all_goals (
              let caught := [("status", encoded (ProgramRun.statusTerm search.program.status)),
                ("released", .symbol "LNil")] ++ publishedCaller
              apply branch_returns publishedCaller caught state _
                (encoded search.program.publicationTerm) candidatePublicationCases (v "execution") _
              · simpa [publishedCaller, applySubst, Subst.lookup] using
                  variable_returns runtime publishedCaller state "published"
              · simp [candidatePublicationCases, caught, publishedCaller, observed, caller, bindings,
                  Helper.names, ProgramRun.publicationTerm, published, status, ProgramRun.statusTerm,
                  encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · have same : Retained.Execution.commitCandidate ⟨history, .live search⟩ candidate =
                    ⟨history, .live search⟩ := by
                  simp [Retained.Execution.commitCandidate, published, status]
                simpa [same, caught, publishedCaller, observed, caller, bindings, Helper.names,
                  applySubst, Subst.lookup, Retained.Execution.term] using
                  variable_returns runtime caught state "execution")
          | cons receipt rest =>
            cases status : search.program.status with
            | blocked =>
              let caught := [("status", encoded (ProgramRun.statusTerm search.program.status)),
                ("released", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
                  (receipt :: rest)))] ++ publishedCaller
              apply branch_returns publishedCaller caught state _
                (encoded search.program.publicationTerm) candidatePublicationCases (v "execution") _
              · simpa [publishedCaller, applySubst, Subst.lookup] using
                  variable_returns runtime publishedCaller state "published"
              · simp [candidatePublicationCases, caught, publishedCaller, observed, caller, bindings,
                  Helper.names, ProgramRun.publicationTerm, published, status, ProgramRun.statusTerm,
                  encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · have same : Retained.Execution.commitCandidate ⟨history, .live search⟩ candidate =
                    ⟨history, .live search⟩ := by
                  simp [Retained.Execution.commitCandidate, published, status]
                simpa [same, caught, publishedCaller, observed, caller, bindings, Helper.names,
                  applySubst, Subst.lookup, Retained.Execution.term] using
                  variable_returns runtime caught state "execution"
            | pending =>
              let caught := [("status", encoded (ProgramRun.statusTerm search.program.status)),
                ("released", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
                  (receipt :: rest)))] ++ publishedCaller
              apply branch_returns publishedCaller caught state _
                (encoded search.program.publicationTerm) candidatePublicationCases (v "execution") _
              · simpa [publishedCaller, applySubst, Subst.lookup] using
                  variable_returns runtime publishedCaller state "published"
              · simp [candidatePublicationCases, caught, publishedCaller, observed, caller, bindings,
                  Helper.names, ProgramRun.publicationTerm, published, status, ProgramRun.statusTerm,
                  encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · have same : Retained.Execution.commitCandidate ⟨history, .live search⟩ candidate =
                    ⟨history, .live search⟩ := by
                  simp [Retained.Execution.commitCandidate, published, status]
                simpa [same, caught, publishedCaller, observed, caller, bindings, Helper.names,
                  applySubst, Subst.lookup, Retained.Execution.term] using
                  variable_returns runtime caught state "execution"
            | complete =>
              let receiptCaller := [("others", encoded (encodeList
                  ScopedRuleJobReadoutExecution.receiptTerm rest)),
                ("receipt", encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt))] ++
                publishedCaller
              apply branch_returns publishedCaller receiptCaller state _
                (encoded search.program.publicationTerm) candidatePublicationCases candidateIfBody _
              · simpa [publishedCaller, applySubst, Subst.lookup] using
                  variable_returns runtime publishedCaller state "published"
              · simp [candidatePublicationCases, candidateIfBody, receiptCaller, publishedCaller, observed,
                  caller, bindings, Helper.names, ProgramRun.publicationTerm, published, status,
                  ProgramRun.statusTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · unfold candidateIfBody
                have tested := CettaWireAtom.equality_captured_returns runtime receiptCaller state
                  (ScopedRuleJobReadoutExecution.receiptTerm candidate)
                  (ScopedRuleJobReadoutExecution.receiptTerm receipt) "candidate" "receipt"
                  (by simp [receiptCaller, publishedCaller, observed, caller, bindings, Helper.names,
                    applySubst, Subst.lookup])
                  (by simp [receiptCaller, publishedCaller, observed, caller, bindings, Helper.names,
                    applySubst, Subst.lookup])
                cases flag : Retained.receiptWireEq candidate receipt with
                | true =>
                  apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
                    runtime receiptCaller state _ true
                  · have wire :
                        decide (ScopedRuleJobReadoutExecution.receiptTerm candidate =
                          ScopedRuleJobReadoutExecution.receiptTerm receipt) = true := by
                      rw [← Retained.receiptWireEq_eq_decide]
                      exact flag
                    simpa [wire] using tested
                  · simp only [↓reduceIte]
                    have commitShaped :
                        ∀ search' receipt' rest',
                          (⟨history, Retained.Phase.live search⟩ : Retained.Execution).phase =
                            .live search' →
                          search'.program.publication = receipt' :: rest' →
                          search'.program.status = .complete →
                          RhoShaped receipt'.target := by
                      intro search' receipt' rest' live published' _complete'
                      cases live
                      obtain ⟨rfl, rfl⟩ := List.cons.inj (published.symm.trans published')
                      exact targetShaped search receipt rest rfl published status flag
                    have same : Retained.Execution.commitCandidate ⟨history, .live search⟩ candidate =
                        Retained.Execution.commit ⟨history, .live search⟩ := by
                      simp [Retained.Execution.commitCandidate, published, status, flag]
                    simpa [Helper.head, same] using helper_capture .commit receiptCaller state
                      [v "plan", v "execution"]
                      [encoded planTerm, encoded (Retained.Execution.term ⟨history, .live search⟩)]
                      (encoded (Retained.Execution.commit ⟨history, .live search⟩).term) rfl
                      (by simp [receiptCaller, publishedCaller, observed, caller, bindings, Helper.names,
                        Retained.Execution.term, Retained.Phase.term, Search.term, applySubst,
                        Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany])
                      (commit_returns state ⟨history, .live search⟩ commitShaped)
                | false =>
                  apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
                    runtime receiptCaller state _ false
                  · have wire :
                        decide (ScopedRuleJobReadoutExecution.receiptTerm candidate =
                          ScopedRuleJobReadoutExecution.receiptTerm receipt) = false := by
                      rw [← Retained.receiptWireEq_eq_decide]
                      exact flag
                    simpa [wire] using tested
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    have same : Retained.Execution.commitCandidate ⟨history, .live search⟩ candidate =
                        ⟨history, .live search⟩ := by
                      simp [Retained.Execution.commitCandidate, published, status, flag]
                    simpa [same, receiptCaller, publishedCaller, observed, caller, bindings, Helper.names,
                      applySubst, Subst.lookup, Retained.Execution.term] using
                      variable_returns runtime receiptCaller state "execution"
    | done process =>
      let finished := [("process", patternValue process),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller finished state _
        (encoded (Retained.Execution.term ⟨history, .done process⟩)) candidateExecutionCases
        (v "execution") _
      · exact variable_returns runtime caller state "execution"
      · simp [candidateExecutionCases, finished, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, patternValue, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · have same : Retained.Execution.commitCandidate ⟨history, .done process⟩ candidate =
            ⟨history, .done process⟩ := by
          simp [Retained.Execution.commitCandidate]
        simpa [same, finished, caller, bindings, Helper.names, applySubst, Subst.lookup,
          Retained.Execution.term] using
          variable_returns runtime finished state "execution"
    | cancelled =>
      let finished := [("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller finished state _
        (encoded (Retained.Execution.term ⟨history, .cancelled⟩)) candidateExecutionCases
        (v "execution") _
      · exact variable_returns runtime caller state "execution"
      · simp [candidateExecutionCases, finished, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · have same : Retained.Execution.commitCandidate ⟨history, .cancelled⟩ candidate =
            ⟨history, .cancelled⟩ := by
          simp [Retained.Execution.commitCandidate]
        simpa [same, finished, caller, bindings, Helper.names, applySubst, Subst.lookup,
          Retained.Execution.term] using
          variable_returns runtime finished state "execution"

/-- The quoted candidate commit is the model `commitCandidate`. Wire equality of
the whole receipt accepts it; a wire mismatch on a completed publication leaves
the execution in place. Model refusal theorems are not this correspondence. -/
theorem authored_commit_candidate_agrees (state : State) (execution : Retained.Execution)
    (candidate : GeneralRuleJobs.Receipt)
    (targetShaped : ∀ search receipt rest, execution.phase = .live search →
      search.program.publication = receipt :: rest → search.program.status = .complete →
      Retained.receiptWireEq candidate receipt = true →
      RhoShaped receipt.target) :
    PureReturns runtime [] state
      (a "rho:run:commit-candidate" [encoded planTerm, encoded execution.term,
        encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)]) state
      (encoded (execution.commitCandidate candidate).term) ∧
      (∀ search receipt rest, execution.phase = .live search →
        search.program.publication = receipt :: rest →
        search.program.status = .complete →
        Retained.receiptWireEq candidate receipt = true →
        execution.commitCandidate candidate = execution.commit) ∧
      (∀ search receipt rest, execution.phase = .live search →
        search.program.publication = receipt :: rest →
        search.program.status = .complete →
        Retained.receiptWireEq candidate receipt = false →
        execution.commitCandidate candidate = execution) :=
  ⟨commit_candidate_returns state execution candidate targetShaped,
    fun search receipt rest live published complete accepted => by
      cases execution
      cases live
      simp [Retained.Execution.commitCandidate, published, complete, accepted],
    fun search receipt rest live published complete refused => by
      cases execution
      cases live
      simp [Retained.Execution.commitCandidate, published, complete, refused]⟩

private def containsConsBody : Atom :=
  a "if" [a "==" [v "candidate", v "receipt"], Effects.boolean true,
    a "rho:run:contains-receipt" [v "candidate", v "rest"]]
private def containsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean false),
    (a "LCons" [v "receipt", v "rest"], containsConsBody)]
private def containsBody : Atom :=
  a "case" [v "receipts", .expression (containsCases.map fun row => .expression [row.1, row.2])]
private theorem contains_shape : (equation Helper.containsReceipt).body = containsBody := by decide +kernel

/-- Whole-wire receipt membership does not identify equal target values. -/
theorem contains_receipt_returns (state : State) (candidate : GeneralRuleJobs.Receipt)
    (receipts : List GeneralRuleJobs.Receipt) :
    PureReturns runtime [] state
      (a "rho:run:contains-receipt" [encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate),
        encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts)]) state
      (Effects.boolean (receipts.any (Retained.receiptWireEq candidate))) := by
  induction receipts with
  | nil =>
    let caller := bindings Helper.containsReceipt [encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate),
      encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm [])]
    apply helper_call Helper.containsReceipt [] state _ _ _ rfl (closed_arguments _)
    rw [contains_shape]
    unfold containsBody
    apply branch_returns caller caller state _ (.symbol "LNil") containsCases (Effects.boolean false) _
    · exact variable_returns runtime caller state "receipts"
    · simp [containsCases, caller, bindings, Helper.names, CettaWireAtom.encode_list_nil,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · exact grounded_returns runtime caller state (.bool false)
  | cons receipt rest ih =>
    let caller := bindings Helper.containsReceipt [encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate),
      encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (receipt :: rest))]
    let selected := [("rest", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm rest)),
      ("receipt", encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt))] ++ caller
    apply helper_call Helper.containsReceipt [] state _ _ _ rfl (closed_arguments _)
    rw [contains_shape]
    unfold containsBody
    apply branch_returns caller selected state _
      (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (receipt :: rest)))
      containsCases containsConsBody _
    · exact variable_returns runtime caller state "receipts"
    · simp [containsCases, containsConsBody, selected, caller, bindings, Helper.names,
        CettaWireAtom.encode_list_cons, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold containsConsBody
      apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
        runtime selected state _ (Retained.receiptWireEq candidate receipt)
      · simpa only [Retained.receiptWireEq_eq_decide] using
          CettaWireAtom.equality_captured_returns runtime selected state
            (ScopedRuleJobReadoutExecution.receiptTerm candidate)
            (ScopedRuleJobReadoutExecution.receiptTerm receipt) "candidate" "receipt"
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
      · cases flag : Retained.receiptWireEq candidate receipt with
        | true => simpa [flag, Effects.boolean] using grounded_returns runtime selected state (.bool true)
        | false =>
          simpa [flag, Helper.head] using helper_capture Helper.containsReceipt selected state [v "candidate", v "rest"]
            [encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate),
             encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm rest)] _ rfl
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih

private def publishedIfBody : Atom :=
  a "if" [a "rho:run:contains-receipt" [v "candidate", v "receipts"],
    a "rho:run:after-receipt" [v "plan", v "history", v "process", v "candidate"], v "execution"]
private def publishedPublicationCases : SpaceSemantics.Cases :=
  [(a "ProgramPublication" [v "receipts", .symbol "ProgramPublicationComplete"], publishedIfBody),
   (a "ProgramPublication" [v "released", v "status"], v "execution")]
private def publishedLiveBody : Atom :=
  a "let" [v "published", a "gslt:program:publication" [v "observation"],
    a "case" [v "published", .expression (publishedPublicationCases.map fun row => .expression [row.1, row.2])]]
private def publishedExecutionCases : SpaceSemantics.Cases :=
  [(a "RhoProcess" [v "history", a "RhoLive" [a "RhoSearch" [v "process", v "observation"]]],
    publishedLiveBody),
   (a "RhoProcess" [v "history", a "RhoDone" [v "process"]], v "execution"),
   (a "RhoProcess" [v "history", .symbol "RhoCancelled"], v "execution")]
private def publishedBody : Atom :=
  a "case" [v "execution", .expression (publishedExecutionCases.map fun row => .expression [row.1, row.2])]
private theorem published_shape : (equation Helper.commitPublished).body = publishedBody := by decide +kernel

/-- The actual authored operation implements selected occurrence commitment.
Its admission boundary is the completed publication, not the target value. -/
theorem commit_published_returns (state : State) (execution : Retained.Execution)
    (candidate : GeneralRuleJobs.Receipt)
    (targetShaped : ∀ search, execution.phase = .live search →
      search.program.status = .complete → candidate ∈ search.program.publication →
      RhoShaped candidate.target) :
    PureReturns runtime [] state
      (a "rho:run:commit-published" [encoded planTerm, encoded execution.term,
        encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)]) state
      (encoded (execution.commitPublished candidate).term) := by
  let caller := bindings Helper.commitPublished [encoded planTerm, encoded execution.term,
    encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)]
  apply helper_call Helper.commitPublished [] state _ _ _ rfl (closed_arguments _)
  rw [published_shape]
  unfold publishedBody
  cases execution with
  | mk history phase =>
    cases phase with
    | live search =>
      let observed := [("observation", encoded search.program.term),
        ("process", patternValue search.process),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller observed state _
        (encoded (Retained.Execution.term ⟨history, .live search⟩)) publishedExecutionCases
        publishedLiveBody _
      · exact variable_returns runtime caller state "execution"
      · simp [publishedExecutionCases, publishedLiveBody, observed, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, Search.term, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · let pubCaller := ("published", encoded search.program.publicationTerm) :: observed
        apply named_let_returns observed state "published" _
          (encoded search.program.publicationTerm)
          (a "case" [v "published",
            .expression (publishedPublicationCases.map fun row => .expression [row.1, row.2])])
        · simp [observed, caller, bindings, Helper.names, Subst.lookup]
        · exact publication_captured observed state search.program
            (by simp [observed, caller, bindings, Helper.names, applySubst, Subst.lookup])
        · cases status : search.program.status with
          | blocked | pending =>
            let caught := [("status", encoded (ProgramRun.statusTerm search.program.status)),
              ("released", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
                search.program.publication))] ++ pubCaller
            apply branch_returns pubCaller caught state _ (encoded search.program.publicationTerm)
              publishedPublicationCases (v "execution") _
            · simpa [pubCaller, applySubst, Subst.lookup] using variable_returns runtime pubCaller state "published"
            · simp [publishedPublicationCases, caught, pubCaller, observed, caller, bindings,
                Helper.names, ProgramRun.publicationTerm, status, ProgramRun.statusTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · simpa [Retained.Execution.commitPublished, status, caught, pubCaller, observed, caller,
                bindings, Helper.names, applySubst, Subst.lookup] using
                variable_returns runtime caught state "execution"
          | complete =>
            let selected := ("receipts", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
                search.program.publication)) :: pubCaller
            apply branch_returns pubCaller selected state _ (encoded search.program.publicationTerm)
              publishedPublicationCases publishedIfBody _
            · simpa [pubCaller, applySubst, Subst.lookup] using variable_returns runtime pubCaller state "published"
            · simp [publishedPublicationCases, publishedIfBody, selected, pubCaller, observed, caller,
                bindings, Helper.names, ProgramRun.publicationTerm, status, ProgramRun.statusTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · unfold publishedIfBody
              apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
                runtime selected state _ (search.program.publication.any (Retained.receiptWireEq candidate))
              · exact helper_capture Helper.containsReceipt selected state [v "candidate", v "receipts"]
                  [encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate),
                    encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm search.program.publication)]
                  _ rfl (by simp [selected, pubCaller, observed, caller, bindings, Helper.names,
                    applySubst, Subst.lookup]) (contains_receipt_returns state candidate _)
              · cases flag : search.program.publication.any (Retained.receiptWireEq candidate) with
                | false =>
                  simpa [flag, Retained.Execution.commitPublished, status, selected, pubCaller,
                    observed, caller, bindings, Helper.names, applySubst, Subst.lookup] using
                    variable_returns runtime selected state "execution"
                | true =>
                  have shaped := targetShaped search rfl status
                    ((Retained.published_wire_member candidate _).mp flag)
                  simp only [flag, ↓reduceIte, Retained.Execution.commitPublished, status,
                    and_self, ↓reduceIte]
                  exact helper_capture Helper.afterReceipt selected state
                    [v "plan", v "history", v "process", v "candidate"]
                    [encoded planTerm, encoded (encodeList Retained.Commit.term history),
                      patternValue search.process, encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)]
                    _ rfl (by simp [selected, pubCaller, observed, caller, bindings, Helper.names,
                      applySubst, Subst.lookup]) (after_receipt_returns state history search.process candidate shaped)
    | done process =>
      let selected := [("process", patternValue process),
        ("history", encoded (encodeList Retained.Commit.term history))] ++ caller
      apply branch_returns caller selected state _
        (encoded (Retained.Execution.term ⟨history, .done process⟩)) publishedExecutionCases (v "execution") _
      · exact variable_returns runtime caller state "execution"
      · simp [publishedExecutionCases, selected, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · simpa [Retained.Execution.commitPublished, selected, caller, bindings, Helper.names,
          applySubst, Subst.lookup] using variable_returns runtime selected state "execution"
    | cancelled =>
      let selected := ("history", encoded (encodeList Retained.Commit.term history)) :: caller
      apply branch_returns caller selected state _
        (encoded (Retained.Execution.term ⟨history, .cancelled⟩)) publishedExecutionCases (v "execution") _
      · exact variable_returns runtime caller state "execution"
      · simp [publishedExecutionCases, selected, caller, bindings, Helper.names,
          Retained.Execution.term, Retained.Phase.term, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · simpa [Retained.Execution.commitPublished, selected, caller, bindings, Helper.names,
          applySubst, Subst.lookup] using variable_returns runtime selected state "execution"
/-- A sound retained state supplies the target-shape obligation itself.
The authored transition and the resulting chronological proof travel together. -/
theorem commit_published_sound_returns (state : State) {start : Pattern}
    (execution : Retained.Execution) (sound : Retained.Sound start execution)
    (candidate : GeneralRuleJobs.Receipt) :
    PureReturns runtime [] state
      (a "rho:run:commit-published" [encoded planTerm, encoded execution.term,
        encoded (ScopedRuleJobReadoutExecution.receiptTerm candidate)]) state
      (encoded (execution.commitPublished candidate).term) ∧
      Retained.Sound start (execution.commitPublished candidate) := by
  refine ⟨commit_published_returns state execution candidate ?_, sound.commitPublished candidate⟩
  intro search live _ member
  have phase := sound.phase
  rw [live] at phase
  cases phase with
  | live same valid =>
    obtain ⟨_, budget, program⟩ := valid
    rw [program] at member
    have actual := valid_of_mem_publication member
    have typed := sound.typed
    have sealed := sound.sealed
    rw [← same] at typed sealed
    have step := GeneralRho.DepthOne.receipt_step typed actual
    exact proc_rhoShaped
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.rhoStepAt_preserves_closed
        typed sealed step).1

section OccurrenceCells
open Mettapedia.Machines ValidatedCommit ReadOnlyQuery
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Retained
local instance : DecidableEq Bag := by unfold Bag; infer_instance

private def cellReadConsBody : Atom :=
  a "if" [a "==" [v "key", v "found"], v "value", a "rho:run:cell-read" [v "rest", v "key"]]
private def cellReadCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "RhoFresh"),
   (a "LCons" [a "RhoCell" [v "found", v "value"], v "rest"], cellReadConsBody)]
private def cellReadBody : Atom :=
  a "case" [v "cells", .expression (cellReadCases.map fun row => .expression [row.1, row.2])]
private theorem cell_read_shape : (equation Helper.cellRead).body = cellReadBody := by decide +kernel

/-- The actual wire lookup respects newest-first overrides and the fresh default. -/
theorem cell_read_returns (state : State) (store : CellStore) (key : Nat) :
    PureReturns runtime [] state
      (a "rho:run:cell-read" [encoded (CellStore.term store), number key]) state
      (encoded (CellStore.read store key).term) := by
  induction store with
  | nil =>
    let caller := bindings Helper.cellRead [encoded (CellStore.term []), number key]
    apply helper_call Helper.cellRead [] state _ _ _ rfl (closed_arguments _)
    rw [cell_read_shape]
    unfold cellReadBody
    apply branch_returns caller caller state _ (.symbol "LNil") cellReadCases (.symbol "RhoFresh") _
    · exact variable_returns runtime caller state "cells"
    · simp [cellReadCases, caller, bindings, Helper.names, CellStore.term,
        CettaWireAtom.encode_list_nil, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · exact symbol_returns runtime caller state "RhoFresh"
  | cons entry rest ih =>
    obtain ⟨found, value⟩ := entry
    let caller := bindings Helper.cellRead [encoded (CellStore.term ((found, value) :: rest)), number key]
    let selected := [("rest", encoded (CellStore.term rest)), ("value", encoded value.term),
      ("found", number found)] ++ caller
    apply helper_call Helper.cellRead [] state _ _ _ rfl (closed_arguments _)
    rw [cell_read_shape]
    unfold cellReadBody
    apply branch_returns caller selected state _ (encoded (CellStore.term ((found, value) :: rest)))
      cellReadCases cellReadConsBody _
    · exact variable_returns runtime caller state "cells"
    · simp [cellReadCases, cellReadConsBody, selected, caller, bindings, Helper.names,
        CellStore.term, CellStore.entryTerm, encodeList, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold cellReadConsBody
      apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
        runtime selected state _ (decide (key = found))
      · simpa only [Term.natural.injEq] using
          CettaWireAtom.equality_captured_returns runtime selected state (.natural key) (.natural found)
            "key" "found"
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
      · by_cases same : key = found
        · simpa [same, CellStore.read, selected, caller, bindings, Helper.names,
            applySubst, Subst.lookup] using variable_returns runtime selected state "value"
        · simpa [same, CellStore.read, Helper.head] using helper_capture Helper.cellRead selected state [v "rest", v "key"]
            [encoded (CellStore.term rest), number key] _ rfl
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih

private def validateIfBody : Atom :=
  a "if" [a "==" [v "current", v "expected"],
    a "rho:run:validate-reads" [v "cells", v "rest"], Effects.boolean false]
private def validateConsBody : Atom :=
  a "let" [v "current", a "rho:run:cell-read" [v "cells", v "key"], validateIfBody]
private def validateCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true),
   (a "LCons" [a "RhoCell" [v "key", v "expected"], v "rest"], validateConsBody)]
private def validateBody : Atom :=
  a "case" [v "reads", .expression (validateCases.map fun row => .expression [row.1, row.2])]
private theorem validate_shape : (equation Helper.validateReads).body = validateBody := by decide +kernel

/-- Every recorded dependency is compared against the actual current store. -/
theorem validate_reads_returns (state : State) (store : CellStore) (reads : Reads Nat Cell) :
    PureReturns runtime [] state
      (a "rho:run:validate-reads" [encoded (CellStore.term store), encoded (CellStore.term reads)]) state
      (Effects.boolean (checkReads (CellStore.read store) reads)) := by
  induction reads with
  | nil =>
    let caller := bindings Helper.validateReads [encoded (CellStore.term store), encoded (CellStore.term [])]
    apply helper_call Helper.validateReads [] state _ _ _ rfl (closed_arguments _)
    rw [validate_shape]
    unfold validateBody
    apply branch_returns caller caller state _ (.symbol "LNil") validateCases (Effects.boolean true) _
    · exact variable_returns runtime caller state "reads"
    · simp [validateCases, caller, bindings, Helper.names, CellStore.term,
        CettaWireAtom.encode_list_nil, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · exact grounded_returns runtime caller state (.bool true)
  | cons entry rest ih =>
    obtain ⟨key, expected⟩ := entry
    let caller := bindings Helper.validateReads [encoded (CellStore.term store),
      encoded (CellStore.term ((key, expected) :: rest))]
    let selected := [("rest", encoded (CellStore.term rest)), ("expected", encoded expected.term),
      ("key", number key)] ++ caller
    let current := CellStore.read store key
    let observed := ("current", encoded current.term) :: selected
    apply helper_call Helper.validateReads [] state _ _ _ rfl (closed_arguments _)
    rw [validate_shape]
    unfold validateBody
    apply branch_returns caller selected state _ (encoded (CellStore.term ((key, expected) :: rest)))
      validateCases validateConsBody _
    · exact variable_returns runtime caller state "reads"
    · simp [validateCases, validateConsBody, selected, caller, bindings, Helper.names,
        CellStore.term, CellStore.entryTerm, encodeList, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold validateConsBody
      apply named_let_returns selected state "current" _ (encoded current.term) validateIfBody
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture Helper.cellRead selected state [v "cells", v "key"]
          [encoded (CellStore.term store), number key] _ rfl
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
          (cell_read_returns state store key)
      · unfold validateIfBody
        apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
          runtime observed state _ (decide (current = expected))
        · simpa only [Cell.term_injective.eq_iff] using
            CettaWireAtom.equality_captured_returns runtime observed state current.term expected.term
              "current" "expected"
              (by simp [observed, applySubst, Subst.lookup])
              (by simp [observed, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
        · by_cases same : current = expected
          · simpa [same, checkReads, current, Helper.head] using helper_capture Helper.validateReads observed state
              [v "cells", v "rest"] [encoded (CellStore.term store), encoded (CellStore.term rest)]
              _ rfl (by simp [observed, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih
          · simpa [same, checkReads, current, Effects.boolean] using grounded_returns runtime observed state (.bool false)

private def applyWritesConsBody : Atom :=
  a "rho:run:apply-writes" [a "LCons" [a "RhoCell" [v "key", v "value"], v "cells"], v "rest"]
private def applyWritesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", v "cells"),
   (a "LCons" [a "RhoCell" [v "key", v "value"], v "rest"], applyWritesConsBody)]
private def applyWritesBody : Atom :=
  a "case" [v "writes", .expression (applyWritesCases.map fun row => .expression [row.1, row.2])]
private theorem apply_writes_shape : (equation Helper.applyWrites).body = applyWritesBody := by decide +kernel

/-- The authored finite-store update agrees with sequential functional updates. -/
theorem apply_writes_returns (state : State) (writes : Writes Nat Cell) : ∀ store : CellStore,
    PureReturns runtime [] state
      (a "rho:run:apply-writes" [encoded (CellStore.term store), encoded (CellStore.term writes)]) state
      (encoded (CellStore.term (CellStore.write store writes))) := by
  induction writes with
  | nil =>
    intro store
    let caller := bindings Helper.applyWrites [encoded (CellStore.term store), encoded (CellStore.term [])]
    apply helper_call Helper.applyWrites [] state _ _ _ rfl (closed_arguments _)
    rw [apply_writes_shape]
    unfold applyWritesBody
    apply branch_returns caller caller state _ (.symbol "LNil") applyWritesCases (v "cells") _
    · exact variable_returns runtime caller state "writes"
    · simp [applyWritesCases, caller, bindings, Helper.names, CellStore.term,
        CettaWireAtom.encode_list_nil, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · exact variable_returns runtime caller state "cells"
  | cons entry rest ih =>
    intro store
    obtain ⟨key, value⟩ := entry
    let caller := bindings Helper.applyWrites [encoded (CellStore.term store),
      encoded (CellStore.term ((key, value) :: rest))]
    let selected := [("rest", encoded (CellStore.term rest)), ("value", encoded value.term),
      ("key", number key)] ++ caller
    apply helper_call Helper.applyWrites [] state _ _ _ rfl (closed_arguments _)
    rw [apply_writes_shape]
    unfold applyWritesBody
    apply branch_returns caller selected state _ (encoded (CellStore.term ((key, value) :: rest)))
      applyWritesCases applyWritesConsBody _
    · exact variable_returns runtime caller state "writes"
    · simp [applyWritesCases, applyWritesConsBody, selected, caller, bindings, Helper.names,
        CellStore.term, CellStore.entryTerm, encodeList, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold applyWritesConsBody
      exact helper_capture Helper.applyWrites selected state _
        [encoded (CellStore.term ((key, value) :: store)), encoded (CellStore.term rest)] _ rfl
        (by simp [selected, caller, bindings, Helper.names, applySubst, applySubst.applySubstList,
          Subst.lookup, CellStore.term, CellStore.entryTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany]) (ih ((key, value) :: store))

private def commitCellsAcceptBody : Atom :=
  a "let" [v "next", a "rho:run:apply-writes" [v "cells", v "writes"], a "RhoCellsAccepted" [v "next"]]
private def commitCellsIfBody : Atom :=
  a "if" [a "rho:run:validate-reads" [v "cells", v "reads"], commitCellsAcceptBody,
    a "RhoCellsRefused" [v "cells"]]
private def commitCellsCases : SpaceSemantics.Cases :=
  [(a "RhoProposal" [v "reads", v "writes"], commitCellsIfBody)]
private def commitCellsBody : Atom :=
  a "case" [v "proposal", .expression (commitCellsCases.map fun row => .expression [row.1, row.2])]
private theorem commit_cells_shape : (equation Helper.commitCells).body = commitCellsBody := by decide +kernel

/-- Accepted and refused native data operations implement the validated
functional store, including every read and the allocation dependency. -/
theorem commit_cells_returns (state : State) (store : CellStore) (proposal : Proposal Nat Cell) :
    PureReturns runtime [] state
      (a "rho:run:commit-cells" [encoded (CellStore.term store), encoded (CellStore.proposalTerm proposal)]) state
      (encoded (CellStore.resultTerm store (CellStore.commit store proposal))) := by
  let caller := bindings Helper.commitCells [encoded (CellStore.term store), encoded (CellStore.proposalTerm proposal)]
  let selected := [("writes", encoded (CellStore.term proposal.writes)),
    ("reads", encoded (CellStore.term proposal.reads))] ++ caller
  apply helper_call Helper.commitCells [] state _ _ _ rfl (closed_arguments _)
  rw [commit_cells_shape]
  unfold commitCellsBody
  apply branch_returns caller selected state _ (encoded (CellStore.proposalTerm proposal))
    commitCellsCases commitCellsIfBody _
  · exact variable_returns runtime caller state "proposal"
  · simp [commitCellsCases, commitCellsIfBody, selected, caller, bindings, Helper.names,
      CellStore.proposalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup]
  · unfold commitCellsIfBody
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
      runtime selected state _ (checkReads (CellStore.read store) proposal.reads)
    · exact helper_capture Helper.validateReads selected state [v "cells", v "reads"]
        [encoded (CellStore.term store), encoded (CellStore.term proposal.reads)] _ rfl
        (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
        (validate_reads_returns state store proposal.reads)
    · cases valid : checkReads (CellStore.read store) proposal.reads with
      | false =>
        have template : PureData.Template runtime (a "RhoCellsRefused" [v "cells"]) :=
          .constructor _ _ (by decide +kernel) (by decide) (by
            intro child member
            simp only [List.mem_singleton] at member
            subst child
            exact .captured _)
        simpa [valid, CellStore.commit, CellStore.resultTerm, selected, caller, bindings, Helper.names,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return runtime selected state _ template
      | true =>
        simp only [↓reduceIte]
        unfold commitCellsAcceptBody
        let next := CellStore.write store proposal.writes
        let changed := ("next", encoded (CellStore.term next)) :: selected
        apply named_let_returns selected state "next" _ (encoded (CellStore.term next))
          (a "RhoCellsAccepted" [v "next"])
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture Helper.applyWrites selected state [v "cells", v "writes"]
            [encoded (CellStore.term store), encoded (CellStore.term proposal.writes)] _ rfl
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (apply_writes_returns state proposal.writes store)
        · have template : PureData.Template runtime (a "RhoCellsAccepted" [v "next"]) :=
            .constructor _ _ (by decide +kernel) (by decide) (by
              intro child member
              simp only [List.mem_singleton] at member
              subst child
              exact .captured _)
          simpa [changed, next, valid, CellStore.commit, CellStore.resultTerm,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return runtime changed state _ template

/-- An accepted occurrence-cell command is the same actual COMM reaction
as the retained runner, provided the candidate is a checked located COMM.
The frame's occurrence keys are not read or written by this reaction. -/
theorem authored_located_commit (state : State) (store : CellStore)
    (candidate : LocatedComm) (rest : List Nat) (untouched : candidate.keys.Disjoint rest)
    (ready : candidate.Ready (CellStore.read store)) :
    let next := CellStore.write store candidate.proposal.writes
    PureReturns runtime [] state
      (a "rho:run:commit-cells" [encoded (CellStore.term store),
        encoded (CellStore.proposalTerm candidate.proposal)]) state
      (encoded (.application "RhoCellsAccepted" [CellStore.term next])) ∧
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction.Reaction
      (LocatedComm.inventory (CellStore.read store) (candidate.keys ++ rest))
      (LocatedComm.inventory (CellStore.read next) (candidate.keys ++ rest)) := by
  dsimp only
  constructor
  · have accepted := (CellStore.commit_located_iff store candidate).mpr ready
    simpa [accepted, CellStore.resultTerm] using commit_cells_returns state store candidate.proposal
  · rw [CellStore.read_write]
    exact candidate.commit_reaction (CellStore.read store) rest ready untouched

end OccurrenceCells

end Authored

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoRunnerExecution
