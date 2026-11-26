import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramResumptionExecution
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCompletion
import Mettapedia.Machines.ResumableSearchRunner

/-!
# Whole runs of an admitted plan through the PeTTa driver

`gslt_live_runner.metta` runs a source term of any admitted plan step after
step. A running machine keeps the whole program observation of its state. A
tick gives every job more work and resumes it, so no search is restarted. When
the publication releases a receipt, the first released receipt is committed
whole and a new search begins at its target. A complete, empty publication ends
the run as normal; a drained job with unresolved obligations ends it as blocked;
otherwise the machine keeps running.

The model below is that machine: the generic machine of
`Mettapedia.Machines.ResumableSearchRunner` over the driver search `Spec.search`.
Its theorems hold for every number of ticks; none assumes that the source
program terminates.

- `Reached`: every machine reached from `begin` keeps the retained run of its
  current state, `programOf state k` for the work `k` done there, and a history
  whose every committed receipt is valid at the state before it;
- `History.isChain_step`: for an equation-free, stratified plan the history is a
  reduction sequence of the plan's GSLT;
- `done_no_step`: a normal ending is exact, the state has no step;
- `tick_commit_stable`: the committed receipt does not depend on how much more
  work is given; publication only grows by prefix;
- `tick_not_pending_of_saturates`, `progress`: work that covers a state's
  searches never leaves it pending, so every running machine commits or ends
  within finitely many ticks;
- `tick_commits_of_step`: for a statically admitted plan, a state with a step
  commits under such work;
- `begin_returns`, `tick_returns`, `advance_returns`, `trace_returns`: the actual
  PeTTa execution of the authored operations is this model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerExecution

open Mettapedia.OSLF.MeTTaIL Syntax
open GeneralProgramResumptionExecution (JobRun ProgramRun)
open GeneralProgramDriverExecution (Invocation LicensedRequest invocations receipts)
open Mettapedia.Machines

/-! ## The model -/

/-- An admitted plan, with the context and sort of its source terms. -/
structure Spec where
  plan : GeneralExecutionAdmission.Plan
  bound : List TypeExpr
  expected : TypeExpr

namespace Spec

variable (spec : Spec)

/-- The driver's run of the plan on a state, with one budget for every job. -/
def programOf (state : Pattern) (budget : Nat) : ProgramRun :=
  ProgramRun.ofInvocations (invocations spec.plan spec.bound spec.expected state fun _ => budget)

/-- The plan's GSLT. -/
abbrev Step (source target : Pattern) : Prop :=
  (GeneralOccurrenceSemantics.gslt spec.plan spec.bound spec.expected).Step source target

/-- The cost of a job's whole search. -/
def jobCost (job : GeneralRuleJobs.Job) : Nat :=
  (GeneralPremise.Execution.treeStart (GeneralPlanEnvironment.environment spec.plan)
    (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost

/-- A budget saturates a state when it covers the whole search of every job there. -/
def Saturates (budget : Nat) (state : Pattern) : Prop :=
  ∀ job ∈ GeneralRuleJobs.jobs spec.plan spec.bound spec.expected state, spec.jobCost job ≤ budget

theorem programOf_resume (state : Pattern) (first extra : Nat) :
    (spec.programOf state first).resume extra = spec.programOf state (first + extra) := by
  unfold programOf
  rw [ProgramRun.ofInvocations_resume]
  congr 1
  simp only [invocations, List.map_map, Function.comp_def]

theorem programOf_reachable (state : Pattern) (budget : Nat) :
    ∀ job ∈ spec.programOf state budget, job.Reachable :=
  ProgramRun.ofInvocations_reachable _

/-- Every receipt the driver reads out on a state is a valid receipt of the plan there. -/
theorem valid_of_mem_aggregate {state : Pattern} {budget : Nat} {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (spec.programOf state budget).aggregate) :
    receipt.Valid spec.plan spec.bound spec.expected state := by
  rw [programOf, ProgramRun.ofInvocations_aggregate] at member
  obtain ⟨invocation, present, found⟩ := List.mem_flatMap.mp member
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  obtain ⟨answer, _, rfl⟩ := List.mem_map.mp found
  exact answer.property

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

theorem valid_of_mem_publication {state : Pattern} {budget : Nat} {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (spec.programOf state budget).publication) :
    receipt.Valid spec.plan spec.bound spec.expected state :=
  spec.valid_of_mem_aggregate (mem_aggregate_of_mem_publication member)

/-- For an equation-free, stratified plan, a valid receipt is a step of the plan's GSLT. -/
theorem step_of_valid (empty : spec.plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    {state : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid spec.plan spec.bound spec.expected state) :
    spec.Step state receipt.target := by
  apply (GeneralOccurrenceFrontier.LocalEquationFree.completedReceipts_targets_iff_step spec.plan spec.bound
    spec.expected state receipt.target empty checked).mp
  exact List.mem_map.mpr ⟨receipt,
    (GeneralRuleJobExecution.mem_completedReceipts_iff spec.plan spec.bound spec.expected state checked
      receipt).mpr valid, rfl⟩

/-- When every job of the run is complete, its readout is the whole completed readout. -/
theorem aggregate_eq_completed {state : Pattern} {budget : Nat}
    (complete : ∀ job ∈ spec.programOf state budget, job.complete = true) :
    (spec.programOf state budget).aggregate =
      GeneralRuleJobExecution.completedReceipts spec.plan spec.bound spec.expected state := by
  rw [← GeneralProgramDriverExecution.saturated_receipts_eq_completed spec.plan spec.bound spec.expected state
    (fun job => budget + spec.jobCost job) (fun job _ => Nat.le_add_left _ _)]
  rw [programOf, ProgramRun.ofInvocations_aggregate]
  unfold invocations
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro item member
  symm
  have settled := JobRun.settled_of_complete (complete _
    (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨item, member, rfl⟩, rfl⟩))
  have same := JobRun.resume_settled (JobRun.begin _ budget) settled (spec.jobCost item.val)
  rw [JobRun.begin_resume] at same
  exact congrArg JobRun.receipts same

/-- A complete, empty publication leaves no step: every valid receipt would have been released. -/
theorem no_step_of_complete {state : Pattern} {budget : Nat}
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    (published : (spec.programOf state budget).publication = [])
    (complete : (spec.programOf state budget).status = .complete) :
    ∀ receipt : GeneralRuleJobs.Receipt, ¬ receipt.Valid spec.plan spec.bound spec.expected state := by
  intro receipt valid
  have completed := (GeneralRuleJobExecution.mem_completedReceipts_iff spec.plan spec.bound spec.expected state
    checked receipt).mpr valid
  have allComplete := (ProgramRun.status_complete_iff _).mp complete
  rw [← spec.aggregate_eq_completed allComplete, ← ProgramRun.publication_complete _ allComplete,
    published] at completed
  cases completed

/-- A drained job's state is the finished search. -/
theorem begin_state_eq (request : LicensedRequest) (budget : Nat)
    (saturated : (GeneralPremise.Execution.treeStart request.val.environment request.val.goal).cost ≤ budget) :
    (JobRun.begin request budget).state =
      GeneralPremise.Execution.finish request.val.environment request.val.goal :=
  GeneralPremise.Execution.run_eq_finish_of_cost_le _ _ _ saturated

/-- Under a saturating budget every job has drained its agenda. -/
theorem settled_of_saturates {state : Pattern} {budget : Nat} (saturates : spec.Saturates budget state) :
    ∀ job ∈ spec.programOf state budget, job.state.agenda = [] := by
  intro job member
  obtain ⟨invocation, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  have licensed := (GeneralRuleJobs.jobs_spec spec.plan spec.bound spec.expected state item.val).mp item.property
  rw [begin_state_eq ⟨⟨spec.plan, spec.bound, spec.expected, state, item.val⟩, licensed⟩ budget
    (saturates item.val item.property)]
  exact GeneralPremise.Execution.finish_settled _ _

end Spec

/-- When every job has drained its agenda, publication has stopped: complete or blocked. -/
theorem status_ne_pending_of_settled {program : ProgramRun}
    (settled : ∀ job ∈ program, job.state.agenda = []) : program.status ≠ .pending := by
  induction program with
  | nil => simp [ProgramRun.status]
  | cons job rest ih =>
    have idle := settled job List.mem_cons_self
    simp only [ProgramRun.status]
    split
    · exact ih fun later member => settled later (List.mem_cons_of_mem _ member)
    · simp [idle]

/-! ## The driver as a resumable search -/

/-- The driver's status as a search status. -/
def statusOf : ProgramRun.Status → ResumableSearchRunner.Status
  | .complete => .complete
  | .blocked => .blocked
  | .pending => .pending

namespace Spec

variable (spec : Spec)

/-- The program driver as a resumable search: the run of the plan at a state, resumed job by job,
with its ordered publication and status. A receipt is valid when it is a valid receipt of the plan. -/
def search : ResumableSearchRunner.Search Pattern ProgramRun GeneralRuleJobs.Receipt where
  run := spec.programOf
  resume := ProgramRun.resume
  publication := ProgramRun.publication
  status program := statusOf program.status
  target := GeneralRuleJobs.Receipt.target
  Valid state receipt := receipt.Valid spec.plan spec.bound spec.expected state

theorem search_lawful : spec.search.Lawful where
  resume_run := spec.programOf_resume
  publication_prefix state first extra := by
    change (spec.programOf state first).publication <+: (spec.programOf state (first + extra)).publication
    rw [← spec.programOf_resume]
    exact ProgramRun.publication_prefix _ extra
  sound _ _ _ member := spec.valid_of_mem_publication member

end Spec

/-- What a machine is doing. -/
abbrev Phase := ResumableSearchRunner.Phase

/-- A live machine of the driver search: its phase, current state, the retained run there, and
its history, newest first. -/
abbrev Machine := ResumableSearchRunner.Machine Pattern ProgramRun GeneralRuleJobs.Receipt

/-- The phase a run without released receipts stops in. -/
abbrev phaseOf (status : ProgramRun.Status) : Phase := ResumableSearchRunner.phaseOf (statusOf status)

namespace Machine

variable (spec : Spec)

/-- A machine at the source, before any work. -/
abbrev begin (source : Pattern) : Machine := ResumableSearchRunner.Machine.begin spec.search source

/-- One tick: more work for every job of the retained run, then the publication decides. -/
abbrev tick (machine : Machine) (quantum : Nat) : Machine :=
  ResumableSearchRunner.Machine.tick spec.search machine quantum

/-- A page of ticks. -/
abbrev advance (ticks quantum : Nat) (machine : Machine) : Machine :=
  ResumableSearchRunner.Machine.advance spec.search ticks quantum machine

theorem advance_zero (quantum : Nat) (machine : Machine) : advance spec 0 quantum machine = machine := rfl

theorem advance_succ (ticks quantum : Nat) (machine : Machine) :
    advance spec (ticks + 1) quantum machine = advance spec ticks quantum (tick spec machine quantum) := rfl

theorem advance_add (first extra quantum : Nat) (machine : Machine) :
    advance spec (first + extra) quantum machine = advance spec extra quantum (advance spec first quantum machine) :=
  ResumableSearchRunner.Machine.advance_add spec.search first extra quantum machine

/-- A running tick that releases a receipt commits the first one. -/
theorem tick_running_cons {machine : Machine} (running : machine.phase = .running) (quantum : Nat)
    {receipt : GeneralRuleJobs.Receipt} {rest : List GeneralRuleJobs.Receipt}
    (published : (machine.program.resume quantum).publication = receipt :: rest) :
    tick spec machine quantum = ⟨.running, receipt.target, spec.programOf receipt.target 0,
      receipt.target :: machine.states, receipt :: machine.receipts⟩ := by
  have released : spec.search.publication (spec.search.resume machine.program quantum) = receipt :: rest :=
    published
  simp only [tick, ResumableSearchRunner.Machine.tick, running, released]
  rfl

/-- A running tick that releases nothing keeps the resumed run, and its status sets the phase. -/
theorem tick_running_nil {machine : Machine} (running : machine.phase = .running) (quantum : Nat)
    (published : (machine.program.resume quantum).publication = []) :
    tick spec machine quantum =
      { machine with phase := phaseOf (machine.program.resume quantum).status,
                     program := machine.program.resume quantum } := by
  have released : spec.search.publication (spec.search.resume machine.program quantum) = [] := published
  simp only [tick, ResumableSearchRunner.Machine.tick, running, released]
  rfl

theorem tick_done {machine : Machine} (phase : machine.phase = .done) (quantum : Nat) :
    tick spec machine quantum = machine :=
  ResumableSearchRunner.Machine.tick_done spec.search phase quantum

theorem tick_blocked {machine : Machine} (phase : machine.phase = .blocked) (quantum : Nat) :
    tick spec machine quantum = machine :=
  ResumableSearchRunner.Machine.tick_blocked spec.search phase quantum

end Machine

/-! ## Reached machines -/

namespace Spec

variable (spec : Spec)

/-- A chronological history, newest first: it starts at one state and every
committed receipt is valid at the state before it. -/
abbrev History : List Pattern → List GeneralRuleJobs.Receipt → Prop :=
  ResumableSearchRunner.History spec.search

/-- What every machine reached from `begin` satisfies. -/
abbrev Reached (machine : Machine) : Prop := ResumableSearchRunner.Reached spec.search machine

theorem begin_reached (source : Pattern) : spec.Reached (Machine.begin spec source) :=
  ResumableSearchRunner.begin_reached source

theorem tick_reached {machine : Machine} (reached : spec.Reached machine) (quantum : Nat) :
    spec.Reached (Machine.tick spec machine quantum) :=
  ResumableSearchRunner.tick_reached spec.search_lawful reached quantum

theorem advance_reached (ticks quantum : Nat) {machine : Machine} (reached : spec.Reached machine) :
    spec.Reached (Machine.advance spec ticks quantum machine) :=
  ResumableSearchRunner.advance_reached spec.search_lawful ticks quantum reached

/-- **Every finite prefix.** For every number of ticks and every quantum, the
machine reached from the source satisfies the invariant. No termination is assumed. -/
theorem run_reached (source : Pattern) (ticks quantum : Nat) :
    spec.Reached (Machine.advance spec ticks quantum (Machine.begin spec source)) :=
  ResumableSearchRunner.run_reached spec.search_lawful source ticks quantum

/-- The history only grows: a tick keeps every earlier state and receipt. -/
theorem tick_history_suffix (machine : Machine) (quantum : Nat) :
    machine.states <:+ (Machine.tick spec machine quantum).states ∧
      machine.receipts <:+ (Machine.tick spec machine quantum).receipts :=
  ResumableSearchRunner.tick_history_suffix machine quantum

theorem advance_history_suffix (ticks quantum : Nat) (machine : Machine) :
    machine.states <:+ (Machine.advance spec ticks quantum machine).states ∧
      machine.receipts <:+ (Machine.advance spec ticks quantum machine).receipts :=
  ResumableSearchRunner.advance_history_suffix ticks quantum machine

/-- The history is a reduction sequence of the plan's GSLT, read newest first. -/
theorem History.isChain_step (empty : spec.plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    {states : List Pattern} {receipts : List GeneralRuleJobs.Receipt}
    (history : spec.History states receipts) :
    states.IsChain (fun newer older => spec.Step older newer) :=
  ResumableSearchRunner.History.isChain (fun valid => spec.step_of_valid empty checked valid) history

/-- **The run is a reduction sequence.** In chronological order, the states of every
reached machine start at the source and each one steps to the next in the plan's GSLT. -/
theorem run_chain (empty : spec.plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    (source : Pattern) (ticks quantum : Nat) :
    let machine := Machine.advance spec ticks quantum (Machine.begin spec source)
    machine.states.reverse.head? = some source ∧ machine.states.reverse.IsChain spec.Step :=
  ResumableSearchRunner.run_chain spec.search_lawful (fun valid => spec.step_of_valid empty checked valid)
    source ticks quantum

/-- A complete, empty search leaves no step at its state. -/
theorem exact_of_complete (empty : spec.plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    (state : Pattern) (work : Nat)
    (complete : spec.search.status (spec.search.run state work) = .complete)
    (published : spec.search.publication (spec.search.run state work) = []) :
    ∀ target, ¬ spec.Step state target := by
  intro target step
  have status : (spec.programOf state work).status = .complete := by
    change statusOf (spec.programOf state work).status = .complete at complete
    cases equation : (spec.programOf state work).status <;> simp_all [statusOf]
  have member := (GeneralOccurrenceFrontier.LocalEquationFree.completedReceipts_targets_iff_step spec.plan
    spec.bound spec.expected state target empty checked).mpr step
  obtain ⟨receipt, completed, _⟩ := List.mem_map.mp member
  exact spec.no_step_of_complete checked published status receipt
    ((GeneralRuleJobExecution.mem_completedReceipts_iff spec.plan spec.bound spec.expected state
      checked receipt).mp completed)

/-- **A normal ending is exact.** A reached machine that is done has no step at its state. -/
theorem done_no_step (empty : spec.plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    {machine : Machine} (reached : spec.Reached machine) (done : machine.phase = .done) :
    ∀ target, ¬ spec.Step machine.state target :=
  ResumableSearchRunner.done_no_step (spec.exact_of_complete empty checked) reached done

theorem exists_blocked_of_status {program : ProgramRun} (status : program.status = .blocked) :
    ∃ job ∈ program, job.state.agenda = [] ∧ job.complete = false := by
  induction program with
  | nil => simp [ProgramRun.status] at status
  | cons job rest ih =>
    simp only [ProgramRun.status] at status
    by_cases complete : job.complete = true
    · rw [if_pos complete] at status
      obtain ⟨later, member, idle, unfinished⟩ := ih status
      exact ⟨later, List.mem_cons_of_mem _ member, idle, unfinished⟩
    · rw [if_neg complete] at status
      by_cases idle : job.state.agenda.isEmpty = true
      · exact ⟨job, List.mem_cons_self, List.isEmpty_iff.mp idle, by simpa using complete⟩
      · rw [if_neg idle] at status
        cases status

/-- A blocked machine stopped at a drained job that left obligations unresolved. -/
theorem blocked_unresolved {machine : Machine} (reached : spec.Reached machine)
    (blocked : machine.phase = .blocked) :
    ∃ job ∈ machine.program, job.state.agenda = [] ∧ job.complete = false := by
  obtain ⟨_, phase⟩ := reached.stopped (by rw [blocked]; decide)
  rw [blocked] at phase
  apply exists_blocked_of_status
  change ResumableSearchRunner.phaseOf (statusOf machine.program.status) = .blocked at phase
  cases equation : machine.program.status <;>
    simp_all [statusOf, ResumableSearchRunner.phaseOf]

/-! ## The committed receipt is stable -/

/-- **The first released receipt does not change with more work.** -/
theorem first_receipt_stable (program : ProgramRun) (quantum extra : Nat) {receipt : GeneralRuleJobs.Receipt}
    {rest : List GeneralRuleJobs.Receipt} (released : (program.resume quantum).publication = receipt :: rest) :
    ∃ more, (program.resume (quantum + extra)).publication = receipt :: more := by
  have grown := ProgramRun.publication_prefix (program.resume quantum) extra
  rw [ProgramRun.resume_add, released] at grown
  obtain ⟨tail, joined⟩ := grown
  exact ⟨rest ++ tail, by rw [← joined]; rfl⟩

/-- A tick that commits a receipt commits the same one under any larger quantum. -/
theorem tick_commit_stable {machine : Machine} (running : machine.phase = .running) (quantum extra : Nat)
    {receipt : GeneralRuleJobs.Receipt} {rest : List GeneralRuleJobs.Receipt}
    (released : (machine.program.resume quantum).publication = receipt :: rest) :
    Machine.tick spec machine (quantum + extra) = Machine.tick spec machine quantum := by
  obtain ⟨more, later⟩ := first_receipt_stable machine.program quantum extra released
  rw [Machine.tick_running_cons spec running _ later, Machine.tick_running_cons spec running _ released]

/-! ## Progress -/

/-- Work that saturates the state never leaves the run pending. -/
theorem tick_not_pending_of_saturates {machine : Machine} {work : Nat}
    (exact : machine.program = spec.programOf machine.state work) (quantum : Nat)
    (saturates : spec.Saturates (work + quantum) machine.state) :
    (machine.program.resume quantum).status ≠ .pending := by
  rw [exact, spec.programOf_resume]
  exact status_ne_pending_of_settled (spec.settled_of_saturates saturates)

/-- The work a state needs: the largest cost of its jobs. -/
def stateCost (state : Pattern) : Nat :=
  ((GeneralRuleJobs.jobs spec.plan spec.bound spec.expected state).map spec.jobCost).foldr max 0

theorem saturates_stateCost (state : Pattern) {budget : Nat} (enough : spec.stateCost state ≤ budget) :
    spec.Saturates budget state := by
  intro job member
  have bounded : spec.jobCost job ≤ spec.stateCost state := by
    unfold stateCost
    have present := List.mem_map_of_mem (f := spec.jobCost) member
    generalize (GeneralRuleJobs.jobs spec.plan spec.bound spec.expected state).map spec.jobCost = costs at present
    induction costs with
    | nil => cases present
    | cons cost costs ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)
  exact bounded.trans enough

/-- Work that covers a state's cost settles its search. -/
theorem settles (state : Pattern) (work : Nat) (_ : True) (enough : spec.stateCost state ≤ work) :
    spec.search.status (spec.search.run state work) ≠ .pending := by
  change statusOf (spec.programOf state work).status ≠ .pending
  have stopped := status_ne_pending_of_settled (spec.settled_of_saturates (spec.saturates_stateCost state enough))
  cases equation : (spec.programOf state work).status <;> simp_all [statusOf]

/-- Under saturating work a running machine commits a receipt or stops. -/
theorem tick_decides {machine : Machine} (reached : spec.Reached machine) (running : machine.phase = .running)
    (quantum : Nat) {work : Nat} (exact : machine.program = spec.programOf machine.state work)
    (saturates : spec.Saturates (work + quantum) machine.state) :
    (Machine.tick spec machine quantum).receipts.length = machine.receipts.length + 1 ∨
      (Machine.tick spec machine quantum).phase ≠ .running := by
  have _ := reached
  have stopped := spec.tick_not_pending_of_saturates exact quantum saturates
  cases published : (machine.program.resume quantum).publication with
  | cons receipt rest =>
    exact .inl (by rw [Machine.tick_running_cons spec running quantum published]; rfl)
  | nil =>
    refine .inr ?_
    rw [Machine.tick_running_nil spec running quantum published]
    change ResumableSearchRunner.phaseOf (statusOf (machine.program.resume quantum).status) ≠ .running
    cases status : (machine.program.resume quantum).status with
    | complete | blocked => simp [statusOf, ResumableSearchRunner.phaseOf]
    | pending => exact absurd status stopped

/-- **Every search is finite.** With a positive quantum, a running reached machine commits a
receipt or stops within `stateCost` ticks of its state. -/
theorem progress {machine : Machine} (reached : spec.Reached machine) (running : machine.phase = .running)
    {quantum : Nat} (positive : 0 < quantum) :
    ∃ ticks ≤ spec.stateCost machine.state + 1,
      machine.receipts.length < (Machine.advance spec ticks quantum machine).receipts.length ∨
        (Machine.advance spec ticks quantum machine).phase ≠ .running :=
  ResumableSearchRunner.progress (Settles := fun _ => True) spec.settles spec.search_lawful reached trivial
    running positive

/-- **A state with a step commits.** For a statically admitted plan, under work that
saturates a canonical state with a step, the tick commits a receipt. -/
theorem tick_commits_of_step (empty : spec.plan.equations = [])
    (stratified : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    (static : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment spec.plan) = true)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    {machine : Machine} (reached : spec.Reached machine) (running : machine.phase = .running)
    (canonical : machine.state.hasCanonicalBinderMetadata = true) {target : Pattern}
    (step : spec.Step machine.state target) (quantum : Nat) {work : Nat}
    (exact : machine.program = spec.programOf machine.state work)
    (saturates : spec.Saturates (work + quantum) machine.state) :
    ∃ receipt rest, (machine.program.resume quantum).publication = receipt :: rest ∧
      Machine.tick spec machine quantum = ⟨.running, receipt.target, spec.programOf receipt.target 0,
        receipt.target :: machine.states, receipt :: machine.receipts⟩ := by
  have _ := reached
  have complete := ProgramRun.ofInvocations_complete_of_static spec.plan spec.bound spec.expected machine.state
    static finiteProvider canonical (fun _ => work + quantum) saturates
  cases published : (machine.program.resume quantum).publication with
  | cons receipt rest =>
    exact ⟨receipt, rest, rfl, Machine.tick_running_cons spec running quantum published⟩
  | nil =>
    rw [exact, spec.programOf_resume] at published
    have status : (spec.programOf machine.state (work + quantum)).status = .complete :=
      (ProgramRun.status_complete_iff _).mpr complete
    have member := (GeneralOccurrenceFrontier.LocalEquationFree.completedReceipts_targets_iff_step spec.plan
      spec.bound spec.expected machine.state target empty stratified).mpr step
    obtain ⟨receipt, completed, _⟩ := List.mem_map.mp member
    exact absurd ((GeneralRuleJobExecution.mem_completedReceipts_iff spec.plan spec.bound spec.expected
      machine.state stratified receipt).mp completed)
      (spec.no_step_of_complete stratified published status receipt)

/-! ## Commits along a run -/

/-- What one tick does to the history: nothing, or it commits one receipt that is valid at the state. -/
theorem tick_commit_or_keep {machine : Machine} (reached : spec.Reached machine) (quantum : Nat) :
    ((Machine.tick spec machine quantum).state = machine.state ∧
      (Machine.tick spec machine quantum).states = machine.states ∧
      (Machine.tick spec machine quantum).receipts = machine.receipts) ∨
    ∃ receipt : GeneralRuleJobs.Receipt, receipt.Valid spec.plan spec.bound spec.expected machine.state ∧
      Machine.tick spec machine quantum = ⟨.running, receipt.target, spec.programOf receipt.target 0,
        receipt.target :: machine.states, receipt :: machine.receipts⟩ :=
  ResumableSearchRunner.tick_commit_or_keep spec.search_lawful reached quantum

/-- **The first commit of a page.** If a page of ticks commits anything, then after some shorter
page the machine is still at its state, unchanged in history, and the next tick commits a
receipt that is valid at that state. -/
theorem exists_first_commit (quantum : Nat) : ∀ (ticks : Nat) (machine : Machine), spec.Reached machine →
    machine.receipts.length < (Machine.advance spec ticks quantum machine).receipts.length →
    ∃ before ≤ ticks, ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid spec.plan spec.bound spec.expected machine.state ∧
      (Machine.advance spec before quantum machine).state = machine.state ∧
      (Machine.advance spec before quantum machine).states = machine.states ∧
      (Machine.advance spec before quantum machine).receipts = machine.receipts ∧
      spec.Reached (Machine.advance spec before quantum machine) ∧
      Machine.tick spec (Machine.advance spec before quantum machine) quantum =
        ⟨.running, receipt.target, spec.programOf receipt.target 0, receipt.target :: machine.states,
          receipt :: machine.receipts⟩ :=
  ResumableSearchRunner.exists_first_commit spec.search_lawful quantum

/-- Without a commit, a page leaves the state and the history as they were. -/
theorem advance_keep_of_no_commit (quantum : Nat) : ∀ (ticks : Nat) {machine : Machine}, spec.Reached machine →
    (Machine.advance spec ticks quantum machine).receipts.length ≤ machine.receipts.length →
    (Machine.advance spec ticks quantum machine).state = machine.state :=
  ResumableSearchRunner.advance_keep_of_no_commit spec.search_lawful quantum

/-- **Stop or commit.** Under a positive quantum, a running reached machine either stops at its own
state after some page, or after some page has committed one receipt valid at that state. -/
theorem stop_or_commit {machine : Machine} (reached : spec.Reached machine) (running : machine.phase = .running)
    {quantum : Nat} (positive : 0 < quantum) :
    (∃ ticks, (Machine.advance spec ticks quantum machine).phase ≠ .running ∧
      (Machine.advance spec ticks quantum machine).state = machine.state) ∨
    ∃ ticks, ∃ receipt : GeneralRuleJobs.Receipt, receipt.Valid spec.plan spec.bound spec.expected machine.state ∧
      Machine.advance spec ticks quantum machine = ⟨.running, receipt.target, spec.programOf receipt.target 0,
        receipt.target :: machine.states, receipt :: machine.receipts⟩ :=
  ResumableSearchRunner.stop_or_commit (Settles := fun _ => True) spec.settles spec.search_lawful reached trivial
    running positive

/-- A state is well-sorted for the plan. -/
def Typed (state : Pattern) : Prop :=
  Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted spec.plan.snapshot.language
    spec.plan.snapshot.free spec.bound spec.expected state

/-- A committed target is well-sorted. -/
theorem typed_of_valid {state : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid spec.plan spec.bound spec.expected state) : spec.Typed receipt.target :=
  (GeneralPlanEnvironment.typing_iff spec.plan spec.bound spec.expected receipt.target).mp valid.2.2.2.2

/-- Every tick keeps a well-sorted state well-sorted. -/
theorem tick_typed {machine : Machine} (reached : spec.Reached machine) (typed : spec.Typed machine.state)
    (quantum : Nat) : spec.Typed (Machine.tick spec machine quantum).state := by
  rcases spec.tick_commit_or_keep reached quantum with ⟨same, _, _⟩ | ⟨receipt, valid, committed⟩
  · rw [same]; exact typed
  · rw [committed]; exact spec.typed_of_valid valid

/-- **Runs stay well-sorted.** -/
theorem advance_typed (quantum : Nat) : ∀ (ticks : Nat) {machine : Machine}, spec.Reached machine →
    spec.Typed machine.state → spec.Typed (Machine.advance spec ticks quantum machine).state :=
  ResumableSearchRunner.advance_preserves spec.search_lawful (fun valid => spec.typed_of_valid valid) quantum

/-- **Runs follow any relation that valid receipts imply.** -/
theorem advance_reaches {Reduces : Pattern → Pattern → Prop}
    (sound : ∀ {state : Pattern} {receipt : GeneralRuleJobs.Receipt},
      receipt.Valid spec.plan spec.bound spec.expected state → Reduces state receipt.target)
    (quantum : Nat) : ∀ (ticks : Nat) {machine : Machine}, spec.Reached machine →
    Relation.ReflTransGen Reduces machine.state (Machine.advance spec ticks quantum machine).state :=
  ResumableSearchRunner.advance_reaches spec.search_lawful sound quantum

/-- A run stops only by ending its phase: a stopped machine is fixed by every page. -/
theorem advance_stopped {machine : Machine} (stopped : machine.phase ≠ .running) (quantum : Nat) :
    ∀ ticks, Machine.advance spec ticks quantum machine = machine :=
  ResumableSearchRunner.advance_stopped stopped quantum

/-- For a statically admitted plan, a reached machine at a canonical state is never blocked. -/
theorem not_blocked_of_static
    (static : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment spec.plan) = true)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    {machine : Machine} (reached : spec.Reached machine)
    (canonical : machine.state.hasCanonicalBinderMetadata = true) : machine.phase ≠ .blocked := by
  intro blocked
  obtain ⟨job, member, idle, unfinished⟩ := spec.blocked_unresolved reached blocked
  obtain ⟨work, exact⟩ := reached.budget
  change machine.program = spec.programOf machine.state work at exact
  rw [exact] at member
  have reachable := spec.programOf_reachable machine.state work job member
  obtain ⟨invocation, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  have done := JobRun.complete_of_settled_static reachable static finiteProvider canonical idle
  rw [done] at unfinished
  cases unfinished

end Spec

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
    "../../../../../../../../metta/gslt/lib/gslt_live_runner.metta"
    sha256 "b91410165033be6c512507e33e5afb32471fefc5269d14b62fcbd8d50fb5a27c"

/-- The driver with its resumption, then the runner. -/
def runtime : Program := GeneralProgramResumptionExecution.runtime.append source.program

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev terms (values : List Term) : Atom := encoded (encodeList id values)
private abbrev names (values : List String) : Atom := terms (values.map Term.string)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
private abbrev tableValue (table : List (String × TypeExpr)) : Atom :=
  encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm table)

/-! ### The code beneath the runner -/

private def localHeads : List String :=
  ["gslt:live:append", "gslt:live:rest-names", "gslt:live:free-names", "gslt:live:free-names-list",
   "gslt:live:lookup", "gslt:live:entries-on", "gslt:live:execute", "gslt:live:begin", "gslt:live:tick",
   "gslt:live:advance", "gslt:live:reverse-onto", "gslt:live:trace"]

/-- Every head except the runner's own. -/
private def resumptionHeads (head : String) : Bool := !localHeads.contains head

private theorem resumption_closed : ProgramClosed resumptionHeads GeneralProgramResumptionExecution.runtime := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

private theorem resumption_agreement :
    ProgramAgreementOn resumptionHeads GeneralProgramResumptionExecution.runtime runtime := by
  exact appended_program_agreement_of_all _ _ _ (by decide +kernel) (by decide +kernel)

/-- The driver and the resumption run unchanged beneath the runner. -/
private theorem resumption_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin resumptionHeads code = true)
    (returned : PureReturns GeneralProgramResumptionExecution.runtime caller before code after answer) :
    PureReturns runtime caller before code after answer :=
  path_of_closed_agreement resumption_closed resumption_agreement ⟨supported, rfl⟩ returned

private theorem closed_arguments (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value
    exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

/-! ### The runner's equations -/

private inductive Helper where
  | append | restNames | freeNames | freeNamesList | lookup | entriesOn | execute | begin | tick | advance
  | reverseOnto | trace

private def Helper.head : Helper → String
  | .append => "gslt:live:append"
  | .restNames => "gslt:live:rest-names"
  | .freeNames => "gslt:live:free-names"
  | .freeNamesList => "gslt:live:free-names-list"
  | .lookup => "gslt:live:lookup"
  | .entriesOn => "gslt:live:entries-on"
  | .execute => "gslt:live:execute"
  | .begin => "gslt:live:begin"
  | .tick => "gslt:live:tick"
  | .advance => "gslt:live:advance"
  | .reverseOnto => "gslt:live:reverse-onto"
  | .trace => "gslt:live:trace"

private def Helper.names : Helper → List String
  | .append => ["left", "right"]
  | .restNames => ["rest"]
  | .freeNames => ["pattern"]
  | .freeNamesList => ["patterns"]
  | .lookup => ["name", "table"]
  | .entriesOn => ["table", "names"]
  | .execute => ["plan", "source", "budget"]
  | .begin => ["plan", "source"]
  | .tick => ["machine", "quantum"]
  | .advance => ["machine", "ticks", "quantum"]
  | .reverseOnto => ["items", "tail"]
  | .trace => ["machine"]

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
  have own : source.program.equations.filter (fun row => row.head == helper.head) = [equation helper] := by
    cases helper <;> rfl
  simp only [runtime, SpaceSemantics.Program.append, List.filter_append, below, own, List.nil_append]

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

private theorem template_constructor (head : String) (arguments : List Atom)
    (constructor : head ∈ ["LCons", "Binding", "Some", "PremiseEnvironment", "RuleJobReceipt", "LiveRunning",
      "LiveDone", "LiveBlocked", "LiveTrace"])
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
  rcases constructor with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact PureData.Template.constructor _ _ (by decide +kernel) (by decide) children

local macro "live_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply template_constructor _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

/-! ### Lists -/

private def appendCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", v "right"),
   (a "LCons" [v "first", v "rest"],
    a "let" [v "tail", a "gslt:live:append" [v "rest", v "right"], a "LCons" [v "first", v "tail"]])]

private theorem append_shape : (equation .append).body =
    a "case" [v "left", .expression (appendCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- List concatenation keeps every element in order. -/
theorem append_returns (state : State) (left right : List Term) :
    PureReturns runtime [] state (a "gslt:live:append" [terms left, terms right]) state (terms (left ++ right)) := by
  induction left with
  | nil =>
      let caller := bindings .append [terms [], terms right]
      apply helper_call .append [] state _ [terms [], terms right] _ rfl (closed_arguments _)
      rw [append_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") appendCases (v "right") _
      · simpa [caller, bindings, Helper.names, terms, encodeList, CettaWireAtom.encode, applySubst,
          Subst.lookup] using variable_returns runtime caller state "left"
      · simp [caller, bindings, Helper.names, appendCases, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime caller state "right"
  | cons first rest ih =>
      let value := terms (first :: rest)
      let caller := bindings .append [value, terms right]
      let selected := [("rest", terms rest), ("first", encoded first)] ++ caller
      let finished := ("tail", terms (rest ++ right)) :: selected
      apply helper_call .append [] state _ [value, terms right] _ rfl (closed_arguments _)
      rw [append_shape]
      apply branch_returns caller selected state _ value appendCases
        (a "let" [v "tail", a "gslt:live:append" [v "rest", v "right"], a "LCons" [v "first", v "tail"]]) _
      · exact variable_returns runtime caller state "left"
      · simp [selected, caller, value, bindings, Helper.names, appendCases, terms,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded]
      · apply named_let_returns selected state "tail" _ (terms (rest ++ right))
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · apply helper_capture .append selected state [v "rest", v "right"] [terms rest, terms right] _ rfl
          · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
          · exact ih
        · have template : PureData.Template runtime (a "LCons" [v "first", v "tail"]) := by live_template
          simpa [finished, selected, caller, bindings, Helper.names, terms, encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return runtime finished state _ template

private theorem append_names_captured (caller : Subst) (state : State) (left right : List String)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [names left, names right]) :
    PureReturns runtime caller state (a "gslt:live:append" [one, two]) state (names (left ++ right)) := by
  have joined := helper_capture .append caller state [one, two] [names left, names right] _ rfl captured
    (append_returns state (left.map Term.string) (right.map Term.string))
  simpa only [names, List.map_append, Helper.head] using joined

private def restCases : SpaceSemantics.Cases :=
  [(.symbol "RNone", .symbol "LNil"), (a "RSome" [v "name"], a "LCons" [v "name", .symbol "LNil"])]

private theorem rest_shape : (equation .restNames).body =
    a "case" [v "rest", .expression (restCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem rest_names_returns (state : State) (rest : Option String) :
    PureReturns runtime [] state
      (a "gslt:live:rest-names" [encoded (InferenceCettaWire.encodeRest rest)]) state (names rest.toList) := by
  let caller := bindings .restNames [encoded (InferenceCettaWire.encodeRest rest)]
  apply helper_call .restNames [] state _ [encoded (InferenceCettaWire.encodeRest rest)] _ rfl (closed_arguments _)
  rw [rest_shape]
  cases rest with
  | none =>
    apply branch_returns caller caller state _ _ restCases (.symbol "LNil") _
      (variable_returns runtime caller state "rest")
    · simp [caller, bindings, Helper.names, restCases, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup, applySubst]
    · have template : PureData.Template runtime (.symbol "LNil") := PureData.Template.symbol _
      simpa [names, terms, encodeList, CettaWireAtom.encode, applySubst] using
        PureData.template_return runtime caller state _ template
  | some name =>
    let selected := ("name", encoded (.string name)) :: caller
    apply branch_returns caller selected state _ _ restCases (a "LCons" [v "name", .symbol "LNil"]) _
      (variable_returns runtime caller state "rest")
    · simp [selected, caller, bindings, Helper.names, restCases, InferenceCettaWire.encodeRest,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, applySubst]
    · have template : PureData.Template runtime (a "LCons" [v "name", .symbol "LNil"]) := by live_template
      simpa [selected, names, terms, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
        applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime selected state _ template

/-! ### Free names -/

private def substCases : Atom :=
  a "let" [v "left", a "gslt:live:free-names" [v "body"],
    a "let" [v "right", a "gslt:live:free-names" [v "replacement"],
      a "gslt:live:append" [v "left", v "right"]]]

private def collectionCases : Atom :=
  a "let" [v "inner", a "gslt:live:free-names-list" [v "elements"],
    a "let" [v "tail", a "gslt:live:rest-names" [v "rest"],
      a "gslt:live:append" [v "inner", v "tail"]]]

private def freeCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], .symbol "LNil"),
   (a "FVar" [v "name"], a "LCons" [v "name", .symbol "LNil"]),
   (a "PApp" [v "label", v "arguments"], a "gslt:live:free-names-list" [v "arguments"]),
   (a "PLam" [v "binder", v "body"], a "gslt:live:free-names" [v "body"]),
   (a "PMultiLam" [v "arity", v "binders", v "body"], a "gslt:live:free-names" [v "body"]),
   (a "PSubst" [v "body", v "replacement"], substCases),
   (a "PCollection" [v "kind", v "elements", v "rest"], collectionCases)]

private theorem free_shape : (equation .freeNames).body =
    a "case" [v "pattern", .expression (freeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def freeListBody : Atom :=
  a "let" [v "head", a "gslt:live:free-names" [v "pattern"],
    a "let" [v "tail", a "gslt:live:free-names-list" [v "rest"],
      a "gslt:live:append" [v "head", v "tail"]]]

private def freeListCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "pattern", v "rest"], freeListBody)]

private theorem free_list_shape : (equation .freeNamesList).body =
    a "case" [v "patterns", .expression (freeListCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem free_list_of (state : State) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns runtime [] state
      (a "gslt:live:free-names" [patternValue pattern]) state (names pattern.freeFvarNames)) :
    PureReturns runtime [] state (a "gslt:live:free-names-list" [patternsValue patterns]) state
      (names (patterns.flatMap Pattern.freeFvarNames)) := by
  induction patterns with
  | nil =>
    let caller := bindings .freeNamesList [patternsValue []]
    apply helper_call .freeNamesList [] state _ [patternsValue []] _ rfl (closed_arguments _)
    rw [free_list_shape]
    apply branch_returns caller caller state _ _ freeListCases (.symbol "LNil") _
      (variable_returns runtime caller state "patterns")
    · simp [caller, bindings, Helper.names, freeListCases, patternsValue, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
        applySubst]
    · simpa [names, terms, encodeList, CettaWireAtom.encode, applySubst] using
        PureData.template_return runtime caller state _ (PureData.Template.symbol "LNil")
  | cons pattern rest ih =>
    let caller := bindings .freeNamesList [patternsValue (pattern :: rest)]
    let selected := [("rest", patternsValue rest), ("pattern", patternValue pattern)] ++ caller
    let withHead := ("head", names pattern.freeFvarNames) :: selected
    let final := ("tail", names (rest.flatMap Pattern.freeFvarNames)) :: withHead
    apply helper_call .freeNamesList [] state _ [patternsValue (pattern :: rest)] _ rfl (closed_arguments _)
    rw [free_list_shape]
    apply branch_returns caller selected state _ _ freeListCases freeListBody _
      (variable_returns runtime caller state "patterns")
    · simp [selected, caller, bindings, Helper.names, freeListCases, patternsValue, patternValue,
        InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup, applySubst]
    · unfold freeListBody
      apply named_let_returns selected state "head" _ (names pattern.freeFvarNames)
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture .freeNames selected state [v "pattern"] [patternValue pattern] _ rfl
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
          (elements pattern List.mem_cons_self)
      · apply named_let_returns withHead state "tail" _ (names (rest.flatMap Pattern.freeFvarNames))
        · simp [withHead, selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .freeNamesList withHead state [v "rest"] [patternsValue rest] _ rfl
            (by simp [withHead, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (ih fun later member => elements later (List.mem_cons_of_mem _ member))
        · simpa only [List.flatMap_cons] using append_names_captured final state pattern.freeFvarNames
            (rest.flatMap Pattern.freeFvarNames) (v "head") (v "tail")
            (by simp [final, withHead, applySubst, Subst.lookup])

/-- **Free names.** The authored walk lists the free variables of every pattern, in order and
with repetitions, exactly as `Pattern.freeFvarNames`. -/
theorem free_names_returns (state : State) (pattern : Pattern) :
    PureReturns runtime [] state (a "gslt:live:free-names" [patternValue pattern]) state
      (names pattern.freeFvarNames) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    let caller := bindings .freeNames [patternValue (.bvar index)]
    let selected := ("index", number index) :: caller
    apply helper_call .freeNames [] state _ [patternValue (.bvar index)] _ rfl (closed_arguments _)
    rw [free_shape]
    apply branch_returns caller selected state _ _ freeCases (.symbol "LNil") _
      (variable_returns runtime caller state "pattern")
    · simp [selected, caller, bindings, Helper.names, freeCases, patternValue, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, applySubst]
    · simpa [names, terms, encodeList, CettaWireAtom.encode, Pattern.freeFvarNames, applySubst] using
        PureData.template_return runtime selected state _ (PureData.Template.symbol "LNil")
  | hfvar name =>
    let caller := bindings .freeNames [patternValue (.fvar name)]
    let selected := ("name", encoded (.string name)) :: caller
    apply helper_call .freeNames [] state _ [patternValue (.fvar name)] _ rfl (closed_arguments _)
    rw [free_shape]
    apply branch_returns caller selected state _ _ freeCases (a "LCons" [v "name", .symbol "LNil"]) _
      (variable_returns runtime caller state "pattern")
    · simp [selected, caller, bindings, Helper.names, freeCases, patternValue, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, applySubst]
    · have template : PureData.Template runtime (a "LCons" [v "name", .symbol "LNil"]) := by live_template
      simpa [selected, names, terms, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
        applySubst.applySubstList, Subst.lookup, Pattern.freeFvarNames] using
        PureData.template_return runtime selected state _ template
  | happly label arguments ih =>
    let caller := bindings .freeNames [patternValue (.apply label arguments)]
    let selected := [("arguments", patternsValue arguments), ("label", encoded (.string label))] ++ caller
    apply helper_call .freeNames [] state _ [patternValue (.apply label arguments)] _ rfl (closed_arguments _)
    rw [free_shape]
    apply branch_returns caller selected state _ _ freeCases (a "gslt:live:free-names-list" [v "arguments"]) _
      (variable_returns runtime caller state "pattern")
    · simp [selected, caller, bindings, Helper.names, freeCases, patternValue, patternsValue,
        InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup, applySubst]
    · have listed := helper_capture .freeNamesList selected state [v "arguments"] [patternsValue arguments] _ rfl
        (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
        (free_list_of state arguments ih)
      simpa only [Pattern.freeFvarNames, Helper.head] using listed
  | hlambda binder body ih =>
    let caller := bindings .freeNames [patternValue (.lambda binder body)]
    let selected := [("body", patternValue body),
      ("binder", encoded (InferenceCettaWire.encodeBinder binder))] ++ caller
    apply helper_call .freeNames [] state _ [patternValue (.lambda binder body)] _ rfl (closed_arguments _)
    rw [free_shape]
    apply branch_returns caller selected state _ _ freeCases (a "gslt:live:free-names" [v "body"]) _
      (variable_returns runtime caller state "pattern")
    · simp [selected, caller, bindings, Helper.names, freeCases, patternValue,
        InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup, applySubst]
    · simpa only [Pattern.freeFvarNames, Helper.head] using helper_capture .freeNames selected state [v "body"]
        [patternValue body] _ rfl (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih
  | hmultiLambda arity binders body ih =>
    let caller := bindings .freeNames [patternValue (.multiLambda arity binders body)]
    let selected := [("body", patternValue body),
      ("binders", encoded (InferenceCettaWire.encodeList InferenceCettaWire.CettaTerm.string binders)), ("arity", number arity)] ++ caller
    apply helper_call .freeNames [] state _ [patternValue (.multiLambda arity binders body)] _ rfl
      (closed_arguments _)
    rw [free_shape]
    apply branch_returns caller selected state _ _ freeCases (a "gslt:live:free-names" [v "body"]) _
      (variable_returns runtime caller state "pattern")
    · simp [selected, caller, bindings, Helper.names, freeCases, patternValue,
        InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup, applySubst]
    · simpa only [Pattern.freeFvarNames, Helper.head] using helper_capture .freeNames selected state [v "body"]
        [patternValue body] _ rfl (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih
  | hsubst body replacement bodyIh replacementIh =>
    let caller := bindings .freeNames [patternValue (.subst body replacement)]
    let selected := [("replacement", patternValue replacement), ("body", patternValue body)] ++ caller
    let withLeft := ("left", names body.freeFvarNames) :: selected
    let final := ("right", names replacement.freeFvarNames) :: withLeft
    apply helper_call .freeNames [] state _ [patternValue (.subst body replacement)] _ rfl (closed_arguments _)
    rw [free_shape]
    apply branch_returns caller selected state _ _ freeCases substCases _
      (variable_returns runtime caller state "pattern")
    · simp [selected, caller, bindings, Helper.names, freeCases, patternValue,
        InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup, applySubst]
    · unfold substCases
      apply named_let_returns selected state "left" _ (names body.freeFvarNames)
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture .freeNames selected state [v "body"] [patternValue body] _ rfl
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) bodyIh
      · apply named_let_returns withLeft state "right" _ (names replacement.freeFvarNames)
        · simp [withLeft, selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .freeNames withLeft state [v "replacement"] [patternValue replacement] _ rfl
            (by simp [withLeft, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) replacementIh
        · simpa only [Pattern.freeFvarNames] using append_names_captured final state body.freeFvarNames
            replacement.freeFvarNames (v "left") (v "right") (by simp [final, withLeft, applySubst, Subst.lookup])
  | hcollection kind elements rest ih =>
    let caller := bindings .freeNames [patternValue (.collection kind elements rest)]
    let selected := [("rest", encoded (InferenceCettaWire.encodeRest rest)), ("elements", patternsValue elements),
      ("kind", encoded (InferenceCettaWire.encodeCollectionType kind))] ++ caller
    let withInner := ("inner", names (elements.flatMap Pattern.freeFvarNames)) :: selected
    let final := ("tail", names rest.toList) :: withInner
    apply helper_call .freeNames [] state _ [patternValue (.collection kind elements rest)] _ rfl
      (closed_arguments _)
    rw [free_shape]
    apply branch_returns caller selected state _ _ freeCases collectionCases _
      (variable_returns runtime caller state "pattern")
    · simp [selected, caller, bindings, Helper.names, freeCases, patternValue, patternsValue,
        InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup, applySubst]
    · unfold collectionCases
      apply named_let_returns selected state "inner" _ (names (elements.flatMap Pattern.freeFvarNames))
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture .freeNamesList selected state [v "elements"] [patternsValue elements] _ rfl
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
          (free_list_of state elements ih)
      · apply named_let_returns withInner state "tail" _ (names rest.toList)
        · simp [withInner, selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .restNames withInner state [v "rest"]
            [encoded (InferenceCettaWire.encodeRest rest)] _ rfl
            (by simp [withInner, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (rest_names_returns state rest)
        · simpa only [Pattern.freeFvarNames] using append_names_captured final state
            (elements.flatMap Pattern.freeFvarNames) rest.toList (v "inner") (v "tail")
            (by simp [final, withInner, applySubst, Subst.lookup])

/-! ### The free context of a state -/

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)

/-- What a table lookup prints. -/
def lookupTerm : Option TypeExpr → Term
  | none => .symbol "None"
  | some type => .application "Some" [InferenceCettaWire.AuthoredRule.typeTerm type]

private def lookupFound : Atom :=
  a "if" [a "==" [v "key", v "name"], a "Some" [v "type"], a "gslt:live:lookup" [v "name", v "rest"]]

private def lookupCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"),
   (a "LCons" [a "Binding" [v "key", v "type"], v "rest"], lookupFound)]

private theorem lookup_shape : (equation .lookup).body =
    a "case" [v "table", .expression (lookupCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The authored lookup is the first-match lookup of the free table. -/
theorem lookup_returns (state : State) (name : String) (table : List (String × TypeExpr)) :
    PureReturns runtime [] state (a "gslt:live:lookup" [encoded (.string name), tableValue table]) state
      (encoded (lookupTerm (FreeTypeContext.ofList table name))) := by
  induction table with
  | nil =>
    let caller := bindings .lookup [encoded (.string name), tableValue []]
    apply helper_call .lookup [] state _ [encoded (.string name), tableValue []] _ rfl (closed_arguments _)
    rw [lookup_shape]
    apply branch_returns caller caller state _ _ lookupCases (.symbol "None") _
      (variable_returns runtime caller state "table")
    · simp [caller, bindings, Helper.names, lookupCases, tableValue,
        PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        MatchAutomataBindingExecution.payloadBindingsTerm, encodeList, CettaWireAtom.encode,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup, applySubst]
    · simpa [lookupTerm, FreeTypeContext.ofList, CettaWireAtom.encode, applySubst] using
        PureData.template_return runtime caller state _ (PureData.Template.symbol "None")
  | cons entry rest ih =>
    obtain ⟨key, type⟩ := entry
    let caller := bindings .lookup [encoded (.string name), tableValue ((key, type) :: rest)]
    let selected := [("rest", tableValue rest), ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)),
      ("key", encoded (.string key))] ++ caller
    apply helper_call .lookup [] state _ [encoded (.string name), tableValue ((key, type) :: rest)] _ rfl
      (closed_arguments _)
    rw [lookup_shape]
    apply branch_returns caller selected state _ _ lookupCases lookupFound _
      (variable_returns runtime caller state "table")
    · simp [selected, caller, bindings, Helper.names, lookupCases, tableValue,
        PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
        encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, applySubst]
    · unfold lookupFound
      have tested := CettaWireAtom.equality_evaluated_returns runtime selected state (.string key) (.string name)
        (v "key") (v "name") (by decide +kernel) (by decide +kernel)
        (by simpa [selected, applySubst, Subst.lookup] using variable_returns runtime selected state "key")
        (by simpa [selected, caller, bindings, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime selected state "name")
      apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns runtime selected
        state _ (decide (key = name)) _ _ _ (by simpa only [Term.string.injEq] using tested)
      by_cases same : key = name
      · subst same
        have template : PureData.Template runtime (a "Some" [v "type"]) := by live_template
        simpa [selected, lookupTerm, FreeTypeContext.ofList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return runtime selected state _ template
      · have found := helper_capture .lookup selected state [v "name", v "rest"]
          [encoded (.string name), tableValue rest] _ rfl
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih
        simpa [same, FreeTypeContext.ofList, Helper.head] using found

private def entriesFound : Atom :=
  a "case" [v "found", .expression ([(.symbol "None", v "tail"),
    (a "Some" [v "type"], a "LCons" [a "Binding" [v "name", v "type"], v "tail"])].map
      fun row => .expression [row.1, row.2])]

private def entriesBody : Atom :=
  a "let" [v "tail", a "gslt:live:entries-on" [v "table", v "rest"],
    a "let" [v "found", a "gslt:live:lookup" [v "name", v "table"], entriesFound]]

private def entriesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "name", v "rest"], entriesBody)]

private theorem entries_shape : (equation .entriesOn).body =
    a "case" [v "names", .expression (entriesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The authored restriction of the table to a list of names is `entriesOn`. -/
theorem entries_on_returns (state : State) (table : List (String × TypeExpr)) (listed : List String) :
    PureReturns runtime [] state (a "gslt:live:entries-on" [tableValue table, names listed]) state
      (tableValue ((FreeTypeContext.ofList table).entriesOn listed)) := by
  induction listed with
  | nil =>
    let caller := bindings .entriesOn [tableValue table, names []]
    apply helper_call .entriesOn [] state _ [tableValue table, names []] _ rfl (closed_arguments _)
    rw [entries_shape]
    apply branch_returns caller caller state _ _ entriesCases (.symbol "LNil") _
      (variable_returns runtime caller state "names")
    · simp [caller, bindings, Helper.names, entriesCases, names, terms, encodeList, CettaWireAtom.encode,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup, applySubst]
    · simpa [tableValue, FreeTypeContext.entriesOn, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        MatchAutomataBindingExecution.payloadBindingsTerm, encodeList, CettaWireAtom.encode, applySubst] using
        PureData.template_return runtime caller state _ (PureData.Template.symbol "LNil")
  | cons name rest ih =>
    let caller := bindings .entriesOn [tableValue table, names (name :: rest)]
    let selected := [("rest", names rest), ("name", encoded (.string name))] ++ caller
    let tailValue := tableValue ((FreeTypeContext.ofList table).entriesOn rest)
    let withTail := ("tail", tailValue) :: selected
    apply helper_call .entriesOn [] state _ [tableValue table, names (name :: rest)] _ rfl (closed_arguments _)
    rw [entries_shape]
    apply branch_returns caller selected state _ _ entriesCases entriesBody _
      (variable_returns runtime caller state "names")
    · simp [selected, caller, bindings, Helper.names, entriesCases, names, terms, encodeList,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, applySubst]
    · unfold entriesBody
      apply named_let_returns selected state "tail" _ tailValue
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture .entriesOn selected state [v "table", v "rest"] [tableValue table, names rest] _ rfl
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih
      · apply named_let_returns withTail state "found" _ (encoded (lookupTerm (FreeTypeContext.ofList table name)))
        · simp [withTail, selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .lookup withTail state [v "name", v "table"]
            [encoded (.string name), tableValue table] _ rfl
            (by simp [withTail, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (lookup_returns state name table)
        · unfold entriesFound
          cases lookedUp : FreeTypeContext.ofList table name with
          | none =>
            let here := ("found", encoded (lookupTerm none)) :: withTail
            have printed : PureReturns runtime here state (v "found") state (encoded (lookupTerm none)) := by
              simpa [here, applySubst, Subst.lookup] using variable_returns runtime here state "found"
            apply branch_returns here here state _ _ _ (v "tail") _ printed
            · simp [lookupTerm, CettaWireAtom.encode, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, matchAtom]
            · have unfolded : (FreeTypeContext.ofList table).entriesOn (name :: rest) =
                  (FreeTypeContext.ofList table).entriesOn rest := by
                simp [FreeTypeContext.entriesOn, lookedUp]
              rw [unfolded]
              simpa [here, withTail, applySubst, Subst.lookup] using variable_returns runtime here state "tail"
          | some type =>
            let here := ("found", encoded (lookupTerm (some type))) :: withTail
            have printed : PureReturns runtime here state (v "found") state (encoded (lookupTerm (some type))) := by
              simpa [here, applySubst, Subst.lookup] using variable_returns runtime here state "found"
            let chosen := ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)) :: here
            apply branch_returns here chosen state _ _ _
              (a "LCons" [a "Binding" [v "name", v "type"], v "tail"]) _ printed
            · simp [chosen, here, withTail, selected, caller, bindings, Helper.names, lookupTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup]
            · have unfolded : (FreeTypeContext.ofList table).entriesOn (name :: rest) =
                  (name, type) :: (FreeTypeContext.ofList table).entriesOn rest := by
                simp [FreeTypeContext.entriesOn, lookedUp]
              rw [unfolded]
              have template : PureData.Template runtime
                  (a "LCons" [a "Binding" [v "name", v "type"], v "tail"]) := by live_template
              simpa [chosen, here, withTail, selected, caller, bindings, Helper.names, tailValue, tableValue,
                PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
                MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
                encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
                Subst.lookup] using PureData.template_return runtime chosen state _ template

/-! ### Running the driver on a state -/

/-- The plan as the runner receives it: the environment over the whole free table, the free
names of the provider rows, and the plan's data. -/
def planTerm (spec : Spec) (table : List (String × TypeExpr)) : Term :=
  .application "LivePlan"
    [PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment spec.plan)
      table,
     encodeList id ((GeneralPremise.providerFreeNames
      (GeneralPlanEnvironment.environment spec.plan).provider).map Term.string),
     InferenceCettaWire.ContextObservation.permissionsTerm spec.plan.permissions.sites,
     encodeList InferenceCettaWire.AuthoredRule.typeTerm spec.bound,
     InferenceCettaWire.AuthoredRule.typeTerm spec.expected,
     encodeList ScopedRuleJobReadoutExecution.rulePlanTerm spec.plan.rules]

/-- The table lists the plan's free context. -/
def Tabled (spec : Spec) (table : List (String × TypeExpr)) : Prop :=
  (GeneralPlanEnvironment.environment spec.plan).free = FreeTypeContext.ofList table

/-- Every plan's own free types are such a table. -/
theorem tabled_freeTypes (spec : Spec) : Tabled spec spec.plan.snapshot.freeTypes := by
  unfold Tabled
  change spec.plan.snapshot.free = _
  funext name
  unfold GeneralExecutionAdmission.Snapshot.free
  induction spec.plan.snapshot.freeTypes with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, type⟩ := entry
    by_cases same : key = name
    · subst same
      simp [FreeTypeContext.ofList]
    · simp [FreeTypeContext.ofList, same, ih]

def executeQuery (spec : Spec) (table : List (String × TypeExpr)) (state : Pattern) (budget : Nat) : Atom :=
  a "gslt:live:execute" [encoded (planTerm spec table), patternValue state, number budget]

private def driverArguments : List Atom :=
  [a "PremiseEnvironment"
    [v "declarations", v "rewrites", v "specifications", v "provider", v "reflection", v "free"],
   v "permissions", v "bound", v "expected", v "source", v "rules", v "budget"]

private def executeBody : Atom :=
  a "let" [v "own", a "gslt:live:free-names" [v "source"],
    a "let" [v "footprint", a "gslt:live:append" [v "own", v "names"],
      a "let" [v "free", a "gslt:live:entries-on" [v "table", v "footprint"],
        a "gslt:program:execute" driverArguments]]]

private def executeCases : SpaceSemantics.Cases :=
  [(a "LivePlan"
    [a "PremiseEnvironment"
      [v "declarations", v "rewrites", v "specifications", v "provider", v "reflection", v "table"],
     v "names", v "permissions", v "bound", v "expected", v "rules"], executeBody)]

private theorem execute_shape : (equation .execute).body =
    a "case" [v "plan", .expression (executeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem driver_captured (spec : Spec) (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = []) (caller : Subst) (state : State) (source : Pattern)
    (budget : Nat)
    (captured : driverArguments.map (applySubst caller) =
      (GeneralProgramDriverExecution.executeArguments spec.plan spec.bound spec.expected source budget).map
        encoded) :
    PureReturns runtime caller state (a "gslt:program:execute" driverArguments) state
      (encoded (spec.programOf source budget).term) := by
  apply resumption_returns (by decide)
  apply GeneralProgramResumptionExecution.driver_returns (by decide)
  apply PureData.raw_capture_returns GeneralProgramDriverExecution.runtime [] caller state state
    "gslt:program:execute" ((GeneralProgramDriverExecution.executeArguments spec.plan spec.bound spec.expected
      source budget).map encoded) driverArguments _ (by decide +kernel) _ (by decide)
  · rw [closed_arguments, captured]
  · rw [Spec.programOf, ProgramRun.ofInvocations_term]
    exact GeneralProgramDriverExecution.execute_returns state spec.plan finiteProvider spec.bound spec.expected source
      budget
  · intro index bounded
    have checked : (List.range 7).all
        (fun index => argumentIsRaw GeneralProgramDriverExecution.runtime "gslt:program:execute" index) = true := by
      decide +kernel
    apply List.all_eq_true.mp checked index
    simp only [GeneralProgramDriverExecution.executeArguments, List.length_map, List.length_cons,
      List.length_nil] at bounded
    exact List.mem_range.mpr bounded

/-- **The driver on a state's own environment.** The authored call restricts the free table to
the state's free names and the provider's, then runs the presentation entry: its result is the
driver's run of the plan on that state. -/
theorem execute_returns (spec : Spec) {table : List (String × TypeExpr)} (tabled : Tabled spec table)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (state : State) (source : Pattern) (budget : Nat) :
    PureReturns runtime [] state (executeQuery spec table source budget) state
      (encoded (spec.programOf source budget).term) := by
  let environment := GeneralPlanEnvironment.environment spec.plan
  let provided := GeneralPremise.providerFreeNames environment.provider
  let caller := bindings .execute [encoded (planTerm spec table), patternValue source, number budget]
  let selected :=
    [("rules", encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm spec.plan.rules)),
     ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm spec.expected)),
     ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm spec.bound)),
     ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm spec.plan.permissions.sites)),
     ("names", names provided),
     ("table", tableValue table),
     ("reflection", encoded (PremiseOperationsExecution.GeneralExecution.reflectionTerm environment.reflection)),
     ("provider", encoded (PremiseOperationsExecution.GeneralExecution.providerTerm environment.provider)),
     ("specifications", encoded (encodeList PremiseOperationsExecution.GeneralExecution.specificationTerm
       environment.specifications)),
     ("rewrites", encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites)),
     ("declarations", encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm
       environment.language.terms))] ++ caller
  let withOwn := ("own", names source.freeFvarNames) :: selected
  let withFootprint := ("footprint", names (source.freeFvarNames ++ provided)) :: withOwn
  let final := ("free", tableValue ((FreeTypeContext.ofList table).entriesOn (source.freeFvarNames ++ provided)))
    :: withFootprint
  apply helper_call .execute [] state _ [encoded (planTerm spec table), patternValue source, number budget] _ rfl
    (closed_arguments _)
  rw [execute_shape]
  apply branch_returns caller selected state _ (encoded (planTerm spec table)) executeCases executeBody _
    (variable_returns runtime caller state "plan")
  · simp [executeCases, selected, caller, bindings, Helper.names, planTerm, environment, provided, names, terms,
      tableValue, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm, encodeList_map,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold executeBody
    apply named_let_returns selected state "own" _ (names source.freeFvarNames)
    · simp [selected, caller, bindings, Helper.names, Subst.lookup]
    · exact helper_capture .freeNames selected state [v "source"] [patternValue source] _ rfl
        (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
        (free_names_returns state source)
    · apply named_let_returns withOwn state "footprint" _ (names (source.freeFvarNames ++ provided))
      · simp [withOwn, selected, caller, bindings, Helper.names, Subst.lookup]
      · exact append_names_captured withOwn state source.freeFvarNames provided (v "own") (v "names")
          (by simp [withOwn, selected, applySubst, Subst.lookup])
      · apply named_let_returns withFootprint state "free" _
          (tableValue ((FreeTypeContext.ofList table).entriesOn (source.freeFvarNames ++ provided)))
        · simp [withFootprint, withOwn, selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .entriesOn withFootprint state [v "table", v "footprint"]
            [tableValue table, names (source.freeFvarNames ++ provided)] _ rfl
            (by simp [withFootprint, withOwn, selected, applySubst, Subst.lookup])
            (entries_on_returns state table _)
        · apply driver_captured spec finiteProvider final state source budget
          have environmentEq : GeneralProgramDriverExecution.environmentTerm spec.plan source =
              PremiseOperationsExecution.GeneralExecution.environmentTerm environment
                ((FreeTypeContext.ofList table).entriesOn (source.freeFvarNames ++ provided)) := by
            simp only [GeneralProgramDriverExecution.environmentTerm, environment, provided]
            rw [tabled]
          simp [driverArguments, final, withFootprint, withOwn, selected, caller, bindings, Helper.names,
            GeneralProgramDriverExecution.executeArguments, environmentEq, tableValue,
            PremiseOperationsExecution.GeneralExecution.environmentTerm,
            PremiseOperationsExecution.DeclarationTyping.declarationsTerm, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup]

/-! ### Machines on the wire -/

def phaseHead : Phase → String
  | .running => "LiveRunning"
  | .done => "LiveDone"
  | .blocked => "LiveBlocked"

/-- A machine as the runner prints it, with the whole retained run of its state. -/
def Machine.term (spec : Spec) (table : List (String × TypeExpr)) (machine : Machine) : Term :=
  .application (phaseHead machine.phase)
    [planTerm spec table, InferenceCettaWire.encodePattern machine.state, machine.program.term,
     encodeList InferenceCettaWire.encodePattern machine.states,
     encodeList ScopedRuleJobReadoutExecution.receiptTerm machine.receipts]

def beginQuery (spec : Spec) (table : List (String × TypeExpr)) (source : Pattern) : Atom :=
  a "gslt:live:begin" [encoded (planTerm spec table), patternValue source]

private def beginBody : Atom :=
  a "let" [v "observation", a "gslt:live:execute" [v "plan", v "source", number 0],
    a "LiveRunning" [v "plan", v "source", v "observation", a "LCons" [v "source", .symbol "LNil"], .symbol "LNil"]]

private theorem begin_shape : (equation .begin).body = beginBody := by
  decide +kernel

/-- **Begin.** The authored start is the machine at the source, before any work. -/
theorem begin_returns (spec : Spec) {table : List (String × TypeExpr)} (tabled : Tabled spec table)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (state : State) (source : Pattern) :
    PureReturns runtime [] state (beginQuery spec table source) state
      (encoded ((Machine.begin spec source).term spec table)) := by
  let caller := bindings .begin [encoded (planTerm spec table), patternValue source]
  let final := ("observation", encoded (spec.programOf source 0).term) :: caller
  apply helper_call .begin [] state _ [encoded (planTerm spec table), patternValue source] _ rfl
    (closed_arguments _)
  rw [begin_shape]
  unfold beginBody
  apply named_let_returns caller state "observation" _ (encoded (spec.programOf source 0).term)
  · simp [caller, bindings, Helper.names, Subst.lookup]
  · exact helper_capture .execute caller state [v "plan", v "source", number 0]
      [encoded (planTerm spec table), patternValue source, number 0] _ rfl
      (by simp [caller, bindings, Helper.names, applySubst, Subst.lookup, number, CettaWireAtom.encode])
      (execute_returns spec tabled finiteProvider state source 0)
  · have template : PureData.Template runtime
        (a "LiveRunning" [v "plan", v "source", v "observation", a "LCons" [v "source", .symbol "LNil"],
          .symbol "LNil"]) := by live_template
    simpa [final, caller, bindings, Helper.names, Machine.term, Machine.begin, ResumableSearchRunner.Machine.begin,
      Spec.search, phaseHead, encodeList,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
      PureData.template_return runtime final state _ template

/-! ### One tick -/

def tickQuery (spec : Spec) (table : List (String × TypeExpr)) (machine : Machine) (quantum : Nat) : Atom :=
  a "gslt:live:tick" [encoded (machine.term spec table), number quantum]

private def receiptPattern : Atom :=
  a "RuleJobReceipt" [v "job", v "trace", v "captured", v "completed", v "history", v "local", v "target"]

private def commitBody : Atom :=
  a "let" [v "next", a "gslt:live:execute" [v "plan", v "target", number 0],
    a "LiveRunning" [v "plan", v "target", v "next", a "LCons" [v "target", v "states"],
      a "LCons" [receiptPattern, v "receipts"]]]

private def stopped (head : String) : Atom :=
  a head [v "plan", v "source", v "resumed", v "states", v "receipts"]

private def publishedCases : SpaceSemantics.Cases :=
  [(a "ProgramPublication" [a "LCons" [receiptPattern, v "others"], v "status"], commitBody),
   (a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationComplete"], stopped "LiveDone"),
   (a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationBlocked"], stopped "LiveBlocked"),
   (a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationPending"], stopped "LiveRunning")]

private def runningBody : Atom :=
  a "let" [v "resumed", a "gslt:program:resume" [v "observation", v "quantum"],
    a "let" [v "published", a "gslt:program:publication" [v "resumed"],
      a "case" [v "published", .expression (publishedCases.map fun row => .expression [row.1, row.2])]]]

private def tickCases : SpaceSemantics.Cases :=
  [(a "LiveRunning" [v "plan", v "source", v "observation", v "states", v "receipts"], runningBody),
   (v "finished", v "finished")]

private theorem tick_shape : (equation .tick).body =
    a "case" [v "machine", .expression (tickCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem resume_captured (caller : Subst) (state : State) (program : ProgramRun)
    (finite : ∀ job ∈ program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ job ∈ program, job.Reachable) (extra : Nat)
    (captured : [v "observation", v "quantum"].map (applySubst caller) = [encoded program.term, number extra]) :
    PureReturns runtime caller state (a "gslt:program:resume" [v "observation", v "quantum"]) state
      (encoded (program.resume extra).term) := by
  apply resumption_returns (by decide)
  apply PureData.raw_capture_returns GeneralProgramResumptionExecution.runtime [] caller state state
    "gslt:program:resume" [encoded program.term, number extra] [v "observation", v "quantum"] _
    (by decide +kernel) _ (by decide)
  · rw [closed_arguments, captured]
  · exact GeneralProgramResumptionExecution.resume_returns state program finite reachable extra
  · intro index bounded
    have checked : (List.range 2).all
        (fun index => argumentIsRaw GeneralProgramResumptionExecution.runtime "gslt:program:resume" index) = true := by
      decide +kernel
    exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

private theorem publication_captured (caller : Subst) (state : State) (program : ProgramRun)
    (captured : applySubst caller (v "resumed") = encoded program.term) :
    PureReturns runtime caller state (a "gslt:program:publication" [v "resumed"]) state
      (encoded program.publicationTerm) := by
  apply resumption_returns (by decide)
  apply PureData.raw_capture_returns GeneralProgramResumptionExecution.runtime [] caller state state
    "gslt:program:publication" [encoded program.term] [v "resumed"] _ (by decide +kernel) _ (by decide)
  · simp [captured]
  · exact GeneralProgramResumptionExecution.publication_returns state program
  · intro index bounded
    have zero : index = 0 := by simpa using bounded
    subst zero
    decide +kernel

/-- **One tick of the authored runner** is the model's tick, on every reached machine. -/
theorem tick_returns (spec : Spec) {table : List (String × TypeExpr)} (tabled : Tabled spec table)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (state : State) (machine : Machine) (reached : spec.Reached machine) (quantum : Nat) :
    PureReturns runtime [] state (tickQuery spec table machine quantum) state
      (encoded ((Machine.tick spec machine quantum).term spec table)) := by
  obtain ⟨phase, current, program, states, receipts⟩ := machine
  let value := encoded (Machine.term spec table ⟨phase, current, program, states, receipts⟩)
  let caller := bindings .tick [value, number quantum]
  apply helper_call .tick [] state _ [value, number quantum] _ rfl (closed_arguments _)
  rw [tick_shape]
  cases phase with
  | done | blocked =>
    let selected := ("finished", value) :: caller
    apply branch_returns caller selected state _ value tickCases (v "finished") _
      (variable_returns runtime caller state "machine")
    · simp [selected, caller, value, bindings, Helper.names, tickCases, Machine.term, phaseHead,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · simpa [selected, value, Machine.tick, ResumableSearchRunner.Machine.tick, applySubst, Subst.lookup] using
        variable_returns runtime selected state "finished"
  | running =>
    obtain ⟨work, exact⟩ := reached.budget
    change program = spec.programOf current work at exact
    have reachable : ∀ job ∈ program, job.Reachable := by
      rw [exact]
      exact spec.programOf_reachable _ _
    have finite : ∀ job ∈ program, job.request.val.environment.provider.dynamicRelations = [] := by
      rw [exact]
      intro job member
      obtain ⟨invocation, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
      exact finiteProvider
    let resumed := program.resume quantum
    let selected := [("receipts", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts)),
      ("states", encoded (encodeList InferenceCettaWire.encodePattern states)),
      ("observation", encoded program.term), ("source", patternValue current),
      ("plan", encoded (planTerm spec table))] ++ caller
    let withResumed := ("resumed", encoded resumed.term) :: selected
    let final := ("published", encoded resumed.publicationTerm) :: withResumed
    apply branch_returns caller selected state _ value tickCases runningBody _
      (variable_returns runtime caller state "machine")
    · simp [selected, caller, value, bindings, Helper.names, tickCases, Machine.term, phaseHead,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold runningBody
      apply named_let_returns selected state "resumed" _ (encoded resumed.term)
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · exact resume_captured selected state program finite reachable quantum
          (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
      · apply named_let_returns withResumed state "published" _ (encoded resumed.publicationTerm)
        · simp [withResumed, selected, caller, bindings, Helper.names, Subst.lookup]
        · exact publication_captured withResumed state resumed (by simp [withResumed, applySubst, Subst.lookup])
        · have printed : PureReturns runtime final state (v "published") state (encoded resumed.publicationTerm) := by
            simpa [final, applySubst, Subst.lookup] using variable_returns runtime final state "published"
          cases published : resumed.publication with
          | cons receipt rest =>
            have model : Machine.tick spec ⟨.running, current, program, states, receipts⟩ quantum =
                ⟨.running, receipt.target, spec.programOf receipt.target 0, receipt.target :: states,
                  receipt :: receipts⟩ := by
              exact Machine.tick_running_cons spec rfl quantum published
            rw [model]
            have shape : ∃ job trace captured completed history localTarget : Term,
                ScopedRuleJobReadoutExecution.receiptTerm receipt =
                  .application "RuleJobReceipt" [job, trace, captured, completed, history, localTarget,
                    InferenceCettaWire.encodePattern receipt.target] := ⟨_, _, _, _, _, _, rfl⟩
            obtain ⟨job, trace, captured, completed, history, localTarget, receiptShape⟩ := shape
            let chosen := [("status", encoded (ProgramRun.statusTerm resumed.status)),
              ("others", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm rest)),
              ("target", patternValue receipt.target), ("local", encoded localTarget),
              ("history", encoded history), ("completed", encoded completed), ("captured", encoded captured),
              ("trace", encoded trace), ("job", encoded job)] ++ final
            let committed := ("next", encoded (spec.programOf receipt.target 0).term) :: chosen
            apply branch_returns final chosen state _ _ publishedCases commitBody _ printed
            · cases status : resumed.status <;>
                simp [publishedCases, receiptPattern, chosen, final, withResumed, selected, caller, bindings,
                  Helper.names, ProgramRun.publicationTerm, published, status, ProgramRun.statusTerm, encodeList,
                  receiptShape, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · unfold commitBody
              apply named_let_returns chosen state "next" _ (encoded (spec.programOf receipt.target 0).term)
              · simp [chosen, final, withResumed, selected, caller, bindings, Helper.names, Subst.lookup]
              · exact helper_capture .execute chosen state [v "plan", v "target", number 0]
                  [encoded (planTerm spec table), patternValue receipt.target, number 0] _ rfl
                  (by simp [chosen, final, withResumed, selected, caller, bindings, Helper.names, applySubst,
                    Subst.lookup, number, CettaWireAtom.encode])
                  (execute_returns spec tabled finiteProvider state receipt.target 0)
              · have template : PureData.Template runtime
                    (a "LiveRunning" [v "plan", v "target", v "next", a "LCons" [v "target", v "states"],
                      a "LCons" [receiptPattern, v "receipts"]]) := by
                  unfold receiptPattern
                  live_template
                simpa [committed, chosen, final, withResumed, selected, caller, bindings, Helper.names,
                  Machine.term, phaseHead, receiptPattern, receiptShape, encodeList, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
                  PureData.template_return runtime committed state _ template
          | nil =>
            have model : Machine.tick spec ⟨.running, current, program, states, receipts⟩ quantum =
                ⟨phaseOf resumed.status, current, resumed, states, receipts⟩ := by
              exact Machine.tick_running_nil spec rfl quantum published
            rw [model]
            cases status : resumed.status with
            | complete =>
              apply branch_returns final final state _ _ publishedCases (stopped "LiveDone") _ printed
              · simp [publishedCases, receiptPattern, ProgramRun.publicationTerm, published, status,
                  ProgramRun.statusTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom]
              · have template : PureData.Template runtime (stopped "LiveDone") := by
                  unfold stopped
                  live_template
                simpa [final, withResumed, selected, caller, bindings, Helper.names, stopped, Machine.term,
                  phaseHead, phaseOf, statusOf, ResumableSearchRunner.phaseOf, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
                  applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime final state _ template
            | blocked =>
              apply branch_returns final final state _ _ publishedCases (stopped "LiveBlocked") _ printed
              · simp [publishedCases, receiptPattern, ProgramRun.publicationTerm, published, status,
                  ProgramRun.statusTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom]
              · have template : PureData.Template runtime (stopped "LiveBlocked") := by
                  unfold stopped
                  live_template
                simpa [final, withResumed, selected, caller, bindings, Helper.names, stopped, Machine.term,
                  phaseHead, phaseOf, statusOf, ResumableSearchRunner.phaseOf, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
                  applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime final state _ template
            | pending =>
              apply branch_returns final final state _ _ publishedCases (stopped "LiveRunning") _ printed
              · simp [publishedCases, receiptPattern, ProgramRun.publicationTerm, published, status,
                  ProgramRun.statusTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom]
              · have template : PureData.Template runtime (stopped "LiveRunning") := by
                  unfold stopped
                  live_template
                simpa [final, withResumed, selected, caller, bindings, Helper.names, stopped, Machine.term,
                  phaseHead, phaseOf, statusOf, ResumableSearchRunner.phaseOf, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
                  applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime final state _ template

/-! ### Pages of ticks -/

def advanceQuery (spec : Spec) (table : List (String × TypeExpr)) (machine : Machine) (ticks quantum : Nat) :
    Atom :=
  a "gslt:live:advance" [encoded (machine.term spec table), number ticks, number quantum]

private def advanceBody : Atom :=
  a "if" [a "==" [v "ticks", number 0], v "machine",
    a "let" [v "next", a "gslt:live:tick" [v "machine", v "quantum"],
      a "let" [v "remaining", a "-" [v "ticks", number 1],
        a "gslt:live:advance" [v "next", v "remaining", v "quantum"]]]]

private theorem advance_shape : (equation .advance).body = advanceBody := by
  decide +kernel

private theorem ticks_test_returns (caller : Subst) (state : State) (ticks : Nat)
    (captured : applySubst caller (v "ticks") = number ticks) :
    PureReturns runtime caller state (a "==" [v "ticks", number 0]) state
      (Effects.boolean (decide (ticks = 0))) := by
  have tested := CettaWireAtom.equality_evaluated_returns runtime caller state (.natural ticks) (.natural 0)
    (v "ticks") (number 0) (by decide +kernel) (by decide +kernel)
    (by simpa only [captured] using variable_returns runtime caller state "ticks")
    (grounded_returns runtime caller state (.int 0))
  simpa only [Term.natural.injEq] using tested

private theorem predecessor_returns (caller : Subst) (state : State) (ticks : Nat)
    (captured : applySubst caller (v "ticks") = number (ticks + 1)) :
    PureReturns runtime caller state (a "-" [v "ticks", number 1]) state (number ticks) := by
  apply native_binary_call_returns runtime caller state state state state "-"
    (v "ticks") (number 1) (number (ticks + 1)) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns runtime caller state "ticks"
  · exact grounded_returns runtime caller state (.int 1)
  · have casts : ((ticks + 1 : Nat) : Int) - 1 = (ticks : Int) := by omega
    simpa only [number, encoded, CettaWireAtom.encode, casts, Int.natCast_one] using
      StdLib.integer_subtraction state ((ticks + 1 : Nat) : Int) 1

/-- **A page of ticks** is the model's page, from every reached machine. -/
theorem advance_returns (spec : Spec) {table : List (String × TypeExpr)} (tabled : Tabled spec table)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (state : State) (ticks : Nat) : ∀ (machine : Machine), spec.Reached machine → ∀ quantum : Nat,
    PureReturns runtime [] state (advanceQuery spec table machine ticks quantum) state
      (encoded ((Machine.advance spec ticks quantum machine).term spec table)) := by
  induction ticks with
  | zero =>
    intro machine _ quantum
    let caller := bindings .advance [encoded (machine.term spec table), number 0, number quantum]
    apply helper_call .advance [] state _ [encoded (machine.term spec table), number 0, number quantum] _ rfl
      (closed_arguments _)
    rw [advance_shape]
    unfold advanceBody
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns runtime caller state _ true
    · simpa using ticks_test_returns caller state 0
        (by simp [caller, bindings, Helper.names, applySubst, Subst.lookup])
    · simpa [caller, bindings, Helper.names, Machine.advance, ResumableSearchRunner.Machine.advance, applySubst,
        Subst.lookup] using
        variable_returns runtime caller state "machine"
  | succ ticks ih =>
    intro machine reached quantum
    let caller := bindings .advance [encoded (machine.term spec table), number (ticks + 1), number quantum]
    let withNext := ("next", encoded ((Machine.tick spec machine quantum).term spec table)) :: caller
    let final := ("remaining", number ticks) :: withNext
    apply helper_call .advance [] state _
      [encoded (machine.term spec table), number (ticks + 1), number quantum] _ rfl (closed_arguments _)
    rw [advance_shape]
    unfold advanceBody
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns runtime caller state _
      false
    · simpa using ticks_test_returns caller state (ticks + 1)
        (by simp [caller, bindings, Helper.names, applySubst, Subst.lookup])
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply named_let_returns caller state "next" _ (encoded ((Machine.tick spec machine quantum).term spec table))
      · simp [caller, bindings, Helper.names, Subst.lookup]
      · exact helper_capture .tick caller state [v "machine", v "quantum"]
          [encoded (machine.term spec table), number quantum] _ rfl
          (by simp [caller, bindings, Helper.names, applySubst, Subst.lookup])
          (tick_returns spec tabled finiteProvider state machine reached quantum)
      · apply named_let_returns withNext state "remaining" _ (number ticks)
        · simp [withNext, caller, bindings, Helper.names, Subst.lookup]
        · exact predecessor_returns withNext state ticks
            (by simp [withNext, caller, bindings, Helper.names, applySubst, Subst.lookup])
        · have continued := helper_capture .advance final state [v "next", v "remaining", v "quantum"]
            [encoded ((Machine.tick spec machine quantum).term spec table), number ticks, number quantum] _ rfl
            (by simp [final, withNext, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (ih (Machine.tick spec machine quantum) (spec.tick_reached reached quantum) quantum)
          simpa only [Machine.advance, ResumableSearchRunner.Machine.advance, Helper.head] using continued

/-! ### The trace in chronological order -/

private def reverseCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", v "tail"),
   (a "LCons" [v "first", v "rest"],
    a "let" [v "longer", a "LCons" [v "first", v "tail"], a "gslt:live:reverse-onto" [v "rest", v "longer"]])]

private theorem reverse_shape : (equation .reverseOnto).body =
    a "case" [v "items", .expression (reverseCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem reverse_onto_returns (state : State) (items tail : List Term) :
    PureReturns runtime [] state (a "gslt:live:reverse-onto" [terms items, terms tail]) state
      (terms (items.reverseAux tail)) := by
  induction items generalizing tail with
  | nil =>
    let caller := bindings .reverseOnto [terms [], terms tail]
    apply helper_call .reverseOnto [] state _ [terms [], terms tail] _ rfl (closed_arguments _)
    rw [reverse_shape]
    apply branch_returns caller caller state _ _ reverseCases (v "tail") _
      (variable_returns runtime caller state "items")
    · simp [caller, bindings, Helper.names, reverseCases, terms, encodeList, CettaWireAtom.encode,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup, applySubst]
    · simpa [caller, bindings, Helper.names, List.reverseAux, applySubst, Subst.lookup] using
        variable_returns runtime caller state "tail"
  | cons first rest ih =>
    let caller := bindings .reverseOnto [terms (first :: rest), terms tail]
    let selected := [("rest", terms rest), ("first", encoded first)] ++ caller
    let final := ("longer", terms (first :: tail)) :: selected
    apply helper_call .reverseOnto [] state _ [terms (first :: rest), terms tail] _ rfl (closed_arguments _)
    rw [reverse_shape]
    apply branch_returns caller selected state _ _ reverseCases
      (a "let" [v "longer", a "LCons" [v "first", v "tail"], a "gslt:live:reverse-onto" [v "rest", v "longer"]]) _
      (variable_returns runtime caller state "items")
    · simp [selected, caller, bindings, Helper.names, reverseCases, terms, encodeList, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, applySubst, encoded]
    · apply named_let_returns selected state "longer" _ (terms (first :: tail))
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · have template : PureData.Template runtime (a "LCons" [v "first", v "tail"]) := by live_template
        simpa [selected, caller, bindings, Helper.names, terms, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return runtime selected state _ template
      · have continued := helper_capture .reverseOnto final state [v "rest", v "longer"]
          [terms rest, terms (first :: tail)] _ rfl
          (by simp [final, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) (ih (first :: tail))
        simpa only [List.reverseAux, Helper.head] using continued

def statusSymbol : Phase → String
  | .running => "LivePending"
  | .done => "LiveNormal"
  | .blocked => "LiveUnresolved"

/-- The trace: the status, then the states and committed receipts in chronological order. -/
def Machine.traceTerm (machine : Machine) : Term :=
  .application "LiveTrace"
    [.symbol (statusSymbol machine.phase), encodeList InferenceCettaWire.encodePattern machine.states.reverse,
     encodeList ScopedRuleJobReadoutExecution.receiptTerm machine.receipts.reverse]

def traceQuery (spec : Spec) (table : List (String × TypeExpr)) (machine : Machine) : Atom :=
  a "gslt:live:trace" [encoded (machine.term spec table)]

private def traceBody (status : String) : Atom :=
  a "let" [v "ordered", a "gslt:live:reverse-onto" [v "states", .symbol "LNil"],
    a "let" [v "committed", a "gslt:live:reverse-onto" [v "receipts", .symbol "LNil"],
      a "LiveTrace" [.symbol status, v "ordered", v "committed"]]]

private def traceCases : SpaceSemantics.Cases :=
  [(a "LiveRunning" [v "plan", v "source", v "observation", v "states", v "receipts"], traceBody "LivePending"),
   (a "LiveDone" [v "plan", v "source", v "observation", v "states", v "receipts"], traceBody "LiveNormal"),
   (a "LiveBlocked" [v "plan", v "source", v "observation", v "states", v "receipts"], traceBody "LiveUnresolved")]

private theorem trace_shape : (equation .trace).body =
    a "case" [v "machine", .expression (traceCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem reversed_captured (caller : Subst) (state : State) {α : Type} (encode : α → Term)
    (items : List α) (name : String)
    (captured : applySubst caller (v name) = encoded (encodeList encode items)) :
    PureReturns runtime caller state (a "gslt:live:reverse-onto" [v name, .symbol "LNil"]) state
      (encoded (encodeList encode items.reverse)) := by
  have first : applySubst caller (v name) = terms (items.map encode) := by
    rw [captured]
    simp only [terms, encodeList_map, Function.id_comp]
  have reversed := helper_capture .reverseOnto caller state [v name, .symbol "LNil"]
    [terms (items.map encode), terms []] _ rfl
    (by simp only [List.map_cons, List.map_nil, first]; rfl)
    (reverse_onto_returns state (items.map encode) [])
  have same : terms ((items.map encode).reverseAux []) = encoded (encodeList encode items.reverse) := by
    rw [List.reverseAux_eq, List.append_nil, show (items.map encode).reverse = items.reverse.map encode by simp]
    simp only [terms, encodeList_map, Function.id_comp]
  rw [same] at reversed
  simpa only [Helper.head] using reversed

/-- **The trace view.** -/
theorem trace_returns (spec : Spec) (table : List (String × TypeExpr)) (state : State) (machine : Machine) :
    PureReturns runtime [] state (traceQuery spec table machine) state (encoded machine.traceTerm) := by
  obtain ⟨phase, current, program, states, receipts⟩ := machine
  let value := encoded (Machine.term spec table ⟨phase, current, program, states, receipts⟩)
  let caller := bindings .trace [value]
  let selected := [("receipts", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts)),
    ("states", encoded (encodeList InferenceCettaWire.encodePattern states)),
    ("observation", encoded program.term), ("source", patternValue current),
    ("plan", encoded (planTerm spec table))] ++ caller
  let withOrdered := ("ordered", encoded (encodeList InferenceCettaWire.encodePattern states.reverse)) :: selected
  let final := ("committed", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts.reverse))
    :: withOrdered
  apply helper_call .trace [] state _ [value] _ rfl (closed_arguments _)
  rw [trace_shape]
  apply branch_returns caller selected state _ value traceCases (traceBody (statusSymbol phase)) _
    (variable_returns runtime caller state "machine")
  · cases phase <;>
      simp [selected, caller, value, bindings, Helper.names, traceCases, statusSymbol, Machine.term, phaseHead,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold traceBody
    apply named_let_returns selected state "ordered" _ (encoded (encodeList InferenceCettaWire.encodePattern states.reverse))
    · simp [selected, caller, bindings, Helper.names, Subst.lookup]
    · exact reversed_captured selected state _ states "states"
        (by simp [selected, applySubst, Subst.lookup])
    · apply named_let_returns withOrdered state "committed" _
        (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts.reverse))
      · simp [withOrdered, selected, caller, bindings, Helper.names, Subst.lookup]
      · exact reversed_captured withOrdered state _ receipts "receipts"
          (by simp [withOrdered, selected, applySubst, Subst.lookup])
      · have template : PureData.Template runtime
            (a "LiveTrace" [.symbol (statusSymbol phase), v "ordered", v "committed"]) := by live_template
        simpa [final, withOrdered, Machine.traceTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
          applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime final state _ template

/-! ### Whole runs -/

/-- **The authored whole run.** Beginning at a source and running any page of ticks, the actual
PeTTa execution prints the model's machine. Its chronological states are a reduction sequence
of the plan's GSLT from the source, every committed receipt is kept whole, and a normal ending
means the last state has no step. No termination of the source program is assumed. -/
theorem authored_run (spec : Spec) {table : List (String × TypeExpr)} (tabled : Tabled spec table)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (empty : spec.plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment spec.plan).language = true)
    (state : State) (source : Pattern) (ticks quantum : Nat) :
    let machine := Machine.advance spec ticks quantum (Machine.begin spec source)
    PureReturns runtime [] state (beginQuery spec table source) state
        (encoded ((Machine.begin spec source).term spec table)) ∧
      PureReturns runtime [] state (advanceQuery spec table (Machine.begin spec source) ticks quantum) state
        (encoded (machine.term spec table)) ∧
      machine.states.reverse.head? = some source ∧ machine.states.reverse.IsChain spec.Step ∧
      spec.History machine.states machine.receipts ∧
      (machine.phase = .done → ∀ target, ¬ spec.Step machine.state target) := by
  intro machine
  have reached := spec.run_reached source ticks quantum
  obtain ⟨starts, chained⟩ := spec.run_chain empty checked source ticks quantum
  exact ⟨begin_returns spec tabled finiteProvider state source,
    advance_returns spec tabled finiteProvider state ticks _ (spec.begin_reached source) quantum, starts, chained,
    reached.history, spec.done_no_step empty checked reached⟩

end Authored

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerExecution
