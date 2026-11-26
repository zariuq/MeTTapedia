import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramDriverExecution
import Mettapedia.Coalgebra.CoherentPrefixTower
import Mettapedia.Machines.ExecutionHistoryReadout

/-!
# Resumption and publication of program runs

A job's partial receipts grow by prefix as it works, but the program's
concatenation of partial receipts need not: more work on an earlier job can
insert receipts before those already exposed from a later job. A program run
therefore keeps every job's machine state, so that resuming adds work instead
of restarting. Its publication releases the receipts of the complete earlier
jobs, then the current receipts of the first job that is not complete, and
withholds every later job. Publication grows by prefix under every resumption,
and equals the whole readout once every job is complete.

The authored resumption continues each retained premise machine and reads its
receipts again. The authored publication reads each job's own state, never the
flat snapshot. On runs reachable from the original job starts, the actual PeTTa
execution of both is the model of this file. Resuming the driver's observation
of a job enumeration gives exactly the driver's observation of the same jobs
with the added budget.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramResumptionExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open scoped ProgramQuotation
open GeneralProgramDriverExecution (LicensedRequest Invocation requestTerm)

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_program_resumption.metta"
    sha256 "75a25de881ac755715af9600cb56171da430b51452ddeb52c70add2872679c85"

def runtime : Program := GeneralProgramDriverExecution.runtime.append source.program

/-! ## Program runs -/

section Model

/-- One job of a program run, with its machine's whole state retained. -/
structure JobRun where
  request : LicensedRequest
  state : Execution.State request.val.environment request.val.goal

namespace JobRun

/-- The job after `budget` units of work from its start. -/
def begin (request : LicensedRequest) (budget : Nat) : JobRun :=
  ⟨request, Execution.run request.val.environment request.val.goal budget
    (Execution.start request.val.environment request.val.goal)⟩

/-- `extra` more units of work on the retained state. -/
def resume (job : JobRun) (extra : Nat) : JobRun :=
  ⟨job.request, Execution.run job.request.val.environment job.request.val.goal extra job.state⟩

/-- The receipts read out of the answers found so far. -/
def receipts (job : JobRun) : List GeneralRuleJobs.Receipt :=
  (job.state.answers.filterMap
    (GeneralRuleJobExecution.rootProjection job.request.val job.request.property)).map Subtype.val

/-- The semantic receipt suffix of this job's actual retained agenda. The
job keeps its original machine state; this is an observer, not a new runner. -/
def remainingReceipts (job : JobRun) : List GeneralRuleJobs.Receipt :=
  ((Execution.remaining job.state).filterMap
    (GeneralRuleJobExecution.rootProjection job.request.val job.request.property)).map Subtype.val

/-- Complete source receipts from the independently specified direct-style
root results, with the same checked receipt projection as the real driver. -/
def totalReceipts (job : JobRun) : List GeneralRuleJobs.Receipt :=
  ((Execution.results job.request.val.environment job.request.val.goal).filterMap
    (GeneralRuleJobExecution.rootProjection job.request.val job.request.property)).map Subtype.val

/-- No pending work and no unresolved obligation. -/
def complete (job : JobRun) : Bool := job.state.agenda.isEmpty && job.state.unresolved.isEmpty

/-- The retained state was reached from the job's start. Driver runs and their
resumptions have this form. -/
def Reachable (job : JobRun) : Prop :=
  ∃ budget, job.state = Execution.run job.request.val.environment job.request.val.goal budget
    (Execution.start job.request.val.environment job.request.val.goal)

theorem begin_receipts (invocation : Invocation) :
    (begin invocation.1 invocation.2).receipts = GeneralProgramDriverExecution.receipts invocation := rfl

theorem begin_reachable (request : LicensedRequest) (budget : Nat) : (begin request budget).Reachable :=
  ⟨budget, rfl⟩

theorem resume_reachable {job : JobRun} (reachable : job.Reachable) (extra : Nat) :
    (job.resume extra).Reachable := by
  obtain ⟨budget, reached⟩ := reachable
  exact ⟨budget + extra, by simp only [resume, reached, Execution.run_add]⟩

/-- A reachable state keeps every term within the request footprint. -/
theorem covered {job : JobRun} (reachable : job.Reachable) :
    Execution.stateFreeWithin (GeneralRuleJobObservation.requestFootprint job.request.val)
      job.request.val.environment job.request.val.goal job.state := by
  obtain ⟨budget, reached⟩ := reachable
  rw [reached]
  exact Execution.run_from_start_free_within _ _ _
    (provider_coverage_mono _ _ _ (fun _ member => List.mem_append_right _ member)
      (provider_covered_by_own_names job.request.val.environment.provider))
    (Query.DynamicOutputsFreeWithin.of_empty _ _ rfl)
    (GeneralRuleJobObservation.licensed_goal_free_within _ job.request.property) budget

theorem resume_zero (job : JobRun) : job.resume 0 = job := by
  cases job
  rfl

theorem resume_add (job : JobRun) (first second : Nat) :
    (job.resume first).resume second = job.resume (first + second) := by
  simp only [resume, Execution.run_add]

theorem begin_resume (request : LicensedRequest) (budget extra : Nat) :
    (begin request budget).resume extra = begin request (budget + extra) := by
  simp only [begin, resume, Execution.run_add]

/-- Work on a drained job changes nothing. -/
theorem resume_settled (job : JobRun) (settled : job.state.agenda = []) (extra : Nat) :
    job.resume extra = job := by
  cases job with
  | mk request state =>
    simp only [resume, Execution.run]
    rw [Scheduler.run_idle _ extra state settled]

theorem receipts_prefix (job : JobRun) (extra : Nat) : job.receipts <+: (job.resume extra).receipts := by
  obtain ⟨tail, grown⟩ := Execution.receipts_prefix job.request.val.environment job.request.val.goal extra
    job.state
  exact List.IsPrefix.map _ (List.IsPrefix.filterMap _ ⟨tail, grown.symm⟩)

theorem settled_of_complete {job : JobRun} (complete : job.complete = true) : job.state.agenda = [] := by
  simp only [JobRun.complete, Bool.and_eq_true, List.isEmpty_iff] at complete
  exact complete.1

/-- Every reachable job partitions its original ordered receipt list into
current receipts and the suffix represented by its retained actual agenda. -/
theorem receipt_conservation {job : JobRun} (reachable : job.Reachable) :
    job.receipts ++ job.remainingReceipts = job.totalReceipts := by
  obtain ⟨budget, reached⟩ := reachable
  have kept := Execution.run_start_retained job.request.val.environment job.request.val.goal budget
  rw [← reached] at kept
  unfold receipts remainingReceipts totalReceipts
  rw [← List.map_append, ← List.filterMap_append, kept]

theorem totalReceipts_eq_finishState (job : JobRun) :
    job.totalReceipts =
      (GeneralRuleJobExecution.finishState job.request.val job.request.property).answers.map Subtype.val := by
  rw [GeneralRuleJobExecution.finishState_root_readouts, Execution.treeStart_answers]
  rfl

theorem totalReceipts_resume (job : JobRun) (extra : Nat) :
    (job.resume extra).totalReceipts = job.totalReceipts := rfl

/-- Complete jobs have no withheld semantic suffix. The completeness test
also continues to require that unresolved obligations are absent. -/
theorem receipts_eq_total_of_complete {job : JobRun} (reachable : job.Reachable)
    (complete : job.complete = true) : job.receipts = job.totalReceipts := by
  have kept := receipt_conservation reachable
  have idle := settled_of_complete complete
  simpa only [remainingReceipts, Execution.remaining, idle, List.flatMap_nil,
    List.filterMap_nil, List.map_nil, List.append_nil] using kept

/-- All unresolved obligations of a reachable prefix occur in the original
job's full obligation history; no successful-receipt projection erases them. -/
theorem unresolved_prefix_finish {job : JobRun} (reachable : job.Reachable) :
    job.state.unresolved <+: (Execution.finish job.request.val.environment job.request.val.goal).unresolved := by
  obtain ⟨budget, reached⟩ := reachable
  rw [reached]
  exact Execution.run_unresolved_prefix_finish _ _ budget

/-- Resolution is earned from the actual static admission checker and the
licensed occurrence, rather than inferred from an empty success list. -/
theorem finish_resolved_of_static (job : JobRun)
    (checked : GeneralPremise.Static.checkLanguage job.request.val.environment = true)
    (finiteProvider : job.request.val.environment.provider.dynamicRelations = [])
    (canonical : job.request.val.source.hasCanonicalBinderMetadata = true) :
    (Execution.finish job.request.val.environment job.request.val.goal).unresolved = [] := by
  exact GeneralPremise.Static.root_resolved checked
    (GeneralPremise.Static.DynamicAvailability.of_empty finiteProvider)
    (GeneralRuleJobs.Job.selected_rule job.request.property)
    (job.request.property.2.focus_sorted canonical)

theorem complete_of_settled_static {job : JobRun} (reachable : job.Reachable)
    (checked : GeneralPremise.Static.checkLanguage job.request.val.environment = true)
    (finiteProvider : job.request.val.environment.provider.dynamicRelations = [])
    (canonical : job.request.val.source.hasCanonicalBinderMetadata = true)
    (idle : job.state.agenda = []) : job.complete = true := by
  obtain ⟨budget, reached⟩ := reachable
  have absent := Execution.run_resolved_of_finish_resolved job.request.val.environment
    job.request.val.goal budget (finish_resolved_of_static job checked finiteProvider canonical)
  rw [← reached] at absent
  simp only [complete, idle, absent, List.isEmpty_nil, Bool.and_self]

/-- The earned finite work account drains a statically admitted job without
unresolved obligations. Extra budget cannot repeat a committed receipt. -/
theorem begin_complete_of_static (request : LicensedRequest) (budget : Nat)
    (checked : GeneralPremise.Static.checkLanguage request.val.environment = true)
    (finiteProvider : request.val.environment.provider.dynamicRelations = [])
    (canonical : request.val.source.hasCanonicalBinderMetadata = true)
    (sufficient : (Execution.treeStart request.val.environment request.val.goal).cost ≤ budget) :
    (begin request budget).complete = true := by
  apply complete_of_settled_static (begin_reachable request budget) checked finiteProvider canonical
  change (Execution.run request.val.environment request.val.goal budget
    (Execution.start request.val.environment request.val.goal)).agenda = []
  rw [Execution.run_eq_finish_of_cost_le _ _ _ sufficient]
  exact Execution.finish_settled _ _

/-- A job's actual retained-frame runner uses the shared trajectory interface. -/
def trajectory (job : JobRun) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory
      (fun fuel current => current.resume fuel) job :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical _ job
    (by intro current; cases current; rfl)
    (fun first extra current => (resume_add current first extra).symm)

theorem trajectory_receipts_prefix (job : JobRun) (first extra : Nat) :
    ((job.trajectory).observation first).receipts <+:
      ((job.trajectory).observation (first + extra)).receipts :=
  job.trajectory.observer_prefix_after_resume JobRun.receipts
    (fun fuel current => receipts_prefix current fuel) first extra

theorem trajectory_settled (job : JobRun) (first extra : Nat)
    (settled : ((job.trajectory).observation first).state.agenda = []) :
    job.trajectory.observation (first + extra) = job.trajectory.observation first :=
  job.trajectory.observation_constant_after_settlement
    (fun current => current.state.agenda = [])
    (fun current idle fuel => resume_settled current idle fuel) first extra settled

end JobRun

/-- A program run: its jobs, in job order. -/
abbrev ProgramRun := List JobRun

namespace ProgramRun

/-- The run of the original job enumeration, each job with its own budget. -/
def ofInvocations (jobs : List Invocation) : ProgramRun := jobs.map fun job => JobRun.begin job.1 job.2

def resume (program : ProgramRun) (extra : Nat) : ProgramRun := program.map (·.resume extra)

/-- The whole current readout, job by job. This is what `ProgramObservation` carries. -/
def aggregate (program : ProgramRun) : List GeneralRuleJobs.Receipt := program.flatMap JobRun.receipts

/-- The complete original source receipts, in original job order. -/
def totalReceipts (program : ProgramRun) : List GeneralRuleJobs.Receipt :=
  program.flatMap JobRun.totalReceipts

/-- Withheld receipts are observed from actual retained states: the unfinished
job's pending suffix, then both current and pending receipts of every later
job. Later jobs are not restarted or discarded. -/
def withheld : ProgramRun → List GeneralRuleJobs.Receipt
  | [] => []
  | job :: rest => if job.complete then withheld rest else
      job.remainingReceipts ++ rest.flatMap (fun later => later.receipts ++ later.remainingReceipts)

/-- **Publication.** The receipts of the complete earlier jobs, then the current receipts of the
first job that is not complete; every later job is withheld. -/
def publication : ProgramRun → List GeneralRuleJobs.Receipt
  | [] => []
  | job :: rest => if job.complete then job.receipts ++ publication rest else job.receipts

/-- Why publication stops: every job is released, the first job that is not complete is drained
with unresolved obligations, or it still has pending work. -/
inductive Status where
  | complete
  | blocked
  | pending
  deriving DecidableEq

def status : ProgramRun → Status
  | [] => .complete
  | job :: rest =>
      if job.complete then status rest else if job.state.agenda.isEmpty then .blocked else .pending

theorem ofInvocations_reachable (jobs : List Invocation) : ∀ job ∈ ofInvocations jobs, job.Reachable := by
  intro job member
  obtain ⟨invocation, _, rfl⟩ := List.mem_map.mp member
  exact JobRun.begin_reachable _ _

theorem resume_reachable {program : ProgramRun} (reachable : ∀ job ∈ program, job.Reachable)
    (extra : Nat) : ∀ job ∈ program.resume extra, job.Reachable := by
  intro job member
  obtain ⟨original, kept, rfl⟩ := List.mem_map.mp member
  exact JobRun.resume_reachable (reachable original kept) extra

theorem ofInvocations_aggregate (jobs : List Invocation) :
    (ofInvocations jobs).aggregate = jobs.flatMap GeneralProgramDriverExecution.receipts := by
  simp only [aggregate, ofInvocations, List.flatMap_map]
  rfl

theorem resume_zero (program : ProgramRun) : program.resume 0 = program := by
  induction program with
  | nil => rfl
  | cons job rest ih =>
    change job.resume 0 :: ProgramRun.resume rest 0 = job :: rest
    rw [JobRun.resume_zero, ih]

theorem resume_add (program : ProgramRun) (first second : Nat) :
    (program.resume first).resume second = program.resume (first + second) := by
  simp only [resume, List.map_map, Function.comp_def, JobRun.resume_add]

/-- **Exact resumption.** Resuming the original run with `extra` more work per job is the run of
the same jobs with `extra` more budget each. -/
theorem ofInvocations_resume (jobs : List Invocation) (extra : Nat) :
    (ofInvocations jobs).resume extra = ofInvocations (jobs.map fun job => (job.1, job.2 + extra)) := by
  simp only [resume, ofInvocations, List.map_map, Function.comp_def, JobRun.begin_resume]

/-- **Publication grows by prefix** under every resumption. -/
theorem publication_prefix (program : ProgramRun) (extra : Nat) :
    program.publication <+: (program.resume extra).publication := by
  induction program with
  | nil => exact List.prefix_refl _
  | cons job rest ih =>
    have later : ∀ tail, (job.resume extra).receipts <+:
        (if (job.resume extra).complete then (job.resume extra).receipts ++ tail
          else (job.resume extra).receipts) := by
      intro tail
      split
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
    simp only [resume, List.map_cons, publication] at ih ⊢
    by_cases done : job.complete = true
    · rw [if_pos done, JobRun.resume_settled job (JobRun.settled_of_complete done), if_pos done]
      exact List.prefix_append_right_inj _ |>.mpr ih
    · rw [if_neg done]
      exact (JobRun.receipts_prefix job extra).trans (later _)

/-- Once every job is complete, publication is the whole readout. -/
theorem publication_complete (program : ProgramRun) (complete : ∀ job ∈ program, job.complete = true) :
    program.publication = program.aggregate := by
  induction program with
  | nil => rfl
  | cons job rest ih =>
    simp only [publication, aggregate, List.flatMap_cons]
    rw [if_pos (complete job (List.mem_cons_self ..))]
    rw [ih fun other member => complete other (List.mem_cons_of_mem _ member)]
    rfl

theorem retained_receipts_eq_total (program : ProgramRun)
    (reachable : ∀ job ∈ program, job.Reachable) :
    program.flatMap (fun job => job.receipts ++ job.remainingReceipts) = program.totalReceipts := by
  apply List.flatMap_congr
  intro job member
  exact JobRun.receipt_conservation (reachable job member)

/-- Publication and the retained withheld suffix partition the original
ordered source receipts. This is stronger than an endpoint-set comparison. -/
theorem publication_conservation (program : ProgramRun)
    (reachable : ∀ job ∈ program, job.Reachable) :
    program.publication ++ program.withheld = program.totalReceipts := by
  induction program with
  | nil => rfl
  | cons job rest ih =>
    have restReachable : ∀ other ∈ rest, other.Reachable :=
      fun other member => reachable other (List.mem_cons_of_mem _ member)
    simp only [publication, withheld, totalReceipts, List.flatMap_cons]
    by_cases done : job.complete = true
    · rw [if_pos done, if_pos done, List.append_assoc, ih restReachable,
        JobRun.receipts_eq_total_of_complete (reachable job (List.mem_cons_self ..)) done]
      rfl
    · rw [if_neg done, if_neg done, ← List.append_assoc,
        JobRun.receipt_conservation (reachable job (List.mem_cons_self ..)),
        retained_receipts_eq_total rest restReachable]
      rfl

theorem publication_prefix_total (program : ProgramRun)
    (reachable : ∀ job ∈ program, job.Reachable) :
    program.publication <+: program.totalReceipts :=
  ⟨program.withheld, publication_conservation program reachable⟩

theorem totalReceipts_resume (program : ProgramRun) (extra : Nat) :
    (program.resume extra).totalReceipts = program.totalReceipts := by
  simp only [resume, totalReceipts, List.flatMap_map, JobRun.totalReceipts_resume]

/-- Exact resumption preserves both monotone publication and its ordered
conservation against the original job receipts. -/
theorem resume_publication_conservation (program : ProgramRun)
    (reachable : ∀ job ∈ program, job.Reachable) (extra : Nat) :
    program.publication <+: (program.resume extra).publication ∧
      (program.resume extra).publication ++ (program.resume extra).withheld = program.totalReceipts := by
  exact ⟨publication_prefix program extra,
    (publication_conservation _ (resume_reachable reachable extra)).trans (totalReceipts_resume program extra)⟩

/-- The original authored job enumeration has the same complete source
receipt list for every allocation of per-job work budgets. -/
theorem ofInvocations_totalReceipts (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (budget : GeneralRuleJobs.Job → Nat) :
    (ofInvocations (GeneralProgramDriverExecution.invocations plan bound expected source budget)).totalReceipts =
      GeneralRuleJobExecution.completedReceipts plan bound expected source := by
  unfold ofInvocations GeneralProgramDriverExecution.invocations totalReceipts
    GeneralRuleJobExecution.completedReceipts
  rw [List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro item member
  exact JobRun.totalReceipts_eq_finishState _

/-- Budget units are extra work per job, as in the authored library.
The trajectory keeps every job's pending work and unresolved obligations. -/
def trajectory (program : ProgramRun) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory
      (fun fuel current => ProgramRun.resume current fuel) program :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical _ program
    (by
      intro current
      simp only [resume]
      have identity : (fun job : JobRun => job.resume 0) = id := by
        funext job
        cases job
        rfl
      rw [identity, List.map_id])
    (fun first extra current => (resume_add current first extra).symm)

theorem trajectory_publication_prefix (program : ProgramRun) (first extra : Nat) :
    ((program.trajectory).observation first).publication <+:
      ((program.trajectory).observation (first + extra)).publication :=
  program.trajectory.observer_prefix_after_resume ProgramRun.publication
    (fun fuel current => publication_prefix current fuel) first extra

theorem status_complete_iff (program : ProgramRun) :
    program.status = .complete ↔ ∀ job ∈ program, job.complete = true := by
  induction program with
  | nil => simp [status]
  | cons job rest ih =>
    cases done : job.complete with
    | true => simp [status, done, ih]
    | false =>
      constructor
      · intro stopped
        simp only [status, done, Bool.false_eq_true, ↓reduceIte] at stopped
        split at stopped <;> cases stopped
      · intro all
        have released := all job List.mem_cons_self
        rw [done] at released
        cases released

/-- Local static admission plus the actual tree bounds earns complete
execution of every original licensed job; it does not assume completion. -/
theorem ofInvocations_complete_of_static (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment plan) = true)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (canonical : source.hasCanonicalBinderMetadata = true)
    (budget : GeneralRuleJobs.Job → Nat)
    (sufficient : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job) :
    ∀ job ∈ ofInvocations (GeneralProgramDriverExecution.invocations plan bound expected source budget),
      job.complete = true := by
  intro job member
  obtain ⟨invocation, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨item, _, same⟩ := List.mem_map.mp selected
  cases same
  exact JobRun.begin_complete_of_static _ _ checked finiteProvider canonical (sufficient item.val item.property)

/-- At the earned drain bound, the existing publication mechanism releases
exactly all original job receipts in order. -/
theorem publication_eq_completed_of_static (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment plan) = true)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (canonical : source.hasCanonicalBinderMetadata = true)
    (budget : GeneralRuleJobs.Job → Nat)
    (sufficient : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job) :
    (ofInvocations (GeneralProgramDriverExecution.invocations plan bound expected source budget)).publication =
      GeneralRuleJobExecution.completedReceipts plan bound expected source := by
  rw [publication_complete _ (ofInvocations_complete_of_static plan bound expected source checked finiteProvider canonical
    budget sufficient), ofInvocations_aggregate]
  exact GeneralProgramDriverExecution.saturated_receipts_eq_completed plan bound expected source budget sufficient

open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement in
/-- Query-only first-order admission earns publication at the actual drain
bound, without requiring a separate static-checker premise. -/
theorem root_publication_eq_completed_of_queries {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} (facts : QueryProfileFacts language provider)
    (queries : ∀ {index : Nat} {rule : RewriteRule},
      (environment language provider).language.rewrites[index]? = some rule →
      ∀ premise ∈ rule.premises, ∃ relation arguments, premise = .relationQuery relation arguments)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceTyped : WellSorted.OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    (budget : GeneralRuleJobs.Job → Nat)
    (sufficient : ∀ job ∈ GeneralRuleJobs.jobs (rootPlan language provider) bound type source,
      (Execution.treeStart (environment language provider)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job) :
    (ofInvocations (GeneralProgramDriverExecution.invocations
      (rootPlan language provider) bound type source budget)).publication =
      GeneralRuleJobExecution.completedReceipts (rootPlan language provider) bound type source :=
  publication_eq_completed_of_static _ _ _ _ (facts.static_of_queries queries) facts.firstOrder.noDynamic sourceTyped.2.1
    budget sufficient

open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement in
/-- At every budget, published receipts followed by the actual retained
withheld suffix have the full source-root correspondence, including bindings,
query histories and rule origins through their original ordinals. -/
theorem root_publication_guarded_conservation {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} (facts : QueryProfileFacts language provider)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceShape : GeneralFirstOrderProjection.FirstOrder source)
    (sourceTyped : WellSorted.OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    (budget : GeneralRuleJobs.Job → Nat) :
    let program := ofInvocations (GeneralProgramDriverExecution.invocations
      (rootPlan language provider) bound type source budget)
    List.Forall₂ (RuleRunAgreement language provider)
      ((program.publication ++ program.withheld).map receiptReadout)
      (recordedGuardedRootOccurrences (providerRelEnv provider) language provider type source) := by
  dsimp only
  rw [publication_conservation _ (ofInvocations_reachable _), ofInvocations_totalReceipts]
  exact completedReceipts_guarded_recorded_occurrences facts sourceShape sourceTyped

open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement in
/-- The public prefix corresponds to precisely the same number of original
source occurrences; withheld later jobs cannot overtake earlier pending work. -/
theorem root_publication_guarded_prefix {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} (facts : QueryProfileFacts language provider)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceShape : GeneralFirstOrderProjection.FirstOrder source)
    (sourceTyped : WellSorted.OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    (budget : GeneralRuleJobs.Job → Nat) :
    let program := ofInvocations (GeneralProgramDriverExecution.invocations
      (rootPlan language provider) bound type source budget)
    List.Forall₂ (RuleRunAgreement language provider)
      (program.publication.map receiptReadout)
      ((recordedGuardedRootOccurrences (providerRelEnv provider) language provider type source).take
        program.publication.length) := by
  dsimp only
  have full := root_publication_guarded_conservation facts sourceShape sourceTyped budget
  have initialReadout := List.forall₂_take
    (ofInvocations (GeneralProgramDriverExecution.invocations
      (rootPlan language provider) bound type source budget)).publication.length full
  simpa only [List.map_append, List.take_append, List.length_map, List.take_length,
    Nat.sub_self, List.take_zero, List.append_nil, ← List.map_take, List.map_nil] using initialReadout

open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement in
/-- At the earned tree bound, the public results themselves have the complete
ordered original-source correspondence, including binding and query receipts. -/
theorem root_publication_guarded_complete {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} (facts : QueryProfileFacts language provider)
    (queries : ∀ {index : Nat} {rule : RewriteRule},
      (environment language provider).language.rewrites[index]? = some rule →
      ∀ premise ∈ rule.premises, ∃ relation arguments, premise = .relationQuery relation arguments)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceShape : GeneralFirstOrderProjection.FirstOrder source)
    (sourceTyped : WellSorted.OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type source)
    (budget : GeneralRuleJobs.Job → Nat)
    (sufficient : ∀ job ∈ GeneralRuleJobs.jobs (rootPlan language provider) bound type source,
      (Execution.treeStart (environment language provider)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job) :
    List.Forall₂ (RuleRunAgreement language provider)
      ((ofInvocations (GeneralProgramDriverExecution.invocations
        (rootPlan language provider) bound type source budget)).publication.map receiptReadout)
      (recordedGuardedRootOccurrences (providerRelEnv provider) language provider type source) := by
  rw [root_publication_eq_completed_of_queries facts queries sourceTyped budget sufficient]
  exact completedReceipts_guarded_recorded_occurrences facts sourceShape sourceTyped

end ProgramRun

end Model

/-! ## Observations -/

/-- The job's observation, as the driver and the resumption print it. -/
def JobRun.term (job : JobRun) : Term :=
  .application "ProgramJobObservation"
    [requestTerm job.request.val, PremiseOperationsExecution.GeneralExecution.stateTerm job.state,
     encodeList ScopedRuleJobReadoutExecution.receiptTerm job.receipts]

/-- The program's observation: every job's observation and the flat snapshot. -/
def ProgramRun.term (program : ProgramRun) : Term :=
  .application "ProgramObservation"
    [encodeList JobRun.term program, encodeList ScopedRuleJobReadoutExecution.receiptTerm program.aggregate]

def ProgramRun.statusTerm : ProgramRun.Status → Term
  | .complete => .symbol "ProgramPublicationComplete"
  | .blocked => .symbol "ProgramPublicationBlocked"
  | .pending => .symbol "ProgramPublicationPending"

def ProgramRun.publicationTerm (program : ProgramRun) : Term :=
  .application "ProgramPublication"
    [encodeList ScopedRuleJobReadoutExecution.receiptTerm program.publication,
     ProgramRun.statusTerm program.status]

theorem JobRun.begin_term (invocation : Invocation) :
    (JobRun.begin invocation.1 invocation.2).term = GeneralProgramDriverExecution.observationTerm invocation :=
  rfl

theorem ProgramRun.ofInvocations_term (jobs : List Invocation) :
    (ProgramRun.ofInvocations jobs).term = GeneralProgramDriverExecution.programObservationTerm jobs := by
  rw [ProgramRun.term, ProgramRun.ofInvocations_aggregate]
  simp only [ProgramRun.ofInvocations, encodeList_map, GeneralProgramDriverExecution.programObservationTerm]
  rfl

/-! ## The authored resumption -/

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)

private inductive Helper where | resumeJob | resumeJobs | resume | publicationFrom | publication

private def Helper.head : Helper → String
  | .resumeJob => "gslt:program:resume-job"
  | .resumeJobs => "gslt:program:resume-jobs"
  | .resume => "gslt:program:resume"
  | .publicationFrom => "gslt:program:publication-from"
  | .publication => "gslt:program:publication"

private def Helper.names : Helper → List String
  | .resumeJob => ["observation", "extra"]
  | .resumeJobs => ["observations", "extra"]
  | .resume => ["observation", "extra"]
  | .publicationFrom => ["observations"]
  | .publication => ["observation"]

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (source.program.equations.filter (fun equation => equation.head == helper.head))[0]'(by
    cases helper <;> decide +kernel)

private def bindings (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (bindings helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> rfl) (by cases helper <;> decide) length

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
  · have unchanged : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm
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

private def dataHeads : List String :=
  ["Some", "LCons", "PremiseState", "ProgramJobObservation", "ProgramObservation",
   "RuleJobRequestProjection", "ProgramPublication"]

private theorem template_constructor (head : String) (arguments : List Atom)
    (constructor : head ∈ dataHeads)
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at constructor
  rcases constructor with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact PureData.Template.constructor _ _ (by decide +kernel) (by decide) children

local macro "resumption_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.symbol _
  | (apply template_constructor _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

/-! ### The driver beneath -/

private def resumptionHeads : List String :=
  ["gslt:program:resume-job", "gslt:program:resume-jobs", "gslt:program:resume",
   "gslt:program:publication-from", "gslt:program:publication"]

/-- Every head except the resumption's own. The driver runtime is closed under them. -/
def driverHeads (head : String) : Bool := !resumptionHeads.contains head

theorem driver_closed : ProgramClosed driverHeads GeneralProgramDriverExecution.runtime := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

theorem driver_agreement :
    ProgramAgreementOn driverHeads GeneralProgramDriverExecution.runtime runtime := by
  exact appended_program_agreement_of_all _ _ _ (by decide +kernel) (by decide +kernel)

/-- Driver code runs unchanged beside the resumption. -/
theorem driver_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin driverHeads code = true)
    (returned : PureReturns GeneralProgramDriverExecution.runtime caller before code after answer) :
    PureReturns runtime caller before code after answer :=
  path_of_closed_agreement driver_closed driver_agreement ⟨supported, rfl⟩ returned

/-! ### One job -/

private def readoutPayloads (job : JobRun) : List (Option Term) :=
  job.state.answers.map fun result =>
    (GeneralRuleJobExecution.rootProjection job.request.val job.request.property result).map
      (fun answer => ScopedRuleJobReadoutExecution.receiptTerm answer.val)

private theorem readout_payloads_codec (job : JobRun) :
    encodeList (encodeOption id) (readoutPayloads job) =
      encodeList (GeneralRuleJobObservation.rootReadoutTerm job.request.val job.request.property)
        job.state.answers := by
  rw [readoutPayloads, encodeList_map]
  apply congrArg (fun encode => encodeList encode job.state.answers)
  funext result
  dsimp only [Function.comp_def]
  unfold GeneralRuleJobObservation.rootReadoutTerm
  cases GeneralRuleJobExecution.rootProjection job.request.val job.request.property result <;> rfl

private theorem successful_payloads_codec (job : JobRun) :
    encodeList id ((readoutPayloads job).filterMap id) =
      encodeList ScopedRuleJobReadoutExecution.receiptTerm job.receipts := by
  have filtered : (readoutPayloads job).filterMap id =
      job.receipts.map ScopedRuleJobReadoutExecution.receiptTerm := by
    simp [readoutPayloads, JobRun.receipts, List.filterMap_map, List.map_filterMap]
  rw [filtered, encodeList_map]
  rfl

private def requestTemplate : Atom :=
  a "RuleJobRequestProjection" [v "environment", v "permissions", v "bound", v "expected", v "source", v "job"]

private def jobPattern : Atom :=
  a "ProgramJobObservation" [requestTemplate, v "state", v "receipts"]

private def machinePattern : Atom :=
  a "PremiseState" [v "agenda", v "answers", v "unresolved", v "work"]

private def resumedOutput : Atom :=
  a "ProgramJobObservation" [v "request", machinePattern, v "current"]

private def resumedReceipts : Atom :=
  a "let" [v "current", a "gslt:program:receipts" [v "readouts"], resumedOutput]

private def resumedReadouts : Atom :=
  a "let" [v "readouts", a "gslt:rule:job-readouts" [v "request", v "answers"], resumedReceipts]

private def resumedRun : Atom :=
  a "let" [a "Some" [machinePattern], a "gslt:premise:machine-run" [v "environment", v "extra", v "state"],
    resumedReadouts]

private def resumedBody : Atom := a "let" [v "request", requestTemplate, resumedRun]

private def resumeJobCases : SpaceSemantics.Cases := [(jobPattern, resumedBody)]

private theorem resume_job_shape : (equation .resumeJob).body =
    a "case" [v "observation", .expression (resumeJobCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The request's fields, as the observation pattern binds them. -/
private def requestFields (request : GeneralRuleJobExecution.Request) : Subst :=
  [("job", encoded (ScopedRuleJobReadoutExecution.jobTerm request.job)),
   ("source", encoded (InferenceCettaWire.encodePattern request.source)),
   ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.expected)),
   ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
   ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm request.plan.permissions.sites)),
   ("environment", encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
     (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request))))]

/-- One authored call continues the job's retained machine with `extra` more work and reads
the receipts of all its answers again. -/
theorem resume_job_returns (state : State) (job : JobRun)
    (finiteProvider : job.request.val.environment.provider.dynamicRelations = []) (reachable : job.Reachable) (extra : Nat) :
    PureReturns runtime [] state (a "gslt:program:resume-job" [encoded job.term, number extra]) state
      (encoded (job.resume extra).term) := by
  let request := job.request.val
  let caller := bindings .resumeJob [encoded job.term, number extra]
  let selected :=
    [("receipts", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm job.receipts)),
     ("state", encoded (PremiseOperationsExecution.GeneralExecution.stateTerm job.state))] ++
      requestFields request ++ caller
  let requested := ("request", encoded (requestTerm request)) :: selected
  let resumed := Execution.run request.environment request.goal extra job.state
  let observed :=
    [("work", encoded (.natural resumed.work)),
     ("unresolved", encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm
       resumed.unresolved)),
     ("answers", encoded (encodeList PremiseOperationsExecution.GeneralExecution.resultTerm resumed.answers)),
     ("agenda", encoded (encodeList PremiseOperationsExecution.GeneralExecution.taskTerm resumed.agenda))] ++
      requested
  let readouts := encoded (encodeList
    (GeneralRuleJobObservation.rootReadoutTerm request job.request.property) resumed.answers)
  let read := ("readouts", readouts) :: observed
  let current := encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (job.resume extra).receipts)
  let finished := ("current", current) :: read
  obtain ⟨budget, reached⟩ := reachable
  have members : ∀ result ∈ resumed.answers, result ∈ (Execution.run request.environment request.goal
      (budget + extra) (Execution.start request.environment request.goal)).answers := by
    intro result member
    rw [Execution.run_add, ← reached]
    exact member
  apply helper_call .resumeJob [] state _ [encoded job.term, number extra] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [resume_job_shape]
  apply branch_returns caller selected state _ (encoded job.term) resumeJobCases resumedBody _
  · exact variable_returns runtime caller state "observation"
  · simp [selected, caller, requestFields, request, bindings, Helper.names, resumeJobCases, jobPattern,
      requestTemplate, JobRun.term, requestTerm, ScopedRuleJobReadoutExecution.requestProjectionTerm,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · unfold resumedBody
    apply named_let_returns selected state "request" requestTemplate (encoded (requestTerm request))
    · simp [selected, caller, requestFields, bindings, Helper.names, Subst.lookup]
    · have template : PureData.Template runtime requestTemplate := by
        unfold requestTemplate
        resumption_template
      simpa [requestTemplate, selected, caller, requestFields, request, bindings, Helper.names, requestTerm,
        ScopedRuleJobReadoutExecution.requestProjectionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        applySubst, applySubst.applySubstList, Subst.lookup]
        using PureData.template_return runtime selected state requestTemplate template
    · unfold resumedRun
      apply let_returns runtime requested observed state state state _ _ resumedReadouts
        (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm (some resumed))) _
      · apply driver_returns (by rfl)
        apply GeneralProgramDriverExecution.machine_run_captured_returns requested state request finiteProvider extra
          job.state (JobRun.covered ⟨budget, reached⟩) "environment" "extra" "state"
        simp [requested, selected, caller, requestFields, request, bindings, Helper.names, applySubst,
          Subst.lookup]
      · simp [observed, resumed, requested, selected, requestFields, caller, bindings, Helper.names,
          machinePattern, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, encodeOption, encoded,
          PremiseOperationsExecution.GeneralExecution.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · unfold resumedReadouts
        apply named_let_returns observed state "readouts" _ readouts
        · simp [observed, requested, selected, caller, requestFields, bindings, Helper.names, Subst.lookup]
        · apply driver_returns (by rfl)
          apply GeneralRuleReadoutCache.job_readouts_captured_variables_returns_in_extension
            GeneralProgramDriverExecution.runtime GeneralProgramDriverExecution.cache_agreement
            observed state request job.request.property (budget + extra) resumed.answers members
            "request" "answers"
          simp [observed, requested, selected, caller, requestFields, bindings, Helper.names,
            applySubst, Subst.lookup, GeneralRuleReadoutCache.requestTerm, GeneralRuleReadoutCache.resultsTerm,
            requestTerm, request]
        · unfold resumedReceipts
          apply named_let_returns read state "current" _ current
          · simp [read, observed, requested, selected, caller, requestFields, bindings, Helper.names,
              Subst.lookup]
          · apply driver_returns (by rfl)
            dsimp only [current]
            rw [← successful_payloads_codec (job.resume extra)]
            apply GeneralProgramDriverExecution.receipts_captured_returns read state
              (readoutPayloads (job.resume extra))
            rw [readout_payloads_codec]
            simp [read, readouts, request, resumed, JobRun.resume, applySubst, Subst.lookup]
          · have template : PureData.Template runtime resumedOutput := by
              unfold resumedOutput machinePattern
              resumption_template
            simpa [resumedOutput, machinePattern, JobRun.term, JobRun.resume, finished, current, read,
              readouts, observed, resumed, requested, selected, caller, requestFields, request, bindings,
              Helper.names, PremiseOperationsExecution.GeneralExecution.stateTerm,
              PremiseSchedulerExecution.schedulerStateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup]
              using PureData.template_return runtime finished state resumedOutput template

/-! ### Every job -/

private def jobsOutput : Atom :=
  a "ProgramObservation"
    [a "LCons" [a "ProgramJobObservation" [v "request", v "state", v "receipts"], v "later"], v "all"]

private def jobsAppend : Atom :=
  a "let" [v "all", a "gslt:automata:append" [v "receipts", v "laterReceipts"], jobsOutput]

private def jobsTail : Atom :=
  a "let" [a "ProgramObservation" [v "later", v "laterReceipts"],
    a "gslt:program:resume-jobs" [v "rest", v "extra"], jobsAppend]

private def jobsCons : Atom :=
  a "let" [a "ProgramJobObservation" [v "request", v "state", v "receipts"],
    a "gslt:program:resume-job" [v "observation", v "extra"], jobsTail]

private def jobsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "ProgramObservation" [.symbol "LNil", .symbol "LNil"]),
   (a "LCons" [v "observation", v "rest"], jobsCons)]

private theorem resume_jobs_shape : (equation .resumeJobs).body =
    a "case" [v "observations", .expression (jobsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The authored resumption continues every job in order and joins the new receipts. -/
theorem resume_jobs_returns (state : State) (program : ProgramRun)
    (finiteProvider : ∀ job ∈ program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ job ∈ program, job.Reachable) (extra : Nat) :
    PureReturns runtime [] state
      (a "gslt:program:resume-jobs" [encoded (encodeList JobRun.term program), number extra]) state
      (encoded (program.resume extra).term) := by
  induction program with
  | nil =>
      let caller := bindings .resumeJobs [encoded (.symbol "LNil"), number extra]
      apply helper_call .resumeJobs [] state _ [encoded (.symbol "LNil"), number extra] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [resume_jobs_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") jobsCases
        (a "ProgramObservation" [.symbol "LNil", .symbol "LNil"]) _
      · exact variable_returns runtime caller state "observations"
      · simp [caller, bindings, Helper.names, jobsCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have template : PureData.Template runtime (a "ProgramObservation" [.symbol "LNil", .symbol "LNil"]) := by
          resumption_template
        exact PureData.template_return runtime caller state _ template
  | cons job rest ih =>
      let value := encoded (encodeList JobRun.term (job :: rest))
      let caller := bindings .resumeJobs [value, number extra]
      let selected :=
        [("rest", encoded (encodeList JobRun.term rest)), ("observation", encoded job.term)] ++ caller
      let resumed := job.resume extra
      let first :=
        [("receipts", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm resumed.receipts)),
         ("state", encoded (PremiseOperationsExecution.GeneralExecution.stateTerm resumed.state)),
         ("request", encoded (requestTerm resumed.request.val))] ++ selected
      let later :=
        [("laterReceipts", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
           (ProgramRun.resume rest extra).aggregate)),
         ("later", encoded (encodeList JobRun.term (ProgramRun.resume rest extra)))] ++ first
      let combined := encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        (resumed.receipts ++ (ProgramRun.resume rest extra).aggregate))
      let finished := ("all", combined) :: later
      apply helper_call .resumeJobs [] state _ [value, number extra] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [resume_jobs_shape]
      apply branch_returns caller selected state _ value jobsCases jobsCons _
      · exact variable_returns runtime caller state "observations"
      · simp [selected, caller, value, bindings, Helper.names, jobsCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded, CettaWireAtom.encode]
      · unfold jobsCons
        apply let_returns runtime selected first state state state _ _ jobsTail (encoded resumed.term) _
        · apply helper_capture .resumeJob selected state [v "observation", v "extra"]
            [encoded job.term, number extra] _ rfl
          · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
          · exact resume_job_returns state job (finiteProvider job List.mem_cons_self) (reachable job List.mem_cons_self) extra
        · simp [first, selected, caller, bindings, Helper.names, JobRun.term, resumed,
            SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
        · unfold jobsTail
          apply let_returns runtime first later state state state _ _ jobsAppend
            (encoded (ProgramRun.resume rest extra).term) _
          · apply helper_capture .resumeJobs first state [v "rest", v "extra"]
              [encoded (encodeList JobRun.term rest), number extra] _ rfl
            · simp [first, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
            · exact ih (fun other member => finiteProvider other (List.mem_cons_of_mem _ member))
                (fun other member => reachable other (List.mem_cons_of_mem _ member))
          · simp [later, first, selected, caller, bindings, Helper.names, ProgramRun.term,
              SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          · unfold jobsAppend
            apply named_let_returns later state "all" _ combined
            · simp [later, first, selected, caller, bindings, Helper.names, Subst.lookup]
            · apply driver_returns (by rfl)
              apply GeneralProgramDriverExecution.append_returns later state resumed.receipts
                (ProgramRun.resume rest extra).aggregate "receipts" "laterReceipts"
              simp [later, first, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
            · have template : PureData.Template runtime jobsOutput := by
                unfold jobsOutput
                resumption_template
              simpa [jobsOutput, ProgramRun.term, ProgramRun.resume, ProgramRun.aggregate, JobRun.term,
                finished, combined, later, first, selected, caller, bindings, Helper.names, encodeList,
                resumed, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup]
                using PureData.template_return runtime finished state jobsOutput template

/-! ### The program -/

private def resumeCases : SpaceSemantics.Cases :=
  [(a "ProgramObservation" [v "observations", v "snapshot"],
    a "gslt:program:resume-jobs" [v "observations", v "extra"])]

private theorem resume_shape : (equation .resume).body =
    a "case" [v "observation", .expression (resumeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

def resumeQuery (program : ProgramRun) (extra : Nat) : Atom :=
  a "gslt:program:resume" [encoded program.term, number extra]

/-- **The authored resumption of a program run.** It continues every job from its retained
state and reads the receipts again; it never restarts a job. -/
theorem resume_returns (state : State) (program : ProgramRun)
    (finiteProvider : ∀ job ∈ program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ job ∈ program, job.Reachable) (extra : Nat) :
    PureReturns runtime [] state (resumeQuery program extra) state (encoded (program.resume extra).term) := by
  let caller := bindings .resume [encoded program.term, number extra]
  let selected :=
    [("snapshot", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm program.aggregate)),
     ("observations", encoded (encodeList JobRun.term program))] ++ caller
  apply helper_call .resume [] state _ [encoded program.term, number extra] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [resume_shape]
  apply branch_returns caller selected state _ (encoded program.term) resumeCases
    (a "gslt:program:resume-jobs" [v "observations", v "extra"]) _
  · exact variable_returns runtime caller state "observation"
  · simp [selected, caller, bindings, Helper.names, resumeCases, ProgramRun.term,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · apply helper_capture .resumeJobs selected state [v "observations", v "extra"]
      [encoded (encodeList JobRun.term program), number extra] _ rfl
    · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
    · exact resume_jobs_returns state program finiteProvider reachable extra

theorem resume_completed_iff (state after : State) (program : ProgramRun)
    (finiteProvider : ∀ job ∈ program, job.request.val.environment.provider.dynamicRelations = [])
    (reachable : ∀ job ∈ program, job.Reachable) (extra : Nat) (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run runtime evaluatorFuel
      {state, control := .evaluate [] (resumeQuery program extra)} = .complete after answers input output) ↔
      after = state ∧ answers = [encoded (program.resume extra).term] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _ (resume_returns state program finiteProvider reachable extra)
    after answers input output

/-- **Exact resumption of the driver's observation.** Resuming the actual observation of a job
enumeration with `extra` more work per job gives the driver's observation of the same jobs with
`extra` more budget each. -/
theorem resume_program_returns (state : State) (jobs : List Invocation)
    (finiteProvider : ∀ job ∈ jobs, job.1.val.environment.provider.dynamicRelations = []) (extra : Nat) :
    PureReturns runtime [] state
      (a "gslt:program:resume" [encoded (GeneralProgramDriverExecution.programObservationTerm jobs), number extra])
      state (encoded (GeneralProgramDriverExecution.programObservationTerm
        (jobs.map fun job => (job.1, job.2 + extra)))) := by
  have finiteRuns : ∀ job ∈ ProgramRun.ofInvocations jobs,
      job.request.val.environment.provider.dynamicRelations = [] := by
    intro job member
    obtain ⟨invocation, present, same⟩ := List.mem_map.mp member
    cases same
    exact finiteProvider invocation present
  have resumed := resume_returns state (ProgramRun.ofInvocations jobs) finiteRuns
    (ProgramRun.ofInvocations_reachable jobs) extra
  rw [ProgramRun.ofInvocations_resume, ProgramRun.ofInvocations_term] at resumed
  simpa only [resumeQuery, ProgramRun.ofInvocations_term] using resumed

/-! ## The authored publication -/

private def completeRow : Atom :=
  a "LCons" [a "ProgramJobObservation" [v "request",
    a "PremiseState" [.symbol "LNil", v "answers", .symbol "LNil", v "work"], v "receipts"], v "rest"]

private def blockedRow : Atom :=
  a "LCons" [a "ProgramJobObservation" [v "request",
    a "PremiseState" [.symbol "LNil", v "answers", v "unresolved", v "work"], v "receipts"], v "rest"]

private def pendingRow : Atom :=
  a "LCons" [a "ProgramJobObservation" [v "request", v "state", v "receipts"], v "rest"]

private def publishedOutput : Atom := a "ProgramPublication" [v "all", v "status"]

private def publishedAppend : Atom :=
  a "let" [v "all", a "gslt:automata:append" [v "receipts", v "later"], publishedOutput]

private def publishedTail : Atom :=
  a "let" [a "ProgramPublication" [v "later", v "status"],
    a "gslt:program:publication-from" [v "rest"], publishedAppend]

private def publicationCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationComplete"]),
   (completeRow, publishedTail),
   (blockedRow, a "ProgramPublication" [v "receipts", .symbol "ProgramPublicationBlocked"]),
   (pendingRow, a "ProgramPublication" [v "receipts", .symbol "ProgramPublicationPending"])]

private theorem publication_from_shape : (equation .publicationFrom).body =
    a "case" [v "observations",
      .expression (publicationCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The authored publication releases complete jobs in order and stops at the first job that
is not complete, reading each job's own state. -/
theorem publication_from_returns (state : State) (program : ProgramRun) :
    PureReturns runtime [] state
      (a "gslt:program:publication-from" [encoded (encodeList JobRun.term program)]) state
      (encoded program.publicationTerm) := by
  induction program with
  | nil =>
      let caller := bindings .publicationFrom [encoded (.symbol "LNil")]
      apply helper_call .publicationFrom [] state _ [encoded (.symbol "LNil")] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [publication_from_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") publicationCases
        (a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationComplete"]) _
      · exact variable_returns runtime caller state "observations"
      · simp [caller, bindings, Helper.names, publicationCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have template : PureData.Template runtime
            (a "ProgramPublication" [.symbol "LNil", .symbol "ProgramPublicationComplete"]) := by
          resumption_template
        exact PureData.template_return runtime caller state _ template
  | cons job rest ih =>
      let value := encoded (encodeList JobRun.term (job :: rest))
      let caller := bindings .publicationFrom [value]
      let receipts := encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm job.receipts)
      let answers := encoded (encodeList PremiseOperationsExecution.GeneralExecution.resultTerm job.state.answers)
      let work := encoded (.natural job.state.work)
      let request := encoded (requestTerm job.request.val)
      let restValue := encoded (encodeList JobRun.term rest)
      apply helper_call .publicationFrom [] state _ [value] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [publication_from_shape]
      by_cases agendaEmpty : job.state.agenda = []
      · by_cases unresolvedEmpty : job.state.unresolved = []
        · have done : job.complete = true := by simp [JobRun.complete, agendaEmpty, unresolvedEmpty]
          let selected :=
            [("rest", restValue), ("receipts", receipts), ("work", work), ("answers", answers),
             ("request", request)] ++ caller
          let tail :=
            [("status", encoded (ProgramRun.statusTerm (ProgramRun.status rest))),
             ("later", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (ProgramRun.publication rest)))] ++
              selected
          let combined := encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
            (job.receipts ++ (ProgramRun.publication rest)))
          let finished := ("all", combined) :: tail
          apply branch_returns caller selected state _ value publicationCases publishedTail _
          · exact variable_returns runtime caller state "observations"
          · simp only [value, encodeList, JobRun.term, PremiseOperationsExecution.GeneralExecution.stateTerm,
              PremiseSchedulerExecution.schedulerStateTerm, agendaEmpty, unresolvedEmpty]
            simp [selected, caller, receipts, answers, work, request, restValue, bindings, Helper.names,
              publicationCases, completeRow, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, encoded, CettaWireAtom.encode,
              CettaWireAtom.encodeMany]
          · unfold publishedTail
            apply let_returns runtime selected tail state state state _ _ publishedAppend
              (encoded (ProgramRun.publicationTerm rest)) _
            · apply helper_capture .publicationFrom selected state [v "rest"] [restValue] _ rfl
              · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
              · exact ih
            · simp [tail, selected, caller, bindings, Helper.names, ProgramRun.publicationTerm,
                SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · unfold publishedAppend
              apply named_let_returns tail state "all" _ combined
              · simp [tail, selected, caller, bindings, Helper.names, Subst.lookup]
              · apply driver_returns (by rfl)
                apply GeneralProgramDriverExecution.append_returns tail state job.receipts (ProgramRun.publication rest)
                  "receipts" "later"
                simp [tail, selected, caller, receipts, bindings, Helper.names, applySubst, Subst.lookup]
              · have template : PureData.Template runtime publishedOutput := by
                  unfold publishedOutput
                  resumption_template
                simpa [publishedOutput, ProgramRun.publicationTerm, ProgramRun.publication, ProgramRun.status,
                  done, finished, combined, tail, selected, caller, bindings, Helper.names,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
                  Subst.lookup]
                  using PureData.template_return runtime finished state publishedOutput template
        · obtain ⟨obligation, obligations, unresolved⟩ := List.exists_cons_of_ne_nil unresolvedEmpty
          have open_ : job.complete = false := by simp [JobRun.complete, unresolved]
          let unresolvedValue := encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm
            (obligation :: obligations))
          let selected :=
            [("rest", restValue), ("receipts", receipts), ("work", work), ("unresolved", unresolvedValue),
             ("answers", answers), ("request", request)] ++ caller
          apply branch_returns caller selected state _ value publicationCases
            (a "ProgramPublication" [v "receipts", .symbol "ProgramPublicationBlocked"]) _
          · exact variable_returns runtime caller state "observations"
          · simp only [value, encodeList, JobRun.term, PremiseOperationsExecution.GeneralExecution.stateTerm,
              PremiseSchedulerExecution.schedulerStateTerm, agendaEmpty, unresolved]
            simp [selected, caller, receipts, answers, work, request, restValue, unresolvedValue,
              bindings, Helper.names, publicationCases, completeRow, blockedRow,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          · have template : PureData.Template runtime
                (a "ProgramPublication" [v "receipts", .symbol "ProgramPublicationBlocked"]) := by
              resumption_template
            simpa [ProgramRun.publicationTerm, ProgramRun.publication, ProgramRun.status, ProgramRun.statusTerm,
              open_, agendaEmpty, selected, caller, receipts, bindings, Helper.names,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
              Subst.lookup]
              using PureData.template_return runtime selected state _ template
      · obtain ⟨task, tasks, agenda⟩ := List.exists_cons_of_ne_nil agendaEmpty
        have open_ : job.complete = false := by simp [JobRun.complete, agenda]
        let stateValue := encoded (PremiseOperationsExecution.GeneralExecution.stateTerm job.state)
        let selected :=
          [("rest", restValue), ("receipts", receipts), ("state", stateValue), ("request", request)] ++ caller
        apply branch_returns caller selected state _ value publicationCases
          (a "ProgramPublication" [v "receipts", .symbol "ProgramPublicationPending"]) _
        · exact variable_returns runtime caller state "observations"
        · -- Every list of the state is put in constructor form before any pattern is matched.
          by_cases unresolvedEmpty : job.state.unresolved = []
          · simp only [value, encodeList, JobRun.term, PremiseOperationsExecution.GeneralExecution.stateTerm,
              PremiseSchedulerExecution.schedulerStateTerm, agenda, unresolvedEmpty]
            simp [selected, caller, receipts, request, restValue, stateValue,
              PremiseOperationsExecution.GeneralExecution.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
              agenda, unresolvedEmpty, bindings, Helper.names, publicationCases, completeRow, blockedRow, pendingRow,
              encodeList, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          · obtain ⟨obligation, obligations, unresolved⟩ := List.exists_cons_of_ne_nil unresolvedEmpty
            simp only [value, encodeList, JobRun.term, PremiseOperationsExecution.GeneralExecution.stateTerm,
              PremiseSchedulerExecution.schedulerStateTerm, agenda, unresolved]
            simp [selected, caller, receipts, request, restValue, stateValue,
              PremiseOperationsExecution.GeneralExecution.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
              agenda, unresolved, bindings, Helper.names, publicationCases, completeRow, blockedRow, pendingRow,
              encodeList, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
        · have template : PureData.Template runtime
              (a "ProgramPublication" [v "receipts", .symbol "ProgramPublicationPending"]) := by
            resumption_template
          simpa [ProgramRun.publicationTerm, ProgramRun.publication, ProgramRun.status, ProgramRun.statusTerm,
            open_, agenda, selected, caller, receipts, bindings, Helper.names,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup]
            using PureData.template_return runtime selected state _ template

private def publicationTopCases : SpaceSemantics.Cases :=
  [(a "ProgramObservation" [v "observations", v "snapshot"],
    a "gslt:program:publication-from" [v "observations"])]

private theorem publication_shape : (equation .publication).body =
    a "case" [v "observation", .expression (publicationTopCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

def publicationQuery (program : ProgramRun) : Atom :=
  a "gslt:program:publication" [encoded program.term]

/-- **The authored publication of a program run.** -/
theorem publication_returns (state : State) (program : ProgramRun) :
    PureReturns runtime [] state (publicationQuery program) state (encoded program.publicationTerm) := by
  let caller := bindings .publication [encoded program.term]
  let selected :=
    [("snapshot", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm program.aggregate)),
     ("observations", encoded (encodeList JobRun.term program))] ++ caller
  apply helper_call .publication [] state _ [encoded program.term] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [publication_shape]
  apply branch_returns caller selected state _ (encoded program.term) publicationTopCases
    (a "gslt:program:publication-from" [v "observations"]) _
  · exact variable_returns runtime caller state "observation"
  · simp [selected, caller, bindings, Helper.names, publicationTopCases, ProgramRun.term,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · apply helper_capture .publicationFrom selected state [v "observations"]
      [encoded (encodeList JobRun.term program)] _ rfl
    · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
    · exact publication_from_returns state program

theorem publication_completed_iff (state after : State) (program : ProgramRun)
    (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run runtime evaluatorFuel
      {state, control := .evaluate [] (publicationQuery program)} = .complete after answers input output) ↔
      after = state ∧ answers = [encoded program.publicationTerm] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _ (publication_returns state program)
    after answers input output

/-- Whatever the actual run of the publication prints as its receipts is the model's publication. -/
theorem published_receipts_eq (state : State) (program : ProgramRun)
    (published : List GeneralRuleJobs.Receipt) (status : Term)
    (printed : PureReturns runtime [] state (publicationQuery program) state
      (encoded (.application "ProgramPublication"
        [encodeList ScopedRuleJobReadoutExecution.receiptTerm published, status]))) :
    published = program.publication := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel runtime [] state state _ _ printed
  have same := ((publication_completed_iff state state program _ [] []).mp ⟨fuel, completed⟩).2.1
  simp only [List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode, ProgramRun.publicationTerm,
    Term.application.injEq, true_and] at same
  exact encodeList_injective _ ScopedRuleJobReadoutExecution.receiptTerm_injective same.1

/-- **Printed publications grow by prefix.** For a run reachable from the original job starts,
the receipts the actual publication prints after any resumption extend the receipts it printed
before. -/
theorem published_prefix (state : State) (program : ProgramRun) (extra : Nat)
    (before after : List GeneralRuleJobs.Receipt) (beforeStatus afterStatus : Term)
    (printed : PureReturns runtime [] state (publicationQuery program) state
      (encoded (.application "ProgramPublication"
        [encodeList ScopedRuleJobReadoutExecution.receiptTerm before, beforeStatus])))
    (resumed : PureReturns runtime [] state (publicationQuery (program.resume extra)) state
      (encoded (.application "ProgramPublication"
        [encodeList ScopedRuleJobReadoutExecution.receiptTerm after, afterStatus]))) :
    before <+: after := by
  rw [published_receipts_eq state program before beforeStatus printed,
    published_receipts_eq state (program.resume extra) after afterStatus resumed]
  exact ProgramRun.publication_prefix program extra

/-! ## Retained publication delivery

The authored publication returns the whole prefix. A sequential consumer
keeps the common occurrence cursor to deliver only its new suffix. The
receipt's existing injective wire encoding supplies executable equality.
This delivery law does not grant exclusive ownership of a copied cursor or
atomic commitment of an external effect.
-/

namespace Delivery

open Mettapedia.Machines Mettapedia.Machines.ExecutionHistoryReadout

private instance : DecidableEq GeneralRuleJobs.Receipt :=
  fun _ _ => decidable_of_iff _ ScopedRuleJobReadoutExecution.receiptTerm_injective.eq_iff

def advance {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra : Nat) :=
  Publication.advanceValues producer cursor (program.resume extra).publication

/-- Existing ordered publication supplies the cursor's growth condition.
The exact result retains distinct receipt occurrences and absolute ordinals. -/
theorem advance_exact {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra : Nat)
    (consumed : cursor.next = cursor.captured.entries.length)
    (prior : cursor.captured.entries <+: program.publication) :
    advance producer cursor program extra =
      (⟨{ cursor.captured with entries := (program.resume extra).publication },
         (program.resume extra).publication.length⟩,
        some (answerEvents cursor.next producer
          ((program.resume extra).publication.drop cursor.next))) :=
  Publication.advanceValues_accepted producer cursor _ consumed
    (prior.trans (ProgramRun.publication_prefix program extra))

/-- The actual authored publication's printed receipts enter the same
delivery contract; it is not an independently assumed reference readout. -/
theorem advance_printed {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra : Nat) (state : State)
    (published : List GeneralRuleJobs.Receipt) (status : Term)
    (printed : PureReturns runtime [] state (publicationQuery (program.resume extra)) state
      (encoded (.application "ProgramPublication"
        [encodeList ScopedRuleJobReadoutExecution.receiptTerm published, status]))) :
    advance producer cursor program extra = Publication.advanceValues producer cursor published := by
  rw [published_receipts_eq state (program.resume extra) published status printed]
  rfl

/-- Reading the same completed delivery again emits no new occurrence.
Reusing an earlier copied cursor is intentionally outside this guarantee. -/
theorem advance_replay {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra : Nat)
    (consumed : cursor.next = cursor.captured.entries.length)
    (prior : cursor.captured.entries <+: program.publication) :
    advance producer (advance producer cursor program extra).1 (program.resume extra) 0 =
      ((advance producer cursor program extra).1, some []) := by
  have zero : (program.resume extra).resume 0 = program.resume extra := by
    exact (program.resume extra).trajectory.at_zero
  unfold advance
  rw [zero]
  have accepted := Publication.advanceValues_accepted producer cursor
    (program.resume extra).publication consumed
    (prior.trans (ProgramRun.publication_prefix program extra))
  rw [accepted]
  apply Publication.advance_replay

/-- Budget partitioning preserves both the retained cursor and the full
ordered delivery. The boundary between batches may move; equal receipts at
different absolute ordinals remain separate occurrences. -/
theorem advance_partition {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (first extra : Nat)
    (consumed : cursor.next = cursor.captured.entries.length)
    (prior : cursor.captured.entries <+: program.publication) :
    let earlier := advance producer cursor program first
    let later := advance producer earlier.1 (program.resume first) extra
    let together := advance producer cursor program (first + extra)
    later.1 = together.1 ∧
      earlier.2.bind (fun before => later.2.map (before ++ ·)) = together.2 := by
  have firstPrefix := prior.trans (ProgramRun.publication_prefix program first)
  have nextPrefix := ProgramRun.publication_prefix (program.resume first) extra
  obtain ⟨before, firstPublication⟩ := firstPrefix
  obtain ⟨after, nextPublication⟩ := nextPrefix
  dsimp only
  unfold advance
  rw [← ProgramRun.resume_add, ← firstPublication, ← nextPublication, ← firstPublication]
  simpa only [List.append_assoc] using
    Publication.advanceValues_partition producer cursor before after consumed

/-- Bounded delivery uses the source session's actual publication lineage.
The work allowance advances the retained jobs; the independent answer limit
selects only newly committed receipts. The unpublished work stays in the
returned/resumed `ProgramRun`, not in a rebuilt source term. -/
def bounded {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (lineage : StoreReadToken StreamId Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra limit : Nat) :=
  Publication.advanceBounded producer cursor
    ⟨lineage.storeId, lineage.revision, (program.resume extra).publication⟩ limit

theorem bounded_exact {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (lineage : StoreReadToken StreamId Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra limit : Nat)
    (consumed : cursor.next = cursor.captured.entries.length)
    (sameRun : cursor.captured.readToken = lineage)
    (prior : cursor.captured.entries <+: program.publication) :
    bounded producer lineage cursor program extra limit =
      (⟨{ cursor.captured with entries := cursor.captured.entries ++
          ((program.resume extra).publication.drop cursor.next).take limit },
        cursor.next + (((program.resume extra).publication.drop cursor.next).take limit).length⟩,
       some (answerEvents cursor.next producer
         (((program.resume extra).publication.drop cursor.next).take limit))) :=
  Publication.advanceBounded_accepted producer cursor _ limit
    ⟨consumed, sameRun, prior.trans (ProgramRun.publication_prefix program extra)⟩

/-- Receipt data printed by the actual authored publication supplies this
bounded delivery; source validity or a guessed answer list is not consulted. -/
theorem bounded_printed {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (lineage : StoreReadToken StreamId Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra limit : Nat) (state : State)
    (published : List GeneralRuleJobs.Receipt) (status : Term)
    (printed : PureReturns runtime [] state (publicationQuery (program.resume extra)) state
      (encoded (.application "ProgramPublication"
        [encodeList ScopedRuleJobReadoutExecution.receiptTerm published, status]))) :
    bounded producer lineage cursor program extra limit =
      Publication.advanceBounded producer cursor
        ⟨lineage.storeId, lineage.revision, published⟩ limit := by
  rw [published_receipts_eq state (program.resume extra) published status printed]
  rfl

theorem bounded_zero {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (lineage : StoreReadToken StreamId Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra : Nat)
    (consumed : cursor.next = cursor.captured.entries.length)
    (sameRun : cursor.captured.readToken = lineage)
    (prior : cursor.captured.entries <+: program.publication) :
    bounded producer lineage cursor program extra 0 = (cursor, some []) :=
  Publication.advanceBounded_zero producer cursor _
    ⟨consumed, sameRun, prior.trans (ProgramRun.publication_prefix program extra)⟩

/-- A foreign continuation is refused even if its receipt payloads happen
to agree, and even if the requested delivery limit is zero. -/
theorem bounded_foreign_refused {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (lineage : StoreReadToken StreamId Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra limit : Nat)
    (foreign : cursor.captured.readToken ≠ lineage) :
    bounded producer lineage cursor program extra limit = (cursor, none) :=
  Publication.advanceBounded_foreign_refused producer cursor _ limit foreign

/-- The cursor still names a genuine prefix and remains usable after further
retained work extends the same publication. Receipt equality does not merge
their distinct absolute positions. -/
theorem bounded_can_continue {StreamId : Type} [DecidableEq StreamId] (producer : Nat)
    (lineage : StoreReadToken StreamId Nat)
    (cursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (program : ProgramRun) (extra limit later : Nat)
    (consumed : cursor.next = cursor.captured.entries.length)
    (sameRun : cursor.captured.readToken = lineage)
    (prior : cursor.captured.entries <+: program.publication) :
    Publication.Compatible (bounded producer lineage cursor program extra limit).1
      ⟨lineage.storeId, lineage.revision, ((program.resume extra).resume later).publication⟩ := by
  have accepted := Publication.advanceBounded_compatible producer cursor
    (⟨lineage.storeId, lineage.revision, (program.resume extra).publication⟩ :
      RevisionedStoreView StreamId Nat GeneralRuleJobs.Receipt) limit
    ⟨consumed, sameRun, prior.trans (ProgramRun.publication_prefix program extra)⟩
  exact ⟨accepted.1, accepted.2.1,
    accepted.2.2.trans (ProgramRun.publication_prefix (program.resume extra) later)⟩

end Delivery

/-- Once every job is complete, the publication prints the whole readout and reports completion. -/
theorem publication_of_complete (state : State) (program : ProgramRun)
    (complete : ∀ job ∈ program, job.complete = true) :
    PureReturns runtime [] state (publicationQuery program) state
      (encoded (.application "ProgramPublication"
        [encodeList ScopedRuleJobReadoutExecution.receiptTerm program.aggregate,
         .symbol "ProgramPublicationComplete"])) := by
  have published := publication_returns state program
  rw [ProgramRun.publicationTerm, ProgramRun.publication_complete program complete,
    (ProgramRun.status_complete_iff program).mpr complete] at published
  exact published

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramResumptionExecution
