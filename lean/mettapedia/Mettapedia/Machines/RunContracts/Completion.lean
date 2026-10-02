import Mettapedia.Machines.RunObservation
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Demand-relative completion and owned-resource finalization

An observation may finish by exhaustion or by deliberately satisfying finite
demand. Existing depth cuts and external interruptions remain `RunStop` values;
neither is reclassified as deliberate demand satisfaction. Language payloads
are generic data. Faults are a separate control constructor.

A streaming monitor counts answer occurrences without retaining them. Worker
identities, not just their count, prevent a duplicate settlement from concealing
another live worker. Output and cleanup each require explicit acknowledgement;
a later acknowledgement cannot erase a recorded failure. The monitor is proved
against a separate occurrence-list completion relation. This is an abstract
protocol theorem, not native CLI correspondence or a liveness guarantee.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.Completion

inductive Demand where
  | exhaustive
  | prefix (count : Nat)
  deriving DecidableEq, Repr

/-- A deliberate producer stop is distinct from unexpected interruption, even
when enough answers have already arrived. No fault identity is prioritized. -/
inductive ProducerStop (State Fault : Type) where
  | observed (stop : RunStop State)
  | demandSatisfied
  | fault (value : Fault)

/-- Declarative completion uses the actual occurrence list. Bounded observers
must neither overproduce nor call a cutoff an exhausted short result. -/
inductive ObservationComplete {State Fault Answer : Type} :
    Demand → List Answer → ProducerStop State Fault → Prop where
  | exhaustive (answers : List Answer) :
      ObservationComplete .exhaustive answers (.observed .complete)
  | satisfied (count : Nat) (answers : List Answer) (exactCount : answers.length = count) :
      ObservationComplete (.prefix count) answers .demandSatisfied
  | exhausted (count : Nat) (answers : List Answer) (within : answers.length ≤ count) :
      ObservationComplete (.prefix count) answers (.observed .complete)

/-- Executable classifier uses only the streamed count and tagged stop. -/
def completeB {State Fault : Type} : Demand → Nat → ProducerStop State Fault → Bool
  | .exhaustive, _, .observed .complete => true
  | .prefix limit, count, .observed .complete => count ≤ limit
  | .prefix limit, count, .demandSatisfied => count == limit
  | _, _, _ => false

theorem completeB_iff {State Fault Answer : Type} (demand : Demand)
    (answers : List Answer) (stop : ProducerStop State Fault) :
    completeB demand answers.length stop = true ↔ ObservationComplete demand answers stop := by
  constructor
  · cases demand with
    | exhaustive =>
        cases stop with
        | demandSatisfied => simp [completeB]
        | fault value => simp [completeB]
        | observed stop =>
            cases stop <;> simp only [completeB, Bool.false_eq_true, false_implies]
            exact fun _ => ObservationComplete.exhaustive answers
    | «prefix» count =>
        cases stop with
        | demandSatisfied => simpa [completeB] using ObservationComplete.satisfied count answers
        | fault value => simp [completeB]
        | observed stop =>
            cases stop <;> simp only [completeB, Bool.false_eq_true, false_implies]
            exact fun within => ObservationComplete.exhausted count answers (of_decide_eq_true within)
  · intro complete
    cases complete <;> simp_all [completeB]

inductive ActionStatus where
  | pending | success | failure
  deriving DecidableEq, Repr

/-- Failures are sticky; completion acknowledgement resolves pending status. -/
def ActionStatus.acknowledge : ActionStatus → ActionStatus
  | .pending | .success => .success
  | .failure => .failure

/-- Later work invalidates an earlier success acknowledgement, while failures
remain sticky. Output completion is relative to the current answer prefix. -/
def ActionStatus.noteWork : ActionStatus → ActionStatus
  | .pending | .success => .pending
  | .failure => .failure

@[simp] theorem ActionStatus.noteWork_idempotent (status : ActionStatus) :
    status.noteWork.noteWork = status.noteWork := by cases status <;> rfl

inductive Event (Answer : Type) where
  | answer (value : Answer)
  | workerStarted (id : Nat)
  | workerSettled (id : Nat)
  | outputComplete | outputFailed
  | cleanupComplete | cleanupFailed
  deriving DecidableEq, Repr

structure Summary where
  answerCount : Nat
  startedWorkers : Finset Nat
  pendingWorkers : Finset Nat
  output : ActionStatus
  cleanup : ActionStatus
  protocolOK : Bool
  deriving DecidableEq

def Summary.initial : Summary := ⟨0, ∅, ∅, .pending, .pending, true⟩

def consume {Answer : Type} (summary : Summary) : Event Answer → Summary
  | .answer _ =>
      {summary with answerCount := summary.answerCount + 1
                    output := summary.output.noteWork}
  | .workerStarted id =>
      {summary with startedWorkers := insert id summary.startedWorkers
                    pendingWorkers := insert id summary.pendingWorkers
                    cleanup := summary.cleanup.noteWork
                    protocolOK := summary.protocolOK && decide (id ∉ summary.startedWorkers)}
  | .workerSettled id =>
      {summary with pendingWorkers := summary.pendingWorkers.erase id
                    cleanup := summary.cleanup.noteWork
                    protocolOK := summary.protocolOK && decide (id ∈ summary.pendingWorkers)}
  | .outputComplete => {summary with output := summary.output.acknowledge}
  | .outputFailed => {summary with output := .failure}
  | .cleanupComplete => {summary with cleanup := summary.cleanup.acknowledge}
  | .cleanupFailed => {summary with cleanup := .failure}

def scan {Answer : Type} (events : List (Event Answer)) (initial : Summary := .initial) : Summary :=
  events.foldl consume initial

/-- Independent data projection ignores resource and reporting events. -/
def occurrences {Answer : Type} (events : List (Event Answer)) : List Answer :=
  events.filterMap fun event => match event with
    | .answer value => some value
    | _ => none

/-- The incremental counter agrees with a separate occurrence-list observer. -/
theorem scan_count {Answer : Type} (events : List (Event Answer)) (initial : Summary) :
    (scan events initial).answerCount = initial.answerCount + (occurrences events).length := by
  induction events generalizing initial with
  | nil => simp [scan, occurrences]
  | cons event rest ih =>
      change (scan rest (consume initial event)).answerCount = _
      rw [ih]
      cases event <;> simp [consume, occurrences, Nat.add_assoc, Nat.add_comm]

/-- Completion of evaluation and success of external finalization are
independent conjuncts. Pending owned workers prohibit normal completion. -/
def commandSucceeded {State Fault : Type} (demand : Demand)
    (stop : ProducerStop State Fault) (summary : Summary) : Bool :=
  completeB demand summary.answerCount stop &&
    summary.protocolOK && (summary.pendingWorkers == ∅) &&
    (summary.output == .success) && (summary.cleanup == .success)

/-- Executable monitor correspondence with the declarative observation and
resource/reporting contract. The data side uses occurrences, not counters.
The resource conjuncts are the monitor's final fields; the separate worker and
sticky-failure lemmas below establish trace properties of those fields. -/
theorem commandSucceeded_iff {State Fault Answer : Type} (demand : Demand)
    (stop : ProducerStop State Fault) (events : List (Event Answer)) :
    commandSucceeded demand stop (scan events) = true ↔
      ObservationComplete demand (occurrences events) stop ∧
      (scan events).protocolOK = true ∧ (scan events).pendingWorkers = ∅ ∧
      (scan events).output = .success ∧ (scan events).cleanup = .success := by
  have counts : (scan events).answerCount = (occurrences events).length := by
    simpa only [Summary.initial, Nat.zero_add] using scan_count events Summary.initial
  simp only [commandSucceeded, Bool.and_eq_true, beq_iff_eq, counts]
  rw [completeB_iff]
  tauto

/-- Sequential ingestion is compositional; a caller need not keep the event
list after transferring its checked summary to the next chunk. -/
theorem scan_append {Answer : Type} (first second : List (Event Answer)) (initial : Summary) :
    scan (first ++ second) initial = scan second (scan first initial) := by
  simp only [scan, List.foldl_append]

/-- Reference admission reads event history directly. It does not consult
monitor sets or flags. Worker identities are unique for the whole run. -/
def ResourceAdmissible {Answer : Type} (history : List (Event Answer)) : Event Answer → Prop
  | .workerStarted id => Event.workerStarted id ∉ history
  | .workerSettled id => Event.workerStarted id ∈ history ∧ Event.workerSettled id ∉ history
  | _ => True

inductive LegalResourceTrace {Answer : Type} : List (Event Answer) → Prop where
  | nil : LegalResourceTrace []
  | next {history : List (Event Answer)} {event : Event Answer}
      (prior : LegalResourceTrace history) (admitted : ResourceAdmissible history event) :
      LegalResourceTrace (history ++ [event])

/-- Independent history meanings for the two finite-set registers. -/
structure MatchesResourceHistory {Answer : Type} (history : List (Event Answer))
    (summary : Summary) : Prop where
  started : ∀ id, id ∈ summary.startedWorkers ↔ Event.workerStarted id ∈ history
  pending : ∀ id, id ∈ summary.pendingWorkers ↔
    Event.workerStarted id ∈ history ∧ Event.workerSettled id ∉ history
  settlementHasStart : ∀ id, Event.workerSettled id ∈ history → Event.workerStarted id ∈ history

private theorem history_step {Answer : Type} (history : List (Event Answer))
    (summary : Summary) (matching : MatchesResourceHistory history summary)
    (event : Event Answer) (admitted : ResourceAdmissible history event) :
    MatchesResourceHistory (history ++ [event]) (consume summary event) := by
  rcases matching with ⟨starts, pending, hasStart⟩
  cases event with
  | workerStarted worker =>
      have fresh : Event.workerStarted worker ∉ history := admitted
      have notSettled : Event.workerSettled worker ∉ history := fun member => fresh (hasStart worker member)
      constructor
      · intro id
        by_cases same : id = worker
        · subst id; simp [consume]
        · simpa [consume, same, Ne.symm same, List.mem_append] using starts id
      · intro id
        by_cases same : id = worker
        · subst id; simp [consume, notSettled]
        · simpa [consume, same, Ne.symm same, List.mem_append] using pending id
      · intro id settled
        have old : Event.workerSettled id ∈ history := by simpa using settled
        exact List.mem_append_left _ (hasStart id old)
  | workerSettled worker =>
      obtain ⟨started, fresh⟩ := admitted
      constructor
      · intro id
        simpa [consume, List.mem_append] using starts id
      · intro id
        by_cases same : id = worker
        · subst id; simp [consume]
        · simpa [consume, same, Ne.symm same, List.mem_append] using pending id
      · intro id settled
        simp only [List.mem_append, List.mem_singleton, Event.workerSettled.injEq] at settled
        rcases settled with old | same
        · exact List.mem_append_left _ (hasStart id old)
        · subst id; exact List.mem_append_left _ started
  | answer value | outputComplete | outputFailed | cleanupComplete | cleanupFailed =>
      constructor
      · intro id; simpa [consume, List.mem_append] using starts id
      · intro id; simpa [consume, List.mem_append] using pending id
      · intro id settled
        have old : Event.workerSettled id ∈ history := by simpa using settled
        exact List.mem_append_left _ (hasStart id old)

private theorem consume_protocol_iff {Answer : Type} (history : List (Event Answer))
    (summary : Summary) (matching : MatchesResourceHistory history summary)
    (event : Event Answer) :
    (consume summary event).protocolOK = true ↔
      summary.protocolOK = true ∧ ResourceAdmissible history event := by
  cases event <;> simp [consume, ResourceAdmissible, matching.started, matching.pending]

/-- A legal history produces exactly its reference pending/started ownership
and is accepted by the incremental monitor. -/
theorem legal_resource_monitor {Answer : Type} {events : List (Event Answer)}
    (legal : LegalResourceTrace events) :
    (scan events).protocolOK = true ∧ MatchesResourceHistory events (scan events) := by
  induction legal with
  | nil =>
      constructor
      · rfl
      · constructor <;> simp [scan, Summary.initial]
  | @next history event prior admitted ih =>
      obtain ⟨protocol, matching⟩ := ih
      rw [scan_append]
      change (consume (scan history) event).protocolOK = true ∧
        MatchesResourceHistory (history ++ [event]) (consume (scan history) event)
      exact ⟨(consume_protocol_iff history _ matching event).mpr ⟨protocol, admitted⟩,
        history_step history _ matching event admitted⟩

private theorem consume_protocol_requires_prior {Answer : Type} (summary : Summary)
    (event : Event Answer) (accepted : (consume summary event).protocolOK = true) :
    summary.protocolOK = true := by
  cases event <;> simp_all [consume]

/-- Conversely the monitor cannot certify a worker history rejected by the
independent start/settle protocol. -/
theorem monitor_resource_legal {Answer : Type} (events : List (Event Answer))
    (accepted : (scan events).protocolOK = true) : LegalResourceTrace events := by
  induction events using List.reverseRecOn with
  | nil => exact .nil
  | @append_singleton history event ih =>
      rw [scan_append] at accepted
      change (consume (scan history) event).protocolOK = true at accepted
      have priorOK := consume_protocol_requires_prior (scan history) event accepted
      have prior := ih priorOK
      have matching := (legal_resource_monitor prior).2
      exact .next prior ((consume_protocol_iff history _ matching event).mp accepted).2

/-- Exact reference correspondence for ownership protocol validity. -/
theorem protocolOK_iff_legal_resource_trace {Answer : Type} (events : List (Event Answer)) :
    (scan events).protocolOK = true ↔ LegalResourceTrace events :=
  ⟨monitor_resource_legal events, fun legal => (legal_resource_monitor legal).1⟩

/-- Under legal ownership protocol, every started worker is settled exactly
when the pending register is empty. -/
theorem no_pending_iff_all_settled {Answer : Type} (events : List (Event Answer))
    (legal : LegalResourceTrace events) :
    (scan events).pendingWorkers = ∅ ↔
      ∀ id, Event.workerStarted id ∈ events → Event.workerSettled id ∈ events := by
  have pending := (legal_resource_monitor legal).2.pending
  constructor
  · intro empty id started
    by_contra notSettled
    have member := (pending id).mpr ⟨started, notSettled⟩
    simp [empty] at member
  · intro settled
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro id member
    obtain ⟨started, notSettled⟩ := (pending id).mp member
    exact notSettled (settled id started)

/-- The strengthened command contract uses independent answer and ownership
histories. Output/cleanup fields are additionally governed by the sticky
failure and acknowledgement-invalidation laws below. -/
theorem commandSucceeded_reference_iff {State Fault Answer : Type} (demand : Demand)
    (stop : ProducerStop State Fault) (events : List (Event Answer)) :
    commandSucceeded demand stop (scan events) = true ↔
      ObservationComplete demand (occurrences events) stop ∧
      LegalResourceTrace events ∧
      (∀ id, Event.workerStarted id ∈ events → Event.workerSettled id ∈ events) ∧
      (scan events).output = .success ∧ (scan events).cleanup = .success := by
  rw [commandSucceeded_iff]
  constructor
  · rintro ⟨complete, protocol, empty, output, cleanup⟩
    have legal := monitor_resource_legal events protocol
    exact ⟨complete, legal, (no_pending_iff_all_settled events legal).mp empty, output, cleanup⟩
  · rintro ⟨complete, legal, settled, output, cleanup⟩
    exact ⟨complete, (legal_resource_monitor legal).1,
      (no_pending_iff_all_settled events legal).mpr settled, output, cleanup⟩

/-- Relevant work and acknowledgement events for one external action. -/
inductive ActionEvent where
  | work | acknowledged | failed
  deriving DecidableEq, Repr

def applyAction (status : ActionStatus) : ActionEvent → ActionStatus
  | .work => status.noteWork
  | .acknowledged => status.acknowledge
  | .failed => .failure

def runActions (events : List ActionEvent) (initial : ActionStatus) : ActionStatus :=
  events.foldl applyAction initial

/-- Independent history contract: failure never occurred, and the final
relevant event is acknowledgement. Thus it follows all relevant work. -/
def ActionHistorySucceeded (events : List ActionEvent) : Prop :=
  ActionEvent.failed ∉ events ∧ events.getLast? = some .acknowledged

/-- The action monitor is independently characterized by event history.
The failure test is global; otherwise the last relevant event determines
whether the current work has been acknowledged. -/
theorem runActions_history (events : List ActionEvent) :
    runActions events .pending =
      if ActionEvent.failed ∈ events then .failure
      else if events.getLast? = some .acknowledged then .success else .pending := by
  induction events using List.reverseRecOn with
  | nil => rfl
  | append_singleton history event ih =>
      rw [runActions, List.foldl_append]
      change applyAction (runActions history .pending) event = _
      rw [ih]
      by_cases failed : ActionEvent.failed ∈ history
      · cases event <;>
          simp [failed, applyAction, ActionStatus.noteWork, ActionStatus.acknowledge]
      · by_cases acknowledged : history.getLast? = some .acknowledged
        all_goals cases event <;>
          simp [failed, acknowledged, applyAction, ActionStatus.noteWork, ActionStatus.acknowledge]

theorem runActions_success_iff (events : List ActionEvent) :
    runActions events .pending = .success ↔ ActionHistorySucceeded events := by
  rw [runActions_history]
  unfold ActionHistorySucceeded
  by_cases failed : ActionEvent.failed ∈ events
  · simp [failed]
  · simp [failed]

/-- Only events affecting output are retained; worker administration is erased. -/
def outputAction {Answer : Type} : Event Answer → Option ActionEvent
  | .answer _ => some .work
  | .outputComplete => some .acknowledged
  | .outputFailed => some .failed
  | _ => none

/-- Both acquiring and settling owned work invalidate previous cleanup. -/
def cleanupAction {Answer : Type} : Event Answer → Option ActionEvent
  | .workerStarted _ | .workerSettled _ => some .work
  | .cleanupComplete => some .acknowledged
  | .cleanupFailed => some .failed
  | _ => none

def OutputHistorySucceeded {Answer : Type} (events : List (Event Answer)) : Prop :=
  ActionHistorySucceeded (events.filterMap outputAction)

def CleanupHistorySucceeded {Answer : Type} (events : List (Event Answer)) : Prop :=
  ActionHistorySucceeded (events.filterMap cleanupAction)

theorem scan_output_actions {Answer : Type} (events : List (Event Answer)) (initial : Summary) :
    (scan events initial).output = runActions (events.filterMap outputAction) initial.output := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      change (scan rest (consume initial event)).output = _
      rw [ih]
      cases event <;> rfl

theorem scan_cleanup_actions {Answer : Type} (events : List (Event Answer)) (initial : Summary) :
    (scan events initial).cleanup = runActions (events.filterMap cleanupAction) initial.cleanup := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      change (scan rest (consume initial event)).cleanup = _
      rw [ih]
      cases event <;> rfl

theorem output_history_iff {Answer : Type} (events : List (Event Answer)) :
    (scan events).output = .success ↔ OutputHistorySucceeded events := by
  rw [scan_output_actions]
  exact runActions_success_iff _

theorem cleanup_history_iff {Answer : Type} (events : List (Event Answer)) :
    (scan events).cleanup = .success ↔ CleanupHistorySucceeded events := by
  rw [scan_cleanup_actions]
  exact runActions_success_iff _

/-- End-to-end abstract contract: every condition on the right is stated
from independently observed answers, stop reason, or authored event history.
No right-hand predicate mentions the implementation summary. -/
theorem commandSucceeded_full_reference_iff {State Fault Answer : Type} (demand : Demand)
    (stop : ProducerStop State Fault) (events : List (Event Answer)) :
    commandSucceeded demand stop (scan events) = true ↔
      ObservationComplete demand (occurrences events) stop ∧
      LegalResourceTrace events ∧
      (∀ id, Event.workerStarted id ∈ events → Event.workerSettled id ∈ events) ∧
      OutputHistorySucceeded events ∧ CleanupHistorySucceeded events := by
  rw [commandSucceeded_reference_iff, output_history_iff, cleanup_history_iff]

/-- Failure acknowledgement is monotone under every later event. -/
theorem scan_preserves_output_failure {Answer : Type} (events : List (Event Answer))
    (initial : Summary) (failed : initial.output = .failure) :
    (scan events initial).output = .failure := by
  induction events generalizing initial with
  | nil => exact failed
  | cons event rest ih =>
      change (scan rest (consume initial event)).output = .failure
      apply ih
      cases event <;> simp [consume, failed, ActionStatus.acknowledge, ActionStatus.noteWork]

theorem scan_preserves_cleanup_failure {Answer : Type} (events : List (Event Answer))
    (initial : Summary) (failed : initial.cleanup = .failure) :
    (scan events initial).cleanup = .failure := by
  induction events generalizing initial with
  | nil => exact failed
  | cons event rest ih =>
      change (scan rest (consume initial event)).cleanup = .failure
      apply ih
      cases event <;> simp [consume, failed, ActionStatus.acknowledge, ActionStatus.noteWork]

/-- An owned worker survives every event other than its own settlement. -/
theorem scan_retains_worker {Answer : Type} (events : List (Event Answer))
    (initial : Summary) (id : Nat) (pending : id ∈ initial.pendingWorkers)
    (notSettled : Event.workerSettled id ∉ events) :
    id ∈ (scan events initial).pendingWorkers := by
  induction events generalizing initial with
  | nil => exact pending
  | cons event rest ih =>
      change id ∈ (scan rest (consume initial event)).pendingWorkers
      apply ih
      · cases event with
        | workerStarted other => simp [consume, pending]
        | workerSettled other =>
            have different : id ≠ other := by
              intro same
              subst other
              exact notSettled (by simp)
            simp [consume, different, pending]
        | answer value => exact pending
        | outputComplete => exact pending
        | outputFailed => exact pending
        | cleanupComplete => exact pending
        | cleanupFailed => exact pending
      · exact fun member => notSettled (List.mem_cons_of_mem _ member)

/-- Starting a worker and never settling that identity leaves it pending,
regardless of the events for other workers. -/
theorem started_without_settlement_pending {Answer : Type} (events : List (Event Answer))
    (initial : Summary) (id : Nat) (started : Event.workerStarted id ∈ events)
    (notSettled : Event.workerSettled id ∉ events) :
    id ∈ (scan events initial).pendingWorkers := by
  obtain ⟨before, after, equality⟩ := List.mem_iff_append.mp started
  subst events
  rw [scan_append]
  change id ∈ (scan after (consume (scan before initial) (.workerStarted id))).pendingWorkers
  apply scan_retains_worker
  · simp [consume]
  · intro member
    exact notSettled (by simp [member])

/-- A producer's existing observation adapts without treating a live frontier
as empty or interpreting payloads as faults. -/
theorem exhaustive_observation_adapter {State Fault Answer : Type}
    (observation : RunObservation State Answer) :
    completeB .exhaustive observation.answerOccurrences.length
      (.observed observation.stop : ProducerStop State Fault) = true ↔
      observation.stop = .complete := by
  cases observation.stop <;> simp [completeB]

def Event.map {Answer Other : Type} (f : Answer → Other) : Event Answer → Event Other
  | .answer value => .answer (f value)
  | .workerStarted id => .workerStarted id
  | .workerSettled id => .workerSettled id
  | .outputComplete => .outputComplete
  | .outputFailed => .outputFailed
  | .cleanupComplete => .cleanupComplete
  | .cleanupFailed => .cleanupFailed

/-- Ordinary payload replacement, including Error-shaped data, cannot change
counts, finalization, ownership, or the command classification. -/
theorem scan_map_payload {Answer Other : Type} (f : Answer → Other)
    (events : List (Event Answer)) (initial : Summary) :
    scan (events.map (Event.map f)) initial = scan events initial := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      change scan (rest.map (Event.map f)) (consume initial (event.map f)) =
        scan rest (consume initial event)
      have same : consume initial (event.map f) = consume initial event := by
        cases event <;> rfl
      rw [same]
      exact ih _

theorem scan_answers {Answer : Type} (answers : List Answer) (initial : Summary) :
    scan (answers.map Event.answer) initial =
      {initial with
        answerCount := initial.answerCount + answers.length
        output := if answers.length = 0 then initial.output else initial.output.noteWork} := by
  induction answers generalizing initial with
  | nil => simp [scan]
  | cons answer rest ih =>
      change scan (rest.map Event.answer) (consume initial (.answer answer)) = _
      rw [ih]
      cases rest <;> simp [consume, ActionStatus.noteWork_idempotent,
        Nat.add_comm, Nat.add_left_comm]

/-- Only answer events are permuted; effect/resource events outside this block
retain their relative order. Multiplicity is retained. -/
theorem scan_answer_permutation {Answer : Type} (before after : List (Event Answer))
    (left right : List Answer) (perm : left.Perm right) (initial : Summary) :
    scan (before ++ left.map Event.answer ++ after) initial =
      scan (before ++ right.map Event.answer ++ after) initial := by
  simp only [scan, List.foldl_append]
  change scan after (scan (left.map Event.answer) (scan before initial)) =
    scan after (scan (right.map Event.answer) (scan before initial))
  rw [scan_answers, scan_answers, perm.length_eq]

/-- An interrupt is never a successful deliberate stop, even after k answers. -/
theorem interruption_never_complete {State Fault : Type} (demand : Demand) (count : Nat)
    (reason : ResourceInterruption) :
    completeB demand count (.observed (.interrupted reason) : ProducerStop State Fault) = false := by
  cases demand <;> rfl

theorem depth_cut_never_complete {State Fault : Type} (demand : Demand) (count : Nat)
    (pending : List (State × List Nat)) (nonempty : pending ≠ []) :
    completeB demand count (.observed (.depthCut pending nonempty) : ProducerStop State Fault) = false := by
  cases demand <;> rfl

theorem fault_never_complete {State Fault : Type} (demand : Demand) (count : Nat) (fault : Fault) :
    completeB demand count (.fault fault : ProducerStop State Fault) = false := by
  cases demand <;> rfl

theorem pending_worker_prevents_success {State Fault : Type} (demand : Demand)
    (stop : ProducerStop State Fault) (summary : Summary) (id : Nat)
    (pending : id ∈ summary.pendingWorkers) :
    commandSucceeded demand stop summary = false := by
  have nonempty : summary.pendingWorkers ≠ ∅ := by
    intro empty
    simp [empty] at pending
  simp [commandSucceeded, nonempty]

theorem output_failure_prevents_success {State Fault : Type} (demand : Demand)
    (stop : ProducerStop State Fault) (summary : Summary) (failed : summary.output = .failure) :
    commandSucceeded demand stop summary = false := by
  simp [commandSucceeded, failed]

theorem cleanup_failure_prevents_success {State Fault : Type} (demand : Demand)
    (stop : ProducerStop State Fault) (summary : Summary) (failed : summary.cleanup = .failure) :
    commandSucceeded demand stop summary = false := by
  simp [commandSucceeded, failed]

/-- Streaming root faults cannot be converted into command success by answer
counts or successful finalization. Which fault is reported is irrelevant. -/
theorem root_fault_prevents_success {State Fault : Type} (demand : Demand)
    (fault : Fault) (summary : Summary) :
    commandSucceeded demand (.fault fault : ProducerStop State Fault) summary = false := by
  simp [commandSucceeded, fault_never_complete]

/-- An unacknowledged owner makes normal completion impossible. -/
theorem missing_worker_settlement_prevents_success {State Fault Answer : Type}
    (demand : Demand) (stop : ProducerStop State Fault) (events : List (Event Answer))
    (id : Nat) (started : Event.workerStarted id ∈ events)
    (notSettled : Event.workerSettled id ∉ events) :
    commandSucceeded demand stop (scan events) = false :=
  pending_worker_prevents_success demand stop _ id
    (started_without_settlement_pending events Summary.initial id started notSettled)

/-- A failure anywhere in the output trace remains fatal after later events. -/
theorem output_failure_anywhere_prevents_success {State Fault Answer : Type}
    (demand : Demand) (stop : ProducerStop State Fault)
    (before after : List (Event Answer)) :
    commandSucceeded demand stop (scan (before ++ .outputFailed :: after)) = false := by
  apply output_failure_prevents_success
  rw [scan_append]
  exact scan_preserves_output_failure after _ rfl

theorem cleanup_failure_anywhere_prevents_success {State Fault Answer : Type}
    (demand : Demand) (stop : ProducerStop State Fault)
    (before after : List (Event Answer)) :
    commandSucceeded demand stop (scan (before ++ .cleanupFailed :: after)) = false := by
  apply cleanup_failure_prevents_success
  rw [scan_append]
  exact scan_preserves_cleanup_failure after _ rfl

namespace Controls

def finalized (answers : List Nat) : List (Event Nat) :=
  answers.map Event.answer ++ [.outputComplete, .cleanupComplete]

/-- Five answers suffice without an exhaustion claim once owned work is
settled and output/finalization have succeeded. -/
theorem bounded_five_with_settled_tail :
    commandSucceeded (.prefix 5) (.demandSatisfied : ProducerStop Unit Unit)
      (scan ([.workerStarted 10] ++ (List.replicate 5 (.answer 7)) ++
        [.workerSettled 10, .outputComplete, .cleanupComplete])) = true := by decide

theorem zero_demand_without_exploration :
    commandSucceeded (.prefix 0) (.demandSatisfied : ProducerStop Unit Unit)
      (scan (finalized [])) = true := by decide

theorem justified_short_exhaustion :
    commandSucceeded (.prefix 5) (.observed .complete : ProducerStop Unit Unit)
      (scan (finalized [7, 7])) = true := by decide

theorem short_claimed_satisfaction_rejected :
    commandSucceeded (.prefix 5) (.demandSatisfied : ProducerStop Unit Unit)
      (scan (finalized [7, 7])) = false := by decide

theorem cutoff_four_of_five_rejected :
    commandSucceeded (.prefix 5) (.observed (.interrupted .fuelExhausted) : ProducerStop Unit Unit)
      (scan (finalized [1, 2, 3, 4])) = false := by decide

theorem five_then_output_failure_rejected :
    commandSucceeded (.prefix 5) (.demandSatisfied : ProducerStop Unit Unit)
      (scan (finalized [1, 2, 3, 4, 5] ++ [.outputFailed])) = false := by decide

theorem cleanup_acknowledgement_does_not_erase_failure :
    commandSucceeded (.prefix 0) (.demandSatisfied : ProducerStop Unit Unit)
      (scan ([.cleanupFailed, .cleanupComplete, .outputComplete] : List (Event Nat))) = false := by decide

/-- Two settlements of one identity do not settle another owned worker. -/
theorem duplicate_settlement_cannot_hide_worker :
    commandSucceeded (.prefix 0) (.demandSatisfied : ProducerStop Unit Unit)
      (scan ([.workerStarted 1, .workerStarted 2, .workerSettled 1, .workerSettled 1,
        .outputComplete, .cleanupComplete] : List (Event Nat))) = false := by decide

/-- Resource protocol events do not inherit answer permutation invariance. -/
theorem resource_order_is_observable :
    scan ([.workerStarted 1, .workerSettled 1] : List (Event Nat)) ≠
      scan ([.workerSettled 1, .workerStarted 1] : List (Event Nat)) := by decide

/-- An output acknowledgement predating a new answer does not cover it. -/
theorem stale_output_acknowledgement_rejected :
    commandSucceeded (.prefix 1) (.demandSatisfied : ProducerStop Unit Unit)
      (scan ([.outputComplete, .cleanupComplete, .answer 7] : List (Event Nat))) = false := by decide

/-- Starting and settling new owned work invalidates old cleanup success. -/
theorem stale_cleanup_acknowledgement_rejected :
    commandSucceeded (.prefix 0) (.demandSatisfied : ProducerStop Unit Unit)
      (scan ([.outputComplete, .cleanupComplete, .workerStarted 1,
        .workerSettled 1] : List (Event Nat))) = false := by decide

theorem cleanup_before_settlement_needs_new_acknowledgement :
    commandSucceeded (.prefix 0) (.demandSatisfied : ProducerStop Unit Unit)
      (scan ([.workerStarted 1, .cleanupComplete, .workerSettled 1,
        .outputComplete] : List (Event Nat))) = false := by decide

end Controls

end Mettapedia.Machines.RunContracts.Completion
