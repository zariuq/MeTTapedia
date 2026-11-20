import Mettapedia.Machines.Kernel.AuthorityCustody

/-!
# Invocation authority and continuation strategy

An authenticated program run supplies authority. The task currently executing
inside that run supplies only its continuation strategy. Accepted work remains
an obligation until settlement, independently of whether the caller blocks or
polls.

The theorems concern the abstract transition system. The native interfaces
carry separate obligations for authentication, scheduling and settlement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.InvocationContext

inductive ExecutionClass where
  | main | worker
  deriving DecidableEq, Repr

structure Task where
  id : Nat
  run : Nat
  execution : ExecutionClass
  deriving DecidableEq, Repr

structure Context where
  authorityRun : Nat
  task : Task
  deriving DecidableEq, Repr

structure State where
  currentRun : Nat
  nextRequest : Nat
  pending : List Nat
  deriving DecidableEq, Repr

structure Valid (state : State) : Prop where
  unique : state.pending.Nodup
  issued : ∀ request ∈ state.pending, request ≤ state.nextRequest

inductive Outcome where
  | refused
  | blocked (request : Nat)
  | polling (request : Nat)
  deriving DecidableEq, Repr

def authenticated (state : State) (context : Context) : Bool :=
  context.authorityRun == state.currentRun && context.task.run == context.authorityRun

def continuation (execution : ExecutionClass) (request : Nat) : Outcome :=
  match execution with
  | .main => .blocked request
  | .worker => .polling request

def invoke (state : State) (context : Context) (transportAccepted : Bool) : State × Outcome :=
  if authenticated state context && transportAccepted then
    let request := state.nextRequest + 1
    (⟨state.currentRun, request, state.pending ++ [request]⟩,
      continuation context.task.execution request)
  else
    (state, .refused)

def settle (state : State) (request : Nat) : State :=
  if request ∈ state.pending then { state with pending := state.pending.erase request }
  else state

def Accepted (outcome : Outcome) : Prop := outcome ≠ .refused

theorem authenticated_execution_irrelevant (state : State) (context : Context)
    (execution : ExecutionClass) :
    authenticated state { context with task := { context.task with execution := execution } } =
      authenticated state context := by
  simp [authenticated]

theorem custody_execution_irrelevant (state : State) (context : Context)
    (transportAccepted : Bool) (execution : ExecutionClass) :
    (invoke state { context with task := { context.task with execution := execution } }
      transportAccepted).1 = (invoke state context transportAccepted).1 := by
  unfold invoke
  rw [authenticated_execution_irrelevant]
  split <;> rfl

theorem refused_preserves_state (state : State) (context : Context) (transportAccepted : Bool)
    (refused : (invoke state context transportAccepted).2 = .refused) :
    (invoke state context transportAccepted).1 = state := by
  unfold invoke at refused ⊢
  by_cases accepted : (authenticated state context && transportAccepted) = true
  · rw [if_pos accepted] at refused ⊢
    have impossible : continuation context.task.execution (state.nextRequest + 1) ≠ .refused := by
      cases context.task.execution <;> simp [continuation]
    exact (impossible refused).elim
  · rw [if_neg accepted] at refused ⊢

theorem stale_run_refused (state : State) (context : Context)
    (stale : context.authorityRun ≠ state.currentRun) (transportAccepted : Bool) :
    invoke state context transportAccepted = (state, .refused) := by
  simp [invoke, authenticated, stale]

theorem foreign_task_refused (state : State) (context : Context)
    (foreign : context.task.run ≠ context.authorityRun) (transportAccepted : Bool) :
    invoke state context transportAccepted = (state, .refused) := by
  simp [invoke, authenticated, foreign]

theorem transport_refusal_preserves (state : State) (context : Context) :
    invoke state context false = (state, .refused) := by
  simp [invoke]

theorem accepted_creates_custody (state next : State) (context : Context)
    (transportAccepted : Bool) (outcome : Outcome)
    (result : invoke state context transportAccepted = (next, outcome))
    (accepted : Accepted outcome) :
    next.pending = state.pending ++ [state.nextRequest + 1] ∧
      next.nextRequest = state.nextRequest + 1 := by
  simp only [invoke] at result
  split at result
  · cases result
    exact ⟨rfl, rfl⟩
  · cases result
    exact (accepted rfl).elim

theorem Valid.invoke {state : State} (valid : Valid state) (context : Context)
    (transportAccepted : Bool) : Valid (invoke state context transportAccepted).1 := by
  unfold InvocationContext.invoke
  split
  · dsimp
    have fresh : state.nextRequest + 1 ∉ state.pending := by
      intro present
      have bounded := valid.issued _ present
      omega
    constructor
    · rw [List.nodup_append]
      refine ⟨valid.unique, by simp, ?_⟩
      intro old oldPresent newest newestPresent
      simp only [List.mem_singleton] at newestPresent
      subst newest
      exact fun same => fresh (same ▸ oldPresent)
    · intro request present
      simp only [List.mem_append, List.mem_singleton] at present
      rcases present with old | newest
      · change request ≤ state.nextRequest + 1
        exact Nat.le_trans (valid.issued request old) (Nat.le_add_right state.nextRequest 1)
      · subst request
        exact Nat.le_refl _
  · exact valid

theorem Valid.settle {state : State} (valid : Valid state) (request : Nat) :
    Valid (settle state request) := by
  unfold InvocationContext.settle
  split
  · constructor
    · exact valid.unique.erase request
    · intro other present
      exact valid.issued other (List.mem_of_mem_erase present)
  · exact valid

theorem accepted_worker_polls (state : State) (context : Context)
    (worker : context.task.execution = .worker)
    (authority : authenticated state context = true) :
    (invoke state context true).2 = .polling (state.nextRequest + 1) := by
  simp [invoke, authority, continuation, worker]

theorem accepted_main_blocks (state : State) (context : Context)
    (main : context.task.execution = .main)
    (authority : authenticated state context = true) :
    (invoke state context true).2 = .blocked (state.nextRequest + 1) := by
  simp [invoke, authority, continuation, main]

theorem worker_never_main_blocks (state : State) (context : Context)
    (worker : context.task.execution = .worker) (transportAccepted : Bool) (request : Nat) :
    (invoke state context transportAccepted).2 ≠ .blocked request := by
  simp only [invoke]
  split
  · simp [continuation, worker]
  · simp

theorem main_never_worker_polls (state : State) (context : Context)
    (main : context.task.execution = .main) (transportAccepted : Bool) (request : Nat) :
    (invoke state context transportAccepted).2 ≠ .polling request := by
  simp only [invoke]
  split
  · simp [continuation, main]
  · simp

theorem settle_unknown_preserves (state : State) (request : Nat)
    (absent : request ∉ state.pending) : settle state request = state := by
  simp [settle, absent]

theorem settle_removes (state : State) (request : Nat)
    (present : request ∈ state.pending) :
    (settle state request).pending = state.pending.erase request := by
  simp [settle, present]

theorem settle_twice (state : State) (request : Nat)
    (unique : state.pending.Nodup) :
    settle (settle state request) request = settle state request := by
  by_cases present : request ∈ state.pending
  · have absent : request ∉ state.pending.erase request := by
      exact unique.not_mem_erase
    simp [settle, present, absent]
  · simp [settle, present]

/-! ## Deriving a context from dispatch custody

The dispatch observation and current run are read from kernel records. A worker
observation carries its own task and the run to which it is attached. The
`attachedHere` bit represents the scheduler's live attachment on this core.
-/

inductive Selection where
  | idle
  | main (domain task : Nat)
  | worker (domain task run : Nat) (attachedHere : Bool)
  deriving DecidableEq, Repr

def Selection.context (selection : Selection) (domain run : Nat) : Option Context :=
  match selection with
  | .idle => none
  | .main selected task =>
      if domain ≠ 0 ∧ run ≠ 0 ∧ selected = domain ∧ task = run then
        some ⟨run, ⟨task, run, .main⟩⟩
      else none
  | .worker selected task owner attachedHere =>
      if domain ≠ 0 ∧ run ≠ 0 ∧ selected = domain ∧ owner = run ∧
          task ≠ 0 ∧ task ≠ run ∧ attachedHere = true then
        some ⟨owner, ⟨task, owner, .worker⟩⟩
      else none

def invokeSelected (state : State) (domain : Nat) (selection : Selection)
    (transportAccepted : Bool) : State × Outcome :=
  match selection.context domain state.currentRun with
  | none => (state, .refused)
  | some context => invoke state context transportAccepted

theorem selected_stale_worker_refused (state : State) (domain selected task owner : Nat)
    (attachedHere transportAccepted : Bool) (stale : owner ≠ state.currentRun) :
    invokeSelected state domain (.worker selected task owner attachedHere) transportAccepted =
      (state, .refused) := by
  simp [invokeSelected, Selection.context, stale]

theorem selected_foreign_worker_refused (state : State) (domain selected task owner : Nat)
    (attachedHere transportAccepted : Bool) (foreignDomain : selected ≠ domain) :
    invokeSelected state domain (.worker selected task owner attachedHere) transportAccepted =
      (state, .refused) := by
  simp [invokeSelected, Selection.context, foreignDomain]

theorem selected_detached_worker_refused (state : State) (domain selected task owner : Nat)
    (transportAccepted : Bool) :
    invokeSelected state domain (.worker selected task owner false) transportAccepted =
      (state, .refused) := by
  simp [invokeSelected, Selection.context]

theorem selected_worker_issues_same_obligation (state : State) (domain task : Nat)
    (liveDomain : domain ≠ 0) (liveRun : state.currentRun ≠ 0)
    (liveTask : task ≠ 0) (workerTask : task ≠ state.currentRun) :
    let main := invokeSelected state domain (.main domain state.currentRun) true
    let worker := invokeSelected state domain (.worker domain task state.currentRun true) true
    main.1 = worker.1 ∧ main.2 = .blocked (state.nextRequest + 1) ∧
      worker.2 = .polling (state.nextRequest + 1) := by
  simp [invokeSelected, Selection.context, liveDomain, liveRun, liveTask, workerTask,
    invoke, authenticated, continuation]

theorem Valid.invokeSelected {state : State} (valid : Valid state) (domain : Nat)
    (selection : Selection) (transportAccepted : Bool) :
    Valid (InvocationContext.invokeSelected state domain selection transportAccepted).1 := by
  unfold InvocationContext.invokeSelected
  split
  · exact valid
  · exact valid.invoke _ _

example : (invokeSelected ⟨7, 10, [8, 9]⟩ 42 (.worker 42 1073741824 7 true) true).2 =
    .polling 11 := by decide
example : (invokeSelected ⟨7, 10, [8, 9]⟩ 42 (.worker 42 1073741824 6 true) true).2 =
    .refused := by decide

#print axioms selected_stale_worker_refused
#print axioms selected_worker_issues_same_obligation

/-! ## A main task's register receive

Admission of a call and delivery of an inbox event are different actions.
The event can be an older reply or a queued message. An armed receive belongs
to the waiting main task and run. A worker may explicitly read the domain's
inbox, but being scheduled never discharges the main task's receive.
-/

namespace RegisterReceive

structure Inbox (Event : Type) where
  reply : Option Event
  queued : List Event
  deriving DecidableEq, Repr

structure Ticket where
  task : Nat
  run : Nat
  deriving DecidableEq, Repr

structure Delivery (Event : Type) where
  waiting : Option Ticket
  inbox : Inbox Event
  event : Option Event
  deriving DecidableEq, Repr

variable {Event : Type}

def take (inbox : Inbox Event) : Inbox Event × Option Event :=
  match inbox.reply, inbox.queued with
  | some reply, _ => ({ inbox with reply := none }, some reply)
  | none, event :: rest => (⟨none, rest⟩, some event)
  | none, [] => (inbox, none)

def resume (waiting : Option Ticket) (task : Task) (inbox : Inbox Event) : Delivery Event :=
  match task.execution with
  | .worker => ⟨waiting, inbox, none⟩
  | .main =>
      if waiting = some ⟨task.id, task.run⟩ then
        let (remaining, event) := take inbox
        ⟨none, remaining, event⟩
      else
        ⟨none, inbox, none⟩

theorem worker_resume_preserves (waiting : Option Ticket) (task : Task) (inbox : Inbox Event)
    (worker : task.execution = .worker) :
    resume waiting task inbox = ⟨waiting, inbox, none⟩ := by
  simp [resume, worker]

theorem stale_run_preserves_inbox (ticket : Ticket) (task : Task) (inbox : Inbox Event)
    (main : task.execution = .main) (stale : ticket.run ≠ task.run) :
    resume (some ticket) task inbox = ⟨none, inbox, none⟩ := by
  cases ticket
  simp_all [resume]

theorem wrong_task_preserves_inbox (ticket : Ticket) (task : Task) (inbox : Inbox Event)
    (main : task.execution = .main) (different : ticket.task ≠ task.id) :
    resume (some ticket) task inbox = ⟨none, inbox, none⟩ := by
  cases ticket
  simp_all [resume]

theorem reply_precedes_queue (task : Task) (reply : Event) (queued : List Event)
    (main : task.execution = .main) :
    resume (some ⟨task.id, task.run⟩) task ⟨some reply, queued⟩ =
      ⟨none, ⟨none, queued⟩, some reply⟩ := by
  simp [resume, main, take]

theorem queue_head_preserves_tail (task : Task) (first : Event) (rest : List Event)
    (main : task.execution = .main) :
    resume (some ⟨task.id, task.run⟩) task ⟨none, first :: rest⟩ =
      ⟨none, ⟨none, rest⟩, some first⟩ := by
  simp [resume, main, take]

theorem resume_once (waiting : Option Ticket) (task : Task) (inbox : Inbox Event)
    (main : task.execution = .main) :
    let first := resume waiting task inbox
    resume first.waiting task first.inbox = ⟨none, first.inbox, none⟩ := by
  have cleared : (resume waiting task inbox).waiting = none := by
    simp only [resume, main]
    split
    · cases take inbox <;> rfl
    · rfl
  change resume (resume waiting task inbox).waiting task (resume waiting task inbox).inbox = _
  rw [cleared]
  simp [resume, main]

example : resume (some ⟨7, 7⟩) ⟨7, 7, .main⟩ (⟨none, [42, 43]⟩ : Inbox Nat) =
    ⟨none, ⟨none, [43]⟩, some 42⟩ := by decide

example : resume (some ⟨7, 7⟩) ⟨7, 8, .main⟩ (⟨some 42, [43]⟩ : Inbox Nat) =
    ⟨none, ⟨some 42, [43]⟩, none⟩ := by decide

#print axioms worker_resume_preserves
#print axioms stale_run_preserves_inbox
#print axioms wrong_task_preserves_inbox
#print axioms reply_precedes_queue
#print axioms queue_head_preserves_tail
#print axioms resume_once

end RegisterReceive

/-! ## Correlated requests outlive the submitting worker

The scheduler supplies provenance at submission. The request then belongs to
the run's window. Hearing checks the stamped run, and collection checks the
task currently selected for that run. A worker can depart between these steps.
-/

namespace RunRequests

open CorrelatedReplies (Config Result Window)

structure State (Peer : Type) where
  domain : Nat
  run : Nat
  window : Window Peer
  deriving DecidableEq

structure Receipt where
  domain : Nat
  run : Nat
  task : Nat
  request : Nat
  deriving DecidableEq

variable {Peer : Type}

def submit (config : Config Peer) (state : State Peer) (selection : Selection)
    (peer : Peer) (registered room : Bool) : State Peer × Result × Option Receipt :=
  match selection.context state.domain state.run with
  | none => (state, .refused, none)
  | some current =>
      let (window, result) := CorrelatedReplies.admit config state.window peer registered room
      let receipt := match result with
        | .admitted id => some ⟨state.domain, current.authorityRun, current.task.id, id⟩
        | _ => none
      ({ state with window }, result, receipt)

def hear [DecidableEq Peer] (state : State Peer) (peer : Peer) (receipt : Receipt) :
    State Peer × Result :=
  if receipt.domain = state.domain ∧ receipt.run = state.run then
    let (window, result) := CorrelatedReplies.claim state.window peer receipt.request
    ({ state with window }, result)
  else (state, .refused)

def collect (state : State Peer) (selection : Selection) (request : Nat) : State Peer × Result :=
  match selection.context state.domain state.run with
  | none => (state, .refused)
  | some _ =>
      let (window, result) := CorrelatedReplies.poll state.window request
      ({ state with window }, result)

def rebirth (state : State Peer) (nextRun : Nat) : State Peer :=
  { state with run := nextRun, window := ⟨state.window.issued, []⟩ }

theorem detached_submit_refused (config : Config Peer) (state : State Peer)
    (domain task run : Nat) (peer : Peer) (registered room : Bool) :
    submit config state (.worker domain task run false) peer registered room =
      (state, .refused, none) := by
  simp [submit, Selection.context]

theorem detached_collect_refused (state : State Peer) (domain task run request : Nat) :
    collect state (.worker domain task run false) request = (state, .refused) := by
  simp [collect, Selection.context]

theorem same_run_admission (config : Config Peer) (state : State Peer)
    (task : Nat) (peer : Peer) (registered room : Bool)
    (domainLive : state.domain ≠ 0) (runLive : state.run ≠ 0)
    (taskLive : task ≠ 0) (workerTask : task ≠ state.run) :
    let main := submit config state (.main state.domain state.run) peer registered room
    let worker := submit config state (.worker state.domain task state.run true) peer registered room
    main.1 = worker.1 ∧ main.2.1 = worker.2.1 := by
  simp [submit, Selection.context, domainLive, runLive, taskLive, workerTask]

theorem worker_receipt_records_provenance (config : Config Peer) (state : State Peer)
    (task request : Nat) (peer : Peer) (registered room : Bool)
    (domainLive : state.domain ≠ 0) (runLive : state.run ≠ 0)
    (taskLive : task ≠ 0) (workerTask : task ≠ state.run)
    (accepted : (CorrelatedReplies.admit config state.window peer registered room).2 =
      .admitted request) :
    (submit config state (.worker state.domain task state.run true) peer registered room).2.2 =
      some ⟨state.domain, state.run, task, request⟩ := by
  rcases step : CorrelatedReplies.admit config state.window peer registered room with ⟨w, result⟩
  rw [step] at accepted
  simp [submit, Selection.context, domainLive, runLive, taskLive, workerTask, step, accepted]

theorem stale_receipt_cannot_be_heard [DecidableEq Peer] (state : State Peer)
    (peer : Peer) (receipt : Receipt) (stale : receipt.run ≠ state.run) :
    hear state peer receipt = (state, .refused) := by
  simp [hear, stale]

theorem rebirth_keeps_sequence (state : State Peer) (nextRun request : Nat) :
    (rebirth state nextRun).window.issued = state.window.issued ∧
    CorrelatedReplies.lookup (rebirth state nextRun).window request = none := by
  simp [rebirth, CorrelatedReplies.lookup]

theorem collect_once (state : State Peer) (selection : Selection) (request value : Nat)
    (delivered : (collect state selection request).2 = .value value) :
    let next := (collect state selection request).1
    collect next selection request = (next, .refused) := by
  cases selected : selection.context state.domain state.run with
  | none => simp [collect, selected] at delivered
  | some context =>
      rcases polled : CorrelatedReplies.poll state.window request with ⟨window, result⟩
      have consumed : CorrelatedReplies.poll window request = (window, .refused) := by
        have observed : (CorrelatedReplies.poll state.window request).2 = .value value := by
          simpa [collect, selected, polled] using delivered
        simpa [polled] using CorrelatedReplies.poll_consumes_once state.window request value observed
      simp [collect, selected, polled, consumed]

example :
    let config : Config Nat := ⟨8, 100, fun peer => peer == 2⟩
    let start : State Nat := ⟨42, 51, ⟨5, []⟩⟩
    let sent := submit config start (.worker 42 1073741824 51 true) 2 true true
    let receipt : Receipt := ⟨42, 51, 1073741824, 6⟩
    let heard := (hear sent.1 2 receipt).1
    let done := { heard with window := (CorrelatedReplies.complete heard.window 2 6 63).1 }
    sent.2.2 = some receipt ∧
    (collect done (.worker 42 1073741824 51 false) 6).2 = .refused ∧
    (collect done (.main 42 51) 6).2 = .value 63 ∧
    (collect (rebirth done 52) (.main 42 52) 6).2 = .refused := by decide

#print axioms same_run_admission
#print axioms worker_receipt_records_provenance
#print axioms stale_receipt_cannot_be_heard
#print axioms collect_once

end RunRequests

namespace DeferredReplies

structure Reply where
  peer : Nat
  run : Nat
  request : Nat
  deriving DecidableEq, Repr

inductive Observation where
  | unknown | retired | current (run : Nat)
  deriving DecidableEq, Repr

inductive Disposition where
  | retain | deliver | retire
  deriving DecidableEq, Repr

inductive Submission where
  | accepted | retry | terminal
  deriving DecidableEq, Repr

/-- A held run observation gates attempts to publish. A terminal transport
    refusal releases the reply only after an attempt was allowed. -/
def observedDisposition (observation : Observation) (blocked : Bool)
    (submit : Unit → Submission) (reply : Reply) : Disposition :=
  match observation with
  | .unknown => .retain
  | .retired => .retire
  | .current run =>
      if reply.run ≠ run then .retire
      else if blocked then .retain
      else match submit () with
        | .accepted => .deliver
        | .retry => .retain
        | .terminal => .retire

structure Batch where
  pending : List Reply
  delivered : List Reply
  retired : List Reply
  deriving DecidableEq, Repr

/-- One pass over pending Files replies with held run observations. -/
def poll (observe : Reply → Observation) (submit : Reply → Submission) (blocked : List Nat) :
    List Reply → Batch
  | [] => ⟨[], [], []⟩
  | reply :: rest =>
      match observedDisposition (observe reply) (decide (reply.peer ∈ blocked))
          (fun _ => submit reply) reply with
      | .retire =>
          let tail := poll observe submit blocked rest
          { tail with retired := reply :: tail.retired }
      | .retain =>
          let tail := poll observe submit (reply.peer :: blocked) rest
          { tail with pending := reply :: tail.pending }
      | .deliver =>
          let tail := poll observe submit blocked rest
          { tail with delivered := reply :: tail.delivered }

theorem wrong_run_retires (reply : Reply) (run : Nat) (blocked : Bool)
    (submit : Unit → Submission) (wrong : reply.run ≠ run) :
    observedDisposition (.current run) blocked submit reply = .retire := by
  simp [observedDisposition, wrong]

theorem delivery_requires_current {reply : Reply} {observation : Observation} {blocked : Bool}
    {submit : Unit → Submission}
    (delivered : observedDisposition observation blocked submit reply = .deliver) :
    observation = .current reply.run ∧ blocked = false ∧ submit () = .accepted := by
  cases observation with
  | unknown | retired => simp [observedDisposition] at delivered
  | current run =>
      by_cases current : reply.run = run
      · subst run
        cases blocked <;> cases h : submit () <;> simp_all [observedDisposition]
      · simp [observedDisposition, current] at delivered

theorem conserves_replies (observe : Reply → Observation) (submit : Reply → Submission)
    (blocked : List Nat) (replies : List Reply) :
    let batch := poll observe submit blocked replies
    (batch.pending ++ batch.delivered ++ batch.retired).Perm replies := by
  induction replies generalizing blocked with
  | nil => exact .nil
  | cons reply rest ih =>
      let tail := poll observe submit blocked rest
      have restPerm : (tail.pending ++ tail.delivered ++ tail.retired).Perm rest := ih blocked
      cases outcome : observedDisposition (observe reply) (decide (reply.peer ∈ blocked))
          (fun _ => submit reply) reply with
      | retain =>
          simpa [poll, outcome] using List.Perm.cons reply (ih (reply.peer :: blocked))
      | retire =>
          have moved := List.perm_middle (a := reply)
            (l₁ := tail.pending ++ tail.delivered) (l₂ := tail.retired)
          simpa [poll, outcome, tail] using moved.trans (List.Perm.cons reply restPerm)
      | deliver =>
          have moved := List.perm_middle (a := reply)
            (l₁ := tail.pending) (l₂ := tail.delivered ++ tail.retired)
          have tailPerm : (tail.pending ++ (tail.delivered ++ tail.retired)).Perm rest := by
            simpa only [List.append_assoc] using restPerm
          simpa [poll, outcome, tail, List.append_assoc] using
            moved.trans (List.Perm.cons reply tailPerm)

theorem accounted (observe : Reply → Observation) (submit : Reply → Submission)
    (blocked : List Nat) (replies : List Reply) :
    let batch := poll observe submit blocked replies
    batch.pending.length + batch.delivered.length + batch.retired.length = replies.length := by
  simpa only [List.length_append] using (conserves_replies observe submit blocked replies).length_eq

theorem delivered_matches_observation (observe : Reply → Observation)
    (submit : Reply → Submission) (replies : List Reply) (blocked : List Nat) :
    ∀ reply ∈ (poll observe submit blocked replies).delivered,
      observe reply = .current reply.run ∧ submit reply = .accepted := by
  induction replies generalizing blocked with
  | nil => simp [poll]
  | cons head rest ih =>
      cases outcome : observedDisposition (observe head) (decide (head.peer ∈ blocked))
          (fun _ => submit head) head with
      | retire => simpa [poll, outcome] using ih blocked
      | retain => simpa [poll, outcome] using ih (head.peer :: blocked)
      | deliver =>
          intro reply present
          simp [poll, outcome] at present
          rcases present with same | later
          · subst reply
            obtain ⟨current, _, accepted⟩ := delivery_requires_current outcome
            exact ⟨current, accepted⟩
          · exact ih blocked reply later

theorem blocked_peer (observe : Reply → Observation) (submit : Reply → Submission)
    (replies : List Reply)
    (peer : Nat) (blocked : List Nat) (member : peer ∈ blocked) :
    ∀ reply ∈ (poll observe submit blocked replies).delivered, reply.peer ≠ peer := by
  induction replies generalizing blocked with
  | nil => simp [poll]
  | cons reply rest ih =>
      have extended : peer ∈ reply.peer :: blocked := List.mem_cons_of_mem _ member
      cases outcome : observedDisposition (observe reply) (decide (reply.peer ∈ blocked))
          (fun _ => submit reply) reply with
      | retire => simpa [poll, outcome] using ih blocked member
      | retain => simpa [poll, outcome] using ih (reply.peer :: blocked) extended
      | deliver =>
          have head : reply.peer ∉ blocked := by
            simpa using (delivery_requires_current outcome).2.1
          intro item present
          simp [poll, outcome] at present
          rcases present with same | later
          · subst item
            exact fun equal => head (equal.symm ▸ member)
          · exact ih blocked member item later

theorem retained_head_blocks_followers (observe : Reply → Observation)
    (submit : Reply → Submission) (first : Reply) (rest : List Reply)
    (waiting : observedDisposition (observe first) false (fun _ => submit first) first = .retain) :
    first ∈ (poll observe submit [] (first :: rest)).pending ∧
    ∀ reply ∈ (poll observe submit [] (first :: rest)).delivered, reply.peer ≠ first.peer := by
  constructor
  · simp [poll, waiting]
  · simpa [poll, waiting] using
      blocked_peer observe submit rest first.peer [first.peer] (by simp)

example : poll (fun reply => .current reply.run)
    (fun reply => if reply.request = 1 then .retry else if reply.request = 2 then .terminal
      else .accepted) []
    [⟨7, 1, 1⟩, ⟨7, 1, 2⟩, ⟨8, 1, 3⟩] =
    ⟨[⟨7, 1, 1⟩, ⟨7, 1, 2⟩], [⟨8, 1, 3⟩], []⟩ := by decide

example : observedDisposition (.current 2) false (fun _ => .accepted) ⟨7, 1, 1⟩ =
    .retire := by decide
example : observedDisposition .unknown false (fun _ => .terminal) ⟨7, 1, 1⟩ =
    .retain := by decide
example : poll (fun reply => .current reply.run)
    (fun reply => if reply.request = 1 then .terminal else .accepted) []
    [⟨7, 1, 1⟩, ⟨7, 1, 2⟩] =
    ⟨[], [⟨7, 1, 2⟩], [⟨7, 1, 1⟩]⟩ := by decide

#print axioms wrong_run_retires
#print axioms delivery_requires_current
#print axioms conserves_replies
#print axioms delivered_matches_observation
#print axioms accounted
#print axioms retained_head_blocks_followers

end DeferredReplies

/-! ## Legacy replies ahead of a correlated result

One live caller has legacy replies ahead of a correlated result in the
service's FIFO. Legacy delivery needs a free one-deep reply slot. The client
may continue listening while its correlated request is pending. Each turn
models a service opportunity with no new arrivals to this prefix.
-/

namespace MixedReplies

structure State where
  older : Nat
  slotFull : Bool
  ready : Bool
  deriving DecidableEq

def service (s : State) : State :=
  if s.older = 0 then { s with ready := true }
  else if s.slotFull then s
  else { s with older := s.older - 1, slotFull := true }

def turn (listen : Bool) (s : State) : State :=
  service (if listen then { s with slotFull := false } else s)

def run (listen : Bool) (s : State) : Nat → State
  | 0 => s
  | n + 1 => run listen (turn listen s) n

theorem full_slot_preserves_queue (s : State) (full : s.slotFull = true)
    (pending : 0 < s.older) (turns : Nat) : run false s turns = s := by
  have holds : turn false s = s := by simp [turn, service, full, Nat.ne_of_gt pending]
  induction turns with
  | zero => rfl
  | succ n ih => simpa [run, holds] using ih

theorem no_early_publication (s : State) (turns : Nat)
    (valid : s.ready = true → s.older = 0) :
    (run true s turns).ready = true → (run true s turns).older = 0 := by
  have preserved (state : State) (v : state.ready = true → state.older = 0) :
      (turn true state).ready = true → (turn true state).older = 0 := by
    by_cases empty : state.older = 0
    · simp [turn, service, empty]
    · intro h
      have older : state.ready = true := by simpa [turn, service, empty] using h
      exact (empty (v older)).elim
  induction turns generalizing s with
  | zero => exact valid
  | succ n ih => exact ih (turn true s) (preserved s valid)

theorem listening_reaches_correlated (s : State) : (run true s (s.older + 1)).ready = true := by
  suffices bound : ∀ (n : Nat) (state : State), state.older = n →
      (run true state (n + 1)).ready = true from bound s.older s rfl
  intro n
  induction n with
  | zero =>
      intro state older
      simp [run, turn, service, older]
  | succ n ih =>
      intro state older
      have next : (turn true state).older = n := by simp [turn, service, older]
      exact ih (turn true state) next

example : (run false ⟨2, true, false⟩ 12).ready = false := by decide
example : (run true ⟨2, true, false⟩ 3).ready = true := by decide

#print axioms full_slot_preserves_queue
#print axioms no_early_publication
#print axioms listening_reaches_correlated

end MixedReplies

/-! ## Prepared program launch

A Files ticket retains the installation path and arguments for one Spindle
run. Shell consumes it after a current observation. The staged program can
start once the correlated Files binding reply has settled successfully.
-/

namespace ProgramLaunch

structure Ticket where
  number : Nat
  run : Nat
  deriving DecidableEq, Repr

structure Prepared where
  issued : Nat
  pending : Option Ticket
  deriving DecidableEq, Repr

def prepare (state : Prepared) (run limit : Nat) : Prepared :=
  if state.issued < limit then
    let next := state.issued + 1
    ⟨next, some ⟨next, run⟩⟩
  else state

def take (state : Prepared) (observation : DeferredReplies.Observation) (number : Nat) :
    Prepared × Bool :=
  match state.pending with
  | none => (state, false)
  | some ticket =>
      if number ≠ ticket.number then (state, false)
      else match observation with
      | .unknown => (state, false)
      | .retired => ({ state with pending := none }, false)
      | .current run => ({ state with pending := none }, run == ticket.run)

theorem newly_prepared_number (state : Prepared) (run limit : Nat)
    (room : state.issued < limit) :
    (prepare state run limit).pending = some ⟨state.issued + 1, run⟩ := by
  simp [prepare, room]

theorem unknown_retains_ticket (state : Prepared) (number : Nat) :
    take state .unknown number = (state, false) := by
  cases h : state.pending <;> simp [take, h]

theorem matching_take_once (state : Prepared) (number run : Nat)
    (accepted : (take state (.current run) number).2 = true) :
    take (take state (.current run) number).1 (.current run) number =
      ((take state (.current run) number).1, false) := by
  cases h : state.pending with
  | none => simp [take, h] at accepted
  | some ticket =>
      by_cases matching : number = ticket.number
      · simp [take, h, matching]
      · simp [take, h, matching] at accepted

theorem stale_preparer_refused (state : Prepared) (ticket : Ticket) (run : Nat)
    (held : state.pending = some ticket) (stale : run ≠ ticket.run) :
    take state (.current run) ticket.number = ({ state with pending := none }, false) := by
  simp [take, held, stale]

inductive LaunchPhase where
  | awaiting | bound | active | refused
  deriving DecidableEq, Repr

inductive Event where
  | reply (request : Nat) (success : Bool)
  | activate
  deriving DecidableEq, Repr

def step (request : Nat) (phase : LaunchPhase) (event : Event) : LaunchPhase :=
  match phase, event with
  | .awaiting, .reply id success =>
      if id = request then (if success then .bound else .refused) else .awaiting
  | .bound, .activate => .active
  | _, _ => phase

def Ready (phase : LaunchPhase) : Prop := phase = .bound ∨ phase = .active

private theorem ready_after_step (request : Nat) (phase : LaunchPhase) (event : Event)
    (ready : Ready (step request phase event)) :
    Ready phase ∨ event = .reply request true := by
  cases phase with
  | awaiting =>
      cases event with
      | activate => simp [step, Ready] at ready
      | reply id success =>
          by_cases same : id = request <;> cases success <;> simp_all [step, Ready]
  | bound => exact Or.inl (Or.inl rfl)
  | active => exact Or.inl (Or.inr rfl)
  | refused => cases event <;> simp [step, Ready] at ready

private theorem ready_after_events (request : Nat) (phase : LaunchPhase) (events : List Event)
    (ready : Ready (events.foldl (step request) phase)) :
    Ready phase ∨ .reply request true ∈ events := by
  induction events generalizing phase with
  | nil => exact Or.inl ready
  | cons first rest ih =>
      change Ready (rest.foldl (step request) (step request phase first)) at ready
      rcases ih (step request phase first) ready with head | tail
      · rcases ready_after_step request phase first head with old | receipt
        · exact Or.inl old
        · exact Or.inr (by simp [receipt])
      · exact Or.inr (List.mem_cons_of_mem _ tail)

theorem activation_requires_binding_reply (request : Nat) (events : List Event)
    (active : events.foldl (step request) .awaiting = .active) :
    .reply request true ∈ events := by
  rcases ready_after_events request .awaiting events (Or.inr active) with initial | reply
  · simp [Ready] at initial
  · exact reply

example : [Event.reply 7 true, .activate].foldl (step 7) .awaiting = .active := by decide
example : [Event.reply 6 true, .activate].foldl (step 7) .awaiting = .awaiting := by decide
example : [Event.reply 7 false, .activate].foldl (step 7) .awaiting = .refused := by decide

#print axioms matching_take_once
#print axioms stale_preparer_refused
#print axioms activation_requires_binding_reply

end ProgramLaunch

/-! ## Child launch receipts

An accepted notification is distinct from the observation that authorizes it.
A terminal notice identifies the child run. A successful transport submission
to the held starter identifies the publication. Failed submissions preserve
the pending receipt. This state follows one already admitted child.
-/

namespace ChildLaunch

structure Subject where
  row : Nat
  task : Nat
  deriving DecidableEq, Repr

structure Run where
  parent : Subject
  child : Subject
  deriving DecidableEq, Repr

structure Delivery where
  started : Bool := false
  terminal : Bool := false
  done : Bool := false
  deriving DecidableEq, Repr

inductive Event where
  | started (receiver : Subject) (accepted : Bool)
  | terminal (sender : Subject)
  | done (receiver : Subject) (accepted : Bool)
  deriving DecidableEq, Repr

def step (run : Run) (delivery : Delivery) : Event → Delivery
  | .started receiver accepted =>
      if receiver = run.parent ∧ accepted = true then { delivery with started := true }
      else delivery
  | .terminal sender =>
      if sender = run.child then { delivery with terminal := true } else delivery
  | .done receiver accepted =>
      if receiver = run.parent ∧ accepted = true ∧
          delivery.started = true ∧ delivery.terminal = true then
        { delivery with done := true }
      else delivery

theorem refusal_retains_delivery (run : Run) (delivery : Delivery) (receiver : Subject) :
    step run delivery (.started receiver false) = delivery ∧
    step run delivery (.done receiver false) = delivery := by
  simp [step]

theorem stale_terminal_retains_delivery (run : Run) (delivery : Delivery) (sender : Subject)
    (stale : sender ≠ run.child) : step run delivery (.terminal sender) = delivery := by
  simp [step, stale]

def Evidence (run : Run) (events : List Event) (delivery : Delivery) : Prop :=
  (delivery.started = true → .started run.parent true ∈ events) ∧
  (delivery.terminal = true → .terminal run.child ∈ events) ∧
  (delivery.done = true →
    .started run.parent true ∈ events ∧ .terminal run.child ∈ events ∧
      .done run.parent true ∈ events)

private theorem extend (run : Run) (events : List Event) (delivery : Delivery) (event : Event)
    (evidence : Evidence run events delivery) :
    Evidence run (events ++ [event]) (step run delivery event) := by
  have retained (e : Event) (mem : e ∈ events) : e ∈ events ++ [event] :=
    List.mem_append_left _ mem
  rcases evidence with ⟨started, terminal, done⟩
  have old : Evidence run (events ++ [event]) delivery :=
    ⟨fun h => retained _ (started h), fun h => retained _ (terminal h), fun h =>
      let ⟨s, t, d⟩ := done h
      ⟨retained _ s, retained _ t, retained _ d⟩⟩
  cases event with
  | started receiver accepted =>
      simp only [step]
      split
      next h =>
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨fun _ => by simp, old.2.1, old.2.2⟩
      next => exact old
  | terminal sender =>
      simp only [step]
      split
      next h =>
        subst sender
        exact ⟨old.1, fun _ => by simp, old.2.2⟩
      next => exact old
  | done receiver accepted =>
      simp only [step]
      split
      next h =>
        obtain ⟨rfl, rfl, ready, ended⟩ := h
        exact ⟨old.1, old.2.1, fun _ => ⟨old.1 ready, old.2.1 ended, by simp⟩⟩
      next => exact old

private theorem trace_from (run : Run) (events history : List Event) (initial : Delivery)
    (evidence : Evidence run history initial) :
    Evidence run (history ++ events) (events.foldl (step run) initial) := by
  induction events generalizing history initial with
  | nil => simpa using evidence
  | cons head tail ih =>
      simpa only [List.append_assoc, List.singleton_append, List.foldl_cons] using
        ih (history ++ [head]) (step run initial head) (extend run history initial head evidence)

theorem trace_has_evidence (run : Run) (events : List Event) :
    Evidence run events (events.foldl (step run) {}) := by
  simpa only [List.nil_append] using trace_from run events [] {} (by simp [Evidence])

theorem done_has_parent_start_and_child_terminal (run : Run) (events : List Event)
    (done : (events.foldl (step run) {}).done = true) :
    .started run.parent true ∈ events ∧ .terminal run.child ∈ events ∧
      .done run.parent true ∈ events :=
  (trace_has_evidence run events).2.2 done

def exampleRun : Run := ⟨⟨42, 50⟩, ⟨43, 51⟩⟩

example : ([.terminal ⟨43, 49⟩, .started ⟨42, 50⟩ true, .done ⟨42, 50⟩ true].foldl
    (step exampleRun) {}).done = false := by decide
example : ([.terminal ⟨43, 51⟩, .started ⟨42, 50⟩ false, .started ⟨42, 50⟩ true,
    .done ⟨42, 50⟩ true].foldl (step exampleRun) {}).done = true := by decide

#print axioms done_has_parent_start_and_child_terminal

end ChildLaunch

/-! ## Bounded pipe input

Offers may accept a prefix. A hang-up closes further offers and preserves
the FIFO for reads. Accepted and delivered bytes are trace observations.
The native ring and the held IPC adapter implement this transition contract.
-/

namespace PipeInput

structure Buffer (α : Type) where
  pending : List α := []
  accepted : List α := []
  delivered : List α := []
  closed : Bool := false
  deriving DecidableEq

inductive Event (α : Type) where
  | offer (bytes : List α)
  | receive (count : Nat)
  | hangUp

variable {α : Type}

def step (limit : Nat) (buffer : Buffer α) : Event α → Buffer α
  | .offer bytes =>
      if buffer.closed then buffer
      else
        let admitted := bytes.take (limit - buffer.pending.length)
        { buffer with pending := buffer.pending ++ admitted, accepted := buffer.accepted ++ admitted }
  | .receive count =>
      { buffer with pending := buffer.pending.drop count,
                    delivered := buffer.delivered ++ buffer.pending.take count }
  | .hangUp => { buffer with closed := true }

def Valid (limit : Nat) (buffer : Buffer α) : Prop :=
  buffer.pending.length ≤ limit ∧ buffer.delivered ++ buffer.pending = buffer.accepted

theorem valid_step (limit : Nat) (buffer : Buffer α) (event : Event α)
    (valid : Valid limit buffer) : Valid limit (step limit buffer event) := by
  rcases valid with ⟨fits, fifo⟩
  cases event with
  | offer bytes =>
      by_cases closed : buffer.closed = true
      · simpa [step, closed, Valid] using And.intro fits fifo
      · simp only [step, if_neg closed, Valid, List.length_append, List.length_take]
        constructor
        · have short := Nat.min_le_left (limit - buffer.pending.length) bytes.length
          omega
        · rw [← List.append_assoc, fifo]
  | receive count =>
      simp only [step, Valid, List.length_drop]
      exact ⟨Nat.le_trans (Nat.sub_le _ _) fits,
        by rw [List.append_assoc, List.take_append_drop, fifo]⟩
  | hangUp =>
      exact ⟨fits, fifo⟩

theorem valid_trace (limit : Nat) (buffer : Buffer α) (events : List (Event α))
    (valid : Valid limit buffer) : Valid limit (events.foldl (step limit) buffer) := by
  induction events generalizing buffer with
  | nil => exact valid
  | cons head tail ih =>
      exact ih (step limit buffer head) (valid_step limit buffer head valid)

theorem offer_after_hangup (limit : Nat) (buffer : Buffer α) (bytes : List α) :
    step limit (step limit buffer .hangUp) (.offer bytes) = step limit buffer .hangUp := by
  simp [step]

theorem drained_input_matches_accepted (limit : Nat) (events : List (Event α))
    (empty : (events.foldl (step limit) {}).pending = []) :
    (events.foldl (step limit) {}).delivered = (events.foldl (step limit) {}).accepted := by
  have valid := valid_trace limit ({} : Buffer α) events (by simp [Valid])
  simpa only [empty, List.append_nil] using valid.2

example :
    ([.offer [1, 2, 3, 4], .receive 2, .offer [4, 5], .hangUp, .receive 4].foldl
      (step 3) {}).delivered = [1, 2, 3, 4, 5] := by decide
example :
    ([.offer [1], .hangUp, .offer [2], .receive 2].foldl
      (step 3) {}).delivered = [1] := by decide

#print axioms drained_input_matches_accepted

end PipeInput

/-! ## Discarding a staged image

This tracks the task and remaining frame leases of an unstarted image.
Release steps represent allocator observations. The row becomes reusable
only after those leases settle, and staging again advances the task.
-/

namespace StagedDiscard

inductive Phase where
  | staged | discarding | reusable | running
  deriving DecidableEq, Repr

structure Row where
  task : Nat
  phase : Phase
  frames : Nat
  deriving DecidableEq, Repr

inductive Event where
  | discard (task : Nat)
  | release (task count : Nat)
  | reclaimed (task : Nat)
  | stage (task frames : Nat)
  | activate (task : Nat)

def step (row : Row) : Event → Row
  | .discard task =>
      if task = row.task ∧ row.phase = .staged then { row with phase := .discarding } else row
  | .release task count =>
      if task = row.task ∧ row.phase = .discarding ∧ count ≤ row.frames then
        { row with frames := row.frames - count }
      else row
  | .reclaimed task =>
      if task = row.task ∧ row.phase = .discarding ∧ row.frames = 0 then
        { row with phase := .reusable }
      else row
  | .stage task frames =>
      if row.phase = .reusable ∧ row.task < task then ⟨task, .staged, frames⟩ else row
  | .activate task =>
      if task = row.task ∧ row.phase = .staged then { row with phase := .running } else row

theorem reusable_has_released_leases (row : Row) (event : Event)
    (released : row.phase = .reusable → row.frames = 0) :
    (step row event).phase = .reusable → (step row event).frames = 0 := by
  cases event <;> simp only [step] <;> split <;> simp_all

def Closed (task : Nat) (row : Row) : Prop :=
  task ≤ row.task ∧ (row.task = task → row.phase = .discarding ∨ row.phase = .reusable)

theorem closed_preserved (task : Nat) (row : Row) (event : Event)
    (closed : Closed task row) : Closed task (step row event) := by
  rcases closed with ⟨issued, stopped⟩
  cases event with
  | discard who =>
      by_cases h : who = row.task ∧ row.phase = .staged
      · simp [step, h, Closed, issued]
      · simpa [step, h, Closed] using And.intro issued stopped
  | release who count =>
      by_cases h : who = row.task ∧ row.phase = .discarding ∧ count ≤ row.frames
      · simpa [step, h, Closed] using And.intro issued stopped
      · simpa [step, h, Closed] using And.intro issued stopped
  | reclaimed who =>
      by_cases h : who = row.task ∧ row.phase = .discarding ∧ row.frames = 0
      · simp [step, h, Closed, issued]
      · simpa [step, h, Closed] using And.intro issued stopped
  | stage next frames =>
      by_cases h : row.phase = .reusable ∧ row.task < next
      · have fresh : task < next := Nat.lt_of_le_of_lt issued h.2
        simp [step, h, Closed, Nat.le_of_lt fresh, Nat.ne_of_gt fresh]
      · simpa [step, h, Closed] using And.intro issued stopped
  | activate who =>
      by_cases h : who = row.task ∧ row.phase = .staged
      · have fresh : row.task ≠ task := by
          intro same
          simpa [h.2] using stopped same
        simp [step, h, Closed, issued, fresh]
      · simpa [step, h, Closed] using And.intro issued stopped

theorem running_after_discard_has_fresh_task (task frames : Nat) (events : List Event)
    (running : (events.foldl step ⟨task, .discarding, frames⟩).phase = .running) :
    task < (events.foldl step ⟨task, .discarding, frames⟩).task := by
  have through (row : Row) (events : List Event) (closed : Closed task row) :
      Closed task (events.foldl step row) := by
    induction events generalizing row with
    | nil => exact closed
    | cons next rest ih => exact ih (step row next) (closed_preserved task row next closed)
  obtain ⟨issued, stopped⟩ := through ⟨task, .discarding, frames⟩ events
    ⟨Nat.le_refl _, fun _ => Or.inl rfl⟩
  exact Nat.lt_of_le_of_ne issued (fun same => by simpa [running] using stopped same.symm)

example : [Event.discard 7, .release 7 2, .reclaimed 7].foldl step ⟨7, .staged, 3⟩ =
    ⟨7, .discarding, 1⟩ := by decide
example : [Event.discard 7, .release 7 3, .reclaimed 7, .stage 8 4, .activate 7,
    .activate 8].foldl step ⟨7, .staged, 3⟩ = ⟨8, .running, 4⟩ := by decide

#print axioms reusable_has_released_leases
#print axioms running_after_discard_has_fresh_task

end StagedDiscard

def exampleState : State := ⟨7, 10, [8, 9]⟩
def exampleMain : Context := ⟨7, ⟨70, 7, .main⟩⟩
def exampleWorker : Context := ⟨7, ⟨1073741824, 7, .worker⟩⟩
def exampleStaleWorker : Context := ⟨6, ⟨1073741824, 6, .worker⟩⟩

example : (invoke exampleState exampleMain true).2 = .blocked 11 := by decide
example : (invoke exampleState exampleWorker true).2 = .polling 11 := by decide
example : invoke exampleState exampleStaleWorker true = (exampleState, .refused) := by decide
example : (invoke exampleState exampleWorker true).1.pending = [8, 9, 11] := by decide
example : settle (settle exampleState 8) 8 = settle exampleState 8 := by decide

#print axioms authenticated_execution_irrelevant
#print axioms custody_execution_irrelevant
#print axioms refused_preserves_state
#print axioms accepted_creates_custody
#print axioms Valid.invoke
#print axioms Valid.settle
#print axioms worker_never_main_blocks
#print axioms settle_twice

end Mettapedia.Machines.Kernel.InvocationContext
