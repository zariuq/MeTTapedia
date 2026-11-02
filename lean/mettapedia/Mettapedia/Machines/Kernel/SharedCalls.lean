import Mettapedia.Machines.Kernel.CorrelatedReplies

/-!
# Shared calls and finite wake obligations

The correlated-call core already issues non-reused identities and permits one
designated executor to claim a queued call. This module gives shared readers
a non-consuming observation and proves that a claimed call cannot regain its
execution permit under later core operations.

A separate wake ticket has an explicit deadline and one notification receipt.
Expiration, completion and acknowledgement cannot notify it twice. Eventual
execution by a scheduler is a separate progress assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.CorrelatedReplies.Shared

variable {Peer : Type} [DecidableEq Peer]

def observe (w : Window Peer) (id : Nat) : Result :=
  match lookup w id with
  | some c => match c.phase with
    | .ready value => .value value
    | _ => .pending
  | none => .refused

omit [DecidableEq Peer] in
theorem shared_result (w : Window Peer) (id value : Nat)
    (ready : ∃ c, lookup w id = some c ∧ c.phase = .ready value) :
    observe w id = .value value := by
  obtain ⟨c, found, phase⟩ := ready
  simp [observe, found, phase]

theorem complete_then_observe (w : Window Peer) (actor : Peer) (id value : Nat)
    (finished : (complete w actor id value).2 = .done) :
    observe (complete w actor id value).1 id = .value value := by
  obtain ⟨c, found⟩ := completion_retained w actor id value finished
  exact shared_result _ _ _ ⟨_, found, rfl⟩

def Spent (w : Window Peer) (id : Nat) : Prop :=
  ∀ c, lookup w id = some c → c.phase ≠ .queued

theorem spent_refuses_claim (w : Window Peer) (id : Nat) (spent : Spent w id) (actor : Peer) :
    claim w actor id = (w, .refused) := by
  unfold claim
  split
  · rename_i c found
    simp [spent c found]
  · rfl

theorem claim_spends (w : Window Peer) (actor : Peer) (id : Nat)
    (claimed : (claim w actor id).2 = .done) : Spent (claim w actor id).1 id := by
  unfold claim at claimed ⊢
  split at claimed <;> try contradiction
  rename_i c found
  split at claimed <;> try contradiction
  rename_i eligible
  intro next nextFound
  have normalized : lookup (setPhase w id .heard) id = some next := by
    simpa [eligible] using nextFound
  clear nextFound
  rw [lookup_setPhase, found] at normalized
  cases normalized
  simp

omit [DecidableEq Peer] in
theorem lookup_append_other (w : Window Peer) (newCall : Call Peer) (id : Nat)
    (different : newCall.id ≠ id) :
    lookup ⟨w.issued + 1, w.calls ++ [newCall]⟩ id = lookup w id := by
  simp only [lookup, List.find?_append]
  cases found : w.calls.find? (fun c => c.id == id) <;> simp [different]

omit [DecidableEq Peer] in
theorem spent_setPhase (w : Window Peer) (id other : Nat) (phase : Phase)
    (spent : Spent w id) (notQueued : phase ≠ .queued) : Spent (setPhase w other phase) id := by
  intro c found
  by_cases same : id = other
  · subst other
    rw [lookup_setPhase] at found
    cases old : lookup w id <;> simp [old] at found
    cases found
    exact notQueued
  · rw [lookup_setPhase_other w other id phase same] at found
    exact spent c found

omit [DecidableEq Peer] in
theorem spent_remove (w : Window Peer) (id other : Nat) (spent : Spent w id) :
    Spent (remove w other) id := by
  intro c found
  by_cases same : id = other
  · subst other; rw [lookup_remove] at found; contradiction
  · rw [lookup_remove_other w other id same] at found
    exact spent c found

theorem spent_step (config : Config Peer) (w : Window Peer) (op : Op Peer) (id : Nat)
    (old : id ≤ w.issued) (spent : Spent w id) : Spent (step config w op).1 id := by
  cases op with
  | admit peer registered room =>
      simp only [step, admit]
      split <;> try exact spent
      split <;> try exact spent
      split <;> try exact spent
      intro c found
      rw [lookup_append_other] at found
      · exact spent c found
      · dsimp; omega
  | claim actor other =>
      simp only [step, claim]
      split <;> try exact spent
      split <;> try exact spent
      exact spent_setPhase w id other .heard spent (by simp)
  | complete actor other value =>
      simp only [step, complete]
      split <;> try exact spent
      split <;> try exact spent
      exact spent_setPhase w id other (.ready value) spent (by simp)
  | poll other =>
      simp only [step, poll]
      split <;> try exact spent
      split <;> try exact spent
      exact spent_remove w id other spent
  | cancel other =>
      simp only [step, cancel]
      split <;> try exact spent
      exact spent_remove w id other spent

theorem spent_run (config : Config Peer) (w : Window Peer) (ops : List (Op Peer)) (id : Nat)
    (old : id ≤ w.issued) (spent : Spent w id) : Spent (run config w ops) id := by
  induction ops generalizing w with
  | nil => exact spent
  | cons op rest ih =>
      exact ih (step config w op).1 (Nat.le_trans old (step_issued_monotone config w op))
        (spent_step config w op id old spent)

theorem later_readers_cannot_restart (config : Config Peer) (w : Window Peer)
    (actor laterActor : Peer) (id : Nat) (ops : List (Op Peer))
    (old : id ≤ w.issued) (claimed : (claim w actor id).2 = .done) :
    claim (run config (claim w actor id).1 ops) laterActor id =
      (run config (claim w actor id).1 ops, .refused) := by
  apply spent_refuses_claim
  apply spent_run config _ ops id
  · exact Nat.le_trans old (step_issued_monotone config w (.claim actor id))
  · exact claim_spends w actor id claimed

end Mettapedia.Machines.Kernel.CorrelatedReplies.Shared

namespace Mettapedia.Machines.Kernel.WakeTicket

inductive Phase where
  | pending | notified | consumed
  deriving DecidableEq, Repr

structure Ticket where
  call : Nat
  reader : Nat
  deadline : Nat
  phase : Phase
  notifications : Nat
  deriving DecidableEq, Repr

def Valid (ticket : Ticket) : Prop :=
  ticket.notifications = if ticket.phase = .pending then 0 else 1

def register (call reader now delay : Nat) : Option Ticket :=
  if delay = 0 then none else some ⟨call, reader, now + delay, .pending, 0⟩

def notify (ticket : Ticket) : Ticket :=
  if ticket.phase = .pending then
    { ticket with phase := .notified, notifications := ticket.notifications + 1 }
  else ticket

def expire (now : Nat) (ticket : Ticket) : Ticket :=
  if ticket.deadline ≤ now then notify ticket else ticket

def consume (ticket : Ticket) : Ticket :=
  if ticket.phase = .notified then { ticket with phase := .consumed } else ticket

theorem register_future (call reader now delay : Nat) (ticket : Ticket)
    (registered : register call reader now delay = some ticket) :
    ticket.call = call ∧ ticket.reader = reader ∧ now < ticket.deadline ∧ Valid ticket := by
  unfold register at registered
  split at registered <;> try contradiction
  cases registered
  simp [Valid]
  omega

theorem notify_valid (ticket : Ticket) (valid : Valid ticket) : Valid (notify ticket) := by
  rcases ticket with ⟨call, reader, deadline, phase, notifications⟩
  cases phase <;> simp_all [Valid, notify]

theorem consume_valid (ticket : Ticket) (valid : Valid ticket) : Valid (consume ticket) := by
  rcases ticket with ⟨call, reader, deadline, phase, notifications⟩
  cases phase <;> simp_all [Valid, consume]

theorem expire_valid (now : Nat) (ticket : Ticket) (valid : Valid ticket) :
    Valid (expire now ticket) := by
  unfold expire
  split
  · exact notify_valid ticket valid
  · exact valid

theorem notify_once (ticket : Ticket) : notify (notify ticket) = notify ticket := by
  rcases ticket with ⟨call, reader, deadline, phase, notifications⟩
  cases phase <;> simp [notify]

theorem consume_once (ticket : Ticket) : consume (consume ticket) = consume ticket := by
  rcases ticket with ⟨call, reader, deadline, phase, notifications⟩
  cases phase <;> simp [consume]

theorem expired_not_pending (now : Nat) (ticket : Ticket) (due : ticket.deadline ≤ now) :
    (expire now ticket).phase ≠ .pending := by
  rcases ticket with ⟨call, reader, deadline, phase, notifications⟩
  cases phase <;> simp_all [expire, notify]

theorem notification_bound (ticket : Ticket) (valid : Valid ticket) : ticket.notifications ≤ 1 := by
  rw [valid]
  split <;> omega

inductive Action where
  | completion (call : Nat)
  | timeout (now : Nat)
  | acknowledge

def step (ticket : Ticket) : Action → Ticket
  | .completion call => if call = ticket.call then notify ticket else ticket
  | .timeout now => expire now ticket
  | .acknowledge => consume ticket

def run (ticket : Ticket) (actions : List Action) : Ticket := actions.foldl step ticket

theorem step_valid (ticket : Ticket) (action : Action) (valid : Valid ticket) :
    Valid (step ticket action) := by
  cases action with
  | completion call =>
      simp only [step]
      split
      · exact notify_valid ticket valid
      · exact valid
  | timeout now => exact expire_valid now ticket valid
  | acknowledge => exact consume_valid ticket valid

theorem run_valid (ticket : Ticket) (actions : List Action) (valid : Valid ticket) :
    Valid (run ticket actions) := by
  induction actions generalizing ticket with
  | nil => exact valid
  | cons action rest ih => exact ih (step ticket action) (step_valid ticket action valid)

theorem notification_bound_all_interleavings (ticket : Ticket) (actions : List Action)
    (valid : Valid ticket) : (run ticket actions).notifications ≤ 1 :=
  notification_bound _ (run_valid ticket actions valid)

theorem unrelated_completion_ignored (ticket : Ticket) (other : Nat)
    (different : other ≠ ticket.call) : step ticket (.completion other) = ticket := by
  simp [step, different]

theorem zero_delay_refused (call reader now : Nat) : register call reader now 0 = none := by
  simp [register]

def exampleTicket : Ticket := ⟨7, 2, 10, .pending, 0⟩

theorem example_completion_timeout_acknowledgement :
    run exampleTicket [.completion 8, .completion 7, .timeout 10,
      .completion 7, .acknowledge, .acknowledge] = ⟨7, 2, 10, .consumed, 1⟩ := by
  decide

theorem example_timeout_wakes :
    (run exampleTicket [.completion 8, .timeout 10]).phase = .notified := by
  decide

#print axioms register_future
#print axioms expired_not_pending
#print axioms notify_valid
#print axioms notification_bound_all_interleavings

end Mettapedia.Machines.Kernel.WakeTicket
