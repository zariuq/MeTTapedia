import Mettapedia.Protocols.Mail.Mailbox

/-!
# Input settlement: wakes, dispositions and delivery identity

An agent's kernel is woken while some input delivery is unsettled. Settlement is
recorded per delivery identity in the store-and-forward mailbox of
`Mettapedia.Protocols.Mail.Mailbox`: `stored` is the durable log of deliveries,
`seen` the settled identities and `unread` what is still pending. A turn shows the
kernel some pending deliveries. The kernel's actions are durable as they happen;
a committed turn boundary then settles what was shown. A crash between the
actions and the boundary skips that settlement, so the same deliveries are shown
again: delivery is at least once.

Proved here:

* Settlement only filters: settling any identities removes exactly those
  deliveries from the pending list (`unread_ackAll`). Arrival settles nothing
  (`deliver_seen`), and a delivery with a fresh identity is pending and wakes the
  kernel whatever its text (`fresh_delivery_wakes`).
* With no new input, every run whose woken turns each settle something wakes at
  most as often as there were pending deliveries (`wakeCount_le`). A committed
  boundary settles something whatever the kernel did (`committed_turn_progress`,
  `committed_runs_bounded`).
* Under the live discipline a disposition writes workflow status only, a store
  the wake does not read. A run of turns that crash before their boundary leaves
  the mailbox unchanged and wakes on every turn, whatever the kernel does,
  dispositions included (`live_crash_loop`). Under the repaired discipline a
  disposition settles the delivery it names in the same transaction, so a
  disposition of something shown is progress even when the turn crashes
  (`repaired_disposition_progress`, `repaired_settling_bounded`). A kernel that
  neither commits nor disposes is shown the same input again under either
  discipline (`no_disposition_crash_loop`). Settling on presentation instead
  loses input that a crash interrupts, as `PettaClaw.InputDelivery` shows.
* Settling by any key coarser than delivery identity (a content digest, a
  "same notice" class) hides a later, distinct delivery that shares the key
  (`coarse_key_swallows`), for instance a person repeating a short reply, while
  identity keeps it (`identity_key_keeps`). A kind computed through any view that
  identifies two deliveries of different true kinds is wrong on one of them
  (`kind_view_errs`): text cannot separate a machine notice from a person quoting
  it, and a channel shared by people and workers cannot separate them either.
* Workflow records. The live rules refuse `addressed` for an input that no
  committed turn has processed. From a deferred, unprocessed input, `defer` and
  `addressed` return the identical record (`live_attempts_fixed`), and every
  disposition except `keep` leaves it open and unprocessed (`live_trap`). The
  only escapes are a `keep` that re-kinds the input as a task
  (`live_keep_escape`) or a later committed checkpoint (`live_settle_escape`).
  The repaired rule deletes that one refusal and lets an accepted disposition
  settle the input it names; the repaired projection leaves out covered batches,
  whose deliveries the covering batch carries. One `addressed` then closes every
  open operator row (`repaired_addressed_closes`), and every other refusal stays
  (`repaired_keeps_guards`). Repaired dispositions settle and are idempotent
  (`repaired_settles`, `disposeRepaired_idempotent`). The repaired `defer` equals
  a live `defer` followed by a committed settlement, in one transaction and
  without a later turn (`repaired_defer_is_settled_defer`). In the ledger one
  transaction settles the delivery and closes the record
  (`dispose_closes_both_layers`).
* An effect keyed by the delivery it answers and its ordinal is performed at most
  once, however often that delivery is shown again (`keyed_effects_at_most_once`).
  This is the input-side counterpart of request-identity replay in
  `PettaClaw.LlmLedger`; a key with a fresh nonce per attempt repeats the effect.

The kernel is arbitrary: the run theorems quantify over every sequence of
actions, so kernels with memory, randomness or a language model are covered.
Nothing here proves that a kernel chooses to dispose, that an engine does not
crash, or that a runtime's code refines these transitions. The open-work
projection is modelled without its focus row, and a request formed from several
deliveries is modelled as one delivery: the repaired transaction settles each of
them.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.InputSettlement

open Mettapedia.Protocols.Mail

/-! ## Pending deliveries and the wake predicate -/

/-- The substrate wakes the kernel exactly while some delivery is unsettled. -/
def Wakes (b : Mailbox) : Prop := b.unread ≠ []

/-- Settle several identities, one after another. -/
def ackAll (b : Mailbox) (ids : List MessageId) : Mailbox := ids.foldl Mailbox.ack b

/-- Settling an identity removes exactly the pending deliveries with that identity. -/
theorem unread_ack (b : Mailbox) (id : MessageId) :
    (b.ack id).unread = b.unread.filter (fun m => m.id ≠ id) := by
  unfold Mailbox.ack Mailbox.unread
  split
  · rw [List.filter_filter]
    congr 1
    funext m
    simp [List.mem_append, not_or]
    exact Bool.and_comm _ _
  · next h =>
    symm
    rw [List.filter_eq_self]
    intro m hm
    simp only [List.mem_filter, decide_eq_true_eq] at hm
    simp only [decide_eq_true_eq]
    intro hid
    subst hid
    exact h ⟨List.mem_map_of_mem hm.1, hm.2⟩

theorem unread_ackAll (b : Mailbox) (ids : List MessageId) :
    (ackAll b ids).unread = b.unread.filter (fun m => m.id ∉ ids) := by
  induction ids generalizing b with
  | nil => simp [ackAll]
  | cons id ids ih =>
    show (ackAll (b.ack id) ids).unread = _
    rw [ih, unread_ack, List.filter_filter]
    congr 1
    funext m
    simp [not_or]
    exact Bool.and_comm _ _

theorem ackAll_unread_length_le (b : Mailbox) (ids : List MessageId) :
    (ackAll b ids).unread.length ≤ b.unread.length := by
  rw [unread_ackAll]
  exact List.length_filter_le _ _

theorem ackAll_unread_length_lt (b : Mailbox) (ids : List MessageId) {m : Message}
    (hm : m ∈ b.unread) (hid : m.id ∈ ids) :
    (ackAll b ids).unread.length < b.unread.length := by
  rw [unread_ackAll]
  exact List.length_filter_lt_length_iff_exists.mpr ⟨m, hm, by simpa using hid⟩

/-- Arrival never settles anything. -/
theorem deliver_seen (b : Mailbox) (m : Message) : (b.deliver m).seen = b.seen := by
  unfold Mailbox.deliver
  split <;> rfl

/-- A delivery whose identity the mailbox has not stored is pending after it arrives,
and wakes the kernel, whatever its text. -/
theorem fresh_delivery_wakes {b : Mailbox} (hb : b.Valid) {m : Message}
    (fresh : m.id ∉ b.ids) : m ∈ (b.deliver m).unread ∧ Wakes (b.deliver m) := by
  have hseen : m.id ∉ b.seen := fun h => fresh (hb.seenStored _ h)
  have hmem : m ∈ (b.deliver m).unread := by
    unfold Mailbox.unread Mailbox.deliver
    simp [fresh, hseen]
  exact ⟨hmem, List.ne_nil_of_mem hmem⟩

/-! ## Turns and runs -/

/-- What settlement can see of a kernel action: a disposition naming a delivery, or
anything else (a reply, a rest, a no-op, a tool call). -/
inductive Action where
  | dispose (id : MessageId)
  | other
  deriving DecidableEq, Repr

/-- The identities a turn's actions dispose of. -/
def disposed : List Action → List MessageId
  | [] => []
  | .dispose id :: as => id :: disposed as
  | .other :: as => disposed as

theorem mem_disposed {id : MessageId} {acts : List Action} :
    id ∈ disposed acts ↔ Action.dispose id ∈ acts := by
  induction acts with
  | nil => simp [disposed]
  | cons a as ih =>
    cases a with
    | dispose x => simp only [disposed, List.mem_cons, ih, Action.dispose.injEq]
    | other => simp [disposed, ih]

/-- How a successful disposition affects settlement. -/
inductive Discipline where
  /-- A disposition writes workflow status only; the committed boundary settles. -/
  | live
  /-- A disposition also settles the delivery it names, in the same transaction. -/
  | repaired
  deriving DecidableEq, Repr

def Discipline.settles : Discipline → List Action → List MessageId
  | .live, _ => []
  | .repaired, acts => disposed acts

/-- The batch a turn shows: pending deliveries, and some whenever any are pending
(all of a conversation's pending updates, or one mail or job completion). -/
structure Presenter where
  batch : Mailbox → List Message
  batch_pending : ∀ b m, m ∈ batch b → m ∈ b.unread
  batch_nonempty : ∀ b, b.unread ≠ [] → batch b ≠ []

/-- One turn. The kernel's dispositions are durable as they happen; a committed boundary
then settles the shown batch. `commits = false` is a crash, or a failed provider call or
history write, before that boundary. -/
def turn (d : Discipline) (p : Presenter) (b : Mailbox) (acts : List Action)
    (commits : Bool) : Mailbox :=
  ackAll b (d.settles acts ++ if commits then (p.batch b).map Message.id else [])

/-- A turn: the kernel's actions and whether its boundary committed. -/
abbrev Turn := List Action × Bool

/-- The mailbox after consecutive turns with no arrival between them. -/
def final (d : Discipline) (p : Presenter) : Mailbox → List Turn → Mailbox
  | b, [] => b
  | b, t :: ts => final d p (turn d p b t.1 t.2) ts

/-- How many turns of a run found something pending. -/
def wakeCount (d : Discipline) (p : Presenter) : Mailbox → List Turn → Nat
  | _, [] => 0
  | b, t :: ts => (if b.unread = [] then 0 else 1) + wakeCount d p (turn d p b t.1 t.2) ts

/-- Every turn of the run that found something pending settled something. -/
def Progressive (d : Discipline) (p : Presenter) : Mailbox → List Turn → Prop
  | _, [] => True
  | b, t :: ts => (Wakes b → (turn d p b t.1 t.2).unread.length < b.unread.length) ∧
      Progressive d p (turn d p b t.1 t.2) ts

theorem turn_unread_length_le (d : Discipline) (p : Presenter) (b : Mailbox)
    (acts : List Action) (commits : Bool) :
    (turn d p b acts commits).unread.length ≤ b.unread.length :=
  ackAll_unread_length_le _ _

/-- No livelock: without arrivals, a run whose woken turns each settle something wakes at
most as many times as there were pending deliveries. -/
theorem wakeCount_le {d : Discipline} {p : Presenter} :
    ∀ (b : Mailbox) (ts : List Turn),
      Progressive d p b ts → wakeCount d p b ts ≤ b.unread.length
  | _, [], _ => Nat.zero_le _
  | b, t :: ts, ⟨h, hs⟩ => by
    have ih := wakeCount_le (turn d p b t.1 t.2) ts hs
    simp only [wakeCount]
    by_cases hb : b.unread = []
    · have hle := turn_unread_length_le d p b t.1 t.2
      rw [hb] at hle
      simp only [hb, if_true, List.length_nil] at hle ⊢
      omega
    · have hlt := h hb
      simp only [hb, if_false]
      omega

/-- A committed boundary settles part of what was pending, whatever the kernel did. -/
theorem committed_turn_progress (d : Discipline) (p : Presenter) (b : Mailbox)
    (acts : List Action) (hw : Wakes b) :
    (turn d p b acts true).unread.length < b.unread.length := by
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ (p.batch_nonempty b hw)
  exact ackAll_unread_length_lt b _ (p.batch_pending b m hm)
    (List.mem_append_right _ (by simpa using List.mem_map_of_mem (f := Message.id) hm))

/-- Wakes without new input are bounded by the pending deliveries when every turn commits,
for every kernel and either discipline. -/
theorem committed_runs_bounded (d : Discipline) (p : Presenter) (b : Mailbox)
    (acts : List (List Action)) :
    wakeCount d p b (acts.map fun a => (a, true)) ≤ b.unread.length := by
  apply wakeCount_le
  induction acts generalizing b with
  | nil => trivial
  | cons a as ih => exact ⟨committed_turn_progress d p b a, ih _⟩

/-- A turn that crashes before its boundary and disposes of nothing changes nothing,
under either discipline. -/
theorem no_disposition_crash_stutters (d : Discipline) (p : Presenter) (b : Mailbox)
    (acts : List Action) (none : disposed acts = []) : turn d p b acts false = b := by
  cases d <;> simp [turn, Discipline.settles, none, ackAll]

/-- Under the live discipline a crashing turn changes nothing, dispositions included. -/
theorem live_crash_stutters (p : Presenter) (b : Mailbox) (acts : List Action) :
    turn .live p b acts false = b := by
  simp [turn, Discipline.settles, ackAll]

theorem crash_loop_of_stutter {d : Discipline} {p : Presenter} {b : Mailbox}
    (hw : Wakes b) (acts : List (List Action))
    (stutter : ∀ a ∈ acts, turn d p b a false = b) :
    final d p b (acts.map fun a => (a, false)) = b ∧
      wakeCount d p b (acts.map fun a => (a, false)) = acts.length := by
  induction acts with
  | nil => simp [final, wakeCount]
  | cons a as ih =>
    have ha := stutter a List.mem_cons_self
    have ih := ih (fun a' h => stutter a' (List.mem_cons_of_mem _ h))
    have hb : ¬ b.unread = [] := hw
    constructor
    · simp only [List.map_cons, final, ha]
      exact ih.1
    · simp only [List.map_cons, wakeCount, ha, hb, if_false, ih.2, List.length_cons]
      omega

/-- The live crash loop: if each turn dies between its effects and its boundary, the
same deliveries are shown on every turn, whatever the kernel does, dispositions included.
The wake count equals the number of turns, with no bound. -/
theorem live_crash_loop (p : Presenter) {b : Mailbox} (hw : Wakes b)
    (acts : List (List Action)) :
    final .live p b (acts.map fun a => (a, false)) = b ∧
      wakeCount .live p b (acts.map fun a => (a, false)) = acts.length :=
  crash_loop_of_stutter hw acts (fun a _ => live_crash_stutters p b a)

/-- Neither discipline can help a kernel that never commits and never disposes: with
at-least-once delivery the same input is shown again on every turn. -/
theorem no_disposition_crash_loop (d : Discipline) (p : Presenter) {b : Mailbox}
    (hw : Wakes b) (acts : List (List Action)) (none : ∀ a ∈ acts, disposed a = []) :
    wakeCount d p b (acts.map fun a => (a, false)) = acts.length :=
  (crash_loop_of_stutter hw acts (fun a h => no_disposition_crash_stutters d p b a (none a h))).2

/-- Under the repaired discipline a disposition of a pending delivery is progress, even when
the turn crashes before its boundary. -/
theorem repaired_disposition_progress (p : Presenter) (b : Mailbox) (acts : List Action)
    (commits : Bool) {m : Message} (hm : m ∈ b.unread) (hd : m.id ∈ disposed acts) :
    (turn .repaired p b acts commits).unread.length < b.unread.length :=
  ackAll_unread_length_lt b _ hm (List.mem_append_left _ hd)

/-- In every woken turn the boundary committed or the kernel disposed of a delivery it
was shown. -/
def Settling (d : Discipline) (p : Presenter) : Mailbox → List Turn → Prop
  | _, [] => True
  | b, t :: ts => (Wakes b → t.2 = true ∨ ∃ m ∈ p.batch b, m.id ∈ disposed t.1) ∧
      Settling d p (turn d p b t.1 t.2) ts

/-- Under the repaired discipline every settling run is bounded by the pending deliveries,
crashes included. Under the live discipline the same kernel behaviour can loop for ever
(`live_crash_loop`). -/
theorem repaired_settling_bounded (p : Presenter) (b : Mailbox) (ts : List Turn)
    (h : Settling .repaired p b ts) : wakeCount .repaired p b ts ≤ b.unread.length := by
  apply wakeCount_le
  induction ts generalizing b with
  | nil => trivial
  | cons t ts ih =>
    obtain ⟨ht, hs⟩ := h
    refine ⟨fun hw => ?_, ih _ hs⟩
    rcases ht hw with hc | ⟨m, hm, hd⟩
    · obtain ⟨acts, c⟩ := t
      simp only at hc
      subst hc
      exact committed_turn_progress _ p b acts hw
    · exact repaired_disposition_progress p b t.1 t.2 (p.batch_pending b m hm) hd

/-! ## Identity and kind -/

/-- The pending deliveries when settlement is recorded under some key of a delivery. -/
def pendingBy {K : Type} [DecidableEq K] (key : Message → K) (settled : List K)
    (log : List Message) : List Message :=
  log.filter fun m => key m ∉ settled

/-- Settling one delivery under a key it shares with a later, distinct delivery hides the
later one: it is never pending, so it never wakes the kernel. -/
theorem coarse_key_swallows {K : Type} [DecidableEq K] (key : Message → K) {m₁ m₂ : Message}
    (same : key m₁ = key m₂) (log : List Message) :
    m₂ ∉ pendingBy key [key m₁] (log ++ [m₂]) := by
  simp [pendingBy, same]

/-- Delivery identity keeps every later delivery that has another identity. -/
theorem identity_key_keeps {m₁ m₂ : Message} (distinct : m₁.id ≠ m₂.id)
    (log : List Message) :
    m₂ ∈ pendingBy Message.id [m₁.id] (log ++ [m₂]) := by
  simp [pendingBy, Ne.symm distinct]

/-- One person sends the same short reply twice: two deliveries. A content key swallows
the second; delivery identity shows it. -/
example :
    let first : Message := ⟨"update:1", "operator", ["agent"], 0, "", [], [], "ok"⟩
    let again : Message := ⟨"update:2", "operator", ["agent"], 60, "", [], [], "ok"⟩
    again ∉ pendingBy Message.body [first.body] [first, again] ∧
      again ∈ pendingBy Message.id [first.id] [first, again] := by
  decide

/-- Any kind computed from a view that identifies two deliveries of different true kinds
is wrong on one of them. -/
theorem kind_view_errs {V Kind : Type} (view : Message → V) (classify : V → Kind)
    (truth : Message → Kind) {m₁ m₂ : Message} (same : view m₁ = view m₂)
    (differ : truth m₁ ≠ truth m₂) :
    classify (view m₁) ≠ truth m₁ ∨ classify (view m₂) ≠ truth m₂ := by
  by_cases h : classify (view m₁) = truth m₁
  · right
    intro h₂
    rw [← same] at h₂
    exact differ (h.symm.trans h₂)
  · exact Or.inl h

/-- A person who quotes a worker's completion notice sends the notice's text. No function
of the text gives both deliveries their kind; the authenticated sender does. -/
example (classify : String → Bool) :
    let notice : Message := ⟨"mail:1", "worker", ["agent"], 0, "", [], [], "work done"⟩
    let quote : Message := ⟨"mail:2", "operator", ["agent"], 9, "", [], [], "work done"⟩
    let fromPerson : Message → Bool := fun m => m.originator == "operator"
    classify notice.body ≠ fromPerson notice ∨ classify quote.body ≠ fromPerson quote := by
  intro notice quote fromPerson
  exact kind_view_errs Message.body classify fromPerson rfl (by decide)

/-! ## Keyed effects -/

/-- An effect log keyed by an idempotency key: a key already present is a replay. -/
def perform {K : Type} [DecidableEq K] (log : List K) (k : K) : List K :=
  if k ∈ log then log else log ++ [k]

theorem perform_nodup {K : Type} [DecidableEq K] {log : List K} (h : log.Nodup) (k : K) :
    (perform log k).Nodup := by
  unfold perform
  split
  · exact h
  · next hk => exact List.Nodup.append h (List.nodup_singleton k) (by simpa using hk)

theorem mem_perform_of_mem {K : Type} [DecidableEq K] {log : List K} {k' : K} (h : k' ∈ log)
    (k : K) : k' ∈ perform log k := by
  unfold perform
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_perform_self {K : Type} [DecidableEq K] (log : List K) (k : K) :
    k ∈ perform log k := by
  unfold perform
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton_self k)

/-- Replies keyed by the delivery they answer and their ordinal in the answering turn: for
each presentation of a delivery, the kernel emits whatever replies it chooses. Every emitted
key is performed, and none twice, however often the delivery is shown again. -/
theorem keyed_effects_at_most_once (shown : List (List (MessageId × Nat))) :
    (shown.flatten.foldl perform []).Nodup ∧
      ∀ k ∈ shown.flatten, k ∈ shown.flatten.foldl perform [] := by
  suffices h : ∀ (ks : List (MessageId × Nat)) (log : List (MessageId × Nat)),
      log.Nodup → (ks.foldl perform log).Nodup ∧
        (∀ k ∈ log, k ∈ ks.foldl perform log) ∧ ∀ k ∈ ks, k ∈ ks.foldl perform log by
    obtain ⟨hn, -, hk⟩ := h _ [] List.nodup_nil
    exact ⟨hn, hk⟩
  intro ks
  induction ks with
  | nil => exact fun _ h => ⟨h, fun _ hk => hk, fun _ hk => absurd hk List.not_mem_nil⟩
  | cons k ks ih =>
    intro log h
    obtain ⟨hn, hkeep, hnew⟩ := ih _ (perform_nodup h k)
    refine ⟨hn, fun k' hk' => hkeep _ (mem_perform_of_mem hk' k), fun k' hk' => ?_⟩
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hkeep _ (mem_perform_self log k')
    · exact hnew _ hk'

/-- A fresh nonce per presentation makes every presentation a new effect. -/
example :
    ((List.range 3).map (fun nonce => ("mail:1", nonce))).foldl perform [] =
      [("mail:1", 0), ("mail:1", 1), ("mail:1", 2)] := by
  decide

/-! ## Workflow records and dispositions -/

inductive Kind where
  | message | notification | task | goal | autonomous
  deriving DecidableEq, Repr

inductive Status where
  | active | processed | waitingUser | deferred | addressed | achieved | cancelled | covered
  deriving DecidableEq, Repr

inductive Disposition where
  | keep | waitingUser | defer | addressed | reopen
  deriving DecidableEq, Repr

/-- A request record as the open-work projection reads it. -/
structure Record where
  kind : Kind
  /-- Closed by the operator's workflow rather than by its own checker. -/
  operator : Bool
  status : Status
  /-- A committed turn (and, once repaired, a disposition) took the input over. -/
  processed : Bool
  deriving DecidableEq, Repr

def Kind.isInput : Kind → Bool
  | .message | .notification => true
  | _ => false

def Disposition.target : Disposition → Status
  | .keep => .active
  | .waitingUser => .waitingUser
  | .defer => .deferred
  | .addressed => .addressed
  | .reopen => .active

/-- The open-work projection's membership rule. -/
def Open (r : Record) : Bool :=
  r.status == .active || r.status == .waitingUser || r.status == .deferred ||
    r.status == .covered || (r.status == .processed && r.kind.isInput)

/-- The repaired projection also leaves out a covered batch: the batch that covers it
carries every one of its deliveries, so it is not separate work. -/
def OpenRepaired (r : Record) : Bool := Open r && r.status != .covered

/-- Refusals both disciplines keep: terminal records, goals and autonomous work take no
disposition; `addressed` is not for records with their own checker; a covered batch is
only kept or reopened. -/
def guardRefusal (d : Disposition) (r : Record) : Bool :=
  r.status == .achieved || r.status == .cancelled || r.kind == .goal ||
    r.kind == .autonomous || (d == .addressed && !r.operator) ||
    (r.status == .covered && !(d == .keep || d == .reopen))

/-- The live rule adds one refusal: an input is addressed only after a turn processed it. -/
def liveRefusal (d : Disposition) (r : Record) : Bool :=
  guardRefusal d r || (d == .addressed && r.kind.isInput && !r.processed)

/-- What an accepted disposition writes: its status, and the task kind for `keep` and for a
covered batch. -/
def Disposition.write (d : Disposition) (r : Record) : Record :=
  { r with kind := if d == .keep || r.status == .covered then .task else r.kind
           status := d.target }

def disposeLive (d : Disposition) (r : Record) : Record :=
  if liveRefusal d r then r else d.write r

/-- Repaired: the extra refusal is deleted and an accepted disposition settles the input. -/
def disposeRepaired (d : Disposition) (r : Record) : Record :=
  if guardRefusal d r then r else { d.write r with processed := true }

/-- The committed checkpoint's settlement of the turn's input focus. -/
def settle (r : Record) : Record :=
  if r.kind.isInput && !r.processed then
    { r with processed := true, status := if r.status == .active then .processed else r.status }
  else r

/-- The trapped shape: an operator input, unprocessed, active, deferred or awaiting the
user. A fresh notification has it; a turn that crashed before its checkpoint leaves it. -/
def Trapped (r : Record) : Prop :=
  r.kind.isInput = true ∧ r.operator = true ∧ r.processed = false ∧
    (r.status = .active ∨ r.status = .deferred ∨ r.status = .waitingUser)

theorem Trapped.isOpen {r : Record} (h : Trapped r) : Open r = true := by
  obtain ⟨_, _, _, hs | hs | hs⟩ := h <;> simp [Open, hs]

theorem Trapped.not_guarded {r : Record} (h : Trapped r) (d : Disposition) :
    guardRefusal d r = false := by
  obtain ⟨hk, ho, _, hs⟩ := h
  have hgoal : r.kind ≠ .goal := by intro e; simp [e, Kind.isInput] at hk
  have hauto : r.kind ≠ .autonomous := by intro e; simp [e, Kind.isInput] at hk
  rcases hs with hs | hs | hs <;> simp [guardRefusal, hs, ho, hgoal, hauto]

/-- A fresh notification is trapped, and a live `defer` keeps it so: the state a crashed
turn leaves behind once its disposition was recorded but its checkpoint was not. -/
theorem live_trap_reachable :
    let fresh : Record := ⟨.notification, true, .active, false⟩
    Trapped fresh ∧ disposeLive .defer fresh = ⟨.notification, true, .deferred, false⟩ ∧
      Trapped (disposeLive .defer fresh) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Trapped, Kind.isInput, disposeLive, liveRefusal, guardRefusal, Disposition.write,
      Disposition.target]

/-- The attempts that change nothing: on a deferred, unprocessed operator input, `addressed`
is refused and `defer` writes back the same record. -/
theorem live_attempts_fixed {r : Record} (h : Trapped r) (hd : r.status = .deferred) :
    disposeLive .addressed r = r ∧ disposeLive .defer r = r := by
  obtain ⟨hk, ho, hp, _⟩ := h
  have hg := (Trapped.not_guarded ⟨hk, ho, hp, Or.inr (Or.inl hd)⟩)
  constructor
  · simp [disposeLive, liveRefusal, hk, hp]
  · have hd' : liveRefusal .defer r = false := by simp [liveRefusal, hg]
    simp only [disposeLive, hd', Bool.false_eq_true, if_false, Disposition.write,
      Disposition.target]
    cases r
    simp_all

theorem live_trap_step {r : Record} (h : Trapped r) (d : Disposition) (hd : d ≠ .keep) :
    Trapped (disposeLive d r) := by
  obtain ⟨hk, ho, hp, hs⟩ := h
  have hg := Trapped.not_guarded ⟨hk, ho, hp, hs⟩ d
  have hcov : r.status ≠ .covered := by rcases hs with hs | hs | hs <;> simp [hs]
  cases d with
  | keep => exact absurd rfl hd
  | addressed =>
    have : disposeLive .addressed r = r := by simp [disposeLive, liveRefusal, hk, hp]
    rw [this]
    exact ⟨hk, ho, hp, hs⟩
  | defer =>
    have hr : liveRefusal .defer r = false := by simp [liveRefusal, hg]
    simp only [disposeLive, hr, Bool.false_eq_true, if_false, Disposition.write,
      Disposition.target]
    refine ⟨?_, ho, hp, Or.inr (Or.inl rfl)⟩
    simpa [hcov] using hk
  | waitingUser =>
    have hr : liveRefusal .waitingUser r = false := by simp [liveRefusal, hg]
    simp only [disposeLive, hr, Bool.false_eq_true, if_false, Disposition.write,
      Disposition.target]
    refine ⟨?_, ho, hp, Or.inr (Or.inr rfl)⟩
    simpa [hcov] using hk
  | reopen =>
    have hr : liveRefusal .reopen r = false := by simp [liveRefusal, hg]
    simp only [disposeLive, hr, Bool.false_eq_true, if_false, Disposition.write,
      Disposition.target]
    refine ⟨?_, ho, hp, Or.inl rfl⟩
    simpa [hcov] using hk

/-- The attention trap. Once no committed turn will process the input, every sequence of
live dispositions without `keep` leaves it open and unprocessed. -/
theorem live_trap {r : Record} (h : Trapped r) (ds : List Disposition)
    (hds : ∀ d ∈ ds, d ≠ .keep) :
    Open (ds.foldl (fun r d => disposeLive d r) r) = true ∧
      (ds.foldl (fun r d => disposeLive d r) r).processed = false := by
  induction ds generalizing r with
  | nil => exact ⟨h.isOpen, h.2.2.1⟩
  | cons d ds ih =>
    exact ih (live_trap_step h d (hds d List.mem_cons_self))
      (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))

/-- The first escape: `keep` turns the input into a task, which `addressed` then closes. -/
theorem live_keep_escape {r : Record} (h : Trapped r) :
    Open (disposeLive .addressed (disposeLive .keep r)) = false := by
  obtain ⟨hk, ho, hp, hs⟩ := h
  have hg := Trapped.not_guarded ⟨hk, ho, hp, hs⟩ .keep
  have hr : liveRefusal .keep r = false := by simp [liveRefusal, hg]
  have hkeep : disposeLive .keep r = { r with kind := .task, status := .active } := by
    simp [disposeLive, hr, Disposition.write, Disposition.target]
  rw [hkeep]
  simp [disposeLive, liveRefusal, guardRefusal, ho, Kind.isInput, Disposition.write,
    Disposition.target, Open]

/-- The second escape: a committed checkpoint settles the input (a runtime can stage the
deferred input for its next checkpoint), after which `addressed` closes it. It needs that
checkpoint to commit and a later turn. -/
theorem live_settle_escape {r : Record} (h : Trapped r) :
    Open (disposeLive .addressed (settle r)) = false := by
  obtain ⟨hk, ho, hp, hs⟩ := h
  have hcov : r.status ≠ .covered := by rcases hs with hs | hs | hs <;> simp [hs]
  have hset : (settle r).processed = true ∧ (settle r).kind = r.kind ∧
      (settle r).operator = r.operator ∧ (settle r).status ≠ .covered ∧
      (settle r).status ≠ .achieved ∧ (settle r).status ≠ .cancelled := by
    rcases hs with hs | hs | hs <;> simp [settle, hk, hp, hs]
  obtain ⟨hp', hk', ho', hc', ha', hn'⟩ := hset
  have hgoal : r.kind ≠ .goal := by intro e; simp [e, Kind.isInput] at hk
  have hauto : r.kind ≠ .autonomous := by intro e; simp [e, Kind.isInput] at hk
  have hr : liveRefusal .addressed (settle r) = false := by
    simp [liveRefusal, guardRefusal, hp', hk', ho', ho, hc', ha', hn', hgoal, hauto]
  simp [disposeLive, hr, Disposition.write, Disposition.target, Open]

/-- The repaired rule: every operator row of the repaired projection that is not a goal or
autonomous work leaves the projection after one `addressed`, which also settles it. -/
theorem repaired_addressed_closes (r : Record) (hopen : OpenRepaired r = true)
    (ho : r.operator = true) (hgoal : r.kind ≠ .goal) (hauto : r.kind ≠ .autonomous) :
    OpenRepaired (disposeRepaired .addressed r) = false ∧
      (disposeRepaired .addressed r).processed = true := by
  have hst : r.status ≠ .achieved ∧ r.status ≠ .cancelled ∧ r.status ≠ .covered := by
    cases hs : r.status <;> simp_all [OpenRepaired, Open]
  have hg : guardRefusal .addressed r = false := by
    simp [guardRefusal, ho, hgoal, hauto, hst.1, hst.2.1, hst.2.2]
  simp [disposeRepaired, hg, Disposition.write, Disposition.target, OpenRepaired, Open]

/-- Every accepted repaired disposition settles the record it names. -/
theorem repaired_settles (d : Disposition) (r : Record) (h : guardRefusal d r = false) :
    (disposeRepaired d r).processed = true := by
  simp [disposeRepaired, h]

/-- Repeating a repaired disposition changes nothing: retries are safe. -/
theorem disposeRepaired_idempotent (d : Disposition) (r : Record) :
    disposeRepaired d (disposeRepaired d r) = disposeRepaired d r := by
  unfold disposeRepaired
  by_cases h : guardRefusal d r = true
  · simp [h]
  · have hf : guardRefusal d r = false := by simpa using h
    cases d <;> cases r with
    | mk kind operator status processed =>
      cases kind <;> cases status <;> cases operator <;>
        simp_all [guardRefusal, Disposition.write, Disposition.target]

/-- The repair deletes exactly one refusal. Whatever the repaired rule refuses, the live
rule refuses; what only the live rule refuses is `addressed` on an operator input that no
committed turn has processed. -/
theorem repaired_keeps_guards (d : Disposition) (r : Record) :
    (guardRefusal d r = true → liveRefusal d r = true) ∧
      (liveRefusal d r = true → guardRefusal d r = false →
        d = .addressed ∧ r.operator = true ∧ r.kind.isInput = true ∧
          r.processed = false) := by
  refine ⟨fun h => by simp [liveRefusal, h], fun hl hg => ?_⟩
  simp only [liveRefusal, hg, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at hl
  obtain ⟨⟨hd, hk⟩, hp⟩ := hl
  subst hd
  refine ⟨rfl, ?_, hk, hp⟩
  cases ho : r.operator
  · simp [guardRefusal, ho] at hg
  · rfl

/-- The repaired `defer` does in one transaction what a live `defer` does together with a
later committed checkpoint that settles the deferred input. -/
theorem repaired_defer_is_settled_defer {r : Record} (h : Trapped r) :
    disposeRepaired .defer r = settle (disposeLive .defer r) := by
  obtain ⟨hk, ho, hp, hs⟩ := h
  have hg := Trapped.not_guarded ⟨hk, ho, hp, hs⟩ .defer
  have hr : liveRefusal .defer r = false := by simp [liveRefusal, hg]
  have hcov : r.status ≠ .covered := by rcases hs with hs | hs | hs <;> simp [hs]
  simp [disposeRepaired, disposeLive, hg, hr, settle, Disposition.write, Disposition.target,
    hcov, hk, hp]

/-! ## One transaction for both layers -/

/-- The input ledger: deliveries with their settlement, and the request record of each. -/
structure Ledger where
  box : Mailbox
  record : MessageId → Record

/-- A repaired disposition is one transaction: an accepted disposition writes the record and
settles the delivery; a refused one changes nothing. -/
def Ledger.dispose (l : Ledger) (id : MessageId) (d : Disposition) : Ledger :=
  if guardRefusal d (l.record id) then l
  else ⟨l.box.ack id, Function.update l.record id (disposeRepaired d (l.record id))⟩

/-- One `addressed` on a pending operator input removes it from both views at once: the
wake no longer sees its delivery and the open-work projection no longer lists its record. -/
theorem dispose_closes_both_layers (l : Ledger) {m : Message} (hm : m ∈ l.box.unread)
    (hopen : OpenRepaired (l.record m.id) = true) (ho : (l.record m.id).operator = true)
    (hgoal : (l.record m.id).kind ≠ .goal) (hauto : (l.record m.id).kind ≠ .autonomous) :
    m ∉ (l.dispose m.id .addressed).box.unread ∧
      (l.dispose m.id .addressed).box.unread.length < l.box.unread.length ∧
      OpenRepaired ((l.dispose m.id .addressed).record m.id) = false := by
  have hst : (l.record m.id).status ≠ .achieved ∧ (l.record m.id).status ≠ .cancelled ∧
      (l.record m.id).status ≠ .covered := by
    cases hs : (l.record m.id).status <;> simp_all [OpenRepaired, Open]
  have hg : guardRefusal .addressed (l.record m.id) = false := by
    simp [guardRefusal, ho, hgoal, hauto, hst.1, hst.2.1, hst.2.2]
  simp only [Ledger.dispose, hg, Bool.false_eq_true, if_false, Function.update_self]
  refine ⟨?_, ?_, (repaired_addressed_closes _ hopen ho hgoal hauto).1⟩
  · rw [unread_ack]
    simp
  · rw [unread_ack]
    exact List.length_filter_lt_length_iff_exists.mpr ⟨m, hm, by simp⟩

end Mettapedia.Protocols.Agents.InputSettlement
