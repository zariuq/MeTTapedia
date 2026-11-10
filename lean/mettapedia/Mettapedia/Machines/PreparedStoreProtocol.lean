import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStore

/-!
# A prepared primitive store publication protocol

The model separates source request keys from physical occurrence identities.
Repeated request keys select each stored occurrence once; equal payloads at
distinct occurrences remain distinct. A pending operation is immutable as one
tagged value. Recording is bound to that preparation and is constructed from
its actual published selection, with length derived from initialized records.

This is a serialized primitive-effect contract, not a rollback transaction
around an entire source firing. Physical allocation, retained-pointer lifetime,
machine-word overflow and C correspondence are not proved here. Readiness is a
semantic dependency condition: the direct publication function consumes its
evidence without rematching. A checked wrapper is also supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedStoreProtocol

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe u v
variable {O : Type u} {Key : Type v} [DecidableEq Key]

structure World (O : Type u) where
  space : Nat
  rows : List O
  unique : rows.Nodup

inductive Operation (O : Type u) (Key : Type v) where
  | append (made : List O)
  | erase (keys : List Key)
  deriving DecidableEq, Repr

inductive Kind where
  | append | erase
  deriving DecidableEq, Repr

def Operation.kind : Operation O Key → Kind
  | .append _ => .append
  | .erase _ => .erase

def Operation.made : Operation O Key → List O
  | .append made => made
  | .erase _ => []

def select (label : O → Key) (keys : List Key) (rows : List O) : List O :=
  rows.filter fun occurrence => decide (label occurrence ∈ keys)

theorem select_membership (label : O → Key) (keys : List Key) (rows : List O) (occurrence : O) :
    occurrence ∈ select label keys rows ↔ occurrence ∈ rows ∧ label occurrence ∈ keys := by
  simp [select]

theorem select_distinct (label : O → Key) (keys : List Key) (world : World O) :
    (select label keys world.rows).Nodup := world.unique.filter _

/-- Request multiplicity is not occurrence multiplicity. -/
theorem duplicate_requests_irrelevant (label : O → Key) (keys : List Key) (rows : List O) :
    select label keys.eraseDups rows = select label keys rows := by
  simp [select]

variable [DecidableEq O]

def Admissible (world : World O) (operation : Operation O Key) : Prop :=
  operation.made.Nodup ∧ Disjoint operation.made.toFinset world.rows.toFinset

instance (world : World O) (operation : Operation O Key) : Decidable (Admissible world operation) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Plan (O : Type u) (Key : Type v) where
  space : Nat
  operation : Operation O Key
  selected : List O
  ticket : Option Nat
  deriving DecidableEq, Repr

def Plan.taken (plan : Plan O Key) : List O :=
  match plan.operation with
  | .append _ => []
  | .erase _ => plan.selected

def Plan.made (plan : Plan O Key) : List O := plan.operation.made

def build (label : O → Key) (world : World O) (operation : Operation O Key)
    (ticket : Option Nat) : Plan O Key :=
  ⟨world.space, operation,
    match operation with | .append _ => [] | .erase keys => select label keys world.rows,
    ticket⟩

/-- Removal readiness observes the complete requested region; append
readiness requires a fresh, distinct made footprint. This is not a whole-world
revision policy and does not require unrelated rows to stay unchanged. -/
def Ready (label : O → Key) (world : World O) (plan : Plan O Key) : Prop :=
  plan.space = world.space ∧
    match plan.operation with
    | .append made => plan.selected = [] ∧ made.Nodup ∧ Disjoint made.toFinset world.rows.toFinset
    | .erase keys => plan.selected = select label keys world.rows

instance (label : O → Key) (world : World O) (plan : Plan O Key) : Decidable (Ready label world plan) := by
  unfold Ready
  cases plan.operation <;> infer_instance

theorem build_ready (label : O → Key) (world : World O) (operation : Operation O Key)
    (ticket : Option Nat) (admissible : Admissible world operation) :
    Ready label world (build label world operation ticket) := by
  cases operation with
  | append made => exact ⟨rfl, rfl, admissible⟩
  | erase keys => exact ⟨rfl, rfl⟩

theorem ready_taken_distinct (label : O → Key) (world : World O) (plan : Plan O Key)
    (ready : Ready label world plan) : plan.taken.Nodup := by
  cases op : plan.operation with
  | append made => simp [Plan.taken, op]
  | erase keys =>
      have chosen : plan.selected = select label keys world.rows := by simpa [Ready, op] using ready.2
      simpa [Plan.taken, op, chosen] using select_distinct label keys world

theorem ready_taken_present (label : O → Key) (world : World O) (plan : Plan O Key)
    (ready : Ready label world plan) : ∀ occurrence ∈ plan.taken, occurrence ∈ world.rows := by
  cases op : plan.operation with
  | append made => simp [Plan.taken, op]
  | erase keys =>
      have chosen : plan.selected = select label keys world.rows := by simpa [Ready, op] using ready.2
      intro occurrence member
      exact ((select_membership label keys world.rows occurrence).mp
        (by simpa [Plan.taken, op, chosen] using member)).1

theorem ready_made (label : O → Key) (world : World O) (plan : Plan O Key)
    (ready : Ready label world plan) :
    plan.made.Nodup ∧ Disjoint plan.made.toFinset world.rows.toFinset := by
  cases op : plan.operation with
  | append made =>
      have clauses : plan.selected = [] ∧ made.Nodup ∧ Disjoint made.toFinset world.rows.toFinset := by
        simpa [op] using ready.2
      simpa [Plan.made, Operation.made, op] using clauses.2
  | erase keys => simp [Plan.made, Operation.made, op]

def updatedRows (world : World O) (plan : Plan O Key) : List O :=
  OrderedStore.publish world.rows ⟨plan.taken, [], plan.made⟩

theorem updated_unique (label : O → Key) (world : World O) (plan : Plan O Key)
    (ready : Ready label world plan) : (updatedRows world plan).Nodup := by
  have made := ready_made label world plan ready
  apply List.nodup_append.mpr
  refine ⟨world.unique.filter _, made.1, ?_⟩
  intro left old right fresh same
  subst right
  exact Finset.disjoint_left.mp made.2 (List.mem_toFinset.mpr fresh)
    (List.mem_toFinset.mpr (List.mem_filter.mp old).1)

omit [DecidableEq Key] in
theorem updated_membership (world : World O) (plan : Plan O Key) (occurrence : O) :
    occurrence ∈ updatedRows world plan ↔
      (occurrence ∈ world.rows ∧ occurrence ∉ plan.taken) ∨ occurrence ∈ plan.made := by
  simp [updatedRows, OrderedStore.publish, OrderedStore.survivors]

/-- The taken list is exactly the physical difference, not just a claimed
count or a set of values which happen to look like removed values. -/
theorem removed_exact (label : O → Key) (world : World O) (plan : Plan O Key)
    (ready : Ready label world plan) (occurrence : O) :
    occurrence ∈ world.rows ∧ occurrence ∉ updatedRows world plan ↔ occurrence ∈ plan.taken := by
  rw [updated_membership]
  constructor
  · rintro ⟨old, gone⟩
    by_contra notTaken
    exact gone (Or.inl ⟨old, notTaken⟩)
  · intro taken
    have old := ready_taken_present label world plan ready occurrence taken
    refine ⟨old, ?_⟩
    rintro (⟨_, notTaken⟩ | made)
    · exact notTaken taken
    · exact Finset.disjoint_left.mp (ready_made label world plan ready).2
        (List.mem_toFinset.mpr made) (List.mem_toFinset.mpr old)

theorem made_exact (label : O → Key) (world : World O) (plan : Plan O Key)
    (ready : Ready label world plan) (occurrence : O) :
    occurrence ∈ updatedRows world plan ∧ occurrence ∉ world.rows ↔ occurrence ∈ plan.made := by
  rw [updated_membership]
  constructor
  · rintro ⟨(⟨old, _⟩ | made), absent⟩
    · exact (absent old).elim
    · exact made
  · intro made
    refine ⟨Or.inr made, ?_⟩
    intro old
    exact Finset.disjoint_left.mp (ready_made label world plan ready).2
      (List.mem_toFinset.mpr made) (List.mem_toFinset.mpr old)

structure Receipt (O : Type u) (Key : Type v) where
  space : Nat
  ticket : Nat
  kind : Kind
  taken : List (O × Key)
  made : List (O × Key)
  deriving DecidableEq, Repr

/-- There is no independently mutable claimed-length field. -/
def Receipt.length (receipt : Receipt O Key) : Nat := receipt.taken.length + receipt.made.length

def record (label : O → Key) (plan : Plan O Key) : Option (Receipt O Key) :=
  plan.ticket.map fun ticket =>
    ⟨plan.space, ticket, plan.operation.kind,
      plan.taken.map (fun occurrence => (occurrence, label occurrence)),
      plan.made.map (fun occurrence => (occurrence, label occurrence))⟩

omit [DecidableEq O] [DecidableEq Key] in
theorem record_exact (label : O → Key) (plan : Plan O Key) (receipt : Receipt O Key)
    (recorded : record label plan = some receipt) :
    plan.ticket = some receipt.ticket ∧ receipt.space = plan.space ∧
      receipt.kind = plan.operation.kind ∧
      receipt.taken = plan.taken.map (fun occurrence => (occurrence, label occurrence)) ∧
      receipt.made = plan.made.map (fun occurrence => (occurrence, label occurrence)) ∧
      receipt.length = plan.taken.length + plan.made.length := by
  obtain ⟨ticket, reserved, rfl⟩ := Option.map_eq_some_iff.mp recorded
  exact ⟨reserved, rfl, rfl, rfl, rfl, by simp [Receipt.length]⟩

omit [DecidableEq O] [DecidableEq Key] in
theorem unrecorded (label : O → Key) (plan : Plan O Key) (noRecord : plan.ticket = none) :
    record label plan = none := by simp [record, noRecord]

inductive Slot (O : Type u) (Key : Type v) where
  | empty
  | pending (plan : Plan O Key)
  | consumed
  deriving DecidableEq, Repr

structure State (O : Type u) (Key : Type v) where
  world : World O
  slot : Slot O Key
  nextTicket : Nat

inductive Preparation where
  | prepared
  | busy
  | allocationFailed
  | invalidRequest
  deriving DecidableEq, Repr

/-- An unavailable slot is rejected before constructing or retagging a plan.
The reservation flag models capacity acquisition, not native allocator code. -/
def prepare (label : O → Key) (operation : Operation O Key) (recording reserved : Bool)
    (state : State O Key) : Preparation × State O Key :=
  match state.slot with
  | .pending _ | .consumed => (.busy, state)
  | .empty =>
      if !reserved then (.allocationFailed, state)
      else if Admissible state.world operation then
        let ticket := if recording then some (state.nextTicket + 1) else none
        (.prepared, { state with
          slot := .pending (build label state.world operation ticket)
          nextTicket := if recording then state.nextTicket + 1 else state.nextTicket })
      else (.invalidRequest, state)

theorem rejected_prepare_preserves_state (label : O → Key) (operation : Operation O Key)
    (recording reserved : Bool) (state : State O Key)
    (rejected : (prepare label operation recording reserved state).1 ≠ .prepared) :
    (prepare label operation recording reserved state).2 = state := by
  cases slot : state.slot <;> simp only [prepare, slot] at rejected ⊢
  split_ifs at rejected ⊢ <;> simp_all

theorem busy_preserves_plan (label : O → Key) (operation : Operation O Key)
    (recording reserved : Bool) (state : State O Key) (plan : Plan O Key)
    (pending : state.slot = .pending plan) :
    prepare label operation recording reserved state = (.busy, state) := by simp [prepare, pending]

theorem no_recording_no_ticket_allocation (label : O → Key) (operation : Operation O Key)
    (reserved : Bool) (state : State O Key) :
    (prepare label operation false reserved state).2.nextTicket = state.nextTicket := by
  cases slot : state.slot <;> simp only [prepare, slot]
  all_goals split_ifs <;> simp_all

theorem preparation_preserves_world (label : O → Key) (operation : Operation O Key)
    (recording reserved : Bool) (state : State O Key) :
    (prepare label operation recording reserved state).2.world = state.world := by
  cases slot : state.slot <;> simp only [prepare, slot]
  all_goals split_ifs <;> rfl

theorem successful_preparation_ready (label : O → Key) (operation : Operation O Key)
    (recording reserved : Bool) (state : State O Key)
    (success : (prepare label operation recording reserved state).1 = .prepared) :
    ∃ plan, (prepare label operation recording reserved state).2.slot = .pending plan ∧
      Ready label state.world plan ∧
      plan.ticket = (if recording then some (state.nextTicket + 1) else none) := by
  cases slot : state.slot with
  | pending plan => simp [prepare, slot] at success
  | consumed => simp [prepare, slot] at success
  | empty =>
      cases reserved with
      | false => simp [prepare, slot] at success
      | true =>
          by_cases allowed : Admissible state.world operation
          · simp only [prepare, slot, Bool.not_true, Bool.false_eq_true, if_false, allowed, if_true]
            exact ⟨_, rfl, build_ready label state.world operation _ allowed, rfl⟩
          · simp [prepare, slot, allowed] at success

inductive Fault where
  | notPrepared | receiptMismatch | stale
  deriving DecidableEq, Repr

inductive Publication (O : Type u) (Key : Type v) where
  | refused (fault : Fault)
  | noMatch
  | committed (receipt : Option (Receipt O Key))
  deriving DecidableEq, Repr

/-- The actual store update needs no second selection pass. Receipt payloads
come from this plan; no caller-supplied payload can be substituted here. -/
def publishReady (label : O → Key) (state : State O Key) (plan : Plan O Key)
    (ready : Ready label state.world plan) : Publication O Key × State O Key :=
  let after : State O Key :=
    { state with
      world := ⟨state.world.space, updatedRows state.world plan, updated_unique label state.world plan ready⟩
      slot := .consumed }
  if plan.operation.kind = .erase ∧ plan.taken = [] then (.noMatch, after)
  else (.committed (record label plan), after)

def publish (label : O → Key) (expectedTicket : Option Nat) (state : State O Key) :
    Publication O Key × State O Key :=
  match state.slot with
  | .empty | .consumed => (.refused .notPrepared, state)
  | .pending plan =>
      if expectedTicket ≠ plan.ticket then (.refused .receiptMismatch, state)
      else if ready : Ready label state.world plan then publishReady label state plan ready
      else (.refused .stale, { state with slot := .consumed })

theorem mismatched_receipt_refused (label : O → Key) (state : State O Key) (plan : Plan O Key)
    (pending : state.slot = .pending plan) (expected : Option Nat) (different : expected ≠ plan.ticket) :
    publish label expected state = (.refused .receiptMismatch, state) := by
  simp [publish, pending, different]

/-- Established readiness licenses the direct path; checked publication is
not an extra semantic pass imposed on every implementation. -/
theorem publish_under_ready (label : O → Key) (state : State O Key) (plan : Plan O Key)
    (pending : state.slot = .pending plan) (ready : Ready label state.world plan) :
    publish label plan.ticket state = publishReady label state plan ready := by
  simp [publish, pending, ready]

theorem refusal_preserves_world (label : O → Key) (expected : Option Nat) (state : State O Key)
    (fault : Fault) (refused : (publish label expected state).1 = .refused fault) :
    (publish label expected state).2.world = state.world := by
  cases slot : state.slot with
  | empty => simp [publish, slot]
  | consumed => simp [publish, slot]
  | pending plan =>
      by_cases different : expected ≠ plan.ticket
      · simp [publish, slot, different]
      · by_cases ready : Ready label state.world plan
        · have actual : publish label expected state = publishReady label state plan ready := by
            simp [publish, slot, different, ready]
          rw [actual] at refused
          unfold publishReady at refused
          split_ifs at refused
        · simp [publish, slot, different, ready]

theorem publication_consumes (label : O → Key) (expected : Option Nat) (state : State O Key)
    (receipt : Option (Receipt O Key))
    (success : (publish label expected state).1 = .committed receipt) :
    (publish label expected state).2.slot = .consumed := by
  cases slot : state.slot with
  | empty => simp [publish, slot] at success
  | consumed => simp [publish, slot]
  | pending plan =>
      by_cases different : expected ≠ plan.ticket
      · simp [publish, slot, different] at success
      · by_cases ready : Ready label state.world plan
        · simp only [publish, slot, different, if_false, dif_pos ready]
          unfold publishReady
          split_ifs <;> rfl
        · simp [publish, slot, different, ready] at success

theorem consumed_refused (label : O → Key) (state : State O Key)
    (consumed : state.slot = .consumed) (expected : Option Nat) :
    publish label expected state = (.refused .notPrepared, state) := by
  simp [publish, consumed]

theorem cannot_republish (label : O → Key) (expected : Option Nat) (state : State O Key)
    (receipt : Option (Receipt O Key))
    (success : (publish label expected state).1 = .committed receipt) (next : Option Nat) :
    publish label next (publish label expected state).2 =
      (.refused .notPrepared, (publish label expected state).2) := by
  exact consumed_refused label _ (publication_consumes label expected state receipt success) next

theorem successful_publication_exact (label : O → Key) (expected : Option Nat) (state : State O Key)
    (receipt : Option (Receipt O Key))
    (success : (publish label expected state).1 = .committed receipt) :
    ∃ plan, state.slot = .pending plan ∧ Ready label state.world plan ∧
      expected = plan.ticket ∧ record label plan = receipt ∧
      (publish label expected state).2.world.rows = updatedRows state.world plan := by
  cases slot : state.slot with
  | empty => simp [publish, slot] at success
  | consumed => simp [publish, slot] at success
  | pending plan =>
      by_cases different : expected ≠ plan.ticket
      · simp [publish, slot, different] at success
      · by_cases ready : Ready label state.world plan
        · have actual : publish label expected state = publishReady label state plan ready := by
            simp [publish, slot, different, ready]
          rw [actual] at success ⊢
          by_cases empty : plan.operation.kind = .erase ∧ plan.taken = []
          · simp [publishReady, empty] at success
          · refine ⟨plan, rfl, ready, Classical.not_not.mp different, ?_, ?_⟩
            · simpa [publishReady, empty] using success
            · simp [publishReady, empty]
        · simp [publish, slot, different, ready] at success

theorem successful_receipt_exact (label : O → Key) (expected : Option Nat) (state : State O Key)
    (receipt : Receipt O Key)
    (success : (publish label expected state).1 = .committed (some receipt)) :
    ∃ plan, state.slot = .pending plan ∧ Ready label state.world plan ∧
      expected = plan.ticket ∧ record label plan = some receipt ∧
      (publish label expected state).2.world.rows = updatedRows state.world plan :=
  successful_publication_exact label expected state (some receipt) success

/-- Every advertised taken entry names precisely an occurrence removed by
this publication, with that occurrence's actual immutable payload. -/
theorem successful_receipt_taken_iff (label : O → Key) (expected : Option Nat) (state : State O Key)
    (receipt : Receipt O Key) (success : (publish label expected state).1 = .committed (some receipt))
    (occurrence : O) (key : Key) :
    (occurrence, key) ∈ receipt.taken ↔ key = label occurrence ∧
      occurrence ∈ state.world.rows ∧ occurrence ∉ (publish label expected state).2.world.rows := by
  obtain ⟨plan, _, ready, _, recorded, updated⟩ := successful_receipt_exact label expected state receipt success
  have contents := (record_exact label plan receipt recorded).2.2.2.1
  rw [contents, updated]
  constructor
  · intro member
    obtain ⟨selected, present, equal⟩ := List.mem_map.mp member
    have same := Prod.mk.inj equal
    rcases same with ⟨rfl, rfl⟩
    exact ⟨rfl, (removed_exact label state.world plan ready selected).mpr present⟩
  · rintro ⟨rfl, removed⟩
    exact List.mem_map.mpr ⟨occurrence,
      (removed_exact label state.world plan ready occurrence).mp removed, rfl⟩

theorem successful_receipt_has_unique_occurrences (label : O → Key) (expected : Option Nat)
    (state : State O Key) (receipt : Receipt O Key)
    (success : (publish label expected state).1 = .committed (some receipt)) :
    (receipt.taken.map Prod.fst).Nodup := by
  obtain ⟨plan, _, ready, _, recorded, _⟩ := successful_receipt_exact label expected state receipt success
  rw [(record_exact label plan receipt recorded).2.2.2.1]
  rw [List.map_map]
  change (plan.taken.map id).Nodup
  rw [List.map_id]
  exact ready_taken_distinct label state.world plan ready

theorem preparation_ticket_monotone (label : O → Key) (operation : Operation O Key)
    (recording reserved : Bool) (state : State O Key) :
    state.nextTicket ≤ (prepare label operation recording reserved state).2.nextTicket := by
  cases slot : state.slot with
  | pending plan => simp [prepare, slot]
  | consumed => simp [prepare, slot]
  | empty =>
      simp only [prepare, slot]
      split_ifs <;> simp_all

/-- In a serial issuer history, a successfully recorded preparation receives
a strictly newer ticket. Independent forked copies of the issuer are not
licensed by this theorem. No ticket is issued on a refused preparation. -/
theorem recorded_preparation_advances_ticket (label : O → Key) (operation : Operation O Key)
    (reserved : Bool) (state : State O Key)
    (success : (prepare label operation true reserved state).1 = .prepared) :
    (prepare label operation true reserved state).2.nextTicket = state.nextTicket + 1 := by
  cases slot : state.slot with
  | pending plan => simp [prepare, slot] at success
  | consumed => simp [prepare, slot] at success
  | empty =>
      cases reserved with
      | false => simp [prepare, slot] at success
      | true =>
          by_cases allowed : Admissible state.world operation
          · simp [prepare, slot, allowed]
          · simp [prepare, slot, allowed] at success

end Mettapedia.Machines.PreparedStoreProtocol
