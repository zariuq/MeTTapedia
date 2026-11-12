import Mettapedia.Machines.PreparedStoreProtocol
import Mettapedia.Machines.OperatorChoice.ObserverContracts

/-!
# Immediate operations and observable prepared publication

The immediate algorithm appends or filters ordered rows directly. The staged
algorithm uses the existing preparation and publication protocol. Their public
observations forget only the private ticket and receipt, not refusals, answers,
or the reached store. Recording capacity is separate from effect capacity:
erasing an observable allocation failure is not justified by receipt erasure.

These are serialized operation and observation laws. They do not specify a C
layout, prove machine-code correspondence, or identify logical cost with time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ImmediateStorePublication

open PreparedStoreProtocol
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

section Core

universe u v
variable {O : Type u} {Key : Type v} [DecidableEq O] [DecidableEq Key]

structure Request (O : Type u) (Key : Type v) where
  operation : Operation O Key
  effectCapacity : Bool

inductive Reply where
  | preparationFailed (reason : Preparation)
  | publicationFailed (reason : Fault)
  | noMatch
  | committed
  deriving DecidableEq, Repr

def directRows (label : O → Key) (operation : Operation O Key) (rows : List O) : List O :=
  match operation with
  | .append made => rows ++ made
  | .erase keys => rows.filter fun occurrence => decide (label occurrence ∉ keys)

theorem direct_unique (label : O → Key) (world : World O) (operation : Operation O Key)
    (allowed : Admissible world operation) : (directRows label operation world.rows).Nodup := by
  cases operation with
  | append made =>
      apply List.nodup_append.mpr
      refine ⟨world.unique, allowed.1, ?_⟩
      intro old present new madeMember same
      subst new
      exact Finset.disjoint_left.mp allowed.2 (List.mem_toFinset.mpr madeMember)
        (List.mem_toFinset.mpr present)
  | erase keys => exact world.unique.filter _

def directReply (label : O → Key) (operation : Operation O Key) (rows : List O) : Reply :=
  match operation with
  | .append _ => .committed
  | .erase keys =>
      if rows.any (fun occurrence => decide (label occurrence ∈ keys)) then .committed else .noMatch

/-- No pending plan, ticket or receipt is constructed by this operation. -/
def immediate (label : O → Key) (world : World O) (request : Request O Key) : Reply × World O :=
  if !request.effectCapacity then (.preparationFailed .allocationFailed, world)
  else if allowed : Admissible world request.operation then
    (directReply label request.operation world.rows,
      ⟨world.space, directRows label request.operation world.rows,
        direct_unique label world request.operation allowed⟩)
  else (.preparationFailed .invalidRequest, world)

def observePublication : Publication O Key → Reply
  | .refused reason => .publicationFailed reason
  | .noMatch => .noMatch
  | .committed _ => .committed

abbrev Ledger (O : Type u) := World O × Nat

/-- Each request owns a fresh protocol slot. The serial survives between
requests only to identify optional records, never as a source occurrence ID. -/
def staged (label : O → Key) (recording recordCapacity : Bool)
    (ledger : Ledger O) (request : Request O Key) : Reply × Ledger O :=
  let state : State O Key := ⟨ledger.1, .empty, ledger.2⟩
  let reserved := request.effectCapacity && (!recording || recordCapacity)
  let prepared := prepare label request.operation recording reserved state
  if prepared.1 = .prepared then
    let expected := if recording then some (ledger.2 + 1) else none
    let result := publish label expected prepared.2
    (observePublication result.1, (result.2.world, result.2.nextTicket))
  else (.preparationFailed prepared.1, (prepared.2.world, prepared.2.nextTicket))

theorem direct_rows_eq_publication (label : O → Key) (world : World O)
    (operation : Operation O Key) (ticket : Option Nat) :
    directRows label operation world.rows = updatedRows world (build label world operation ticket) := by
  cases operation with
  | append made => simp [directRows, updatedRows, build, Plan.taken, Plan.made,
      Operation.made, OrderedStore.publish, OrderedStore.survivors]
  | erase keys =>
      simp only [directRows, updatedRows, build, Plan.taken, Plan.made,
        Operation.made, OrderedStore.publish, OrderedStore.survivors, List.append_nil]
      apply List.filter_congr
      intro occurrence present
      simp [select, present]

theorem direct_reply_eq_publication (label : O → Key) (world : World O)
    (operation : Operation O Key) (ticket : Option Nat) (serial : Nat)
    (allowed : Admissible world operation) :
    directReply label operation world.rows =
      observePublication (publishReady label
        ⟨world, .pending (build label world operation ticket), serial⟩
        (build label world operation ticket) (build_ready label world operation ticket allowed)).1 := by
  cases operation with
  | append made => simp [directReply, publishReady, build, Operation.kind, observePublication, record]
  | erase keys =>
      have empty_iff :
          world.rows.any (fun occurrence => decide (label occurrence ∈ keys)) = false ↔
            select label keys world.rows = [] :=
        List.any_eq_false.trans List.filter_eq_nil_iff.symm
      by_cases empty : select label keys world.rows = []
      · have absent := empty_iff.mpr empty
        simp [directReply, publishReady, build, Operation.kind, Plan.taken,
          observePublication, empty, absent]
      · have present : world.rows.any (fun occurrence => decide (label occurrence ∈ keys)) = true := by
          cases h : world.rows.any (fun occurrence => decide (label occurrence ∈ keys)) with
          | false => exact (empty (empty_iff.mp h)).elim
          | true => rfl
        simp [directReply, publishReady, build, Operation.kind, Plan.taken,
          observePublication, empty, present]

omit [DecidableEq O] in
theorem world_ext {first second : World O} (space : first.space = second.space)
    (rows : first.rows = second.rows) : first = second := by
  cases first
  cases second
  cases space
  cases rows
  rfl

theorem staged_fuses (label : O → Key) (recording recordCapacity : Bool)
    (ledger : Ledger O) (request : Request O Key)
    (recordAvailable : recording = true → recordCapacity = true) :
    immediate label ledger.1 request =
      ((staged label recording recordCapacity ledger request).1,
        (staged label recording recordCapacity ledger request).2.1) := by
  have capacity : (!recording || recordCapacity) = true := by
    cases recording <;> simp_all
  by_cases reserved : request.effectCapacity = true
  · by_cases allowed : Admissible ledger.1 request.operation
    · let ticket := if recording then some (ledger.2 + 1) else none
      let serial := if recording then ledger.2 + 1 else ledger.2
      let plan := build label ledger.1 request.operation ticket
      let next : State O Key := ⟨ledger.1, .pending plan, serial⟩
      have prepared :
          prepare label request.operation recording
            (request.effectCapacity && (!recording || recordCapacity))
            ⟨ledger.1, .empty, ledger.2⟩ = (.prepared, next) := by
        simp [prepare, capacity, reserved, allowed, next, plan, ticket, serial]
      have ready : Ready label ledger.1 plan := build_ready label _ _ _ allowed
      have published := publish_under_ready label next plan rfl ready
      simp only [staged, prepared, ite_true]
      change immediate label ledger.1 request =
        (observePublication (publish label plan.ticket next).1,
          (publish label plan.ticket next).2.world)
      rw [published]
      apply Prod.ext
      · simpa only [immediate, reserved, Bool.not_true, Bool.false_eq_true,
          if_false, dif_pos allowed] using
          direct_reply_eq_publication label ledger.1 request.operation ticket serial allowed
      · simp only [immediate, reserved, Bool.not_true, Bool.false_eq_true,
          if_false, dif_pos allowed, publishReady]
        split_ifs <;> apply world_ext
        all_goals first
          | rfl
          | exact direct_rows_eq_publication label ledger.1 request.operation ticket
    · simp [staged, immediate, capacity, reserved, prepare, allowed]
  · have noCapacity : request.effectCapacity = false := Bool.eq_false_iff.mpr reserved
    simp [staged, immediate, capacity, noCapacity, prepare]

theorem publish_preserves_serial (label : O → Key) (expected : Option Nat)
    (state : State O Key) : (publish label expected state).2.nextTicket = state.nextTicket := by
  cases slot : state.slot with
  | empty => simp [publish, slot]
  | consumed => simp [publish, slot]
  | pending plan =>
      simp only [publish, slot]
      split_ifs <;> simp only [publishReady]
      all_goals split_ifs <;> rfl

theorem unrecorded_serial_unchanged (label : O → Key) (recordCapacity : Bool)
    (ledger : Ledger O) (request : Request O Key) :
    (staged label false recordCapacity ledger request).2.2 = ledger.2 := by
  simp only [staged, Bool.false_eq_true, ite_false]
  split_ifs
  · exact (publish_preserves_serial label _ _).trans
      (no_recording_no_ticket_allocation label request.operation _ _)
  · exact no_recording_no_ticket_allocation label request.operation _ _

theorem committed_requires_capacity_and_admission (label : O → Key) (world : World O)
    (request : Request O Key) (committed : (immediate label world request).1 = .committed) :
    request.effectCapacity = true ∧ Admissible world request.operation := by
  by_cases capacity : request.effectCapacity = true
  · by_cases admitted : Admissible world request.operation
    · exact ⟨capacity, admitted⟩
    · simp [immediate, capacity, admitted] at committed
  · have absent := Bool.eq_false_iff.mpr capacity
    simp [immediate, absent] at committed

theorem immediate_result_rows (label : O → Key) (world : World O)
    (request : Request O Key) (capacity : request.effectCapacity = true)
    (admitted : Admissible world request.operation) :
    (immediate label world request).2.rows = directRows label request.operation world.rows := by
  simp [immediate, capacity, admitted]

end Core

section Adaptive

variable {O Key : Type} [DecidableEq O] [DecidableEq Key]

/-- The commuting equation preserves every finite adaptive client, including
its reached world and ordered history, not just a single operation's result. -/
theorem adaptive_fuses (label : O → Key) (recording : Bool) {Answer : Type}
    (program : ReadOnlyQuery.Program (Request O Key) Reply Answer) (ledger : Ledger O) :
    QueryState.run (immediate label) program ledger.1 =
      OperatorChoice.ObserverContracts.eraseObservation Prod.fst
        (QueryState.run (staged label recording true) program ledger) := by
  exact OperatorChoice.ObserverContracts.run_erasure_on
    (staged label recording true) (immediate label) Prod.fst
    (fun state => state.1.rows.Nodup)
    (fun state _ request => (staged label recording true state request).2.1.unique)
    (fun state _ request => staged_fuses label recording true state request (fun _ => rfl))
    program ledger ledger.1.unique

/-- Optional records and their issuer state are irrelevant to this public
client interface when recording capacity is available. -/
theorem adaptive_receipt_erasure (label : O → Key) {Answer : Type}
    (program : ReadOnlyQuery.Program (Request O Key) Reply Answer) (ledger : Ledger O) :
    OperatorChoice.ObserverContracts.eraseObservation Prod.fst
        (QueryState.run (staged label true true) program ledger) =
      OperatorChoice.ObserverContracts.eraseObservation Prod.fst
        (QueryState.run (staged label false true) program ledger) := by
  rw [← adaptive_fuses label true, ← adaptive_fuses label false]

end Adaptive

namespace Controls

def emptyWorld : World Nat := ⟨7, [], by simp⟩
def copies : World Nat := ⟨7, [0, 2, 1], by decide⟩
def put : Request Nat Nat := ⟨.append [3], true⟩

theorem capacity_failure_is_visible :
    (staged id true false (emptyWorld, 0) put).1 ≠
      (immediate id emptyWorld put).1 := by decide

theorem equal_payload_copies_are_both_removed :
    (immediate (fun occurrence => occurrence % 2) copies ⟨.erase [0], true⟩).2.rows = [1] := by
  decide

theorem duplicate_keys_do_not_duplicate_consumption :
    (immediate (fun occurrence => occurrence % 2) copies ⟨.erase [0, 0], true⟩).2.rows = [1] := by
  decide

theorem requested_receipt_distinguishes_recording :
    record id (build id emptyWorld (.append [3]) (some 1)) ≠
      record id (build id emptyWorld (.append [3]) none) := by decide

def appendThenRefuse : ReadOnlyQuery.Program (Request Nat Nat) Reply (Reply × Reply) :=
  .read put fun first => .read put fun second => .pure (first, second)

theorem refusal_does_not_undo_the_earlier_publication :
    let result := QueryState.run (immediate id) appendThenRefuse emptyWorld
    result.answer = (.committed, .preparationFailed .invalidRequest) ∧
      result.state.rows = [3] := by decide

theorem retained_slot_replay_is_not_an_immediate_operation :
    let stale : State Nat Nat := ⟨copies, .pending (build id copies (.erase [0]) none), 0⟩
    let changed : State Nat Nat := { stale with world := emptyWorld }
    (publish id none changed).1 = .refused .stale ∧
      (immediate id emptyWorld ⟨.erase [0], true⟩).1 = .noMatch := by decide

end Controls

end Mettapedia.Machines.ImmediateStorePublication
