import Mettapedia.GSLT.Core.InferenceRecording
import Mettapedia.Machines.TraceObservationBoundary
import Mettapedia.Machines.VariableInventory
import Mettapedia.GSLT.Core.OpenTotalityObservation

/-!
# Owned execution history readouts

Native call/return ports project to the existing bounded recording prefix and
causal receipt. Recording positions distinguish equal answer occurrences;
producer links distinguish one producer's several uses from separate producers.
The readout does not supply replay authority or observe a foreign callback's
interior. Payload transport and recording completeness are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ExecutionHistoryReadout

open Mettapedia.GSLT.Core.InferenceControl.Recording

inductive Kind where
  | call | returned | alternative | redo | fault | suspend | resume | cancel
  | answer | external | complete | use
  deriving DecidableEq, Repr

structure Event (Payload : Type*) where
  ordinal : Nat
  kind : Kind
  producer : Option Nat
  payload : Option Payload
  deriving DecidableEq, Repr

variable {Payload NextPayload : Type*}

/-- Only published answer ports enter this ordered projection. A missing
answer payload refuses the projection rather than silently deleting it. -/
def answers : List (Event Payload) → Option (List Payload)
  | [] => some []
  | event :: rest => do
      let first ← if event.kind = .answer then event.payload.map List.singleton else some []
      let remaining ← answers rest
      pure (first ++ remaining)

theorem answers_append (first second : List (Event Payload)) :
    answers (first ++ second) = (do
      let left ← answers first
      let right ← answers second
      pure (left ++ right)) := by
  induction first with
  | nil => simp [answers]
  | cons event rest ih =>
      by_cases isAnswer : event.kind = .answer
      · cases available : event.payload <;>
          simp [answers, isAnswer, available, ih, Option.bind_assoc, List.append_assoc]
      · simp [answers, isAnswer, ih]

def answerEvents (first producer : Nat) : List Payload → List (Event Payload)
  | [] => []
  | value :: rest =>
      ⟨first, .answer, some producer, some value⟩ :: answerEvents (first + 1) producer rest

@[simp] theorem answerEvents_length (first producer : Nat) (values : List Payload) :
    (answerEvents first producer values).length = values.length := by
  induction values generalizing first <;> simp_all [answerEvents]

@[simp] theorem answers_answerEvents (first producer : Nat) (values : List Payload) :
    answers (answerEvents first producer values) = some values := by
  induction values generalizing first <;> simp_all [answerEvents, answers, List.singleton]

theorem answers_no_answer_ports (events : List (Event Payload))
    (ports : ∀ event ∈ events, event.kind ≠ .answer) : answers events = some [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have head := ports event (by simp)
      have tail : ∀ item ∈ rest, item.kind ≠ .answer := by
        intro item member
        exact ports item (by simp [member])
      simp [answers, head, ih tail]

def completeAnswers (record : Prefix (Event Payload)) : Option (List Payload) :=
  record.complete?.bind answers

/-- The actual publication loop's ordered bag is recovered when the entire
declared prefix fits. Calls, returns and completion ports surrounding it may
remain in the history; they do not become extra answers. -/
theorem publication_readout (capacity first producer : Nat)
    (before after : List (Event Payload)) (values : List Payload)
    (beforePorts : ∀ event ∈ before, event.kind ≠ .answer)
    (afterPorts : ∀ event ∈ after, event.kind ≠ .answer)
    (fits : (before ++ answerEvents first producer values ++ after).length ≤ capacity) :
    completeAnswers ((Prefix.initial capacity).append
      (before ++ answerEvents first producer values ++ after)) = some values := by
  have full := (Prefix.complete_iff capacity
    (before ++ answerEvents first producer values ++ after)).2 fits
  unfold completeAnswers
  rw [full]
  simp [answers_append, answers_no_answer_ports before beforePorts,
    answers_no_answer_ports after afterPorts]

theorem truncated_readout_refused (capacity : Nat) (events : List (Event Payload))
    (tooMany : capacity < events.length) :
    completeAnswers ((Prefix.initial capacity).append events) = none := by
  have omitted : events.length - capacity ≠ 0 := by omega
  simp [completeAnswers, Prefix.complete?, Prefix.initial_omitted, omitted]

/-- Resumption appends to the retained prefix, retaining its capacity and
omissions. It cannot create a fresh complete recording of an earlier run. -/
theorem resumption_readout (record : Prefix (Event Payload))
    (before after : List (Event Payload)) :
    completeAnswers ((record.append before).append after) =
      completeAnswers (record.append (before ++ after)) := by
  rw [Prefix.append_append]

def mapPayload (mapping : Payload → NextPayload) (event : Event Payload) : Event NextPayload :=
  ⟨event.ordinal, event.kind, event.producer, event.payload.map mapping⟩

theorem answers_transport (mapping : Payload → NextPayload) (events : List (Event Payload)) :
    answers (events.map (mapPayload mapping)) = (answers events).map (List.map mapping) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      by_cases isAnswer : event.kind = .answer
      · cases available : event.payload <;> cases tail : answers rest <;>
          simp [answers, mapPayload, isAnswer, available, ih, tail, List.singleton]
      · simp [answers, mapPayload, isAnswer, ih]

theorem complete_answers_transport (mapping : Payload → NextPayload)
    (record : Prefix (Event Payload)) :
    completeAnswers (record.map (mapPayload mapping)) =
      (completeAnswers record).map (List.map mapping) := by
  unfold completeAnswers
  rw [Prefix.complete?_map]
  cases available : record.complete? <;> simp [answers_transport]

/-- Equal values have unequal recording positions. Erasing one of them is a
loss of observation, despite equality of the remaining semantic value. -/
theorem equal_answers_keep_positions (first producer : Nat) (value : Payload) :
    (answerEvents first producer [value, value]).map Event.ordinal = [first, first + 1] ∧
      answers (answerEvents first producer [value, value]) = some [value, value] := by
  simp [answerEvents, answers, List.singleton]

theorem deleting_equal_answer_changes_readout (first producer : Nat) (value : Payload) :
    answers (answerEvents first producer [value, value]) ≠
      answers (answerEvents first producer [value]) := by
  simp only [answers_answerEvents, ne_eq, Option.some.injEq]
  intro equal
  have lengths := congrArg List.length equal
  simp at lengths

/-! Producer causality uses the existing receipt identities, not payload
identity. The following is the owned producer/delivery component: one Call
occurrence can support arbitrarily many separate Use occurrences. -/

def useEvents (first producer : Nat) : Nat → List (CausalEvent Nat)
  | 0 => []
  | count + 1 => ⟨first, [producer]⟩ :: useEvents (first + 1) producer count

private theorem uses_ordered (available : List Nat) (first producer count : Nat)
    (earlier : ∀ value ∈ available, value < first) (live : producer ∈ available) :
    CausalReceipt.Ordered available (useEvents first producer count) := by
  induction count generalizing first available with
  | zero => trivial
  | succ count ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro present
        exact Nat.lt_irrefl first (earlier first present)
      · intro cause depends
        simpa only [List.mem_singleton.mp depends] using live
      · apply ih (available ++ [first]) (first + 1)
        · intro value member
          rcases List.mem_append.mp member with old | added
          · exact (earlier value old).trans (by omega)
          · have same := List.mem_singleton.mp added
            omega
        · exact List.mem_append_left _ live

def producerReceipt (count : Nat) : CausalReceipt Nat where
  roots := (useEvents 2 1 count).map CausalEvent.event
  events := ⟨1, []⟩ :: useEvents 2 1 count

theorem producer_receipt_wellFormed (count : Nat) :
    CausalReceipt.WellFormed [] (producerReceipt count) := by
  refine ⟨by simp, ?_, ?_⟩
  · refine ⟨by simp, by simp, ?_⟩
    exact uses_ordered [1] 2 1 count (by simp) (by simp)
  · intro root present
    simpa [producerReceipt, CausalReceipt.known, CausalReceipt.flattenedSupport] using
      List.mem_cons_of_mem 1 present

theorem producer_receipt_check (count : Nat) :
    CausalReceipt.check [] (producerReceipt count) = true :=
  (CausalReceipt.check_iff [] _).2 (producer_receipt_wellFormed count)

theorem producer_receipt_acyclic (count event : Nat) :
    ¬ Relation.TransGen (producerReceipt count).Direct event event :=
  CausalReceipt.no_causal_cycle [] _ (producer_receipt_wellFormed count) event

theorem two_uses_remain_distinct :
    (producerReceipt 2).flattenedSupport = [1, 2, 3] := by decide

theorem lost_use_changes_receipt :
    (producerReceipt 2).flattenedSupport ≠ (producerReceipt 1).flattenedSupport := by decide

theorem forward_producer_is_refused :
    CausalReceipt.check [] (⟨[2], [⟨1, []⟩, ⟨2, [3]⟩]⟩ : CausalReceipt Nat) = false := by decide

/-! A complete ancestry readout uses the same bounded prefix. Captured
boundary references remain explicit, and omitted events refuse a claim about
the complete represented ancestry. This does not authenticate native edges. -/

variable {Occurrence : Type*}

def completeAncestors [DecidableEq Occurrence] (record : Prefix (CausalEvent Occurrence))
    (boundary roots : List Occurrence) (identity : Occurrence) : Option (List Occurrence) :=
  (record.graph? boundary roots).bind fun receipt => receipt.ancestors? boundary identity

/-- Recording that fits yields the same ancestry as the checked receipt,
including its original captured boundary and selected occurrence. -/
theorem recorded_ancestry [DecidableEq Occurrence] (receipt : CausalReceipt Occurrence)
    (capacity : Nat) (boundary : List Occurrence) (identity : Occurrence)
    (fits : receipt.events.length ≤ capacity) :
    completeAncestors ((Prefix.initial capacity).append receipt.events)
      boundary receipt.roots identity = receipt.ancestors? boundary identity := by
  have full := (Prefix.complete_iff capacity receipt.events).2 fits
  unfold completeAncestors Prefix.graph?
  rw [full]
  change (if receipt.check boundary then some receipt else none).bind
    (fun checked => checked.ancestors? boundary identity) = receipt.ancestors? boundary identity
  cases checked : receipt.check boundary <;> simp [checked, CausalReceipt.ancestors?]

/-- A bounded recording cannot turn a missing suffix into a complete
ancestry certificate, even if the selected node lies in the retained prefix. -/
theorem truncated_ancestry_refused [DecidableEq Occurrence]
    (capacity : Nat) (events : List (CausalEvent Occurrence))
    (boundary roots : List Occurrence) (identity : Occurrence)
    (tooMany : capacity < events.length) :
    completeAncestors ((Prefix.initial capacity).append events) boundary roots identity = none := by
  have omitted : ((Prefix.initial capacity).append events).omitted ≠ 0 := by
    rw [Prefix.initial_omitted]
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt tooMany)
  unfold completeAncestors
  rw [Prefix.graph?_truncated boundary roots _ omitted]
  rfl

theorem ancestry_resumption [DecidableEq Occurrence] (record : Prefix (CausalEvent Occurrence))
    (before after : List (CausalEvent Occurrence))
    (boundary roots : List Occurrence) (identity : Occurrence) :
    completeAncestors ((record.append before).append after) boundary roots identity =
      completeAncestors (record.append (before ++ after)) boundary roots identity := by
  rw [Prefix.append_append]

/-- An accepted ancestry readout carries the existing complete graph
certificate and the exact retained causal relation. Native event authenticity
remains an independent obligation. -/
theorem complete_ancestry_sound [DecidableEq Occurrence]
    (record : Prefix (CausalEvent Occurrence)) (boundary roots : List Occurrence)
    (identity : Occurrence) (result : List Occurrence)
    (reported : completeAncestors record boundary roots identity = some result) :
    ∃ receipt : CausalReceipt Occurrence,
      record.complete? = some receipt.events ∧ receipt.roots = roots ∧
      receipt.WellFormed boundary ∧ identity ∈ receipt.known boundary ∧
      ∀ cause, cause ∈ result ↔
        cause = identity ∨ Relation.TransGen receipt.Direct cause identity := by
  obtain ⟨receipt, graphRead, ancestryRead⟩ := Option.bind_eq_some_iff.mp reported
  obtain ⟨complete, _, sameRoots⟩ := Prefix.graph?_sound boundary roots record receipt graphRead
  obtain ⟨valid, known, exactCauses⟩ :=
    CausalReceipt.ancestors?_exact boundary receipt identity result ancestryRead
  exact ⟨receipt, complete, sameRoots, valid, known, exactCauses⟩

/-- A complete retained graph supports both distinct uses of one producer. -/
theorem complete_producer_ancestry :
    completeAncestors ((Prefix.initial 3).append (producerReceipt 2).events) [] [2, 3] 2 =
      some [2, 1] ∧
    completeAncestors ((Prefix.initial 3).append (producerReceipt 2).events) [] [2, 3] 3 =
      some [3, 1] := by decide

/-- Recording only the producer and its first use does not justify a complete
explanation of either use in the three-occurrence history. -/
theorem truncated_producer_ancestry :
    completeAncestors ((Prefix.initial 2).append (producerReceipt 2).events) [] [2, 3] 2 = none ∧
    completeAncestors ((Prefix.initial 2).append (producerReceipt 2).events) [] [2, 3] 3 = none := by
  decide

namespace Candidate

variable {Key Revision Reason : Type*}

/-- Admission is not completion. A pending decision cannot license rejection
or closure; a rejected decision retains its particular explanation. -/
inductive Decision (Reason : Type*) where
  | admitted
  | pending
  | rejected (reason : Reason)
  deriving DecidableEq, Repr

/-- Candidate keys identify occurrences, not equal printed payloads. The
linear inventory oracle is read newest-first for this observation. -/
def latest [DecidableEq Key] (events : List (Key × Decision Reason)) (key : Key) :
    Option (Decision Reason) :=
  (VariableInventory.scan events.reverse key).map Prod.snd

@[simp] theorem latest_none_iff [DecidableEq Key]
    (events : List (Key × Decision Reason)) (key : Key) :
    latest events key = none ↔ key ∉ events.map Prod.fst := by
  simp [latest, VariableInventory.scan_none_iff, List.map_reverse]

/-- A later decision supersedes the earlier decision for that same occurrence.
It does not change any other occurrence's latest decision. -/
theorem latest_append [DecidableEq Key]
    (before after : List (Key × Decision Reason)) (key : Key) :
    latest (before ++ after) key = (latest after key).or (latest before key) := by
  simp only [latest, List.reverse_append, VariableInventory.scan_append]
  cases VariableInventory.scan after.reverse key <;>
    cases VariableInventory.scan before.reverse key <;> rfl

@[simp] theorem latest_new [DecidableEq Key]
    (events : List (Key × Decision Reason)) (key : Key) (decision : Decision Reason) :
    latest (events ++ [(key, decision)]) key = some decision := by
  rw [latest_append]
  simp [latest, VariableInventory.scan_cons]

theorem latest_other [DecidableEq Key]
    (events : List (Key × Decision Reason)) (key other : Key)
    (decision : Decision Reason) (different : other ≠ key) :
    latest (events ++ [(other, decision)]) key = latest events key := by
  rw [latest_append]
  simp [latest, different, VariableInventory.scan]

/-- Renaming occurrence identities preserves the latest verdict exactly.
The mapping cannot collapse separate candidates into one occurrence. -/
theorem latest_transport {NextKey : Type*} [DecidableEq Key] [DecidableEq NextKey]
    (mapping : Key → NextKey) (faithful : Function.Injective mapping)
    (events : List (Key × Decision Reason)) (key : Key) :
    latest (events.map (fun entry => (mapping entry.1, entry.2))) (mapping key) =
      latest events key := by
  unfold latest
  rw [← List.map_reverse]
  have lookup := VariableInventory.scan_transport mapping faithful
    (fun decision : Decision Reason => decision) events.reverse key
  rw [lookup]
  cases VariableInventory.scan events.reverse key <;> rfl

inductive Explanation (Reason : Type*) where
  | staleContext
  | outsideInquiry
  | incompleteRecording
  | noRecordedDecision
  | recorded (decision : Decision Reason)
  deriving DecidableEq, Repr

/-- The revision includes every context component observed by this inquiry.
A missing decision is explicitly unrecorded, not a checked rejection. Calling
it unexamined also requires a faithful recording from the inquiry's start. -/
def explain [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (key : Key) : Explanation Reason :=
  if captured ≠ current then .staleContext
  else if key ∉ inventory then .outsideInquiry
  else match record.complete? with
    | none => .incompleteRecording
    | some events => match latest events key with
      | none => .noRecordedDecision
      | some decision => .recorded decision

theorem explain_recorded [DecidableEq Key] [DecidableEq Revision]
    (revision : Revision) (inventory : List Key)
    (events : List (Key × Decision Reason)) (capacity : Nat) (key : Key)
    (present : key ∈ inventory) (fits : events.length ≤ capacity) :
    explain revision revision inventory ((Prefix.initial capacity).append events) key =
      match latest events key with
      | none => .noRecordedDecision
      | some decision => .recorded decision := by
  simp [explain, present, (Prefix.complete_iff capacity events).2 fits]

theorem explain_missing [DecidableEq Key] [DecidableEq Revision]
    (revision : Revision) (inventory : List Key)
    (events : List (Key × Decision Reason)) (capacity : Nat) (key : Key)
    (present : key ∈ inventory) (fits : events.length ≤ capacity)
    (missing : key ∉ events.map Prod.fst) :
    explain revision revision inventory ((Prefix.initial capacity).append events) key =
      .noRecordedDecision := by
  rw [explain_recorded revision inventory events capacity key present fits,
    (latest_none_iff events key).2 missing]

theorem explain_truncated [DecidableEq Key] [DecidableEq Revision]
    (revision : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (key : Key)
    (present : key ∈ inventory) (omitted : record.omitted ≠ 0) :
    explain revision revision inventory record key = .incompleteRecording := by
  simp [explain, present, Prefix.complete?, omitted]

/-- The explanation transports through the same occurrence map as the
bounded recording. Capacity, omissions, revision and decision meanings stay
fixed; only candidate identities change. -/
theorem explain_transport {NextKey : Type*}
    [DecidableEq Key] [DecidableEq NextKey] [DecidableEq Revision]
    (mapping : Key → NextKey) (faithful : Function.Injective mapping)
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (key : Key) :
    explain captured current (inventory.map mapping)
      (record.map (fun entry => (mapping entry.1, entry.2))) (mapping key) =
        explain captured current inventory record key := by
  have member : mapping key ∈ inventory.map mapping ↔ key ∈ inventory := by
    constructor
    · intro mapped
      obtain ⟨candidate, present, same⟩ := List.mem_map.mp mapped
      exact faithful same ▸ present
    · intro present
      exact List.mem_map_of_mem present
  by_cases same : captured = current
  · by_cases present : key ∈ inventory
    · cases complete : record.complete? with
      | none => simp [explain, same, member, present, Prefix.complete?_map, complete]
      | some events =>
          simp [explain, same, member, present, Prefix.complete?_map, complete,
            latest_transport mapping faithful]
    · simp [explain, same, member, present]
  · simp [explain, same]

def rejections [DecidableEq Key] (events : List (Key × Decision Reason)) :
    List Key → Option (List (Key × Reason))
  | [] => some []
  | key :: rest => match latest events key with
      | some (.rejected reason) =>
          (rejections events rest).map ((key, reason) :: ·)
      | _ => none

/-- Exact per-occurrence coverage: every inventory position has a recorded
latest rejection. Equal payloads never merge two different keys. -/
theorem rejections_iff [DecidableEq Key] (events : List (Key × Decision Reason))
    (inventory : List Key) (result : List (Key × Reason)) :
    rejections events inventory = some result ↔
      List.Forall₂ (fun key entry => entry.1 = key ∧
        latest events key = some (.rejected entry.2)) inventory result := by
  induction inventory generalizing result with
  | nil => cases result <;> simp [rejections]
  | cons key rest ih =>
      cases decision : latest events key with
      | none => cases result <;> simp [rejections, decision, List.forall₂_cons]
      | some decisionValue =>
          cases decisionValue with
          | admitted => cases result <;> simp [rejections, decision, List.forall₂_cons]
          | pending => cases result <;> simp [rejections, decision, List.forall₂_cons]
          | rejected reason =>
              cases result with
              | nil => simp [rejections, decision]
              | cons entry tail =>
                  cases entry with
                  | mk entryKey entryReason =>
                      simp [rejections, decision, List.forall₂_cons, ih, and_assoc, and_comm,
                        eq_comm]

theorem rejections_transport {NextKey : Type*} [DecidableEq Key] [DecidableEq NextKey]
    (mapping : Key → NextKey) (faithful : Function.Injective mapping)
    (events : List (Key × Decision Reason)) (inventory : List Key) :
    rejections (events.map (fun entry => (mapping entry.1, entry.2))) (inventory.map mapping) =
      (rejections events inventory).map (List.map (fun entry => (mapping entry.1, entry.2))) := by
  induction inventory with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.map_cons, rejections, latest_transport mapping faithful]
      cases decision : latest events key with
      | none => rfl
      | some decisionValue =>
          cases decisionValue with
          | admitted => rfl
          | pending => rfl
          | rejected reason =>
              rw [ih]
              cases rejections events rest <;> rfl

/-- Complete rejection coverage for this captured finite inventory. It does
not by itself close a search frontier or authenticate the inventory. -/
def completeRejections? [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) : Option (List (Key × Reason)) :=
  if captured = current then record.complete?.bind (fun events => rejections events inventory)
  else none

theorem complete_rejections_sound [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (result : List (Key × Reason))
    (accepted : completeRejections? captured current inventory record = some result) :
    captured = current ∧ ∃ events,
      record.complete? = some events ∧
      List.Forall₂ (fun key entry => entry.1 = key ∧
        latest events key = some (.rejected entry.2)) inventory result := by
  unfold completeRejections? at accepted
  split at accepted
  · rename_i currentContext
    obtain ⟨events, complete, rejected⟩ := Option.bind_eq_some_iff.mp accepted
    exact ⟨currentContext, events, complete, (rejections_iff events inventory result).1 rejected⟩
  · simp at accepted

theorem rejections_missing [DecidableEq Key]
    (events : List (Key × Decision Reason)) (inventory : List Key) (key : Key)
    (present : key ∈ inventory) (missing : latest events key = none) :
    rejections events inventory = none := by
  cases result : rejections events inventory with
  | none => rfl
  | some entries =>
      have covered := (rejections_iff events inventory entries).1 result
      have examined : latest events key ≠ none := by
        clear result
        induction covered with
        | nil => simp at present
        | @cons candidate entry rest entries head tail ih =>
            rcases List.mem_cons.mp present with same | later
            · rw [same, head.2]
              simp
            · exact ih later
      exact (examined missing).elim

theorem complete_rejections_resumption [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (before after : List (Key × Decision Reason)) :
    completeRejections? captured current inventory ((record.append before).append after) =
      completeRejections? captured current inventory (record.append (before ++ after)) := by
  rw [Prefix.append_append]

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.OpenTotalityObservation

/-- Closed absence additionally inspects the actual controlled run. The
returned coverage is the existing empty-frontier witness, not a new flag.
Native adapters must still justify this system, census, revision and history. -/
def closedAbsence? {Node Answer Memory : Type*} [DecidableEq Node] [DecidableEq Answer]
    [DecidableEq Key] [DecidableEq Revision]
    (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) (captured current : Revision)
    (inventory : List Key) (record : Prefix (Key × Decision Reason)) :
    Option (ControlledCoverage system controller roots fuel × List (Key × Reason)) :=
  match completeRejections? captured current inventory record with
  | none => none
  | some rejected =>
      let outcome := InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)
      if closed : outcome.search.frontier = [] then
        if outcome.search.events = [] then some (⟨closed⟩, rejected) else none
      else none

theorem closed_absence_sound {Node Answer Memory : Type*}
    [DecidableEq Node] [DecidableEq Answer] [DecidableEq Key] [DecidableEq Revision]
    (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) (captured current : Revision)
    (inventory : List Key) (record : Prefix (Key × Decision Reason))
    (result : ControlledCoverage system controller roots fuel × List (Key × Reason))
    (accepted : closedAbsence? system controller roots fuel captured current
      inventory record = some result) :
    completeRejections? captured current inventory record = some result.2 ∧
      (InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)).search.events = [] := by
  unfold closedAbsence? at accepted
  split at accepted
  · simp at accepted
  · rename_i rejected complete
    dsimp only at accepted
    split at accepted
    · split at accepted
      · have same := Option.some.inj accepted
        subst result
        exact ⟨complete, by assumption⟩
      · simp at accepted
    · simp at accepted

/-- A closed absence readout has zero answer denotation under the existing
additive account law. It is a theorem about that qualified branching system,
not a conclusion from zero allowance, missing trace entries or source hashes. -/
theorem closed_absence_denotation {Node Answer Memory : Type*}
    [DecidableEq Node] [DecidableEq Answer] [DecidableEq Key] [DecidableEq Revision]
    (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (denotation : AdditiveDenotation system) (roots : List Node) (fuel : Nat)
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason))
    (result : ControlledCoverage system controller roots fuel × List (Key × Reason))
    (accepted : closedAbsence? system controller roots fuel captured current
      inventory record = some result) : foldValues denotation.value roots = 0 := by
  have noAnswers := (closed_absence_sound system controller roots fuel captured current
    inventory record result accepted).2
  have preserved := InferenceControl.Snapshot.completed_run_denotation system controller
    denotation roots fuel result.1.frontierEmpty
  rw [noAnswers] at preserved
  simpa [eventBag] using preserved.symm

namespace Controls

private def decisions : List (Nat × Decision Nat) :=
  [(1, .rejected 7), (2, .pending), (3, .admitted)]

theorem distinct_candidate_statuses :
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 1 =
      .recorded (.rejected 7) ∧
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 2 =
      .recorded .pending ∧
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 3 =
      .recorded .admitted ∧
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 5 =
      .noRecordedDecision := by decide

theorem changed_and_truncated_refused :
    explain 4 5 [1, 2, 3] ((Prefix.initial 3).append decisions) 1 = .staleContext ∧
    explain 4 4 [1, 2, 3] ((Prefix.initial 1).append decisions) 1 =
      .incompleteRecording := by decide

theorem newest_decision_wins :
    latest (decisions ++ [(1, .pending)]) 1 = some .pending ∧
    latest (decisions ++ [(1, .pending)]) 2 = some .pending := by decide

theorem incomplete_inventory_refused :
    completeRejections? 4 4 [1, 2] ((Prefix.initial 3).append decisions) = none ∧
    completeRejections? 4 4 [1, 5] ((Prefix.initial 3).append decisions) = none := by decide

private def finiteInquiry : BranchingSystem Nat Nat where
  emit _ := none
  successors node := if node = 0 then [1, 2] else []

private def fullRejections : Prefix (Nat × Decision Nat) :=
  (Prefix.initial 2).append [(1, .rejected 7), (2, .rejected 8)]

theorem actual_closed_search_accepted :
    (closedAbsence? finiteInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 3 4 4 [1, 2] fullRejections).isSome = true := by decide

/-- The same complete rejection trace cannot close a still-live run, including
a run with no execution allowance. -/
theorem live_and_zero_allowance_refused :
    (closedAbsence? finiteInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 2 4 4 [1, 2] fullRejections).isNone = true ∧
    (closedAbsence? finiteInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 0 4 4 [1, 2] fullRejections).isNone = true := by decide

theorem same_reason_keeps_candidate_occurrences :
    completeRejections? 4 4 [1, 2]
      ((Prefix.initial 2).append [(1, Decision.rejected 7), (2, .rejected 7)]) =
        some [(1, 7), (2, 7)] := by decide

theorem late_capture_is_not_coverage :
    completeRejections? 4 4 [1, 2]
      ((Prefix.initial 1).append [(2, Decision.rejected 8)]) = none := by decide

theorem collapsed_identity_changes_latest :
    latest ([(1, Decision.rejected 7), (2, .pending)] : List (Nat × Decision Nat)) 1 =
      some (.rejected 7) ∧
    latest ([(1, Decision.rejected 7), (2, .pending)].map
      (fun entry : Nat × Decision Nat => (0, entry.2))) 0 = some .pending := by decide

private def answeringInquiry : BranchingSystem Nat Nat where
  emit node := if node = 2 then some 99 else none
  successors node := if node = 0 then [1, 2] else []

/-- Rejection metadata cannot override an actual answer in the controlled
run. This also separates complete execution from closed answer absence. -/
theorem actual_answer_blocks_absence :
    (closedAbsence? answeringInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 3 4 4 [1, 2] fullRejections).isNone = true := by decide

end Controls
end Candidate

end Mettapedia.Machines.ExecutionHistoryReadout
