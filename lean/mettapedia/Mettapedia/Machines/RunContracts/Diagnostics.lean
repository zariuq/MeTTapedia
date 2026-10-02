import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.List.Perm.Basic

/-!
# Structured diagnostic evidence and bounded presentation

Unhandled fault occurrences form a multiset. Selecting a diagnostic witness
does not impose a first-fault observation: any genuine occurrence may be shown.
The bounded collector independently counts every fault while retaining only a
bounded list of details. Even a zero detail budget retains the failure summary.

Returned values and unhandled faults are different constructors, independent of
the spelling or structure of a value. A clear fault summary is not a successful
run theorem: completion, test verdicts and output finalization are separate
obligations. Equality of fault status does not imply program equivalence.

Human and machine presentations below are typed records with independently
defined semantic projections. Their authoritative fields agree; wording may
vary. No text parser, JSON/SARIF serializer, C adapter, or runtime refinement is
claimed. The model is finite and its exact counters are natural numbers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.Diagnostics

structure Diagnostic (Code Origin Payload : Type*) where
  id : Nat
  code : Code
  origin : Origin
  payload : Payload
  deriving DecidableEq, Repr

inductive Event (Value Fault : Type*) where
  | returned (value : Value)
  | unhandled (fault : Fault)
  deriving DecidableEq, Repr

inductive FaultStatus where
  | clear
  | failed
  deriving DecidableEq, Repr

def statusOf (total : Nat) : FaultStatus := if total = 0 then .clear else .failed

@[simp] theorem statusOf_clear_iff (total : Nat) : statusOf total = .clear ↔ total = 0 := by
  simp [statusOf]

@[simp] theorem statusOf_failed_iff (total : Nat) :
    statusOf total = .failed ↔ total ≠ 0 := by
  simp [statusOf]

variable {Value Other Fault Code Origin Payload : Type*}

/-- Specification: returned data contributes no unhandled fault occurrence. -/
def faultEvidence : List (Event Value Fault) → Multiset Fault
  | [] => 0
  | .returned _ :: rest => faultEvidence rest
  | .unhandled d :: rest => d ::ₘ faultEvidence rest

def evidenceStatus (evidence : Multiset Fault) : FaultStatus := statusOf evidence.card

@[simp] theorem evidenceStatus_clear_iff (evidence : Multiset Fault) :
    evidenceStatus evidence = .clear ↔ evidence = 0 := by
  simp [evidenceStatus, Multiset.card_eq_zero]

@[simp] theorem evidenceStatus_failed_iff (evidence : Multiset Fault) :
    evidenceStatus evidence = .failed ↔ evidence ≠ 0 := by
  simp [evidenceStatus, Multiset.card_eq_zero]

/-- Nothing selects a preferred order among genuine diagnostic witnesses. -/
def ValidSelection (evidence : Multiset Fault) : Option Fault → Prop
  | none => evidence = 0
  | some d => d ∈ evidence

def selectionStatus : Option Fault → FaultStatus
  | none => .clear
  | some _ => .failed

theorem genuine_witness_is_valid (evidence : Multiset Fault) (d : Fault)
    (genuine : d ∈ evidence) : ValidSelection evidence (some d) := genuine

theorem valid_selection_status (evidence : Multiset Fault) (selected : Option Fault)
    (valid : ValidSelection evidence selected) :
    selectionStatus selected = evidenceStatus evidence := by
  cases selected with
  | none => simp_all [ValidSelection, selectionStatus, evidenceStatus, statusOf]
  | some d =>
      have positive : 0 < evidence.card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨d, valid⟩
      simp [selectionStatus, evidenceStatus, statusOf, Nat.ne_of_gt positive]

theorem valid_selections_agree_on_failure (evidence : Multiset Fault)
    (a b : Option Fault) (ha : ValidSelection evidence a) (hb : ValidSelection evidence b) :
    selectionStatus a = selectionStatus b :=
  (valid_selection_status evidence a ha).trans (valid_selection_status evidence b hb).symm

theorem faultEvidence_perm {xs ys : List (Event Value Fault)} (permutation : xs.Perm ys) :
    faultEvidence xs = faultEvidence ys := by
  induction permutation with
  | nil => rfl
  | cons e _ ih => cases e <;> simp [faultEvidence, ih]
  | swap a b rest => cases a <;> cases b <;> simp [faultEvidence, Multiset.cons_swap]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem status_perm {xs ys : List (Event Value Fault)} (permutation : xs.Perm ys) :
    evidenceStatus (faultEvidence xs) = evidenceStatus (faultEvidence ys) := by
  rw [faultEvidence_perm permutation]

def Event.mapValue (f : Value → Other) : Event Value Fault → Event Other Fault
  | .returned v => .returned (f v)
  | .unhandled d => .unhandled d

theorem map_values_preserves_evidence (f : Value → Other) (events : List (Event Value Fault)) :
    faultEvidence (events.map (Event.mapValue f)) = faultEvidence events := by
  induction events with
  | nil => rfl
  | cons e rest ih => cases e <;> simp [Event.mapValue, faultEvidence, ih]

/-- An implementation state: total faults and a bounded sequence of details. -/
structure Collected (Fault : Type*) where
  total : Nat
  shown : List Fault
  deriving DecidableEq, Repr

/-- Bounded detail collection. Exhausting the display budget does not stop
fault accounting; every unhandled event increments the total exactly once. -/
def collect : Nat → List (Event Value Fault) → Collected Fault
  | _, [] => ⟨0, []⟩
  | budget, .returned _ :: rest => collect budget rest
  | 0, .unhandled _ :: rest =>
      let tail := collect 0 rest
      ⟨tail.total + 1, []⟩
  | budget + 1, .unhandled d :: rest =>
      let tail := collect budget rest
      ⟨tail.total + 1, d :: tail.shown⟩

theorem collect_total (budget : Nat) (events : List (Event Value Fault)) :
    (collect budget events).total = (faultEvidence events).card := by
  induction events generalizing budget with
  | nil => rfl
  | cons e rest ih =>
      cases e with
      | returned v => exact ih budget
      | unhandled d => cases budget <;> simp [collect, faultEvidence, ih]

theorem collect_zero_shown (events : List (Event Value Fault)) :
    (collect 0 events).shown = [] := by
  induction events with
  | nil => rfl
  | cons e rest ih => cases e <;> simp [collect, ih]

/-- Occurrence containment preserves duplicates, not just membership of values. -/
theorem collect_occurrences_le (budget : Nat) (events : List (Event Value Fault)) :
    ((collect budget events).shown : Multiset Fault) ≤ faultEvidence events := by
  induction events generalizing budget with
  | nil => exact le_rfl
  | cons e rest ih =>
      cases e with
      | returned v => exact ih budget
      | unhandled d =>
          cases budget with
          | zero => exact Multiset.zero_le _
          | succ budget =>
              exact Multiset.cons_le_cons d (ih budget)

theorem collect_shown_length (budget : Nat) (events : List (Event Value Fault)) :
    (collect budget events).shown.length = min budget (faultEvidence events).card := by
  induction events generalizing budget with
  | nil => simp [collect, faultEvidence]
  | cons e rest ih =>
      cases e with
      | returned v => exact ih budget
      | unhandled d =>
          cases budget with
          | zero => simp [collect, faultEvidence]
          | succ budget => simp [collect, faultEvidence, ih, Nat.succ_min_succ]

/-- Refinement of bounded storage against the independently defined fault bag. -/
theorem collect_refines (budget : Nat) (events : List (Event Value Fault)) :
    (collect budget events).total = (faultEvidence events).card ∧
    ((collect budget events).shown : Multiset Fault) ≤ faultEvidence events ∧
    (collect budget events).shown.length = min budget (faultEvidence events).card :=
  ⟨collect_total _ _, collect_occurrences_le _ _, collect_shown_length _ _⟩

theorem displayed_witness_genuine (budget : Nat) (events : List (Event Value Fault))
    (d : Fault) (shown : d ∈ (collect budget events).shown) : d ∈ faultEvidence events :=
  Multiset.mem_of_le (collect_occurrences_le budget events) (Multiset.mem_coe.mpr shown)

theorem truncation_preserves_status (a b : Nat) (events : List (Event Value Fault)) :
    statusOf (collect a events).total = statusOf (collect b events).total := by
  rw [collect_total, collect_total]

/-- Detail budgets and collection order may both change without changing the
fault summary. This is not an equivalence of the returned values or effects. -/
theorem collect_status_perm (a b : Nat) {xs ys : List (Event Value Fault)}
    (permutation : xs.Perm ys) :
    statusOf (collect a xs).total = statusOf (collect b ys).total := by
  rw [collect_total, collect_total, faultEvidence_perm permutation]

theorem fault_prevents_clear_summary (budget : Nat) (events : List (Event Value Fault))
    (d : Fault) (unhandled : d ∈ faultEvidence events) :
    statusOf (collect budget events).total = .failed := by
  rw [collect_total, statusOf_failed_iff]
  exact Nat.ne_of_gt (Multiset.card_pos_iff_exists_mem.mpr ⟨d, unhandled⟩)

def omitted (c : Collected Fault) : Nat := c.total - c.shown.length

theorem collect_omitted (budget : Nat) (events : List (Event Value Fault)) :
    omitted (collect budget events) = (faultEvidence events).card - budget := by
  simp only [omitted, collect_total, collect_shown_length]
  omega

/-- This is one possible display policy, not the required semantic observer. -/
def firstWitness : List (Event Value Fault) → Option Fault
  | [] => none
  | .returned _ :: rest => firstWitness rest
  | .unhandled d :: _ => some d

theorem firstWitness_valid (events : List (Event Value Fault)) :
    ValidSelection (faultEvidence events) (firstWitness events) := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
      cases e with
      | returned v => exact ih
      | unhandled d => simp [firstWitness, faultEvidence, ValidSelection]

/-! ## Typed presentations, before serialization -/

structure HumanEntry (Code Origin Payload : Type*) where
  wording : String
  stableId : Nat
  classification : Code
  source : Origin
  evidence : Payload
  deriving DecidableEq, Repr

structure MachineEntry (Code Origin Payload : Type*) where
  id : Nat
  code : Code
  origin : Origin
  payload : Payload
  deriving DecidableEq, Repr

def renderHumanEntry (wording : Diagnostic Code Origin Payload → String)
    (d : Diagnostic Code Origin Payload) : HumanEntry Code Origin Payload :=
  ⟨wording d, d.id, d.code, d.origin, d.payload⟩

def renderMachineEntry (d : Diagnostic Code Origin Payload) : MachineEntry Code Origin Payload :=
  ⟨d.id, d.code, d.origin, d.payload⟩

def HumanEntry.facts (d : HumanEntry Code Origin Payload) : Diagnostic Code Origin Payload :=
  ⟨d.stableId, d.classification, d.source, d.evidence⟩

def MachineEntry.facts (d : MachineEntry Code Origin Payload) : Diagnostic Code Origin Payload :=
  ⟨d.id, d.code, d.origin, d.payload⟩

structure HumanReport (Code Origin Payload : Type*) where
  heading : String
  status : FaultStatus
  faultCount : Nat
  omittedDetails : Nat
  details : List (HumanEntry Code Origin Payload)
  deriving DecidableEq, Repr

structure MachineReport (Code Origin Payload : Type*) where
  total : Nat
  status : FaultStatus
  diagnostics : List (MachineEntry Code Origin Payload)
  omitted : Nat
  deriving DecidableEq, Repr

structure ReportFacts (Code Origin Payload : Type*) where
  total : Nat
  status : FaultStatus
  shown : List (Diagnostic Code Origin Payload)
  omitted : Nat
  deriving DecidableEq, Repr

def renderHuman (heading : String) (wording : Diagnostic Code Origin Payload → String)
    (c : Collected (Diagnostic Code Origin Payload)) : HumanReport Code Origin Payload :=
  ⟨heading, statusOf c.total, c.total, omitted c, c.shown.map (renderHumanEntry wording)⟩

def renderMachine (c : Collected (Diagnostic Code Origin Payload)) :
    MachineReport Code Origin Payload :=
  ⟨c.total, statusOf c.total, c.shown.map renderMachineEntry, c.total - c.shown.length⟩

def HumanReport.facts (r : HumanReport Code Origin Payload) : ReportFacts Code Origin Payload :=
  ⟨r.faultCount, r.status, r.details.map HumanEntry.facts, r.omittedDetails⟩

def MachineReport.facts (r : MachineReport Code Origin Payload) : ReportFacts Code Origin Payload :=
  ⟨r.total, r.status, r.diagnostics.map MachineEntry.facts, r.omitted⟩

theorem presentations_agree (heading : String) (wording : Diagnostic Code Origin Payload → String)
    (c : Collected (Diagnostic Code Origin Payload)) :
    (renderHuman heading wording c).facts = (renderMachine c).facts := by
  simp [renderHuman, renderMachine, HumanReport.facts, MachineReport.facts,
    HumanEntry.facts, MachineEntry.facts, renderHumanEntry, renderMachineEntry,
    List.map_map, Function.comp_def, omitted]

theorem wording_preserves_facts (heading₁ heading₂ : String)
    (wording₁ wording₂ : Diagnostic Code Origin Payload → String)
    (c : Collected (Diagnostic Code Origin Payload)) :
    (renderHuman heading₁ wording₁ c).facts = (renderHuman heading₂ wording₂ c).facts :=
  (presentations_agree _ _ c).trans (presentations_agree _ _ c).symm

theorem machine_report_failed_iff (budget : Nat)
    (events : List (Event Value (Diagnostic Code Origin Payload))) :
    (renderMachine (collect budget events)).status = .failed ↔ faultEvidence events ≠ 0 := by
  simp [renderMachine, collect_total, Multiset.card_eq_zero]

/-- Every machine detail retains the original identifier, classification,
origin and payload of an actual unhandled occurrence. -/
theorem machine_report_detail_genuine (budget : Nat)
    (events : List (Event Value (Diagnostic Code Origin Payload)))
    (d : Diagnostic Code Origin Payload)
    (shown : d ∈ (renderMachine (collect budget events)).facts.shown) :
    d ∈ faultEvidence events := by
  have member : d ∈ (collect budget events).shown := by
    simpa [renderMachine, MachineReport.facts, renderMachineEntry, MachineEntry.facts,
      List.map_map, Function.comp_def] using shown
  exact displayed_witness_genuine budget events d member

namespace Controls

abbrev D := Diagnostic String Nat String

def first : D := ⟨10, "assertion-mismatch", 3, "expected 2; received 1"⟩
def second : D := ⟨20, "output-failure", 9, "report write failed"⟩

def left : List (Event String D) := [.unhandled first, .unhandled second]
def right : List (Event String D) := [.unhandled second, .unhandled first]

theorem first_witness_changes_under_permutation :
    left.Perm right ∧ firstWitness left ≠ firstWitness right := by
  constructor
  · exact List.Perm.swap _ _ []
  · decide

theorem different_witnesses_same_failure :
    evidenceStatus (faultEvidence left) = .failed ∧
    evidenceStatus (faultEvidence right) = .failed := by decide

theorem zero_budget_cannot_hide_failure :
    (collect 0 left).shown = [] ∧ (collect 0 left).total = 2 ∧
    statusOf (collect 0 left).total = .failed ∧ omitted (collect 0 left) = 2 := by decide

theorem one_detail_retains_total :
    collect 1 left = ⟨2, [first]⟩ := by decide

theorem order_changes_display_not_failure :
    (collect 1 left).shown ≠ (collect 1 right).shown ∧
    statusOf (collect 1 left).total = statusOf (collect 1 right).total := by decide

theorem duplicate_fault_occurrences_count :
    collect 1 ([.unhandled first, .unhandled first] : List (Event String D)) =
      ⟨2, [first]⟩ := by decide

inductive Datum where
  | symbol (name : String)
  | error (diagnostic : D)
  deriving DecidableEq, Repr

theorem caught_error_data_is_not_unhandled :
    faultEvidence ([.returned (.error first)] : List (Event Datum D)) = 0 ∧
    statusOf (collect 0 ([.returned (.error first)] : List (Event Datum D))).total = .clear := by
  decide

theorem error_spelling_does_not_classify_failure :
    statusOf (collect 1 ([.returned "Error"] : List (Event String D))).total = .clear ∧
    statusOf (collect 1 ([.unhandled ⟨1, "plain", 0, "ordinary text"⟩] :
      List (Event String D))).total = .failed := by decide

theorem caught_data_cannot_erase_sibling_fault :
    collect 1 ([.unhandled second, .returned (.error first)] : List (Event Datum D)) =
      ⟨1, [second]⟩ := by decide

def returnedValues : List (Event Value Fault) → List Value
  | [] => []
  | .returned v :: rest => v :: returnedValues rest
  | .unhandled _ :: rest => returnedValues rest

/-- Equal diagnostic status alone establishes no equality of program answers. -/
theorem equal_status_different_answers :
    let a : List (Event Nat D) := [.returned 1]
    let b : List (Event Nat D) := [.returned 2]
    statusOf (collect 0 a).total = statusOf (collect 0 b).total ∧
    returnedValues a ≠ returnedValues b := by decide

theorem wording_changes_presentation_not_facts :
    let c : Collected D := ⟨1, [first]⟩
    renderHuman "failure" (fun _ => "assertion failed") c ≠
      renderHuman "échec" (fun _ => "assertion incorrecte") c ∧
    (renderHuman "failure" (fun _ => "assertion failed") c).facts =
      (renderHuman "échec" (fun _ => "assertion incorrecte") c).facts := by decide

end Controls

end Mettapedia.Machines.RunContracts.Diagnostics
