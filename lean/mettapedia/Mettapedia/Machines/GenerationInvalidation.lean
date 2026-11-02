import Mettapedia.Machines.RevisionedQueryFacts

/-!
# Generation invalidation refines physical cache clearing

The reference bank erases its entries on every invalidation. The target bank
retains cold entries and changes a positive generation, erasing only before
generation reuse. Publication can overwrite any selected slot. A reachable
slot never has a generation greater than the current generation; this is
essential to rule out resurrection before wraparound.

Payloads may contain the complete revision-scoped inquiry and result. The
projection preserves those payloads exactly, so existing exact-key lookup
and fact-soundness laws apply downstream. Native mutation coverage, stamp
completeness, thread confinement and machine-integer correspondence remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GenerationInvalidation

variable {Slot Payload : Type} [DecidableEq Slot]

structure Cell (Payload : Type) where
  generation : Nat
  payload : Payload

structure State (Slot Payload : Type) where
  generation : Nat
  slots : Slot → Option (Cell Payload)

def WellFormed (limit : Nat) (state : State Slot Payload) : Prop :=
  0 < state.generation ∧ state.generation ≤ limit ∧
    ∀ slot cell, state.slots slot = some cell → cell.generation ≤ state.generation

def initial : State Slot Payload := ⟨1, fun _ => none⟩

def project (state : State Slot Payload) (slot : Slot) : Option Payload :=
  (state.slots slot).bind fun cell =>
    if cell.generation = state.generation then some cell.payload else none

def publish (state : State Slot Payload) (slot : Slot) (payload : Payload) :
    State Slot Payload :=
  { state with slots := Function.update state.slots slot (some ⟨state.generation, payload⟩) }

def invalidate (limit : Nat) (state : State Slot Payload) : State Slot Payload :=
  if state.generation = limit then initial
  else { state with generation := state.generation + 1 }

omit [DecidableEq Slot] in
theorem initial_wellFormed (limit : Nat) (positive : 0 < limit) :
    WellFormed limit (initial : State Slot Payload) := by
  simp [WellFormed, initial]
  omega

omit [DecidableEq Slot] in
theorem initial_empty : project (initial : State Slot Payload) = fun _ => none := by
  rfl

theorem publish_project (state : State Slot Payload) (slot : Slot) (payload : Payload) :
    project (publish state slot payload) = Function.update (project state) slot (some payload) := by
  funext observed
  by_cases same : observed = slot
  · subst observed
    simp [project, publish]
  · simp only [project, publish, Function.update_of_ne same]
    rfl

theorem publish_wellFormed (limit : Nat) (state : State Slot Payload)
    (valid : WellFormed limit state) (slot : Slot) (payload : Payload) :
    WellFormed limit (publish state slot payload) := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro observed cell found
  by_cases same : observed = slot
  · subst observed
    simp only [publish, Function.update_self, Option.some.injEq] at found
    subst cell
    exact Nat.le_refl _
  · apply valid.2.2 observed cell
    simpa [publish, same] using found

omit [DecidableEq Slot] in
theorem invalidate_wellFormed (limit : Nat) (state : State Slot Payload)
    (valid : WellFormed limit state) : WellFormed limit (invalidate limit state) := by
  by_cases last : state.generation = limit
  · have positive := valid.1
    simpa [invalidate, last] using initial_wellFormed limit (by omega : 0 < limit)
  · refine ⟨?_, ?_, ?_⟩
    · simp [invalidate, last]
    · simp only [invalidate, last, ↓reduceIte]
      have bound := valid.2.1
      omega
    · intro slot cell found
      simp only [invalidate, last, ↓reduceIte] at found ⊢
      have older := valid.2.2 slot cell found
      omega

omit [DecidableEq Slot] in
theorem invalidate_empty (limit : Nat) (state : State Slot Payload)
    (valid : WellFormed limit state) :
    project (invalidate limit state) = fun _ => none := by
  by_cases last : state.generation = limit
  · simp [invalidate, last, initial_empty]
  · funext slot
    cases found : state.slots slot with
    | none => simp [project, invalidate, last, found]
    | some cell =>
      have older := valid.2.2 slot cell found
      have different : cell.generation ≠ state.generation + 1 := by omega
      simp [project, invalidate, last, found, different]

omit [DecidableEq Slot] in
theorem invalidate_without_wrap_keeps_storage (limit : Nat) (state : State Slot Payload)
    (notLast : state.generation ≠ limit) :
    (invalidate limit state).slots = state.slots := by
  simp [invalidate, notLast]

omit [DecidableEq Slot] in
theorem invalidate_at_wrap_erases_storage (limit : Nat) (state : State Slot Payload)
    (last : state.generation = limit) :
    (invalidate limit state).slots = fun _ => none := by
  simp [invalidate, last, initial]

inductive Event (Slot Payload : Type)
  | publish (slot : Slot) (payload : Payload)
  | invalidate

def targetStep (limit : Nat) (state : State Slot Payload) : Event Slot Payload → State Slot Payload
  | .publish slot payload => publish state slot payload
  | .invalidate => invalidate limit state

def referenceStep (bank : Slot → Option Payload) : Event Slot Payload → Slot → Option Payload
  | .publish slot payload => Function.update bank slot (some payload)
  | .invalidate => fun _ => none

theorem step_wellFormed (limit : Nat) (state : State Slot Payload)
    (valid : WellFormed limit state) (event : Event Slot Payload) :
    WellFormed limit (targetStep limit state event) := by
  cases event with
  | publish slot payload => exact publish_wellFormed limit state valid slot payload
  | invalidate => exact invalidate_wellFormed limit state valid

theorem step_refines_clear (limit : Nat) (state : State Slot Payload)
    (valid : WellFormed limit state) (event : Event Slot Payload) :
    project (targetStep limit state event) = referenceStep (project state) event := by
  cases event with
  | publish slot payload => exact publish_project state slot payload
  | invalidate => exact invalidate_empty limit state valid

def runTarget (limit : Nat) : State Slot Payload → List (Event Slot Payload) → State Slot Payload
  | state, [] => state
  | state, event :: rest => runTarget limit (targetStep limit state event) rest

def runReference : (Slot → Option Payload) → List (Event Slot Payload) → Slot → Option Payload
  | bank, [] => bank
  | bank, event :: rest => runReference (referenceStep bank event) rest

theorem trace_refines_clear (limit : Nat) (events : List (Event Slot Payload))
    (state : State Slot Payload) (valid : WellFormed limit state) :
    project (runTarget limit state events) = runReference (project state) events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
    simp only [runTarget, runReference]
    rw [ih _ (step_wellFormed limit state valid event), step_refines_clear limit state valid event]

theorem trace_wellFormed (limit : Nat) (events : List (Event Slot Payload))
    (state : State Slot Payload) (valid : WellFormed limit state) :
    WellFormed limit (runTarget limit state events) := by
  induction events generalizing state with
  | nil => exact valid
  | cons event rest ih => exact ih _ (step_wellFormed limit state valid event)

/-- Projection equality preserves the existing independently defined exact lookup. -/
theorem exact_lookup_refines {Stamp Key Fact : Type} [DecidableEq Stamp] [DecidableEq Key]
    (limit : Nat) (events : List (Event Slot (RevisionedQueryFacts.Entry Stamp Key Fact)))
    (state : State Slot (RevisionedQueryFacts.Entry Stamp Key Fact))
    (valid : WellFormed limit state) (probeSlots : List Slot) (stamp : Stamp) (key : Key) :
    RevisionedQueryFacts.lookup stamp key
        (probeSlots.filterMap (project (runTarget limit state events))) =
      RevisionedQueryFacts.lookup stamp key
        (probeSlots.filterMap (runReference (project state) events)) := by
  rw [trace_refines_clear limit events state valid]

/-- Reusing a stamp without erasing its old cells resurrects stale facts. -/
theorem wrap_without_erasure_resurrects :
    project (⟨1, fun (_ : Unit) => some ⟨1, 7⟩⟩ : State Unit Nat) () = some 7 ∧
      project (invalidate 2 (⟨2, fun (_ : Unit) => some ⟨1, 7⟩⟩ : State Unit Nat)) () = none := by
  decide

end Mettapedia.Machines.GenerationInvalidation
