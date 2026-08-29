import Mettapedia.GSLT.Core.OccurrenceHeapProtocol

/-!
# Heterogeneous heap dispatch

An indexed heap lookup may expose either a proof occurrence or an opaque
guest entry.  This GSLT retains that sum until the caller selects a branch.
It is deliberately smaller than an assertion machine or a proof machine: its
only authority is exact owner-scoped lookup.

The occurrence branch has a forward specialization into
`OccurrenceHeapProtocol`.  Under that specialization, an opaque result becomes
the proof protocol's explicit wrong-entry-kind fault; the dispatcher itself
does not call an opaque entry erroneous.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HeterogeneousHeapDispatch

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.OccurrenceHeapProtocol

variable {Owner Identity Value Other : Type}

inductive Fault (Owner : Type) where
  | wrongOwner (requested resident : Owner)
  | missingIndex (owner : Owner) (index : Nat)
deriving DecidableEq

inductive Control (Owner Identity Value Other : Type) where
  | lookup (owner : Owner) (index : Nat)
  | foundOccurrence (owner : Owner) (index : Nat)
      (occurrence : Occurrence Identity Value)
  | foundOpaque (owner : Owner) (index : Nat) (value : Other)
  | fault (failure : Fault Owner)
deriving DecidableEq

structure State (Owner Identity Value Other : Type) where
  owner : Owner
  heap : List (Entry Identity Value Other)
  control : Control Owner Identity Value Other
deriving DecidableEq

inductive Step :
    State Owner Identity Value Other →
      State Owner Identity Value Other → Prop where
  | occurrence (owner : Owner) (heap : List (Entry Identity Value Other))
      (index : Nat) (item : Occurrence Identity Value)
      (found : heap[index]? = some (.occurrence item)) :
      Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .foundOccurrence owner index item⟩
  | opaque (owner : Owner) (heap : List (Entry Identity Value Other))
      (index : Nat) (value : Other)
      (found : heap[index]? = some (.opaque value)) :
      Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .foundOpaque owner index value⟩
  | missing (owner : Owner) (heap : List (Entry Identity Value Other))
      (index : Nat) (absent : heap[index]? = none) :
      Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .fault (.missingIndex owner index)⟩
  | wrongOwner (resident requested : Owner)
      (heap : List (Entry Identity Value Other)) (index : Nat)
      (different : requested ≠ resident) :
      Step ⟨resident, heap, .lookup requested index⟩
        ⟨resident, heap, .fault (.wrongOwner requested resident)⟩

def gslt (Owner Identity Value Other : Type) : GSLT where
  Term := State Owner Identity Value Other
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- A present entry is classified by its actual constructor. -/
theorem present_entry_dispatches (owner : Owner)
    (heap : List (Entry Identity Value Other)) (index : Nat)
    (entry : Entry Identity Value Other) (found : heap[index]? = some entry) :
    match entry with
    | .occurrence item => Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .foundOccurrence owner index item⟩
    | .opaque value => Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .foundOpaque owner index value⟩ := by
  cases entry with
  | occurrence item => exact Step.occurrence owner heap index item found
  | «opaque» value => exact Step.opaque owner heap index value found

/-- The same indexed cell cannot dispatch as both an occurrence and an opaque
entry. -/
theorem occurrence_opaque_exclusive
    (heap : List (Entry Identity Value Other)) (index : Nat)
    (item : Occurrence Identity Value) (value : Other) :
    heap[index]? = some (.occurrence item) →
      heap[index]? = some (.opaque value) → False := by
  intro occurrenceFound opaqueFound
  rw [occurrenceFound] at opaqueFound
  cases opaqueFound

/-! ## Proof-channel specialization -/

def Fault.toOccurrence : Fault Owner → OccurrenceHeapProtocol.Fault Owner
  | .wrongOwner requested resident => .wrongOwner requested resident
  | .missingIndex owner index => .missingIndex owner index

def Control.toOccurrence : Control Owner Identity Value Other →
    OccurrenceHeapProtocol.Control Owner Identity Value
  | .lookup owner index => .lookup owner index
  | .foundOccurrence owner index item => .holding owner index item
  | .foundOpaque owner index _ => .fault (.wrongEntryKind owner index)
  | .fault failure => .fault failure.toOccurrence

def State.toOccurrence (state : State Owner Identity Value Other) :
    OccurrenceHeapProtocol.State Owner Identity Value Other :=
  { owner := state.owner
    heap := state.heap
    control := state.control.toOccurrence }

theorem step_toOccurrence {source target : State Owner Identity Value Other}
    (step : Step source target) :
    OccurrenceHeapProtocol.Step source.toOccurrence target.toOccurrence := by
  cases step with
  | occurrence owner heap index item found =>
      exact OccurrenceHeapProtocol.Step.lookupHit owner heap index item found
  | «opaque» owner heap index value found =>
      exact OccurrenceHeapProtocol.Step.lookupOpaque owner heap index value found
  | missing owner heap index absent =>
      exact OccurrenceHeapProtocol.Step.lookupMissing owner heap index absent
  | wrongOwner resident requested heap index different =>
      exact OccurrenceHeapProtocol.Step.lookupWrongOwner resident requested
        heap index different

/-- Forgetting the opaque branch into an explicit proof-channel fault is a
forward GSLT transformation. -/
def proofChannelTranslation :
    OperationalTranslation (gslt Owner Identity Value Other)
      (OccurrenceHeapProtocol.gslt Owner Identity Value Other) where
  mapTerm := State.toOccurrence
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := step_toOccurrence

/-- Positive and negative controls over one mixed heap. -/
theorem mixed_heap_dispatch_canary :
    let first : Occurrence Nat Nat := ⟨7, 11⟩
    let heap : List (Entry Nat Nat String) :=
      [.opaque "assertion", .occurrence first]
    Step ⟨(), heap, .lookup () 0⟩
        ⟨(), heap, .foundOpaque () 0 "assertion"⟩ ∧
      Step ⟨(), heap, .lookup () 1⟩
        ⟨(), heap, .foundOccurrence () 1 first⟩ ∧
      ¬ ∃ item, Step ⟨(), heap, .lookup () 0⟩
        ⟨(), heap, .foundOccurrence () 0 item⟩ := by
  dsimp
  constructor
  · exact Step.opaque () _ 0 "assertion" rfl
  constructor
  · exact Step.occurrence () _ 1 ⟨7, 11⟩ rfl
  · rintro ⟨item, step⟩
    cases step
    simp_all

#print axioms present_entry_dispatches
#print axioms occurrence_opaque_exclusive
#print axioms step_toOccurrence
#print axioms proofChannelTranslation
#print axioms mixed_heap_dispatch_canary

end Mettapedia.GSLT.HeterogeneousHeapDispatch
