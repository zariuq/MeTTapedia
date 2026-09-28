import Mettapedia.Machines.SharedContinuation
import Mettapedia.GSLT.Dynamics.ContextIndexedSwitching
import Mettapedia.GSLT.Dynamics.CertifiedRepresentationPlanning

/-!
# Incremental continuation transfer along realization routes

The reference frontier and the shared continuation arena implement the same
ordered operational fragment. Both directions of transfer retain all pending
returns, branch contexts, alternatives and already emitted answer occurrences.
Arbitrary repeated transfers therefore compose through the existing Region/Hole
realization machinery, including work/proof-plan selection.

The context boundary acts only on residual branches: it cannot rewrite an
already published answer. It can represent refinement or rollback of a binding
image when those operations are supplied by the source semantics. Cancellation
discards residual work while retaining the emitted prefix.

This is a runtime realization theorem. A structural GSLT-IL `via` morphism alone
does not supply this runtime evidence, a capture map or an ownership lease.
Source-language hosting and native frame lifetime remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GraphTheory.Representation
open RegionHolePlan RepresentationSwitching
open OrderedOccurrenceBodyAlgebra
open ContextIndexedSwitching (regionCategory repeats repeats_add)

variable {Context Control Call Frame Answer : Type}

inductive Boundary (Context : Type) where
  | context (change : Context → Context)
  | cancel

def referenceBoundary : Boundary Context → State Context Control Frame Answer →
    State Context Control Frame Answer
  | .context change, state =>
      { state with frontier := state.frontier.map fun task =>
        { task with context := change task.context } }
  | .cancel, state => { state with frontier := [] }

def sharedBoundary : Boundary Context → CheckedState Context Control Frame Answer →
    CheckedState Context Control Frame Answer
  | .context change, state =>
      ⟨{ state.1 with frontier := state.1.frontier.map fun task =>
          { task with context := change task.context } }, by
        refine ⟨state.2.1, ?_⟩
        intro task member
        change task ∈ state.1.frontier.map (fun task =>
          { task with context := change task.context }) at member
        obtain ⟨original, originalMember, equalTask⟩ := List.mem_map.mp member
        rw [← equalTask]
        exact state.2.2 original originalMember⟩
  | .cancel, state => ⟨{ state.1 with frontier := [] }, state.2.1, by simp⟩

theorem decode_boundary (boundary : Boundary Context)
    (state : CheckedState Context Control Frame Answer) :
    (sharedBoundary boundary state).1.decode = referenceBoundary boundary state.1.decode := by
  cases boundary <;>
    simp [sharedBoundary, referenceBoundary, ArenaState.decode, RootTask.decode, List.map_map]

theorem decode_steps (program : Program Context Control Call Frame Answer)
    (count : Nat) (state : CheckedState Context Control Frame Answer) :
    (repeats (checkedStep program) count state).1.decode =
      repeats (step program) count state.1.decode := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [repeats, ih, decode_checkedStep]

/-- This equality retains a nonempty emitted prefix and a nonempty residual
frontier equally; no whole-query restart occurs at the boundary. -/
theorem split_execution_exact (program : Program Context Control Call Frame Answer)
    (before after : Nat) (state : State Context Control Frame Answer) :
    repeats (step program) after
      (repeats (checkedStep program) before (encode state)).1.decode =
      repeats (step program) (before + after) state := by
  rw [decode_steps, decode_encode, repeats_add]

def referenceRealization (program : Program Context Control Call Frame Answer) :
    RegionHolePlan.Realization regionCategory (fun _ _ : Unit => Boundary Context) functionCategory where
  objectMap _ := State Context Control Frame Answer
  mapRegion count := repeats (step program) count
  mapHole := referenceBoundary
  map_identity _ := rfl
  map_compose first second := funext (repeats_add (step program) first second)

def sharedRealization (program : Program Context Control Call Frame Answer) :
    RegionHolePlan.Realization regionCategory (fun _ _ : Unit => Boundary Context) functionCategory where
  objectMap _ := CheckedState Context Control Frame Answer
  mapRegion count := repeats (checkedStep program) count
  mapHole := sharedBoundary
  map_identity _ := rfl
  map_compose first second := funext (repeats_add (checkedStep program) first second)

def sharedToReference (program : Program Context Control Call Frame Answer) :
    RealizationTransformation (sharedRealization program) (referenceRealization program) where
  component _ := ArenaState.decode ∘ Subtype.val
  region_naturality count := funext (decode_steps program count)
  hole_naturality boundary := funext (decode_boundary boundary)

inductive Engine where
  | reference
  | shared

def family (program : Program Context Control Call Frame Answer) :
    Family regionCategory (fun _ _ : Unit => Boundary Context) functionCategory Engine where
  reference := referenceRealization program
  engine
    | .reference => referenceRealization program
    | .shared => sharedRealization program
  decode
    | .reference => RealizationTransformation.identity (referenceRealization program)
    | .shared => sharedToReference program

/-- Reification is charged by the chosen account; it is not asserted to be
free or to preserve raw addresses. Native implementations can use cheaper
certified direct transfers without changing the logical frontier. -/
def enter (program : Program Context Control Call Frame Answer) (charge : Resources) :
    Transfer (family program) .reference .shared () where
  convert := encode
  commutes := funext decode_encode
  resources := charge

def leave (program : Program Context Control Call Frame Answer) (charge : Resources) :
    Transfer (family program) .shared .reference () where
  convert := ArenaState.decode ∘ Subtype.val
  commutes := rfl
  resources := charge

theorem mixed_execution_exact (program : Program Context Control Call Frame Answer)
    (execution : Execution (family program) .reference () .reference ())
    (state : State Context Control Frame Answer) :
    execution.denote state =
      Plan.denote (referenceRealization program) execution.erase state := by
  exact congrFun (Execution.denote_decode execution) state

/-- Work-plan selection consumes the same certified runtime family. Selection
may depend on finite program support, but does not become binding authority. -/
def plannedRoute (program : Program Context Control Call Frame Answer)
    (plan : Plan Unit (fun _ _ => Nat) (fun _ _ => Boundary Context) () ())
    (execution : Execution (family program) .reference () .shared ())
    (exactSource : execution.erase = plan) :
    CertifiedRepresentationPlanning.CertifiedRoute (family program) .reference plan where
  finish := .shared
  execution := execution
  source_exact := exactSource

end Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching
