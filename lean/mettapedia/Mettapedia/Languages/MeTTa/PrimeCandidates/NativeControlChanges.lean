import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeRouteDemand
import Mettapedia.Machines.BranchLocalNeed.SharedContinuationInstance
import Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching
import Mettapedia.GSLT.Core.ConsumerGenerations

/-!
# Native continuation transfer and goal revision

The shared-return representation is instantiated with the authored equation
evaluator, its actual bound cells, branch worlds and resume tokens. A transfer
changes storage without rebuilding the call or forgetting its emitted prefix.

Goal revision rechecks retained witnesses. Detached pure collection consumers
carry generation ownership; revoking an obsolete generation preserves source
production and the newly admitted consumer. It is a cancellation contract,
not a scheduling permutation or a certificate for the new goal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeControlChanges

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines
open Mettapedia.GSLT.Core
open BranchingTemporal
open InferenceControl (WorkOccurrence)
open NativeEquationNeed

abbrev NativeTask := NeedContinuation.NeedTask Origin Local Resume Rule Atom Empty String Empty
abbrev NativeState := NeedContinuation.NeedState Origin Local Resume Rule Atom Empty String Empty
abbrev NativeContext := NeedContinuation.Context Origin Rule Atom Empty String Empty

def initialTask (term : Atom) : NativeTask :=
  let source := NeedExecution.eraseMachine (initial term)
  ⟨⟨source.world, source.work⟩, .force rootCell, []⟩

def initialState (term : Atom) : NativeState := ⟨[initialTask term], []⟩

/-- The shared program starts from the independently constructed native Need
machine; its heap contains the authored root expression, rather than answers. -/
theorem initial_decodes (term : Atom) :
    NeedContinuation.machines (initialState term) =
      [NeedExecution.eraseMachine (initial term)] := rfl

/-- A native Need force may need a separate shared dispatch quantum. Both
representations retain the same physical alternatives and return obligations. -/
theorem native_shared_step (equations : Program) (task : NativeTask)
    (pending : List NativeTask) (published : List (NativeContext × Outcome))
    (settled : task.control.isClaim = false) :
    ∃ emitted fresh,
      (SharedContinuation.step (NeedContinuation.program (specification equations)))^[
          NeedContinuation.cost (specification equations) task] ⟨task :: pending, published⟩ =
        ⟨fresh ++ pending, published ++ emitted⟩ ∧
      (∀ next ∈ fresh, next.control.isClaim = false) ∧
      emitted.map NeedContinuation.answerMachine ++ fresh.map NeedContinuation.taskMachine =
        NeedExecution.step (specification equations) (NeedContinuation.taskMachine task) :=
  NeedContinuation.step_exact (specification equations) task pending published settled

theorem native_shared_quantum_bound (equations : Program) (task : NativeTask) :
    0 < NeedContinuation.cost (specification equations) task ∧
      NeedContinuation.cost (specification equations) task ≤ 2 :=
  NeedContinuation.cost_pos_le_two (specification equations) task

/-- The boundary can be reached with any captured environment, return stack,
branch state and prefix. The residual, rather than the original query, moves. -/
theorem transfer_retains_native_state (equations : Program) (before after : Nat)
    (state : NativeState) :
    Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats
      (SharedContinuation.step (NeedContinuation.program (specification equations))) after
      (Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats
        (SharedContinuation.checkedStep (NeedContinuation.program (specification equations)))
        before (SharedContinuation.encode state)).1.decode =
      Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats
        (SharedContinuation.step (NeedContinuation.program (specification equations)))
        (before + after) state :=
  Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching.split_execution_exact
    (NeedContinuation.program (specification equations)) before after state

abbrev NativeOccurrence := WorkOccurrence NativeMachine

def reprioritize {Memory : Type} (order : Scheduler NativeOccurrence)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) :=
  { state with search := { state.search with frontier := order.reorder state.search.frontier } }

theorem priority_retains_source_account {Memory : Type} (equations : Program) (depth : Nat)
    (order : Scheduler NativeOccurrence)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) :
    FiniteSearchCertificate.account (occurrenceSystem equations) depth
      (reprioritize order state).search =
        FiniteSearchCertificate.account (occurrenceSystem equations) depth state.search :=
  FiniteSearchCertificate.reorder_account (occurrenceSystem equations) depth state.search.events
    (order.reorder state.search.frontier) state.search.frontier
    (order.reorder_complete state.search.frontier)

def witnesses {Memory : Type}
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) : List Atom :=
  state.search.events.filterMap fun event => match event.value.1 with
    | .value value => some value
    | _ => none

def assess {Memory : Type} (goal : List Atom → Bool)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) : Bool :=
  goal (witnesses state)

theorem priority_retains_witnesses {Memory : Type} (order : Scheduler NativeOccurrence)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) :
    witnesses (reprioritize order state) = witnesses state := rfl

abbrev JointWork := ResumableJointSelection.Work Atom
abbrev OwnedWork := ConsumerGenerations.Task NativeOccurrence JointWork

def collectionConsumer (goals : Nat → List Atom → Bool) (generation : Nat) :=
  ResumableJointSelection.system (goals generation)

/-- Revocation projects to the surviving current-generation computation. It
cannot inherit an obsolete success or manufacture source steps. -/
theorem detached_consumers_after_revision (equations : Program)
    (goals : Nat → List Atom → Bool) (old current : Nat) (different : old ≠ current)
    (pending : List OwnedWork) (next : NativeOccurrence ⊕ JointWork) :
    Generated (ConsumerGenerations.system (occurrenceSystem equations)
        (collectionConsumer goals)) (ConsumerGenerations.revoke old pending)
      (ConsumerGenerations.embed current next) ↔
    Generated (ConsumerGenerations.currentSystem (occurrenceSystem equations)
        (collectionConsumer goals current))
      (pending.filterMap (ConsumerGenerations.current? current)) next :=
  ConsumerGenerations.generated_after_revocation (occurrenceSystem equations)
    (collectionConsumer goals) old current different pending next

theorem revision_retains_native_occurrences (old : Nat) (pending : List OwnedWork) :
    (ConsumerGenerations.revoke old pending).filterMap ConsumerGenerations.source? =
      pending.filterMap ConsumerGenerations.source? :=
  ConsumerGenerations.source_preserved old pending

/-- Goal replacement creates one new collection root from the retained native
answers and revokes old pure consumer work. Source producers are retained. -/
def reviseConsumer {Memory : Type} (old current requested : Nat)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory)
    (pending : List OwnedWork) : List OwnedWork :=
  .consumer current (ResumableJointSelection.initial requested (witnesses state)) ::
    ConsumerGenerations.revoke old pending

theorem revised_consumer_retains_source {Memory : Type} (old current requested : Nat)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory)
    (pending : List OwnedWork) :
    (reviseConsumer old current requested state pending).filterMap ConsumerGenerations.source? =
      pending.filterMap ConsumerGenerations.source? := by
  simpa [reviseConsumer, List.filterMap_cons, ConsumerGenerations.source?] using
    revision_retains_native_occurrences old pending

theorem revised_consumer_root {Memory : Type} (old current requested : Nat)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory)
    (pending : List OwnedWork) :
    ConsumerGenerations.Task.consumer current
      (ResumableJointSelection.initial requested (witnesses state)) ∈
        reviseConsumer old current requested state pending := List.mem_cons_self

namespace Controls

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

example : NeedContinuation.cost (specification NativeEquationNeed.Controls.program)
    (initialTask (NativeEquationNeed.Controls.call "twice"
      [NativeEquationNeed.Controls.call "coin"])) = 2 := by decide +kernel

/-- Existing answers satisfy the old occurrence goal but fail the revised
coverage goal. Reordering them supplies no missing final obligation. -/
example :
    let retained := execute NativeRouteDemand.program (NativeRouteDemand.query 4) 7 3000
    assess (DemandExecution.atLeast 7) retained = true ∧
      assess NativeRouteDemand.coversAll retained = false ∧
      witnesses (reprioritize Scheduler.reverseBreadthFirst retained) = witnesses retained :=
  by decide +kernel

def pending : List OwnedWork :=
  [.source (NativeRouteDemand.root 4),
   .consumer 0 (ResumableJointSelection.initial 7 NativeRouteDemand.allRoutes),
   .source (NativeRouteDemand.root 4),
   .consumer 1 (ResumableJointSelection.initial 7 NativeRouteDemand.allRoutes)]

example : (ConsumerGenerations.revoke 0 pending).filterMap ConsumerGenerations.source? =
    [NativeRouteDemand.root 4, NativeRouteDemand.root 4] := rfl

example : (ConsumerGenerations.receipt 0 pending).length = 1 := rfl

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeControlChanges
