import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallCache
import Mettapedia.Machines.OperatorChoice.ObserverContracts

/-!
# Adaptive source-call classification through program changes

The concrete service either queries the actual PeTTa written-call predicate or
installs a new registry. Its cache representation is maintained independently
of the reference service. The local service square lifts to every finite
adaptive client, preserving complete ordered replies and the final registry.
Thus warming and invalidation are not assumed to preserve a whole run.

The observation erases classification cache storage, not source declarations,
effects, body results, typing policy or execution costs. A completed finite
client can be a prefix of a larger interaction; no language termination claim
or C correspondence is made here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.AdaptiveCallCache

open Mettapedia.Languages.MeTTa.PeTTa
open PeTTaCallCache PeTTaActivation
open Mettapedia.Machines
open Mettapedia.Machines.ReadOnlyQuery (Program)
open Mettapedia.Machines.OperatorChoice.ObserverContracts

inductive Request where
  | classify (head : String)
  | install (registry : SpaceSemantics.Program)

structure State where
  registry : SpaceSemantics.Program
  cache : Cache

def Valid (state : State) : Prop := Sound state.registry state.cache

def source (state : State) : Request → Bool × State
  | .classify head =>
      match state.cache head with
      | some value => (value, state)
      | none =>
          let value := callable state.registry head
          (value, { state with cache := Function.update state.cache head (some value) })
  | .install registry =>
      (true, ⟨registry, transfer state.registry registry state.cache⟩)

def reference (registry : SpaceSemantics.Program) : Request → Bool × SpaceSemantics.Program
  | .classify head => (callable registry head, registry)
  | .install replacement => (true, replacement)

theorem source_preserves_valid (state : State) (valid : Valid state) (request : Request) :
    Valid (source state request).2 := by
  cases request with
  | classify head =>
      cases found : state.cache head with
      | some value => simpa [source, found] using valid
      | none =>
          simpa [source, found, Valid, warm] using warm_sound valid head
  | install registry => exact transfer_sound valid

theorem service_square (state : State) (valid : Valid state) (request : Request) :
    reference state.registry request = ((source state request).1, (source state request).2.registry) := by
  cases request with
  | classify head =>
      cases found : state.cache head with
      | none => simp [source, reference, found]
      | some value =>
          have same := valid head value found
          simp [source, reference, found, same]
  | install registry => rfl

/-- Every adaptive sequence, including queries chosen from earlier replies, sees the same result. -/
theorem adaptive_run_erasure {Answer : Type} (program : Program Request Bool Answer)
    (state : State) (valid : Valid state) :
    QueryState.run reference program state.registry =
      eraseObservation State.registry (QueryState.run source program state) :=
  run_erasure_on source reference State.registry Valid source_preserves_valid service_square
    program state valid

/-- All observable replies, their order, and the final registry survive erasure together. -/
theorem adaptive_observations {Answer : Type} (program : Program Request Bool Answer)
    (state : State) (valid : Valid state) :
    (QueryState.run source program state).answer = (QueryState.run reference program state.registry).answer ∧
    (QueryState.run source program state).reads = (QueryState.run reference program state.registry).reads ∧
    (QueryState.run source program state).state.registry =
      (QueryState.run reference program state.registry).state := by
  have same := adaptive_run_erasure program state valid
  exact ⟨(congrArg QueryState.Observation.answer same).symm,
    (congrArg QueryState.Observation.reads same).symm,
    (congrArg QueryState.Observation.state same).symm⟩

namespace Controls

def program : Program Request Bool (Bool × Bool) :=
  .read (.classify "worker") fun first =>
    .read (.install PeTTaCallCache.Controls.changedRegistry) fun _ =>
      .read (.classify "worker") fun second => .pure (first, second)

def initial : State := ⟨PeTTaCallCache.Controls.coldRegistry, empty⟩

theorem new_definition_changes_next_reply :
    (QueryState.run source program initial).answer = (false, true) := by decide +kernel

theorem initial_valid : Valid initial := empty_sound _

end Controls
end Mettapedia.Languages.MeTTa.ContextualTransform.AdaptiveCallCache
