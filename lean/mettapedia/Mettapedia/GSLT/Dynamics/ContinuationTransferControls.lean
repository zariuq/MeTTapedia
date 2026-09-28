import Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching

/-!
# Continuation transfer controls

Two nested returns surround an ordered nondeterministic call. Equal answer
occurrences remain distinct, and branches use different context values while
sharing immutable return nodes. Transfers occur after publication and while
returns remain pending. The negative controls deliberately discard a return,
restart an exhausted prefix, or conflate branch images.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.GSLT.Dynamics.ContinuationTransferControls

open Mettapedia.Machines.SharedContinuation
open ContextIndexedSwitching (repeats)
open ContinuationRegionSwitching
open RegionHolePlan RepresentationSwitching

inductive Control where
  | start
  | helper
  | value (n : Nat)
  deriving DecidableEq, Repr

inductive Call where
  | pick
  | increment
  deriving DecidableEq, Repr

inductive Frame where
  | outer
  | afterPick
  | afterHelper
  deriving DecidableEq, Repr

/-- The context is an abstract branch-local slot value. Resume reads its
current image, not a value cached inside an immutable return frame. -/
def program : Program Nat Control Call Frame Nat where
  inspect
    | .start => .call .pick .afterPick
    | .helper => .call .increment .afterHelper
    | .value n => .ret n
  branches context
    | .pick => [(context, .value 2), (context, .value 2), (context + 10, .value 2)]
    | .increment => [(context, .value 3), (context, .value 4)]
  resume context frame value :=
    match frame with
    | .outer => (context, .value (100 * context + value))
    | .afterPick => (context, .helper)
    | .afterHelper => (context, .value (context + value))

def initial : State Nat Control Frame Nat := ⟨[⟨10, .start, [.outer]⟩], []⟩

def expected : List (Nat × Nat) :=
  [(10, 1013), (10, 1014), (10, 1013), (10, 1014), (20, 2023), (20, 2024)]

theorem reference_nested_returns :
    (repeats (step program) 100 initial).emitted = expected := by decide

theorem shared_nested_returns :
    (repeats (checkedStep program) 100 (encode initial)).1.emitted = expected := by
  have exactState := decode_steps program 100 (encode initial)
  have outputs := congrArg State.emitted exactState
  simpa only [ArenaState.decode, decode_encode] using outputs.trans reference_nested_returns

def suspended : CheckedState Nat Control Frame Nat :=
  repeats (checkedStep program) 6 (encode initial)

theorem suspended_after_first_answer : suspended.1.emitted = [(10, 1013)] := by decide

theorem suspended_has_returns :
    (suspended.1.decode.frontier.map Task.returns).head? = some [.afterHelper, .outer] := by
  decide

theorem handoff_after_publication :
    (repeats (step program) 94 suspended.1.decode).emitted = expected := by
  have exactState := split_execution_exact program 6 94 initial
  exact (congrArg State.emitted exactState).trans reference_nested_returns

/-- Three alternatives share one newly allocated return node, above one
previously imported outer frame. No callee answer is published at this point. -/
theorem shared_call_shape :
    let state := (checkedStep program (encode initial)).1
    state.arena.length = 2 ∧ state.frontier.map RootTask.root = [2, 2, 2] ∧
      state.emitted = [] := by decide

/-- A declared context change affects future returns, including already
entered calls, but leaves the published prefix unchanged. -/
theorem resumed_reads_current_context :
    let changed := sharedBoundary (.context (· + 1)) suspended
    (repeats (checkedStep program) 100 changed).1.emitted =
      [(10, 1013), (11, 1115), (11, 1114), (11, 1115), (21, 2124), (21, 2125)] := by
  decide

def mixed : Execution (family program) .reference () .reference () :=
  .region 2 <|
  .switch (enter program ⟨3, 2, 2, 2, 2⟩) <|
  .region 4 <|
  .switch (leave program ⟨2, 2, 1, 1, 1⟩) <|
  .region 1 <|
  .switch (enter program ⟨3, 2, 2, 2, 2⟩) <|
  .region 93 <|
  .switch (leave program ⟨2, 2, 1, 1, 1⟩) <|
  .done Engine.reference ()

theorem mixed_keeps_full_residual :
    mixed.denote initial = repeats (step program) 100 initial := by
  rw [mixed_execution_exact]
  rfl

theorem mixed_keeps_order_and_duplicates : (mixed.denote initial).emitted = expected := by
  rw [mixed_keeps_full_residual]
  exact reference_nested_returns

theorem cancellation_keeps_published_prefix :
    let stopped := sharedBoundary .cancel suspended
    (repeats (checkedStep program) 20 stopped).1.emitted = [(10, 1013)] ∧
      stopped.1.frontier = [] := by decide

/-- Completed work with no exported roots releases all return nodes. -/
theorem completed_arena_can_retire :
    let state := (repeats (checkedStep program) 100 (encode initial)).1
    (retire? state.arena.length [] state).map (fun next =>
      (next.arena.length, next.frontier.length, next.emitted)) =
        some (0, 0, expected) := by decide

theorem pending_return_prevents_retirement :
    retire? suspended.1.arena.length [] suspended.1 = none := by rfl

/-- Cancellation empties the frontier, but an exported closure may still
own an older root. Declaring it prevents reuse of that address. -/
theorem exported_root_prevents_retirement :
    let stopped := (sharedBoundary .cancel suspended).1
    retire? stopped.arena.length [1] stopped = none := by rfl

theorem cancelled_unowned_arena_can_retire :
    let stopped := (sharedBoundary .cancel suspended).1
    (retire? stopped.arena.length [] stopped).map (fun next =>
      (next.arena.length, next.emitted)) = some (0, [(10, 1013)]) := by decide

theorem dropping_pending_returns_is_wrong :
    let wrong := { suspended.1.decode with
      frontier := suspended.1.decode.frontier.map (fun task => { task with returns := [] }) }
    (repeats (step program) 94 wrong).emitted ≠ expected := by decide

theorem restarting_replays_answers :
    suspended.1.emitted ++ (repeats (step program) 100 initial).emitted ≠ expected := by
  decide

theorem sharing_context_values_is_wrong :
    let wrong := referenceBoundary (.context (fun _ => 10)) suspended.1.decode
    (repeats (step program) 100 wrong).emitted ≠ expected := by decide

theorem invalid_root_is_not_exhaustion :
    arenaStep program ⟨[], [⟨10, .value 7, 1⟩], []⟩ = none ∧
      arenaStep program ⟨[], [], []⟩ = some ⟨[], [], []⟩ := by constructor <;> rfl

/-- Forward trace inclusion alone would admit an extra answer occurrence. -/
theorem prefix_inclusion_does_not_license_replay :
    expected <+: expected ++ [(10, 1013)] ∧ expected ≠ expected ++ [(10, 1013)] := by
  constructor
  · exact ⟨_, rfl⟩
  · decide

namespace ScopedReturn

open ContextIndexedSwitching (ActivationKey Store)

/-- The callee reuses the numeric handle but has a different generation. -/
def caller : ActivationKey := ⟨7, 1⟩
def callee : ActivationKey := ⟨7, 2⟩

structure Context where
  store : Store Nat Nat
  active : ActivationKey

inductive Control where
  | invoke
  | answer (value : Nat)

structure Frame where
  owner : ActivationKey
  slot : Nat

/-- The return site retains its lexical coordinate, while the current branch
image remains authoritative for the value at that coordinate. -/
def program : Program Context Control Unit Frame Nat where
  inspect
    | .invoke => .call () ⟨caller, 0⟩
    | .answer value => .ret value
  branches context _ := [({context with active := callee}, .answer 3)]
  resume context frame _ := (context, .answer (context.store frame.owner frame.slot))

def initial (store : Store Nat Nat) : State Context Control Frame Nat :=
  ⟨[⟨⟨store, caller⟩, .invoke, []⟩], []⟩

/-- This holds for every store, not just the distinguishing example below. -/
theorem caller_coordinate_survives_transfer (store : Store Nat Nat) :
    (repeats (step program) 2
      (repeats (checkedStep program) 1 (encode (initial store))).1.decode).emitted.map Prod.snd =
        [store caller 0] := by
  rw [split_execution_exact]
  rfl

def distinctStore : Store Nat Nat := fun key _ => if key = caller then 41 else 99

theorem callee_scope_cannot_capture_return :
    (repeats (step program) 3 (initial distinctStore)).emitted.map Prod.snd = [41] ∧
      (repeats (step { program with
        resume := fun context frame _ =>
          (context, .answer (context.store context.active frame.slot)) })
        3 (initial distinctStore)).emitted.map Prod.snd = [99] := by
  constructor <;> decide

end ScopedReturn

end Mettapedia.GSLT.Dynamics.ContinuationTransferControls
