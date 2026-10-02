import Mettapedia.GSLT.LanguageDef.NativeOpsSourceEval
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetValues

/-!
# Invocation occurrence accounting

The natural cursor is proof state, separate from the physical external world.
It records invocation order without limiting execution. Projection preserves
every memory cell, ownership entry, context fault and allocator counter. Raw
allocation/release effects preserve the cursor; a call ledger consumes it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

def sourceWithCursor {World : Type} (state : SourceState World) (cursor : Nat) :
    SourceState (World × Nat) :=
  ⟨state.memory, state.fault, state.allocatorAvailable, state.releaseAvailable,
    (state.external, cursor), state.allocatorStats⟩

def targetWithCursor {World : Type} (state : TargetState World) (cursor : Nat) :
    TargetState (World × Nat) :=
  ⟨state.memory, state.fault, state.allocatorAvailable, state.releaseAvailable,
    (state.external, cursor), state.allocatorStats⟩

def sourceWithoutCursor {World : Type} (state : SourceState (World × Nat)) : SourceState World :=
  ⟨state.memory, state.fault, state.allocatorAvailable, state.releaseAvailable,
    state.external.1, state.allocatorStats⟩

def targetWithoutCursor {World : Type} (state : TargetState (World × Nat)) : TargetState World :=
  ⟨state.memory, state.fault, state.allocatorAvailable, state.releaseAvailable,
    state.external.1, state.allocatorStats⟩

theorem source_cursor_projection {World : Type} (state : SourceState World) (cursor : Nat) :
    sourceWithoutCursor (sourceWithCursor state cursor) = state := by cases state; rfl

theorem target_cursor_projection {World : Type} (state : TargetState World) (cursor : Nat) :
    targetWithoutCursor (targetWithCursor state cursor) = state := by cases state; rfl

theorem source_cursor_reconstruction {World : Type} (state : SourceState (World × Nat)) :
    sourceWithCursor (sourceWithoutCursor state) state.external.2 = state := by
  cases state with
  | mk memory fault allocator release external stats => cases external; rfl

theorem target_cursor_reconstruction {World : Type} (state : TargetState (World × Nat)) :
    targetWithCursor (targetWithoutCursor state) state.external.2 = state := by
  cases state with
  | mk memory fault allocator release external stats => cases external; rfl

def InvocationWorldRelated {SourceWorld TargetWorld : Type}
    (related : SourceWorld → TargetWorld → Prop) (source : SourceWorld × Nat)
    (target : TargetWorld × Nat) : Prop := related source.1 target.1 ∧ target.2 = source.2

theorem invocation_state_correspondence {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated related source target) (cursor : Nat) :
    StateRelated (InvocationWorldRelated related) (sourceWithCursor source cursor)
      (targetWithCursor target cursor) :=
  ⟨states.memory, states.fault, states.allocator, states.release, ⟨states.external, rfl⟩,
    states.allocatorStats⟩

theorem invocation_state_projection {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop}
    {source : SourceState (SourceWorld × Nat)} {target : TargetState (TargetWorld × Nat)}
    (states : StateRelated (InvocationWorldRelated related) source target) :
    StateRelated related (sourceWithoutCursor source) (targetWithoutCursor target) ∧
      target.external.2 = source.external.2 :=
  ⟨⟨states.memory, states.fault, states.allocator, states.release, states.external.1,
      states.allocatorStats⟩, states.external.2⟩

def sourceHeapWithCursor {World : Type} (heap : SourceHeapSemantics World) :
    SourceHeapSemantics (World × Nat) where
  width := heap.width
  allocate element count before raw :=
    heap.allocate element count (sourceWithoutCursor before)
      ⟨raw.value, sourceWithoutCursor raw.state⟩ ∧ raw.state.external.2 = before.external.2
  release element value before raw :=
    heap.release element value (sourceWithoutCursor before)
      ⟨raw.value, sourceWithoutCursor raw.state⟩ ∧ raw.state.external.2 = before.external.2

def targetHeapWithCursor {World : Type} (heap : TargetHeapSemantics World) :
    TargetHeapSemantics (World × Nat) where
  width := heap.width
  allocate element count before raw :=
    raw.state.external.2 = before.external.2 ∧
      heap.allocate element count (targetWithoutCursor before)
        ⟨raw.value, targetWithoutCursor raw.state⟩
  release element value before raw :=
    raw.state.external.2 = before.external.2 ∧
      heap.release element value (targetWithoutCursor before)
        ⟨raw.value, targetWithoutCursor raw.state⟩

theorem source_allocation_preserves_invocation_cursor {World : Type}
    (heap : SourceHeapSemantics World) (element : NativeType) (count : NativeWord64.Word)
    {before : SourceState (World × Nat)} {raw : SourceRawResult (World × Nat)}
    (allocated : (sourceHeapWithCursor heap).allocate element count before raw) :
    raw.state.external.2 = before.external.2 := allocated.2

theorem target_release_preserves_invocation_cursor {World : Type}
    (heap : TargetHeapSemantics World) (element : NativeType) (value : TargetValue)
    {before : TargetState (World × Nat)} {raw : TargetRawResult (World × Nat)}
    (released : (targetHeapWithCursor heap).release element value before raw) :
    raw.state.external.2 = before.external.2 := released.1

theorem source_poison_preserves_invocation_cursor {World : Type}
    (state : SourceState (World × Nat)) (fault : NativeWord64.Fault) :
    (sourcePoison state fault).external.2 = state.external.2 := by
  cases prior : state.fault <;> simp [sourcePoison, prior]

theorem target_poison_preserves_invocation_cursor {World : Type}
    (state : TargetState (World × Nat)) (fault : NativeWord64.Fault) :
    (targetPoison state fault).external.2 = state.external.2 := by
  unfold targetPoison
  split <;> rfl

end Mettapedia.GSLT.LanguageDef.NativeOps
