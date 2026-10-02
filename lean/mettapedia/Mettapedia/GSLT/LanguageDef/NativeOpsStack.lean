import Mettapedia.GSLT.LanguageDef.NativeOpsRuntimeState

/-!
# Source-visible locals and target temporary scopes

Local addresses identify cells in a live invocation frame. Calls can therefore
write caller locals through passed references. Scope exit removes its local
cells and newly declared target temporaries; it retains writes to outer cells
and outer temporaries. Frame identities and cell positions are logical storage
names, independent of guest word values or execution bounds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

structure LocalBinding where
  name : String
  type : NativeType
  position : Nat
  deriving DecidableEq, Repr

structure SourceFrame where
  storage : Nat
  nextLocal : Nat
  bindings : List LocalBinding
  deriving DecidableEq, Repr

structure TargetFrame where
  storage : Nat
  nextLocal : Nat
  bindings : List LocalBinding
  temporaryNames : List Nat
  temporaries : Nat → Option TargetValue

structure FrameRelated (source : SourceFrame) (target : TargetFrame) : Prop where
  storage : target.storage = source.storage
  nextLocal : target.nextLocal = source.nextLocal
  bindings : target.bindings = source.bindings

def sourceLocalAddress (frame : SourceFrame) (name : String) : Option Address := do
  let binding ← frame.bindings.find? (fun binding => binding.name == name)
  pure ⟨frame.storage, binding.position, []⟩

def targetLocalAddress (frame : TargetFrame) (name : String) : Option Address := do
  let binding ← frame.bindings.find? (fun binding => binding.name == name)
  some ⟨frame.storage, binding.position, []⟩

theorem local_address_correspondence {source : SourceFrame} {target : TargetFrame}
    (related : FrameRelated source target) (name : String) :
    targetLocalAddress target name = sourceLocalAddress source name := by
  simp only [sourceLocalAddress, targetLocalAddress, related.bindings, related.storage]
  rfl

def sourceLocalValue {World : Type} (frame : SourceFrame) (state : SourceState World)
    (name : String) : Option SourceValue :=
  (sourceLocalAddress frame name).bind (sourceRead state.memory)

def targetLocalValue {World : Type} (frame : TargetFrame) (state : TargetState World)
    (name : String) : Option TargetValue :=
  (targetLocalAddress frame name).bind (targetRead state.memory)

theorem local_value_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (name : String) :
    targetLocalValue targetFrame target name =
      (sourceLocalValue sourceFrame source name).map encodeValue := by
  simp only [sourceLocalValue, targetLocalValue, local_address_correspondence frames]
  cases found : sourceLocalAddress sourceFrame name with
  | none => rfl
  | some address =>
      simpa only [Option.bind_some] using
        memory_read_correspondence source.memory target.memory states.memory address

def sourceDeclareLocal {World : Type} (frame : SourceFrame) (state : SourceState World)
    (name : String) (type : NativeType) (value : SourceValue) :
    SourceFrame × SourceState World :=
  (⟨frame.storage, frame.nextLocal + 1, ⟨name, type, frame.nextLocal⟩ :: frame.bindings⟩,
    { state with memory := sourceStoreCell state.memory frame.storage frame.nextLocal value })

def targetDeclareLocal {World : Type} (frame : TargetFrame) (state : TargetState World)
    (name : String) (type : NativeType) (value : TargetValue) :
    TargetFrame × TargetState World :=
  ({ frame with
      nextLocal := frame.nextLocal + 1
      bindings := ⟨name, type, frame.nextLocal⟩ :: frame.bindings },
    { state with memory := targetStoreCell state.memory frame.storage frame.nextLocal value })

theorem declaration_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (name : String) (type : NativeType) (value : SourceValue) :
    FrameRelated (sourceDeclareLocal sourceFrame source name type value).1
      (targetDeclareLocal targetFrame target name type (encodeValue value)).1 ∧
    StateRelated worldRelated (sourceDeclareLocal sourceFrame source name type value).2
      (targetDeclareLocal targetFrame target name type (encodeValue value)).2 := by
  constructor
  · exact ⟨frames.storage, congrArg (· + 1) frames.nextLocal,
      by simp [sourceDeclareLocal, targetDeclareLocal, frames.nextLocal, frames.bindings]⟩
  · refine ⟨?_, states.fault, states.allocator, states.release, states.external,
      states.allocatorStats⟩
    simp only [sourceDeclareLocal, targetDeclareLocal, frames.storage, frames.nextLocal]
    exact store_cell_correspondence source.memory target.memory states.memory
      sourceFrame.storage sourceFrame.nextLocal value

def sourceDropLocals (memory : SourceMemory) (storage first last : Nat) : SourceMemory :=
  { memory with cells := fun candidate position =>
      if candidate = storage ∧ first ≤ position ∧ position < last then none
      else memory.cells candidate position }

def targetDropLocals (memory : TargetMemory) (storage first last : Nat) : TargetMemory :=
  { memory with cells := fun candidate position =>
      if candidate = storage then
        if first ≤ position then
          if position < last then none else memory.cells candidate position
        else memory.cells candidate position
      else memory.cells candidate position }

/-- An empty lexical allocation interval removes no live cell. -/
theorem targetDropLocals_empty (memory : TargetMemory) (storage boundary : Nat) :
    targetDropLocals memory storage boundary boundary = memory := by
  have same : (fun candidate position =>
      if candidate = storage then
        if boundary ≤ position then
          if position < boundary then none else memory.cells candidate position
        else memory.cells candidate position
      else memory.cells candidate position) = memory.cells := by
    funext candidate position
    by_cases atStorage : candidate = storage
    · by_cases above : boundary ≤ position
      · simp [atStorage, above, Nat.not_lt_of_ge above]
      · simp [atStorage, above]
    · simp [atStorage]
  simp only [targetDropLocals, same]

theorem drop_locals_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (storage first last : Nat) :
    MemoryRelated (sourceDropLocals source storage first last)
      (targetDropLocals target storage first last) := by
  constructor
  · intro candidate position
    by_cases same : candidate = storage <;> by_cases low : first ≤ position <;>
      by_cases high : position < last <;>
      simp [sourceDropLocals, targetDropLocals, same, low, high, related.1]
  · exact related.2

def sourceLeaveScope {World : Type} (marker current : SourceFrame)
    (state : SourceState World) : SourceFrame × SourceState World :=
  ({ current with bindings := marker.bindings },
    { state with
      memory := sourceDropLocals state.memory current.storage
        marker.nextLocal current.nextLocal })

def targetLeaveScope {World : Type} (marker current : TargetFrame)
    (state : TargetState World) : TargetFrame × TargetState World :=
  ({ current with
      bindings := marker.bindings
      temporaryNames := marker.temporaryNames
      temporaries := fun identity => if marker.temporaryNames.contains identity then
        current.temporaries identity else none },
    { state with
      memory := targetDropLocals state.memory current.storage
        marker.nextLocal current.nextLocal })

/-- Closing an unchanged scope keeps its complete state when the temporary
map contains no stale values outside the declared names. -/
theorem targetLeaveScope_self {World : Type} (frame : TargetFrame) (state : TargetState World)
    (completeNames : ∀ identity, frame.temporaryNames.contains identity = false →
      frame.temporaries identity = none) :
    targetLeaveScope frame frame state = (frame, state) := by
  have same : (fun identity => if frame.temporaryNames.contains identity then
      frame.temporaries identity else none) = frame.temporaries := by
    funext identity
    by_cases present : frame.temporaryNames.contains identity = true
    · rw [if_pos present]
    · have absent : frame.temporaryNames.contains identity = false := Bool.eq_false_iff.mpr present
      rw [if_neg present, completeNames identity absent]
  simp only [targetLeaveScope, targetDropLocals_empty, same]

theorem scope_exit_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceMarker sourceFrame : SourceFrame} {targetMarker targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (markers : FrameRelated sourceMarker targetMarker)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) :
    FrameRelated (sourceLeaveScope sourceMarker sourceFrame source).1
      (targetLeaveScope targetMarker targetFrame target).1 ∧
    StateRelated worldRelated (sourceLeaveScope sourceMarker sourceFrame source).2
      (targetLeaveScope targetMarker targetFrame target).2 := by
  constructor
  · exact ⟨frames.storage, frames.nextLocal, markers.bindings⟩
  · refine ⟨?_, states.fault, states.allocator, states.release, states.external,
      states.allocatorStats⟩
    simp only [sourceLeaveScope, targetLeaveScope, markers.nextLocal, frames.nextLocal,
      frames.storage]
    exact drop_locals_correspondence source.memory target.memory states.memory
      sourceFrame.storage sourceMarker.nextLocal sourceFrame.nextLocal

theorem outer_cell_survives_scope_exit (memory : TargetMemory)
    (storage first last position : Nat) (outer : position < first) :
    (targetDropLocals memory storage first last).cells storage position =
      memory.cells storage position := by
  simp [targetDropLocals, Nat.not_le_of_gt outer]

theorem heap_ownership_survives_scope_exit (memory : TargetMemory) (storage first last : Nat) :
    (targetDropLocals memory storage first last).owned = memory.owned := rfl

theorem outer_temporary_update_survives_scope_exit {World : Type}
    (marker current : TargetFrame) (state : TargetState World) (identity : Nat)
    (outer : marker.temporaryNames.contains identity = true) :
    (targetLeaveScope marker current state).1.temporaries identity =
      current.temporaries identity := by
  simp only [targetLeaveScope, outer, if_true]

theorem inner_temporary_does_not_escape_scope {World : Type}
    (marker current : TargetFrame) (state : TargetState World) (identity : Nat)
    (inner : marker.temporaryNames.contains identity = false) :
    (targetLeaveScope marker current state).1.temporaries identity = none := by
  simp only [targetLeaveScope, inner, Bool.false_eq_true, if_false]

end Mettapedia.GSLT.LanguageDef.NativeOps
