import Mettapedia.GSLT.LanguageDef.NativeOpsSourceFunctions
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetFunctions

/-!
# Function parameter frames across native lowering

The independently defined source and target binders agree on arity, local
addresses and stored argument values. The relation includes the entire state,
so argument aliases, ownership, external effects and an existing fault survive
entry unchanged. Fresh invocation storage is equivalent on both sides.

These laws concern entry and scope teardown. They do not assume or establish
correspondence of the intervening function body.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

theorem function_parameter_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (parameters : List Parameter) (arguments : List SourceValue)
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) :
    Option.Rel (fun left right => FrameRelated left.1 right.1 ∧
      StateRelated worldRelated left.2 right.2)
      (sourceBindParameters parameters arguments sourceFrame source)
      (targetBindParameters parameters (encodeValues arguments) targetFrame target) := by
  induction parameters generalizing arguments sourceFrame targetFrame source target with
  | nil =>
      cases arguments with
      | nil => exact .some ⟨frames, states⟩
      | cons _ _ => exact .none
  | cons parameter rest ih =>
      cases arguments with
      | nil => exact .none
      | cons value values =>
          simp only [sourceBindParameters, targetBindParameters, encodeValues]
          obtain ⟨nextFrames, nextStates⟩ := declaration_correspondence frames states
            parameter.name parameter.type value
          exact ih values nextFrames nextStates

theorem function_parameters_preserved {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {parameters : List Parameter} {arguments : List SourceValue}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    {boundFrame : SourceFrame} {boundState : SourceState SourceWorld}
    (bound : sourceBindParameters parameters arguments sourceFrame source =
      some (boundFrame, boundState)) :
    ∃ targetBoundFrame targetBoundState,
      targetBindParameters parameters (encodeValues arguments) targetFrame target =
        some (targetBoundFrame, targetBoundState) ∧
      FrameRelated boundFrame targetBoundFrame ∧
      StateRelated worldRelated boundState targetBoundState := by
  have related := function_parameter_correspondence parameters arguments frames states
  rw [bound] at related
  cases result : targetBindParameters parameters (encodeValues arguments) targetFrame target with
  | none => rw [result] at related; cases related
  | some pair =>
      rw [result] at related
      cases related with
      | some related => exact ⟨pair.1, pair.2, rfl, related⟩

theorem function_parameters_reflected {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {parameters : List Parameter} {arguments : List SourceValue}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    {boundFrame : TargetFrame} {boundState : TargetState TargetWorld}
    (bound : targetBindParameters parameters (encodeValues arguments) targetFrame target =
      some (boundFrame, boundState)) :
    ∃ sourceBoundFrame sourceBoundState,
      sourceBindParameters parameters arguments sourceFrame source =
        some (sourceBoundFrame, sourceBoundState) ∧
      FrameRelated sourceBoundFrame boundFrame ∧
      StateRelated worldRelated sourceBoundState boundState := by
  have related := function_parameter_correspondence parameters arguments frames states
  rw [bound] at related
  cases result : sourceBindParameters parameters arguments sourceFrame source with
  | none => rw [result] at related; cases related
  | some pair =>
      rw [result] at related
      cases related with
      | some related => exact ⟨pair.1, pair.2, rfl, related⟩

theorem function_parameter_refusal_iff {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (parameters : List Parameter) (arguments : List SourceValue)
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) :
    sourceBindParameters parameters arguments sourceFrame source = none ↔
      targetBindParameters parameters (encodeValues arguments) targetFrame target = none := by
  have related := function_parameter_correspondence parameters arguments frames states
  cases left : sourceBindParameters parameters arguments sourceFrame source <;>
    cases right : targetBindParameters parameters (encodeValues arguments) targetFrame target <;>
    rw [left, right] at related <;> cases related <;> simp

theorem source_parameter_arity_exact {World : Type}
    (parameters : List Parameter) (arguments : List SourceValue)
    (frame : SourceFrame) (state : SourceState World) :
    (sourceBindParameters parameters arguments frame state).isSome = true ↔
      parameters.length = arguments.length := by
  induction parameters generalizing arguments frame state with
  | nil => cases arguments <;> simp [sourceBindParameters]
  | cons parameter rest ih =>
      cases arguments with
      | nil => simp [sourceBindParameters]
      | cons value values =>
          simpa only [sourceBindParameters, List.length_cons, Nat.add_right_cancel_iff]
            using ih values (sourceDeclareLocal frame state parameter.name parameter.type value).1
              (sourceDeclareLocal frame state parameter.name parameter.type value).2

theorem target_parameter_arity_exact {World : Type}
    (parameters : List Parameter) (arguments : List TargetValue)
    (frame : TargetFrame) (state : TargetState World) :
    (targetBindParameters parameters arguments frame state).isSome = true ↔
      parameters.length = arguments.length := by
  induction parameters generalizing arguments frame state with
  | nil => cases arguments <;> simp [targetBindParameters]
  | cons parameter rest ih =>
      cases arguments with
      | nil => simp [targetBindParameters]
      | cons value values =>
          simpa only [targetBindParameters, List.length_cons, Nat.add_right_cancel_iff]
            using ih values (targetDeclareLocal frame state parameter.name parameter.type value).1
              (targetDeclareLocal frame state parameter.name parameter.type value).2

theorem fresh_function_frame_correspondence {source : SourceMemory} {target : TargetMemory}
    (related : MemoryRelated source target) (storage : Nat) :
    sourceFreshFrame source storage ↔ targetFreshFrame target storage := by
  constructor
  · rintro ⟨cells, owned⟩
    exact ⟨by rw [related.2 storage, owned]; rfl,
      fun position => by rw [related.1 storage position, cells position]; rfl⟩
  · rintro ⟨owned, cells⟩
    constructor
    · intro position
      have same := related.1 storage position
      rw [cells position] at same
      cases found : source.cells storage position with
      | none => rfl
      | some value => simp [found] at same
    · have same := related.2 storage
      rw [owned] at same
      cases found : source.owned storage with
      | none => rfl
      | some value => simp [found] at same

theorem empty_function_frames_related (storage : Nat) :
    FrameRelated ⟨storage, 0, []⟩ (targetEmptyFrame storage) := ⟨rfl, rfl, rfl⟩

theorem source_parameter_frame_extent {World : Type}
    {parameters : List Parameter} {arguments : List SourceValue}
    {frame boundFrame : SourceFrame} {state boundState : SourceState World}
    (bound : sourceBindParameters parameters arguments frame state =
      some (boundFrame, boundState)) :
    boundFrame.storage = frame.storage ∧
      boundFrame.nextLocal = frame.nextLocal + parameters.length := by
  induction parameters generalizing arguments frame state with
  | nil =>
      cases arguments with
      | nil => cases bound; exact ⟨rfl, rfl⟩
      | cons _ _ => cases bound
  | cons parameter rest ih =>
      cases arguments with
      | nil => cases bound
      | cons value values =>
          obtain ⟨storage, extent⟩ := ih bound
          exact ⟨storage, by simpa [sourceDeclareLocal, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using extent⟩

theorem target_parameter_temporaries_unchanged {World : Type}
    {parameters : List Parameter} {arguments : List TargetValue}
    {frame boundFrame : TargetFrame} {state boundState : TargetState World}
    (bound : targetBindParameters parameters arguments frame state =
      some (boundFrame, boundState)) :
    boundFrame.temporaryNames = frame.temporaryNames ∧
      boundFrame.temporaries = frame.temporaries := by
  induction parameters generalizing arguments frame state with
  | nil =>
      cases arguments with
      | nil => cases bound; exact ⟨rfl, rfl⟩
      | cons _ _ => cases bound
  | cons parameter rest ih =>
      cases arguments with
      | nil => cases bound
      | cons value values =>
          exact ih (frame := (targetDeclareLocal frame state parameter.name parameter.type value).1)
            (state := (targetDeclareLocal frame state parameter.name parameter.type value).2) bound

theorem singleton_parameter_readback {World : Type} (state : SourceState World)
    (storage : Nat) (parameter : Parameter) (value : SourceValue) :
    let bound := sourceDeclareLocal ⟨storage, 0, []⟩ state parameter.name parameter.type value
    sourceLocalValue bound.1 bound.2 parameter.name = some value := by
  simp [sourceDeclareLocal, sourceLocalValue, sourceLocalAddress, sourceRead,
    sourceStoreCell, sourceReadPath]

theorem singleton_parameter_teardown {World : Type} (state : SourceState World)
    (storage : Nat) (parameter : Parameter) (value : SourceValue)
    (fresh : sourceFreshFrame state.memory storage) :
    let marker : SourceFrame := ⟨storage, 0, []⟩
    let bound := sourceDeclareLocal marker state parameter.name parameter.type value
    (sourceLeaveScope marker bound.1 bound.2).2 = state := by
  have cells : (sourceDropLocals (sourceStoreCell state.memory storage 0 value)
      storage 0 1).cells = state.memory.cells := by
    funext candidate position
    by_cases same : candidate = storage
    · subst candidate
      by_cases zero : position = 0
      · subst position
        simp [sourceDropLocals, fresh.1]
      · simp [sourceDropLocals, sourceStoreCell, zero]
    · simp [sourceDropLocals, sourceStoreCell, same]
  have memory : sourceDropLocals (sourceStoreCell state.memory storage 0 value)
      storage 0 1 = state.memory := by
    exact congrArg (fun cells => SourceMemory.mk cells state.memory.owned) cells
  change { state with memory := (sourceDropLocals
    (sourceStoreCell state.memory storage 0 value) storage 0 1) } = state
  rw [memory]

end Mettapedia.GSLT.LanguageDef.NativeOps
