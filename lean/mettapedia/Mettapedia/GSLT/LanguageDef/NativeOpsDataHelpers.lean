import Mettapedia.GSLT.LanguageDef.NativeOpsRuntimeState

/-!
# Checked reference and borrowed-array helpers

These independently defined helpers retain the raw C return and the sticky
context post-state. Reference checks establish nullness only. Index and slice
checks establish the emitted extent and bounds guards; they do not inspect
ownership or manufacture a defined read from dangling storage. Logical array
addresses count elements. Their physical realization must respect the declared
element width and the separately proved unsigned byte-offset guards.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Word Fault encode)
open NativeOpsMemoryGuards

structure SourceRawResult (World : Type) where
  value : SourceValue
  state : SourceState World

structure TargetRawResult (World : Type) where
  value : TargetValue
  state : TargetState World

structure RawResultRelated {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop)
    (source : SourceRawResult SourceWorld) (target : TargetRawResult TargetWorld) : Prop where
  value : target.value = encodeValue source.value
  state : StateRelated worldRelated source.state target.state

def sourceRawFinish {World : Type} (state : SourceState World) (default : SourceValue)
    (operation : Except Fault SourceValue) : SourceRawResult World :=
  match operation with
  | .ok value => ⟨value, state⟩
  | .error fault => ⟨default, sourcePoison state fault⟩

def targetRawFinish {World : Type} (state : TargetState World) (default : TargetValue)
    (operation : Except Fault TargetValue) : TargetRawResult World :=
  match operation with
  | .error fault => ⟨default, targetPoison state fault⟩
  | .ok value => ⟨value, state⟩

theorem raw_finish_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (default : SourceValue)
    (operation : Except Fault SourceValue) :
    RawResultRelated worldRelated (sourceRawFinish source default operation)
      (targetRawFinish target (encodeValue default) (operation.map encodeValue)) := by
  cases operation with
  | ok value => exact ⟨rfl, states⟩
  | error fault => exact ⟨rfl, poison_correspondence states fault⟩

def sourceCheckedValue {World : Type} (state : SourceState World)
    (operation : Except Fault SourceValue) : Except Fault SourceValue :=
  sourceChecked state.fault state.allocatorAvailable state.releaseAvailable (fun _ => operation)

def targetCheckedValue {World : Type} (state : TargetState World)
    (operation : Except Fault TargetValue) : Except Fault TargetValue :=
  targetChecked state.fault state.allocatorAvailable state.releaseAvailable (fun _ => operation)

theorem checked_value_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (operation : Except Fault SourceValue) :
    targetCheckedValue target (operation.map encodeValue) =
      (sourceCheckedValue source operation).map encodeValue := by
  simp only [targetCheckedValue, states.fault, states.allocator, states.release,
    targetChecked, ready_correspondence, sourceCheckedValue, sourceChecked]
  cases sourceReady source.fault source.allocatorAvailable source.releaseAvailable <;> rfl

def sourceReferenceCall {World : Type} (state : SourceState World) (address : Option Address) :
    SourceRawResult World :=
  sourceRawFinish state (.bool false)
    (sourceCheckedValue state ((sourceReference address.isSome).map (fun _ => .bool true)))

def targetReferenceCall {World : Type} (state : TargetState World) (address : Option Address) :
    TargetRawResult World :=
  targetRawFinish state (.bool false)
    (targetCheckedValue state ((targetReference address.isSome).map (fun _ => .bool true)))

theorem reference_call_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (address : Option Address) :
    RawResultRelated worldRelated (sourceReferenceCall source address)
      (targetReferenceCall target address) := by
  have operations :
      (targetReference address.isSome).map (fun _ => TargetValue.bool true) =
        ((sourceReference address.isSome).map (fun _ => SourceValue.bool true)).map encodeValue := by
    cases address <;> rfl
  simp only [sourceReferenceCall, targetReferenceCall, operations]
  rw [checked_value_correspondence states]
  exact raw_finish_correspondence states (.bool false) _

def advanceAddress (address : Address) (count : Nat) : Address :=
  { address with element := address.element + count }

def sourceIndexValue (length width index : Word) (address : Option Address) :
    Except Fault SourceValue :=
  (sourceIndex length width index address.isSome).map
    (fun _ => .reference (address.map (advanceAddress · index.val)))

def targetIndexValue (length width index : BitVec 64) (address : Option Address) :
    Except Fault TargetValue :=
  (targetIndex length width index address.isSome).map
    (fun _ => .reference (address.map (advanceAddress · index.toNat)))

theorem index_value_correspondence (length width index : Word) (address : Option Address) :
    targetIndexValue (encode length) (encode width) (encode index) address =
      (sourceIndexValue length width index address).map encodeValue := by
  have guards := index_correspondence length width index address.isSome
  cases guarded : targetIndex (encode length) (encode width) (encode index) address.isSome with
  | error fault =>
      simp only [guarded, observeNat, Except.map] at guards
      simp only [sourceIndexValue, targetIndexValue, guarded, ← guards, Except.map]
  | ok offset =>
      simp only [guarded, observeNat, Except.map] at guards
      simp only [sourceIndexValue, targetIndexValue, guarded, ← guards, Except.map,
        encodeValue, NativeWord64.encode_toNat]

def sourceIndexCall {World : Type} (state : SourceState World)
    (length width index : Word) (address : Option Address) : SourceRawResult World :=
  sourceRawFinish state (.reference none)
    (sourceCheckedValue state (sourceIndexValue length width index address))

def targetIndexCall {World : Type} (state : TargetState World)
    (length width index : BitVec 64) (address : Option Address) : TargetRawResult World :=
  targetRawFinish state (.reference none)
    (targetCheckedValue state (targetIndexValue length width index address))

theorem index_call_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (length width index : Word) (address : Option Address) :
    RawResultRelated worldRelated (sourceIndexCall source length width index address)
      (targetIndexCall target (encode length) (encode width) (encode index) address) := by
  simp only [sourceIndexCall, targetIndexCall, index_value_correspondence]
  rw [checked_value_correspondence states]
  exact raw_finish_correspondence states (.reference none) _

def sourceSliceValue (length width start count : Word) (address : Option Address) :
    Except Fault SourceValue :=
  (sourceSlice length width start count address.isSome).map (fun offset =>
    .reference (if offset.isNone then none else address.map (advanceAddress · start.val)))

def targetSliceValue (length width start count : BitVec 64) (address : Option Address) :
    Except Fault TargetValue :=
  (targetSlice length width start count address.isSome).map (fun offset =>
    .reference (if offset.isNone then none else address.map (advanceAddress · start.toNat)))

theorem slice_value_correspondence (length width start count : Word) (address : Option Address) :
    targetSliceValue (encode length) (encode width) (encode start) (encode count) address =
      (sourceSliceValue length width start count address).map encodeValue := by
  have guards := slice_correspondence length width start count address.isSome
  cases guarded : targetSlice (encode length) (encode width) (encode start) (encode count)
      address.isSome with
  | error fault =>
      simp only [guarded, observeSlice, Except.map] at guards
      simp only [sourceSliceValue, targetSliceValue, guarded, ← guards, Except.map]
  | ok offset =>
      simp only [guarded, observeSlice, Except.map] at guards
      cases offset <;>
        simp only [sourceSliceValue, targetSliceValue, guarded, ← guards, Except.map,
          Option.map_none, Option.map_some, Option.isNone_none, Option.isNone_some,
          Bool.false_eq_true, if_true, if_false, encodeValue, NativeWord64.encode_toNat]

def sourceSliceCall {World : Type} (state : SourceState World)
    (length width start count : Word) (address : Option Address) : SourceRawResult World :=
  sourceRawFinish state (.reference none)
    (sourceCheckedValue state (sourceSliceValue length width start count address))

def targetSliceCall {World : Type} (state : TargetState World)
    (length width start count : BitVec 64) (address : Option Address) : TargetRawResult World :=
  targetRawFinish state (.reference none)
    (targetCheckedValue state (targetSliceValue length width start count address))

theorem slice_call_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (length width start count : Word) (address : Option Address) :
    RawResultRelated worldRelated (sourceSliceCall source length width start count address)
      (targetSliceCall target (encode length) (encode width) (encode start) (encode count) address) := by
  simp only [sourceSliceCall, targetSliceCall, slice_value_correspondence]
  rw [checked_value_correspondence states]
  exact raw_finish_correspondence states (.reference none) _

theorem raw_result_observation_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceRawResult SourceWorld} {target : TargetRawResult TargetWorld}
    (results : RawResultRelated worldRelated source target) :
    OutcomeRelated worldRelated (sourceObserve source.state source.value)
      (targetObserve target.state target.value) := by
  rw [results.value]
  exact observation_correspondence results.state source.value

theorem empty_slice_returns_null_before_null_guard :
    sourceSliceValue (0 : Word) 1 0 0 none = .ok (.reference none) := by cbv

theorem empty_index_refuses_bounds_before_null_guard :
    targetIndexValue 0 1 0 none = .error .indexOutOfBounds := by cbv

theorem reference_null_refuses :
    sourceReference false = .error .nullReference := rfl

end Mettapedia.GSLT.LanguageDef.NativeOps
