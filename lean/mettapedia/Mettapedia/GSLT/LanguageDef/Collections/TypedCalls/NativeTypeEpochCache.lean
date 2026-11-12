import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeEpochs

/-!
# Scope-epoch publication composes with native entry reuse

A validated compressed source token retains the existing entry/payload image.
Refusal clears the image without undoing source edits. The resulting hit theorem
composes publication histories, current heap metadata and actual raw-source
inference. The row-shape/immutability gate is the existing source projection
gate, not a blanket ban on mutable unrelated data.

The source publication interface and native field/metadata realization remain
separate: this theorem does not establish C notification or concurrency fidelity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochCache

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeSourcePorts (Source)
open RetainedTypePayloads (ExternalView)
open NativeTypeEntryCodec NativeTypeEntrySource
open NativeTypeEntryScope (Image)

def bindImage {size : Nat} (before : NativeTypingScopeEpochs.State size)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image) : Image :=
  if NativeTypingScopeEpochs.check (NativeTypingScopeEpochs.execute before actions)
      (NativeTypingScopeEpochs.token before) && TypeReadScopeMemo.inheritedBound before.scope then
    image
  else ⟨[], []⟩

theorem bind_sound {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom) (heap : ShapeTyping.Heap UInt64)
    (before : NativeTypingScopeEpochs.State size) (epochsValid : NativeTypingScopeEpochs.Valid before)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image)
    (valid : Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      (TypeReadScopeMemo.snapshot configuration before.scope) external) image.entries image.states) :
    Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      (TypeReadScopeMemo.snapshot configuration (NativeTypingScopeEpochs.execute before actions).scope) external)
      (bindImage before actions image).entries (bindImage before actions image).states := by
  by_cases admitted : (NativeTypingScopeEpochs.check (NativeTypingScopeEpochs.execute before actions)
      (NativeTypingScopeEpochs.token before) && TypeReadScopeMemo.inheritedBound before.scope) = true
  · have flags := Bool.and_eq_true_iff.mp admitted
    simp only [bindImage, admitted, if_true]
    rw [NativeTypingScopeEpochs.validated_snapshot configuration before epochsValid actions
      ((TypeReadScopeMemo.inheritedBound_iff _).mp flags.2) flags.1]
    exact valid
  · simp only [bindImage, admitted]
    exact empty_sound heap _ []

theorem bind_state_ids {size : Nat} (before : NativeTypingScopeEpochs.State size)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image)
    (valid : StateIdsPresent image.entries image.states) :
    StateIdsPresent (bindImage before actions image).entries (bindImage before actions image).states := by
  unfold bindImage
  split
  · exact valid
  · intro entry impossible
    cases impossible

theorem bind_payloads_valid {size : Nat} (before : NativeTypingScopeEpochs.State size)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image)
    (valid : RetainedTypePayloads.Valid image.states) :
    RetainedTypePayloads.Valid (bindImage before actions image).states := by
  unfold bindImage
  split
  · exact valid
  · intro types impossible
    cases impossible

/-- A retained hit after source publication and heap activity answers the
fresh raw-source inquiry. The proof uses the independently established source
projection and heap lookup, not equality of precomputed result literals. -/
theorem raw_source_hit {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom) (heap : ShapeTyping.Heap UInt64)
    (before : NativeTypingScopeEpochs.State size) (epochsValid : NativeTypingScopeEpochs.Valid before)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image)
    (valid : Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      (TypeReadScopeMemo.snapshot configuration before.scope) external) image.entries image.states)
    (operations : List (ShapeTyping.HeapOp UInt64)) (address : UInt64) (direct : Bool)
    (arena : UInt32) (epoch : UInt64) (atom : Atom) (types : List Atom)
    (ready : TypeReadSourceProjection.ready
      (TypeReadScopeMemo.rawSource configuration (NativeTypingScopeEpochs.execute before actions).scope) = true)
    (cell : (heap.run operations).cell address = some (atom, arena.toNat))
    (current : (heap.run operations).epoch arena.toNat = epoch.toNat)
    (hit : read (bindImage before actions image).entries (bindImage before actions image).states
      address (modeCode direct) arena epoch = some types) :
    sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      (TypeReadScopeMemo.rawSource configuration (NativeTypingScopeEpochs.execute before actions).scope)
      external direct atom = some types := by
  have kept := source_hit_after_heap_run
    (TypeReadScopeMemo.snapshot configuration (NativeTypingScopeEpochs.execute before actions).scope)
    external normalize subtypes heap (bindImage before actions image).entries (bindImage before actions image).states
    (bind_sound configuration external normalize subtypes heap before epochsValid actions image valid)
    operations address direct arena epoch atom types cell current hit
  have projected := TypeReadSourceProjection.evaluate_project
    (TypeScopeMatcher.currentOps external normalize subtypes)
    (TypeReadScopeMemo.rawSource configuration (NativeTypingScopeEpochs.execute before actions).scope)
    external ready (TypeReadQueryMemoRefinement.completionDepth (.infer direct atom)) (.infer direct atom) ⟨[], 0⟩
  have same : sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
        (TypeReadScopeMemo.snapshot configuration (NativeTypingScopeEpochs.execute before actions).scope) external direct atom =
      sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
        (TypeReadScopeMemo.rawSource configuration (NativeTypingScopeEpochs.execute before actions).scope) external direct atom :=
    congrArg (fun result : Option NativeTypeCallGraph.Reply × TypeReadSupply.Supply => replyTypes result.1) projected
  exact same.symm.trans kept

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochCache
