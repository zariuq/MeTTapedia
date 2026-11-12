import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntrySource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemo

/-!
# Native entry images follow checked source-scope decisions

The represented slot/payload image is retained only when the existing source
session keeps its authority. A new authority clears both arrays. Source packet
equality is derived from the same edit/import/layer validator, so retaining the
image does not assume equal inference answers after a mutation.

The implementation still has to map its compressed native scope token and
allocation/lifetime operations to this decision and the existing heap model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeEntryCodec NativeTypeEntrySource TypeReadScopeMemo
open NativeTypeSourcePorts (Source)
open RetainedTypePayloads (ExternalView)

structure Image where
  entries : Table
  states : States

def refreshImage {size : Nat} (before : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image) : Image :=
  if (refresh before actions).authority = before.authority then image else ⟨[], []⟩

theorem same_authority_snapshot {size : Nat} (configuration : Source) (before : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size))
    (same : (refresh before actions).authority = before.authority) :
    snapshot configuration (refresh before actions).scope = snapshot configuration before.scope := by
  by_cases accepted : (NativeTypingScopeOverlays.check
      (NativeTypingScopeOverlays.execute before.scope actions) (NativeTypingScopeOverlays.token before.scope) &&
      inheritedBound before.scope) = true
  · have flags := Bool.and_eq_true_iff.mp accepted
    simp only [refresh, accepted, if_true]
    exact snapshot_validated configuration before.scope actions ((inheritedBound_iff _).mp flags.2) flags.1
  · dsimp only [refresh] at same
    split at same
    · rename_i tested
      exact False.elim (accepted tested)
    · change before.authority + 1 = before.authority at same
      omega

theorem refreshed_sound {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (heap : ShapeTyping.Heap UInt64) (before : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image)
    (valid : Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      (snapshot configuration before.scope) external) image.entries image.states) :
    Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      (snapshot configuration (refresh before actions).scope) external)
      (refreshImage before actions image).entries (refreshImage before actions image).states := by
  by_cases same : (refresh before actions).authority = before.authority
  · simp only [refreshImage, same, if_true]
    rw [same_authority_snapshot configuration before actions same]
    exact valid
  · simp only [refreshImage, same, if_false]
    exact empty_sound heap _ []

theorem refreshed_state_ids {size : Nat} (before : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image)
    (valid : StateIdsPresent image.entries image.states) :
    StateIdsPresent (refreshImage before actions image).entries (refreshImage before actions image).states := by
  by_cases same : (refresh before actions).authority = before.authority
  · simpa only [refreshImage, same, if_true] using valid
  · simp only [refreshImage, same, if_false]
    intro entry impossible
    cases impossible

theorem refreshed_payloads_valid {size : Nat} (before : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size)) (image : Image)
    (valid : RetainedTypePayloads.Valid image.states) :
    RetainedTypePayloads.Valid (refreshImage before actions image).states := by
  by_cases same : (refresh before actions).authority = before.authority
  · simpa only [refreshImage, same, if_true] using valid
  · simp only [refreshImage, same, if_false]
    intro types impossible
    cases impossible

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryScope
