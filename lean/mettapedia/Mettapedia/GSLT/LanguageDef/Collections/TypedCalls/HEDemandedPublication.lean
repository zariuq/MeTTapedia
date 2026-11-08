import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStickyPublication

/-!
# Publication modes used by the demanded constructor derivation

The two source profiles differ only in publication. The constructor publishes
an unchanged success; its enclosing calls publish an already held success.
Those local facts earn agreement without equating the policies on changed
active expressions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed

def policy (marking : Entry.MarkPolicy) : Policy := { Policy.ready with marking := marking }

theorem read (marking : Entry.MarkPolicy) (frame : Frame) (value : Entry.Value) :
    frame.read (policy marking) value = frame.read Policy.ready value := rfl

theorem unchanged (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (original : Atom) (value : Entry.Value) (frame : BindingFrame)
    (same : original = value.erase) (clean : isErrorAtom value.erase = false) :
    Entry.Value.publish marking original frame value = value.withStatus .held := by
  rcases supported with rfl | rfl
  · rw [← HEStickyPublication.ready_agrees_on_unchanged original value frame same clean]
    exact HEStickyPublication.unchanged_success original value same clean
  · rw [← HEStickyPublication.preserving_policy_matches]
    exact HEStickyPublication.unchanged_success original value same clean

theorem held (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (original : Atom) (value : Entry.Value) (frame : BindingFrame)
    (ready : value.status = .held) (clean : isErrorAtom value.erase = false) :
    Entry.Value.publish marking original frame value = value := by
  rcases supported with rfl | rfl
  · rw [← HEStickyPublication.ready_agrees_on_held original value frame ready clean]
    exact HEStickyPublication.held_survives original value ready
  · rw [← HEStickyPublication.preserving_policy_matches]
    exact HEStickyPublication.held_survives original value ready

theorem preserving_policy : policy .unchangedPreserving = Policy.unchangedPreservingReady .preserve := rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedPublication
