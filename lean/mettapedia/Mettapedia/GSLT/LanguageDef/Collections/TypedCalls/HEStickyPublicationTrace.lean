import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStickyPublication
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedWholeProgram

/-!
# The concrete constructor trace uses only faithful publication cases

The inner constructor is unchanged when first published. The nullary
producer and outer consumer both receive an already held result. These are
exactly the two cases where ready publication agrees with mark-if-unchanged
and preserve-existing publication. This local agreement is separate from a
global evaluator-policy or current type-reader correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStickyPublicationTrace

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed
open HEStickyPublication
open HEDemandedConstructorEdge (heldResult producer consumer)

theorem constructor_publication :
    HEStickyPublication.publish HERepeatedFormalSource.call HERepeatedFormalSource.contextualCall = heldResult := by
  simp [HEStickyPublication.publish, HERepeatedFormalSource.call, HERepeatedFormalSource.contextualCall,
    heldResult, Entry.Value.erase, Entry.Value.withStatus, isErrorAtom]

theorem producer_keeps_constructor_mark : HEStickyPublication.publish producer heldResult = heldResult :=
  held_survives producer heldResult (by simp [heldResult, Entry.Value.status])

theorem consumer_keeps_constructor_mark : HEStickyPublication.publish consumer heldResult = heldResult :=
  held_survives consumer heldResult (by simp [heldResult, Entry.Value.status])

theorem ready_publications_agree_on_this_trace (frame : BindingFrame) :
    HEStickyPublication.publish HERepeatedFormalSource.call HERepeatedFormalSource.contextualCall =
      Entry.Value.publish .successes HERepeatedFormalSource.call frame HERepeatedFormalSource.contextualCall ∧
    HEStickyPublication.publish producer heldResult = Entry.Value.publish .successes producer frame heldResult ∧
    HEStickyPublication.publish consumer heldResult = Entry.Value.publish .successes consumer frame heldResult := by
  refine ⟨ready_agrees_on_unchanged _ _ frame ?_ ?_,
    ready_agrees_on_held producer heldResult frame ?_ ?_, ready_agrees_on_held consumer heldResult frame ?_ ?_⟩
  · simp [HERepeatedFormalSource.call, HERepeatedFormalSource.contextualCall, Entry.Value.erase]
  · simp [HERepeatedFormalSource.contextualCall, Entry.Value.erase, isErrorAtom]
  · simp [heldResult, Entry.Value.status]
  · simp [heldResult, Entry.Value.erase, isErrorAtom]
  · simp [heldResult, Entry.Value.status]
  · simp [heldResult, Entry.Value.erase, isErrorAtom]

/-- The agreement is instantiated after the actual complete authored run,
whose constructor, operator recast and consumer binding were independently
derived. It is not a premise that the result was already evaluated. -/
theorem actual_source_trace (minimal : Minimal.Services) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedConstructorInferred.environment minimal) HEDemandedConstructorEdge.space () [] []
        HEDemandedWholeProgram.sourceCall HEDemandedConstructorInferred.rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) ∧
      HEStickyPublication.publish HERepeatedFormalSource.call HERepeatedFormalSource.contextualCall = heldResult ∧
      HEStickyPublication.publish producer heldResult = heldResult ∧
      HEStickyPublication.publish consumer heldResult = heldResult := by
  obtain ⟨after, ran⟩ := HEDemandedWholeProgram.source_call minimal [] []
  exact ⟨after, ran, constructor_publication, producer_keeps_constructor_mark, consumer_keeps_constructor_mark⟩

/-- Publication agreement is now inside a complete source derivation using
the preserving policy, not only a comparison after a ready-profile run. -/
theorem actual_source_trace_preserving (minimal : Minimal.Services) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedConstructorInferred.environment minimal) HEDemandedConstructorEdge.space () [] []
        HEDemandedWholeProgram.sourceCall HEDemandedConstructorInferred.rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.unchangedPreservingReady .preserve) ∧
      HEStickyPublication.publish HERepeatedFormalSource.call HERepeatedFormalSource.contextualCall = heldResult ∧
      HEStickyPublication.publish producer heldResult = heldResult ∧
      HEStickyPublication.publish consumer heldResult = heldResult := by
  obtain ⟨after, ran⟩ := HEDemandedWholeProgram.source_call_preserving minimal [] []
  exact ⟨after, ran, constructor_publication, producer_keeps_constructor_mark, consumer_keeps_constructor_mark⟩

/-- A closed stored result has no changed ancestor to reopen when the
resolver reads it. This does not model public root-variable replacement. -/
theorem closed_resolver_read_keeps_marks (policy : Policy) (frame : Frame) :
    frame.read policy heldResult = heldResult := by
  apply HEFreshSyntaxBinding.ground_substitution
  simp [heldResult, Entry.Value.erase, Spec.Type.Presentation.TypeSubst.typeVars,
    Spec.Type.Presentation.TypeSubst.typeVarsList]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStickyPublicationTrace
