import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionMarkedSlots

/-!
# Actual single-slot call cases of the completion analysis

For a total one-variable equation with a structural range, the native call
analysis evaluates the variable's provenance, applies the structural return
filter, then searches its eight finite-return candidates. This file keeps
that search and derives its result. It does not replace recursive call-family
analysis with a successful-evaluation premise.

The positive source instance is the existing complete demanded producer and
its ready consuming call. Passing this completion gate is separate from
typing, shape, capacity and other prepared-entry gates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionCallCases

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed
open HECompletionEntry

def candidates : List Summary :=
  [.known true false none, .known true false (some .completed),
   .known true false (some .raw), .known true false (some .collected),
   .known true true none, .known true true (some .completed),
   .known true true (some .raw), .known true true (some .collected)]

def included : Summary → Summary → Bool
  | .known scalar variablePresent marking, .known scalarBound variableBound allowed =>
      (!scalar || scalarBound) && (!variablePresent || variableBound) &&
        (match marking with | none => true | some kind => allowed == some kind)
  | _, _ => false

def candidateSearch (result : Summary) : List Summary → Summary
  | [] => .unknown
  | candidate :: rest => if included result candidate then result else candidateSearch result rest

def singleSlot (argument : Summary) : Summary := candidateSearch (structural (template argument)) candidates

theorem singleSlot_exact (argument : Summary) : singleSlot argument = structural (template argument) := by
  cases argument with
  | unknown => rfl
  | known scalar variablePresent marking =>
      cases scalar <;> cases variablePresent <;> cases marking with
      | none => decide +kernel
      | some marking => cases marking <;> decide +kernel

theorem completed_singleSlot_iff (argument : Summary) :
    finish false (singleSlot argument) = some true ↔
      ∃ scalar, argument = .known scalar false (some .completed) := by
  rw [singleSlot_exact]
  cases argument with
  | unknown => simp [template, structural, finish]
  | known scalar variablePresent marking =>
      cases variablePresent <;> cases marking with
      | none => simp [template, structural, finish]
      | some marking => cases marking <;> simp [template, structural, finish]

theorem completed_field_case (parent : Summary) (fieldKnown : part parent = value) :
    finish false (singleSlot (part parent)) = some true := by
  rw [fieldKnown, singleSlot_exact]
  rfl

theorem raw_singleSlot_declines : finish false (singleSlot raw) = none := rfl
theorem collected_singleSlot_declines : finish false (singleSlot collected) = none := rfl

/-- A checked source producer supplies the actual ready operand. Its source
consumer runs from that reached frame, while the local native completion
analysis derives its flag from the operand's real marks. -/
theorem actual_ready_consumer_trace (minimal : Minimal.Services) (live : List Atom) (scope : List String)
    (symbolAllowed : String → Bool) (normalForm : Entry.Value → Bool) :
    ∃ before after : Frame,
      Stateful.AtomRel (HEDemandedCurrentSource.environment minimal) HEDemandedConstructorEdge.space () live scope
        HEDemandedConstructorProgram.producerCall HEDemandedConstructorEdge.demand Frame.empty
        [(HEDemandedConstructorEdge.heldResult, before)] () (policy := Policy.unchangedPreservingReady .preserve) ∧
      Stateful.CallRel (HEDemandedCurrentSource.environment minimal) HEDemandedConstructorEdge.space () live scope
        HEDemandedConsumerFrame.query HEDemandedConstructorEdge.demand before
        [(HEDemandedConstructorEdge.heldResult, after)] () (policy := Policy.unchangedPreservingReady .preserve) ∧
      readyOperand symbolAllowed normalForm HEDemandedConstructorEdge.heldResult = value ∧
      finish false (singleSlot (readyOperand symbolAllowed normalForm HEDemandedConstructorEdge.heldResult)) = some true := by
  obtain ⟨before, produced⟩ := HEDemandedConstructorProgram.producer_source_with_marking_of_reads
    HEDemandedCurrentReads.reads minimal .unchangedPreserving (Or.inr rfl) live scope
  obtain ⟨after, consumed⟩ := HEDemandedConsumerFrame.consumer_call_with_marking_of_reads
    HEDemandedCurrentReads.reads minimal .unchangedPreserving before live scope
  have ready : readyOperand symbolAllowed normalForm HEDemandedConstructorEdge.heldResult = value := by
    simp [readyOperand, HEDemandedConstructorEdge.heldResult, markedThroughout, markedFields]
  exact ⟨before, after, produced, consumed, ready, by rw [ready, singleSlot_exact]; rfl⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionCallCases
