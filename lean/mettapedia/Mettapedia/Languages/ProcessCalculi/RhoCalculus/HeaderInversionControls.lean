import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-!
# Guard and occurrence controls for core-rho header inversion

Two equal messages are two selectable occurrences even when their contracta
agree. Canonical normalization retains the unconsumed duplicate. A reaction
inside an input body remains suspended at every authored descent depth.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

def zero : Pattern := .apply "PZero" []
def channel : Pattern := .apply "NQuote" [zero]
def forwardingBody : Pattern := .apply "POutput" [channel, .apply "PDrop" [.bvar 0]]

def duplicateMessages : List Header :=
  [.input channel forwardingBody, .output channel zero, .output channel zero]

private theorem channel_typed :
    NameWellSorted rhoReflectivePresentation (fun _ => none) [] channel :=
  .quote .unit

private theorem forwarding_typed :
    ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"] forwardingBody :=
  .output (.quote .unit) (.drop (.bvar rfl))

theorem duplicateMessages_typed :
    ∀ header ∈ duplicateMessages, header.Typed (fun _ => none) := by
  intro header member
  simp only [duplicateMessages, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨channel_typed, forwarding_typed⟩
  · exact ⟨channel_typed, .unit⟩
  · exact ⟨channel_typed, .unit⟩

theorem duplicateMessages_safe : ∀ header ∈ duplicateMessages, header.Safe := by
  intro header member
  simp only [duplicateMessages, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [Header.Safe, channel, forwardingBody, zero, binderSafeAt, binderSafeListAt]

def firstMessage : Selection duplicateMessages where
  inputIndex := 0
  inputBound := by decide
  outputIndex := 0
  outputBound := by decide
  inputChannel := channel
  body := forwardingBody
  outputChannel := channel
  payload := zero
  inputEq := rfl
  outputEq := rfl
  channels := by decide

def secondMessage : Selection duplicateMessages where
  inputIndex := 0
  inputBound := by decide
  outputIndex := 1
  outputBound := by decide
  inputChannel := channel
  body := forwardingBody
  outputChannel := channel
  payload := zero
  inputEq := rfl
  outputEq := rfl
  channels := by decide

theorem two_distinct_message_occurrences :
    firstMessage.outputIndex ≠ secondMessage.outputIndex ∧
      RhoStepAt 1 (parallel duplicateMessages) firstMessage.contractum ∧
      RhoStepAt 1 (parallel duplicateMessages) secondMessage.contractum ∧
      firstMessage.contractum = secondMessage.contractum :=
  ⟨by decide, firstMessage.authored duplicateMessages_typed,
    secondMessage.authored duplicateMessages_typed, rfl⟩

/-- Neither selected communication removes both equal messages. -/
theorem selected_residual_duplicate :
    firstMessage.residue = [.output channel zero] ∧
      secondMessage.residue = [.output channel zero] := ⟨rfl, rfl⟩

theorem forwarding_receives_actual_payload :
    semanticCommSubst forwardingBody zero = .apply "POutput" [channel, zero] := by
  simp [semanticCommSubst, forwardingBody, channel, zero,
    semanticNormalizeProc, semanticNormalizeName, semanticSubstProc,
    semanticSubstName, semanticSubstNameMark]

/-- Canonical inversion returns an original occurrence selection and the
supplied endpoint class for this concrete well-sorted duplicate frontier. -/
theorem canonical_duplicate_endpoint {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (canonicalParallel duplicateMessages) target) :
    ∃ selected : Selection duplicateMessages,
      Canonical.canonicalize target = Canonical.canonicalize selected.contractum :=
  canonical_selection_of_step duplicateMessages_typed duplicateMessages_safe step

def suspendedReaction : Header :=
  .input channel (parallel duplicateMessages)

/-- An enabled reaction inside a guarded continuation supplies no active
frontier step, irrespective of the authored descent allowance. -/
theorem input_guard_blocks_descent {fuel : Nat} {target : Pattern} :
    ¬ RhoStepAt fuel suspendedReaction.pattern target :=
  fun step => nonbag_no_step (Header.nonbag suspendedReaction) step

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversionControls
