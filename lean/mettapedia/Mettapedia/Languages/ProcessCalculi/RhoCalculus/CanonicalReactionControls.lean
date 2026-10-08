import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho

/-!
# Closed COMM, duplicate occurrences and bound-name controls

Two identical outputs give distinct actual firing addresses with one common
endpoint. The complete endpoint therefore cannot decode the selected
occurrences. The same reaction comparison accepts the authored name
equation, while nested input readouts retain the difference between an outer
argument and a newer bound name. Free drop is inert in this COMM profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho

def zero : Pattern := .apply "PZero" []
def channel : Pattern := .apply "NQuote" [zero]
def body : Pattern := .apply "PDrop" [.bvar 0]
def payload : Pattern := output channel zero

theorem input_prime : IsPrime (input channel body) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.input (.quote .unit) (.drop (.bvar rfl)), ?_⟩, ?_, ?_, ?_⟩
  · rfl
  · simp [input, channel, body, zero, IsCanonical, IsCanonicalList]
  · simp [input]
  · intro elements
    simp [input]

theorem output_prime : IsPrime (output channel payload) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.output (.quote .unit) (.output (.quote .unit) .unit), ?_⟩, ?_, ?_, ?_⟩
  · rfl
  · simp [output, channel, payload, zero, IsCanonical, IsCanonicalList]
  · simp [output]
  · intro elements
    simp [output]

def rule : GroundComm := ⟨channel, channel, body, payload, input_prime, output_prime, rfl⟩

theorem actual_result : rule.result.1 = payload := rfl

def oneOutput : Bag :=
  ⟨([output channel payload] : List Pattern), fun pattern membership => by
    have same : pattern = output channel payload := by simpa using membership
    subst pattern
    exact output_prime⟩

def duplicates : Bag := append rule.redex oneOutput

private theorem duplicates_permutation :
    List.Perm (ordered duplicates.1) [input channel body, output channel payload,
      output channel payload] := by
  apply Multiset.coe_eq_coe.mp
  rw [ordered_multiset]
  rfl

private structure InputSelection where
  position : Fin (ordered duplicates.1).length
  inputAt : (ordered duplicates.1)[position.val] = input channel body
  remaining : (ordered duplicates.1).eraseIdx position.val =
    [output channel payload, output channel payload]

private theorem input_selection_exists : Nonempty InputSelection := by
  obtain ⟨i, iBound, j, jBound, inputAt, outputAt, tailPerm⟩ :=
    CanonicalStepperCompleteness.locate_pair duplicates_permutation
  have tail : ((ordered duplicates.1).eraseIdx i).eraseIdx j =
      [output channel payload] := List.perm_singleton.mp tailPerm
  have remainingPerm : List.Perm ((ordered duplicates.1).eraseIdx i)
      [output channel payload, output channel payload] := by
    have perm := (List.getElem_cons_eraseIdx_perm jBound).symm
    rwa [outputAt, tail] at perm
  have remaining : (ordered duplicates.1).eraseIdx i =
      [output channel payload, output channel payload] := by
    exact (List.perm_replicate (n := 2)).mp remainingPerm
  exact ⟨⟨⟨i, iBound⟩, inputAt, remaining⟩⟩

private noncomputable def selected : InputSelection := Classical.choice input_selection_exists

noncomputable def first : Firing duplicates where
  inputIndex := selected.position
  outputIndex := ⟨0, by rw [selected.remaining]; simp⟩
  rule := rule
  inputAt := selected.inputAt
  outputAt := by
    have bound : 0 < ((ordered duplicates.1).eraseIdx selected.position.val).length := by
      rw [selected.remaining]
      decide
    change ((ordered duplicates.1).eraseIdx selected.position.val)[0]'bound =
      output channel payload
    simp [selected.remaining]

noncomputable def second : Firing duplicates where
  inputIndex := selected.position
  outputIndex := ⟨1, by rw [selected.remaining]; simp⟩
  rule := rule
  inputAt := selected.inputAt
  outputAt := by
    have bound : 1 < ((ordered duplicates.1).eraseIdx selected.position.val).length := by
      rw [selected.remaining]
      decide
    change ((ordered duplicates.1).eraseIdx selected.position.val)[1]'bound =
      output channel payload
    simp [selected.remaining]

theorem first_tail : first.tail = [output channel payload] := by
  change (((ordered duplicates.1).eraseIdx selected.position.val).eraseIdx 0) = _
  rw [selected.remaining]
  rfl

theorem second_tail : second.tail = [output channel payload] := by
  change (((ordered duplicates.1).eraseIdx selected.position.val).eraseIdx 1) = _
  rw [selected.remaining]
  rfl

theorem different_occurrences : first ≠ second := by
  intro same
  have positions := congrArg (fun firing : Firing duplicates => firing.outputIndex.val) same
  change (0 : Nat) = 1 at positions
  omega

theorem same_endpoint : first.target = second.target := by
  apply Subtype.ext
  change rule.reactum.1 + (first.tail : Multiset Pattern) =
    rule.reactum.1 + (second.tail : Multiset Pattern)
  rw [first_tail, second_tail]

theorem complete_endpoint_inventory : first.target.1 =
    ([payload, output channel payload] : List Pattern) := by
  change (fromProcess rule.result).1 + (first.tail : Multiset Pattern) = _
  rw [first_tail, fromProcess_inventory, actual_result]
  rfl

theorem both_selected_steps :
    RhoStepAt 1 (toProcess duplicates).1 first.presentation.1 ∧
      RhoStepAt 1 (toProcess duplicates).1 second.presentation.1 :=
  ⟨first.selected_step, second.selected_step⟩

theorem no_selected_occurrence_decoder :
    ¬ ∃ decode : Bag → Firing duplicates, ∀ firing, decode firing.target = firing := by
  rintro ⟨decode, decodes⟩
  apply different_occurrences
  exact (decodes first).symm.trans
    ((congrArg decode same_endpoint).trans (decodes second))

def alternateChannel : Pattern := .apply "NQuote" [.apply "PDrop" [channel]]

theorem literal_names_distinct : alternateChannel ≠ channel := by
  decide

theorem actual_name_equation : canonicalize alternateChannel = canonicalize channel := rfl

def alternateSource : RhoProcess :=
  ofList [input alternateChannel body, output channel payload] (fun pattern membership => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · apply (rhoClosedTermWellSorted_process_iff _).mpr
      exact ⟨.input (.quote (.drop (.quote .unit))) (.drop (.bvar rfl)), rfl⟩
    · exact output_prime.1)

theorem equation_retains_reaction_inventory :
    fromProcess alternateSource = fromProcess (rule.source empty) := by
  apply (fromProcess_eq_iff _ _).mpr
  apply (rhoProcessEquations_iff _ _).mpr
  change canonicalize (.collection .hashBag
      [input alternateChannel body, output channel payload] none) =
    canonicalize (.collection .hashBag
      (input channel body :: output channel payload :: ordered empty.1) none)
  have emptyOrder : ordered empty.1 = [] := by
    simp [ordered, empty]
  rw [emptyOrder]
  have sameInput : canonicalize (input alternateChannel body) =
      canonicalize (input channel body) := by
    unfold input
    rw [CanonicalStepperCompleteness.canonicalize_input,
      CanonicalStepperCompleteness.canonicalize_input, actual_name_equation]
  simp only [CanonicalStepperCompleteness.canonicalize_bag,
    List.map_cons, List.map_nil, sameInput]

theorem public_communication_accepts_name_equation :
    rhoLanguageDefGSLT.Step alternateSource (rule.target empty) := by
  apply (publicStep_iff _ _).mpr
  rw [equation_retains_reaction_inventory]
  exact ⟨rule, empty, rule.source_inventory empty, rule.target_inventory empty⟩

def olderBody : Pattern := input channel (output (.bvar 1) zero)
def newerBody : Pattern := input channel (output (.bvar 0) zero)

theorem older_input_prime : IsPrime (input channel olderBody) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.input (.quote .unit) (.input (.quote .unit) (.output (.bvar rfl) .unit)), ?_⟩,
    ?_, ?_, ?_⟩
  · rfl
  · simp [input, output, olderBody, channel, zero, IsCanonical, IsCanonicalList]
  · simp [input]
  · intro elements
    simp [input]

theorem newer_input_prime : IsPrime (input channel newerBody) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.input (.quote .unit) (.input (.quote .unit) (.output (.bvar rfl) .unit)), ?_⟩,
    ?_, ?_, ?_⟩
  · rfl
  · simp [input, output, newerBody, channel, zero, IsCanonical, IsCanonicalList]
  · simp [input]
  · intro elements
    simp [input]

def older : GroundComm :=
  ⟨channel, channel, olderBody, payload, older_input_prime, output_prime, rfl⟩

def newer : GroundComm :=
  ⟨channel, channel, newerBody, payload, newer_input_prime, output_prime, rfl⟩

theorem outer_argument_readout : older.result.1 =
    input channel (output (.apply "NQuote" [payload]) zero) := rfl

theorem newer_bound_readout : newer.result.1 = input channel (output (.bvar 0) zero) := rfl

theorem actual_nested_results_distinct : older.result.1 ≠ newer.result.1 := by
  rw [outer_argument_readout, newer_bound_readout]
  simp [input, output]

theorem nested_steps_retain_bound_positions :
    RhoStep (older.source empty).1 (older.target empty).1 ∧
      RhoStep (newer.source empty).1 (newer.target empty).1 ∧
      older.result.1 ≠ newer.result.1 :=
  ⟨older.step empty, newer.step empty, actual_nested_results_distinct⟩

/-- The full COMM family does not invent a free-DROP/RUN transition. -/
theorem free_drop_has_no_reaction :
    ¬ ∃ target : Bag, Reaction (fromProcess closedFreeDrop) target := by
  rintro ⟨target, reaction⟩
  have step : rhoLanguageDefGSLT.Step closedFreeDrop (toProcess target) := by
    apply (publicStep_iff _ _).mpr
    simpa using reaction
  obtain ⟨representative, member, _⟩ := canonicalSuccessorList_complete closedFreeDrop step
  rw [canonicalSuccessorList_closedFreeDrop_nil] at member
  simp at member

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls
