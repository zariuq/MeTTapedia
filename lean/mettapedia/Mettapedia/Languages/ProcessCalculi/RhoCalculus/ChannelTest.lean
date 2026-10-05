import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderExecution

/-!
# A communication test for actual rho name equality

A listener and one sender can communicate exactly when their subjects have
the same canonical name. Both directions concern the authored, sorted,
equation-saturated rho theory. Suspended continuation code is arbitrary.
The negative direction quantifies over all actual target representatives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelTest

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion HeaderExecution CanonicalStepperCompleteness CanonicalMatch

def headers (query name body payload : Pattern) : List Header :=
  [.input query body, .output name payload]

/-- The occurrence receipt from a two-header frontier has no alternative
input or output position. Its name comparison is the actual matcher test. -/
theorem selected_channels {query name body payload : Pattern}
    (selected : Selection (headers query name body payload)) :
    rhoCanonicalEquivalent query name = true := by
  have inputBound := selected.inputBound
  change selected.inputIndex < 2 at inputBound
  have inputIndex : selected.inputIndex = 0 := by
    have alternatives : selected.inputIndex = 0 ∨ selected.inputIndex = 1 := by omega
    rcases alternatives with zero | one
    · exact zero
    · have impossible := selected.inputEq
      simp [headers, one] at impossible
  have input := selected.inputEq
  simp only [headers, inputIndex, List.getElem_cons_zero, Header.input.injEq] at input
  have outputBound : selected.outputIndex < 1 := by
    simpa [headers, inputIndex] using selected.outputBound
  have outputIndex : selected.outputIndex = 0 := by omega
  have output : name = selected.outputChannel ∧ payload = selected.payload := by
    simpa [headers, inputIndex, outputIndex] using selected.outputEq
  exact (congrArg₂ rhoCanonicalEquivalent input.1 output.1).trans selected.channels

def selection (query name body payload : Pattern)
    (equal : rhoCanonicalEquivalent query name = true) :
    Selection (headers query name body payload) where
  inputIndex := 0
  inputBound := by simp [headers]
  outputIndex := 0
  outputBound := by simp [headers]
  inputChannel := query
  body := body
  outputChannel := name
  payload := payload
  inputEq := rfl
  outputEq := rfl
  channels := equal

/-- A real authored firing from this source exists exactly when the two
names agree, including every structurally equivalent source redex. -/
theorem enabled_iff {free : FreeSortContext} (query name body payload : Pattern)
    (typed : ∀ header ∈ headers query name body payload, header.Typed free)
    (safe : ∀ header ∈ headers query name body payload, header.Safe) :
    (∃ after, (ParameterizedRewriteSystem.theory free).Step
      (headerProcess (headers query name body payload) typed safe) after) ↔
      rhoCanonicalEquivalent query name = true := by
  constructor
  · rintro ⟨after, step⟩
    obtain ⟨redex, contractum, before, raw, _⟩ := ParameterizedRewriteSystem.step_iff.mp step
    have beforeSC := (ParameterizedRewriteSystem.equations_iff_structuralCongruence _ _).mp before
    have formed := (ParameterizedRewriteSystem.process_iff _ _).mp redex.2
    obtain ⟨selected, _⟩ := equivalent_selection_of_step typed safe formed.1 formed.2
      beforeSC.symm raw
    exact selected_channels selected
  · intro equal
    exact ⟨_, HeaderExecution.selection_step _ typed safe
      (selection query name body payload equal)⟩

theorem no_step_of_distinct {free : FreeSortContext} (query name body payload : Pattern)
    (typed : ∀ header ∈ headers query name body payload, header.Typed free)
    (safe : ∀ header ∈ headers query name body payload, header.Safe)
    (distinct : rhoCanonicalEquivalent query name ≠ true) :
    ∀ after, ¬ (ParameterizedRewriteSystem.theory free).Step
      (headerProcess (headers query name body payload) typed safe) after := by
  intro after step
  exact distinct ((enabled_iff query name body payload typed safe).mp ⟨after, step⟩)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelTest
