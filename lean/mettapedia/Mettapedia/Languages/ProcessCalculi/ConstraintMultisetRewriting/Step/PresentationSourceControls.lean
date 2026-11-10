import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationArgumentControls

/-! # Concrete source normalization and retained provenance

Two source configurations list the same live identities in different orders.
They describe one genuinely resource-changing event after the declared
configuration normalization. Their original source inputs remain different;
a raw-source record therefore cannot factor through abstract-event erasure.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.Parsing
open LanguageDefGrammarAlgebra PresentationExprSemantics
open Interface Payloads OccurrenceProfile ArgumentControls

abbrev candidate : Candidate := (rule, correct)
abbrev after : State := correct.result label rule before

def coreEvent : (effect label).Event (admission label) before after :=
  let allowed := (Execution.admits_iff label rule correct before).mpr both_admitted.1
  ⟨candidate, (Execution.step label).prepares allowed, allowed, rfl⟩

def rawConfiguration : Pattern :=
  .apply "TcConfigurationData" [equationsPattern [], indicesPattern [1, 0]]

def rawConfigurationRoute : Route "TcConfiguration" :=
  .apply (.at ⟨24, by decide +kernel⟩)
    (.cons (equationsRoute []) (.cons (indicesRoute [1, 0]) .nil))

theorem raw_configuration_tree :
    ((syntaxAlgebra Payloads.rules).evaluate rawConfigurationRoute).tree = rawConfiguration := by
  change Pattern.apply "TcConfigurationData"
    [((syntaxAlgebra Payloads.rules).evaluate (equationsRoute [])).tree,
     ((syntaxAlgebra Payloads.rules).evaluate (indicesRoute [1, 0])).tree] = _
  rw [equationsRoute_tree, indicesRoute_tree]
  rfl

def rawState : Pattern := .apply "StateData" [rawConfiguration]

def rawStateTokens : List String := ["(", "state"] ++
  ((syntaxAlgebra Payloads.rules).evaluate rawConfigurationRoute).tokens ++ [")"]

theorem raw_state_derives : GrammarDerives.Derives authoredLanguage "State" rawStateTokens rawState := by
  have data := syntaxEmbedding.derives (evaluate_source_derives data_compiles rawConfigurationRoute)
  rw [raw_configuration_tree] at data
  refine .rule authoredLanguage.terms[25] (by decide +kernel) "State" rfl _ _ ?_
  refine .terminal _ "(" _ _ _ (.terminal _ "state" _ _ _ ?_)
  refine .nonTerminal authoredLanguage.terms[25] "configuration" "TcConfiguration" rfl _ _ data _ _ _ ?_
  exact .terminal _ ")" _ _ _ (.nil _)

def rawRequest : Pattern := request rawState (firingPattern ⟨before, candidate⟩)
def rawTokens : List String := "fire" :: (rawStateTokens ++ firingTokens ⟨before, candidate⟩)
def rawInput : List Nat := SyntaxSource.printTokens rawTokens

theorem raw_request_derives : GrammarDerives.Derives authoredLanguage "Proc" rawTokens rawRequest := by
  refine .rule authoredLanguage.terms[28] (by decide +kernel) "Proc" rfl _ _ ?_
  refine .terminal _ "fire" _ _ _ ?_
  refine .nonTerminal authoredLanguage.terms[28] "state" "State" rfl _ _ raw_state_derives _ _ _ ?_
  simpa only [List.append_nil] using
    (GrammarDerives.DerivesItems.nonTerminal authoredLanguage.terms[28] "firing" "Firing" rfl _ _
      (firing_derives ⟨before, candidate⟩) [] [] [] (.nil _))

theorem raw_request_source : ∃ tree,
    LanguageDefScalarStructural.tree? tree = some rawRequest ∧ Nonempty (Parses "Proc" rawInput tree) :=
  LanguageDefScalarStructural.from_tokens raw_request_derives
    (SyntaxSource.spell_printTokens _) (LanguageDefScalarPrinter.sequence_self _)

theorem raw_state_read : readState rawState = some before := by
  simp [readState, rawState, rawConfiguration, readConfiguration,
    readEquations_pattern, readIndices_pattern, before, Finset.pair_comm]

theorem lower_raw_request : lowerRequest rawRequest =
    some (request (statePattern before) (firingPattern ⟨before, candidate⟩)) := by
  simp [rawRequest, lowerRequest, request, raw_state_read, read_firing_pattern]

theorem before_sorted : before.present.sort (· ≤ ·) = [0, 1] := by
  change (insert 0 {1} : Finset Nat).sort (· ≤ ·) = [0, 1]
  rw [Finset.sort_insert (· ≤ ·) (by simp) (by simp)]
  simp

theorem normalization_is_nonidentity :
    rawRequest ≠ request (statePattern before) (firingPattern ⟨before, candidate⟩) := by
  simp only [rawRequest, request, rawState, rawConfiguration, statePattern,
    configurationPattern, before_sorted]
  decide +kernel

theorem source_inputs_differ : rawInput ≠ requestInput before candidate := by
  simp only [rawInput, requestInput, rawTokens, requestTokens, rawStateTokens,
    stateTokens, firingTokens, configurationTokens, configurationRoute, before_sorted]
  decide +kernel

variable (decision : Decisions (effect label) (admission label))

theorem raw_selected_event : ∃ event : SelectedEvent label decision allParses before after,
    event.input = rawInput ∧ event.abstract label decision = coreEvent := by
  obtain ⟨tree, erased, ⟨parsed⟩⟩ := raw_request_source
  let event : SelectedEvent label decision allParses before after := {
    input := rawInput
    tree := tree
    parsed := parsed
    body := rawRequest
    erased := erased
    routed := source_arguments_routed parsed erased
    candidate := candidate
    lowered := lower_raw_request
    executed := (OccurrenceProfile.execution_iff label decision before after rule correct).mpr
      ⟨both_admitted.1, rfl⟩
    selected := rfl }
  exact ⟨event, rfl, rfl⟩

/-- Distinct retained source events have identical endpoints and the same
abstract event. Erasure is deliberately an observation, not source equality. -/
theorem normalization_identifies_distinct_sources :
    ∃ first second : SelectedEvent label decision allParses before after,
      first.input ≠ second.input ∧ first.abstract label decision = second.abstract label decision ∧
      first ≠ second := by
  obtain ⟨first, firstInput, firstAbstract⟩ := raw_selected_event decision
  obtain ⟨second, secondAbstract, secondInput⟩ := lift_event label decision (allParses_coverage label) coreEvent
  have different : first.input ≠ second.input := by
    rw [firstInput, secondInput]
    exact source_inputs_differ
  exact ⟨first, second, different, firstAbstract.trans secondAbstract.symm,
    fun same => different (congrArg
      (fun event : SelectedEvent label decision allParses before after => event.input) same)⟩

/-- A raw-input observer cannot descend through this normalization quotient. -/
theorem raw_input_does_not_factor :
    ¬ ∃ observe : (effect label).Event (admission label) before after → List Nat,
      ∀ event : SelectedEvent label decision allParses before after,
        observe (event.abstract label decision) = event.input := by
  rintro ⟨observe, respects⟩
  obtain ⟨first, second, different, same, _⟩ := normalization_identifies_distinct_sources decision
  exact different ((respects first).symm.trans ((congrArg observe same).trans (respects second)))

#print axioms coreEvent
#print axioms raw_request_source
#print axioms lower_raw_request
#print axioms normalization_is_nonidentity
#print axioms normalization_identifies_distinct_sources
#print axioms raw_input_does_not_factor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source.Controls
