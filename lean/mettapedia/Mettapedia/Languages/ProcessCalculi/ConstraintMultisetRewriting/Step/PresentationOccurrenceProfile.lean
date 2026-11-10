import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuleExecution

/-! # Interpreting the composed occurrence-language profile

State and candidate forms are the constructors authored by the module entry.
The frame interpretation is the existing binding-tree substitution action;
occurrence labels and preparation/admission decisions are explicit parameters.
The generic effect interpreter supplies the actual query tuples. No successful
transition is assumed by a source constructor or its name.

Configuration normalization is an explicit lowering operation. It uses the
existing exact configuration codec, so occurrence-set order may normalize
while rule/selection order and multiplicity remain represented.

These codecs present execution configurations. They do not require a runtime
to serialize or compare its whole store on each firing; a specialized
interpretation can carry the source-index equality by construction.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.OccurrenceProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Parsing
open Interface Payloads

abbrev State := Execution.State
abbrev Candidate := Execution.Candidate

def statePattern (state : State) : Pattern := .apply "StateData" [configurationPattern state]

def readState : Pattern → Option State
  | .apply "StateData" [configuration] => readConfiguration configuration
  | _ => none

def firingPattern (candidate : (_state : State) × Candidate) : Pattern :=
  .apply "FiringData" [configurationPattern candidate.1,
    rulePattern candidate.2.1, selectionPattern candidate.2.2]

def readFiring : Pattern → Option ((_state : State) × Candidate)
  | .apply "FiringData" [source, rule, selection] => do
      return ⟨← readConfiguration source, (← readRule rule, ← readSelection selection)⟩
  | _ => none

theorem read_state_pattern (state : State) : readState (statePattern state) = some state :=
  readConfiguration_pattern state

theorem read_firing_pattern (candidate : (_state : State) × Candidate) :
    readFiring (firingPattern candidate) = some candidate := by
  rcases candidate with ⟨state, rule, selection⟩
  simp only [readFiring, firingPattern, readConfiguration_pattern, readRule_pattern, readSelection_pattern]
  rfl

def encoding : Encoding State (fun _ => Candidate) where
  state := {
    key := ⟨"tcalc.occurrence-state", 1⟩
    view := statePattern
    expand := readState
    expand_view := read_state_pattern }
  firing := {
    key := ⟨"tcalc.occurrence-candidate", 1⟩
    view := firingPattern
    expand := readFiring
    expand_view := read_firing_pattern }

abbrev effect (label : Nat → Term) := (Execution.step label).effectCore
abbrev admission (label : Nat → Term) : (effect label).Admission :=
  (Execution.step label).eventAdmission

def queries (label : Nat → Term) (decision : Decisions (effect label) (admission label)) : Queries :=
  effectQueries (effect label) (admission label) encoding decision

/-- The actual rewrite of the combined authored language preserves and reflects
this profile's authorized occurrence transition, for supplied decision procedures. -/
theorem execution_iff (label : Nat → Term) (decision : Decisions (effect label) (admission label))
    (before after : State) (rule : RuleInstance Term) (selection : Selection Nat) :
    atState (statePattern after) ∈ rewriteStepWithPremisesUsing (queries label decision).relations
      authoredLanguage (request (statePattern before) (firingPattern ⟨before, (rule, selection)⟩)) ↔
      selection.Valid BindingTrees.action label rule before ∧
      selection.result label rule before = after := by
  rw [authored_root_execution]
  change atState (encoding.state.view (sort := ()) after) ∈
    rewriteStepWithPremisesUsing (effectQueries (effect label) (admission label) encoding decision).relations
      language (request (encoding.state.view (sort := ()) before)
        (encoding.firing.view (sort := ()) ⟨before, (rule, selection)⟩)) ↔ _
  rw [execution_iff_prepared]
  constructor
  · rintro ⟨prepared, permitted, result⟩
    exact ⟨(Execution.admits_iff label rule selection before).mp permitted, result⟩
  · rintro ⟨valid, result⟩
    have admitted := (Execution.admits_iff label rule selection before).mpr valid
    exact ⟨(Execution.step label).prepares admitted, admitted, result⟩

/-- Normalize the source representation and check the candidate's source index.
This operation performs no preparation, admission or store update. -/
def lowerRequest : Pattern → Option Pattern
  | .apply "Request" [source, firing] => do
      let state ← readState source
      let candidate ← readFiring firing
      if statePattern candidate.1 = statePattern state then
        some (request (statePattern state) (firingPattern candidate))
      else none
  | _ => none

theorem lower_canonical (state : State) (candidate : Candidate) :
    lowerRequest (request (statePattern state) (firingPattern ⟨state, candidate⟩)) =
      some (request (statePattern state) (firingPattern ⟨state, candidate⟩)) := by
  simp [lowerRequest, request, read_state_pattern, read_firing_pattern]

/-- Successful lowering retains an actual decoded state and indexed candidate. -/
theorem lower_reflects {source target : Pattern} (lowered : lowerRequest source = some target) :
    ∃ state candidate,
      source = request state candidate ∧
      ∃ (before : State) (firing : Candidate),
        readState state = some before ∧ readFiring candidate = some ⟨before, firing⟩ ∧
        target = request (statePattern before) (firingPattern ⟨before, firing⟩) := by
  cases source with
  | apply head arguments =>
      cases arguments with
      | nil => simp [lowerRequest] at lowered
      | cons source arguments =>
          cases arguments with
          | nil => simp [lowerRequest] at lowered
          | cons firing arguments =>
              cases arguments with
              | cons _ _ => simp [lowerRequest] at lowered
              | nil =>
                  by_cases requestHead : head = "Request"
                  · subst head
                    cases stateRead : readState source with
                    | none => simp [lowerRequest, stateRead] at lowered
                    | some state =>
                        cases firingRead : readFiring firing with
                        | none => simp [lowerRequest, stateRead, firingRead] at lowered
                        | some candidate =>
                            have same : statePattern candidate.1 = statePattern state := by
                              by_contra different
                              simp [lowerRequest, stateRead, firingRead, different] at lowered
                            have indexed : candidate.1 = state := encoding.state.view_injective same
                            rcases candidate with ⟨before, value⟩
                            change before = state at indexed
                            subst before
                            refine ⟨source, firing, rfl, state, value, stateRead, firingRead, ?_⟩
                            simpa [lowerRequest, stateRead, firingRead] using lowered.symm
                  · simp [lowerRequest, requestHead] at lowered
  | _ => simp [lowerRequest] at lowered

theorem lower_idempotent (source : Pattern) :
    (lowerRequest source).bind lowerRequest = lowerRequest source := by
  cases first : lowerRequest source with
  | none => rfl
  | some target =>
      obtain ⟨_, _, _, state, firing, _, _, rfl⟩ := lower_reflects first
      exact lower_canonical state firing

theorem stale_candidate_version_refused (candidate : (_state : State) × Candidate) :
    ExactPresentation.expandDocument encoding.firing (sort := ())
      ⟨⟨"tcalc.occurrence-candidate", 0⟩, firingPattern candidate⟩ = none := rfl

#print axioms read_firing_pattern
#print axioms execution_iff
#print axioms lower_canonical
#print axioms lower_reflects
#print axioms lower_idempotent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.OccurrenceProfile
