import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationBindingApplication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRecovery

/-! # Contextual application prepares an authored occurrence candidate

The source contextual operation and the transform graft prepare the same
replacement rule, including refusals. The resulting rule still needs the
ordinary occurrence admission check. A resource-changing consumer connects
the operation to complete parsed source events and canonical recovery.

This is a contextual-application consumer, not a claim that arbitrary schema
activation or reflective language execution has been qualified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.Parsing
open Interface Payloads

def replacementRule (requestValue result : Payloads.Term) : RuleInstance Payloads.Term :=
  ⟨[requestValue], [], [], [], [result]⟩

def prepareApplication? (requestValue : Payloads.Term) (value : ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) : Option (RuleInstance Payloads.Term) :=
  (instantiateContextual? value ambient depth arguments).map (replacementRule requestValue)

theorem preparation_exact (requestValue : Payloads.Term) (value : ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) :
    prepareApplication? requestValue value ambient depth arguments =
      (instantiateValue? value ambient depth arguments).map
        (fun source => replacementRule requestValue (lowerPattern source)) := by
  rw [prepareApplication?, instantiateContextual_exact, Option.map_map]
  rfl

theorem preparation_origin (requestValue : Payloads.Term) (value : ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) (rule : RuleInstance Payloads.Term) :
    prepareApplication? requestValue value ambient depth arguments = some rule ↔
      ∃ source, instantiateValue? value ambient depth arguments = some source ∧
        replacementRule requestValue (lowerPattern source) = rule := by
  rw [preparation_exact, Option.map_eq_some_iff]

theorem preparation_refuses_iff (requestValue : Payloads.Term) (value : ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) :
    prepareApplication? requestValue value ambient depth arguments = none ↔
      instantiateValue? value ambient depth arguments = none := by
  rw [preparation_exact, Option.map_eq_none_iff]

/-- The source operation determines a rule; occurrence admission remains an
independent obligation, retaining exact resource selection and effects. -/
theorem prepared_execution_iff (label : Nat → Payloads.Term) (requestValue : Payloads.Term)
    (value : ContextualValue) (ambient depth : Nat) (arguments : List Pattern)
    (selection : Selection Nat) (before after : Execution.State) :
    (∃ rule, prepareApplication? requestValue value ambient depth arguments = some rule ∧
      Execution.Executes label (rulePattern rule) (selectionPattern selection)
        (configurationPattern before) (configurationPattern after)) ↔
    ∃ source, instantiateValue? value ambient depth arguments = some source ∧
      selection.Valid BindingTrees.action label (replacementRule requestValue (lowerPattern source)) before ∧
      selection.result label (replacementRule requestValue (lowerPattern source)) before = after := by
  constructor
  · rintro ⟨rule, prepared, executed⟩
    obtain ⟨source, applied, rfl⟩ := (preparation_origin requestValue value ambient depth arguments rule).mp prepared
    exact ⟨source, applied, (Execution.encoded_execution_iff _ _ _ _ _).mp executed⟩
  · rintro ⟨source, applied, valid, result⟩
    refine ⟨replacementRule requestValue (lowerPattern source), ?_, ?_⟩
    · exact (preparation_origin requestValue value ambient depth arguments _).mpr ⟨source, applied, rfl⟩
    · exact (Execution.encoded_execution_iff _ _ _ _ _).mpr ⟨valid, result⟩

namespace ApplicationConsumer

def requestValue : Payloads.Term := .node (.name 7) .nil
def selection : Selection Nat := ⟨[0], [], [1]⟩
def before : Execution.State := ⟨[], {0}⟩
def label (result : Payloads.Term) (occurrence : Nat) : Payloads.Term :=
  if occurrence = 1 then result else requestValue
def rule (result : Payloads.Term) := replacementRule requestValue result
def after (result : Payloads.Term) := selection.result (label result) (rule result) before

theorem valid (result : Payloads.Term) :
    selection.Valid BindingTrees.action (label result) (rule result) before where
  take_distinct := by simp [selection]
  output_distinct := by simp [selection]
  take_length := rfl
  read_length := rfl
  outputs := by simp [selection, label, rule, replacementRule]
  occurrences := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [selection, before, Selection.commit]
    · simp [selection, Selection.commit]
    · simp [selection, Selection.commit]
    · simp [selection, before, Selection.commit]
    · intro query member; simp [selection, Selection.commit] at member
  consistent := by
    refine ⟨Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.idx, ?_⟩
    intro equation member
    have same : equation = (requestValue, requestValue) := by
      simpa [Selection.problem, Selection.equations, selection, rule, replacementRule,
        before, label] using member
    subst equation
    rfl
  checks := by simp [rule, replacementRule]

theorem nonidentity_effect (result : Payloads.Term) :
    before.present = {0} ∧ (after result).present = {1} := by
  simp [before, after, Selection.result, selection, Selection.commit,
    MeTTaCalculus.OccurrenceCommits.fire]

/-- Every successful source application has a real parsed admitted event;
reading its input recovers the same rule and exact occurrence selection. -/
theorem source_application_has_parsed_event (value : ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) (source : Pattern)
    (applied : instantiateValue? value ambient depth arguments = some source)
    (decision : Decisions (OccurrenceProfile.effect (label (lowerPattern source)))
      (OccurrenceProfile.admission (label (lowerPattern source)))) :
    prepareApplication? requestValue value ambient depth arguments = some (rule (lowerPattern source)) ∧
      ∃ event : Source.SelectedEvent (label (lowerPattern source)) decision Source.allParses
          before (after (lowerPattern source)),
        Source.readInput event.input = some ⟨before, (rule (lowerPattern source), selection)⟩ := by
  refine ⟨(preparation_origin requestValue value ambient depth arguments _).mpr ⟨source, applied, rfl⟩, ?_⟩
  let admitted := (Execution.admits_iff (label (lowerPattern source)) _ selection before).mpr (valid _)
  let coreEvent := (Execution.step (label (lowerPattern source))).event
    (rule (lowerPattern source), selection) admitted
  obtain ⟨event, same, _⟩ := Source.lift_event (label (lowerPattern source)) decision
    (Source.allParses_coverage _) coreEvent
  refine ⟨event, ?_⟩
  rw [Source.event_input_recovery]
  have candidate := congrArg (fun e => e.firing) same
  change event.candidate = (rule (lowerPattern source), selection) at candidate
  rw [candidate]

end ApplicationConsumer

#print axioms prepared_execution_iff
#print axioms ApplicationConsumer.source_application_has_parsed_event

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Binding
