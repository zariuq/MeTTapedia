import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequest
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationRuns

/-!
# Installed inference schemas publish only independently derived judgments

The kernel installs the original validated definition's actual rule IDs.
Each firing computes its local source instantiation and retains the actual
activation origin. Client source schemas are arbitrary, but their send rights
cannot publish to protected judgment space. Logical validity uses only the
actual selected protected premises, never proof-shaped public request data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaKernel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open InferenceSchemaActivation (Tm action judgment)
open InferenceSchemaSemantics (ValidValue)

/-- Physical roles of this request/checked-judgment hosting instance. The
ordinary authority system itself permits arbitrary location carriers. -/
inductive Space where
  | requests | judgments
  deriving DecidableEq

abbrev Value := Space × Tm
abbrev locatedAction := LocatedSubstitution.action (N := Space) action
abbrev SourceSchema (C : Type*) := RuleId ⊕ C
abbrev Inputs (X : Type*) := List Pattern ⊕ X

def locate (rule : RuleInstance Tm) : RuleInstance Value :=
  LocatedRequest.lift .requests .judgments .requests .judgments rule

def activation (definition : ValidatedCalculusLanguageDef) {C X : Type*}
    (client : C → X → Option (RuleInstance Value)) : SourceSchema C → Inputs X → Option (RuleInstance Value)
  | .inl id, .inl arguments => (InferenceSchemaActivation.activate definition id arguments).map locate
  | .inr source, .inr inputs => client source inputs
  | _, _ => none

def protectedOccurrence {O : Type*} (location : O → Space) (occurrence : O) : Prop :=
  location occurrence = .judgments

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO}

structure System (definition : ValidatedCalculusLanguageDef) (C : Type uC) (X : Type uX)
    (I : Type uI) (O : Type uO) (location : O → Space) where
  clientActivation : C → X → Option (RuleInstance Value)
  authority : SchemaPublicationAuthority.System (SourceSchema C) Space I O location (protectedOccurrence location)
  kernelSchemas : (authority.process authority.kernel).schemas = definition.1.rules.map (fun rule => .inl rule.id)

def ProtectedValid (definition : ValidatedCalculusLanguageDef) (location : O → Space)
    (payload : O → Tm) (state : Configuration Value O) : Prop :=
  ∀ assignment, locatedAction.Models assignment state.equations →
    ∀ occurrence ∈ state.present, protectedOccurrence location occurrence →
      ValidValue definition (action.apply assignment (payload occurrence))

theorem output_valid {O : Type*} [DecidableEq O] (definition : ValidatedCalculusLanguageDef)
    (id : RuleId) (arguments : List Pattern) {raw : RuleInstance Tm}
    (computed : InferenceSchemaActivation.activate definition id arguments = some raw)
    (location : O → Space) (payload : O → Tm) {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence)) (locate raw) before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem (fun occurrence => (location occurrence, payload occurrence))
      (locate raw) before))
    (incoming : ∀ occurrence ∈ picked.read, ValidValue definition (action.apply assignment (payload occurrence))) :
    ∀ occurrence ∈ picked.made, ValidValue definition (action.apply assignment (payload occurrence)) := by
  obtain ⟨rule, premises, conclusion, lookup, localResult, same⟩ := InferenceSchemaActivation.origin definition id arguments computed
  have equalities : LocatedRequest.EqualityChecks raw := by
    rw [same]
    intro check member
    cases member
  exact InferenceSchemaSemantics.output_valid definition id arguments computed payload
    (LocatedRequest.project_valid action (fun occurrence => (location occurrence, payload occurrence))
      .requests .judgments .requests .judgments equalities qualified) assignment
    (LocatedRequest.project_models action (fun occurrence => (location occurrence, payload occurrence))
      .requests .judgments .requests .judgments qualified assignment solved) incoming

namespace System

variable [DecidableEq O] {definition : ValidatedCalculusLanguageDef} {location : O → Space}
    (system : System definition C X I O location)

def activate : SourceSchema C → Inputs X → Option (RuleInstance Value) := activation definition system.clientActivation

def Step (payload : O → Tm) (actor : I) (before after : Configuration Value O) : Prop :=
  system.authority.Step system.activate locatedAction
    (fun occurrence => (location occurrence, payload occurrence)) actor before after

def Run (payload : O → Tm) (before : Configuration Value O) (actors : List I) (after : Configuration Value O) : Prop :=
  system.authority.Run system.activate locatedAction
    (fun occurrence => (location occurrence, payload occurrence)) before actors after

theorem step_preserves (payload : O → Tm) {actor : I} {before after : Configuration Value O}
    (stepped : system.Step payload actor before after)
    (prior : ProtectedValid definition location payload before) : ProtectedValid definition location payload after := by
  obtain ⟨source, installed, inputs, located, computed, picked, qualified, formed, rfl⟩ := stepped
  intro assignment solved occurrence present protectedHere
  have oldModels := qualified.refines assignment solved
  rcases mem_fire.mp present with survived | produced
  · exact prior assignment oldModels occurrence survived.1 protectedHere
  · have made : occurrence ∈ picked.made := by simpa [Selection.commit] using produced
    by_cases kernelActor : actor = system.authority.kernel
    · subst actor
      rw [system.kernelSchemas] at installed
      obtain ⟨rule, _, rfl⟩ := List.mem_map.mp installed
      cases inputs with
      | inr clientInputs => simp [activate, activation] at computed
      | inl arguments =>
          change (InferenceSchemaActivation.activate definition rule.id arguments).map locate = some located at computed
          obtain ⟨raw, origin, same⟩ := Option.map_eq_some_iff.mp computed
          subst located
          apply output_valid definition rule.id arguments origin location payload qualified assignment solved ?_ occurrence made
          intro source selected
          have routed := LocatedRequest.read_space action location payload
            .requests .judgments .requests .judgments qualified source selected
          exact prior assignment oldModels source (qualified.occurrences.kept_subset (by simpa [Selection.commit] using selected)) routed
    · have allowed := formed occurrence made
      rw [system.authority.soleWriter actor kernelActor occurrence protectedHere] at allowed
      cases allowed

theorem run_preserves (payload : O → Tm) {before after : Configuration Value O} {actors : List I}
    (run : system.Run payload before actors after) (prior : ProtectedValid definition location payload before) :
    ProtectedValid definition location payload after := by
  induction run with
  | nil => exact prior
  | cons stepped rest earlier => exact earlier (system.step_preserves payload stepped prior)

theorem published_judgment_has_source_derivation (payload : O → Tm)
    {before after : Configuration Value O} {actors : List I} (run : system.Run payload before actors after)
    (prior : ProtectedValid definition location payload before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment after.equations) (occurrence : O)
    (present : occurrence ∈ after.present) (isProtected : protectedOccurrence location occurrence)
    (pattern : Pattern) (observed : action.apply assignment (payload occurrence) = judgment pattern) :
    Nonempty (InferenceChecker.Derivation definition pattern) :=
  system.run_preserves payload run prior assignment solved occurrence present isProtected pattern observed

end System
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaKernel
