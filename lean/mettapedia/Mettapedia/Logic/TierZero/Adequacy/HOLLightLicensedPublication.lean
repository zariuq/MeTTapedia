import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationRuns

/-!
# Rooted context licensing and exact theorem publication on actual CMR runs

Private context/path evidence has its own physical location. Arbitrary client
schemas retain their behavior and rights outside both protected locations.
Every newly available context follows original source admission from an
available predecessor and its actual selected protected premises. Old contexts
and theorem rows remain immutable; weakening requires an explicit licensed
inclusion path. This is a logical/existence observation of the ordinary core.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedPublication

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action)
open HOLLightContextActivation (Entry theoremPayload)
open HOLLightContextLicensing
open HOLLightLicensedActivation
open HOLLightLicensedValues

abbrev SourceSchema (C : Type*) := Source ⊕ C
abbrev SourceInputs (X : Type*) := Inputs ⊕ X

def activation (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) {C X : Type*}
    (client : C → X → Option (RuleInstance Value)) : SourceSchema C → SourceInputs X → Option (RuleInstance Value)
  | .inl source, .inl inputs => activate policy contexts entries source inputs
  | .inr source, .inr inputs => client source inputs
  | _, _ => none

def kernelSources (commands : List Nat) : List Source :=
  commands.map Sum.inl ++ [.inr false, .inr true]

def protectedOccurrence {O : Type*} (location : O → Location) (occurrence : O) : Prop :=
  location occurrence ≠ requests

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO}

structure System (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (C : Type uC) (X : Type uX)
    (I : Type uI) (O : Type uO) (location : O → Location) where
  commands : List Nat
  clientActivation : C → X → Option (RuleInstance Value)
  authority : SchemaPublicationAuthority.System (SourceSchema C) Location I O location (protectedOccurrence location)
  kernelSchemas : (authority.process authority.kernel).schemas = (kernelSources commands).map Sum.inl

def Valid (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (location : O → Location) (payload : O → Tm) (state : Configuration Value O) : Prop :=
  ∀ assignment, locatedAction.Models assignment state.equations →
    ∀ occurrence ∈ state.present,
      Meaning initial policy contexts (location occurrence, action.apply assignment (payload occurrence))

namespace System

variable [DecidableEq O] {policy : AxiomPolicy} [DecidablePred policy]
    {contexts : Nat → TheoryContext} {entries : Nat → Option (Entry contexts)} {location : O → Location}
    (system : System policy contexts entries C X I O location)

def activate : SourceSchema C → SourceInputs X → Option (RuleInstance Value) :=
  activation policy contexts entries system.clientActivation

def Step (payload : O → Tm) (actor : I) (before after : Configuration Value O) : Prop :=
  system.authority.Step system.activate locatedAction
    (fun occurrence => (location occurrence, payload occurrence)) actor before after

def Run (payload : O → Tm) (before : Configuration Value O) (actors : List I) (after : Configuration Value O) : Prop :=
  system.authority.Run system.activate locatedAction
    (fun occurrence => (location occurrence, payload occurrence)) before actors after

theorem step_preserves (initial : TheoryContext) (payload : O → Tm) {actor : I} {before after : Configuration Value O}
    (stepped : system.Step payload actor before after)
    (prior : Valid initial policy contexts location payload before) :
    Valid initial policy contexts location payload after := by
  obtain ⟨source, installed, inputs, raw, computed, picked, qualified, formed, rfl⟩ := stepped
  intro assignment solved occurrence present
  have oldModels := qualified.refines assignment solved
  rcases mem_fire.mp present with survived | produced
  · exact prior assignment oldModels occurrence survived.1
  · have made : occurrence ∈ picked.made := by simpa [Selection.commit] using produced
    by_cases kernelActor : actor = system.authority.kernel
    · subst actor
      rw [system.kernelSchemas] at installed
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp installed
      cases inputs with
      | inr clientInputs => simp [activate, activation] at computed
      | inl inputs =>
          change HOLLightLicensedActivation.activate policy contexts entries source inputs = some raw at computed
          exact HOLLightLicensedSemantics.output_valid initial policy contexts entries source inputs computed
            (fun item => (location item, payload item)) qualified assignment solved (by
              intro selected member
              exact prior assignment oldModels selected
                (qualified.occurrences.kept_subset (by simpa [Selection.commit] using member))) occurrence made
    · by_cases publicHere : location occurrence = requests
      · rw [publicHere]
        exact meaning_request initial policy contexts _
      · have allowed := formed occurrence made
        rw [system.authority.soleWriter actor kernelActor occurrence publicHere] at allowed
        cases allowed

theorem run_preserves (initial : TheoryContext) (payload : O → Tm) {before after : Configuration Value O}
    {actors : List I} (run : system.Run payload before actors after)
    (prior : Valid initial policy contexts location payload before) :
    Valid initial policy contexts location payload after := by
  induction run with
  | nil => exact prior
  | cons stepped rest earlier => exact earlier (system.step_preserves initial payload stepped prior)

theorem published_available_context_is_licensed (initial : TheoryContext) (payload : O → Tm)
    {before after : Configuration Value O} {actors : List I} (run : system.Run payload before actors after)
    (prior : Valid initial policy contexts location payload before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment after.equations) (occurrence : O) (present : occurrence ∈ after.present)
    (where_ : location occurrence = licenses) (context : Nat)
    (observed : action.apply assignment (payload occurrence) = available context) :
    Licensed initial policy (contexts context) := by
  apply (system.run_preserves initial payload run prior assignment solved occurrence present).1 context
  exact Prod.ext where_ observed

theorem published_theorem_is_rooted (initial : TheoryContext) (payload : O → Tm)
    {before after : Configuration Value O} {actors : List I} (run : system.Run payload before actors after)
    (prior : Valid initial policy contexts location payload before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment after.equations) (occurrence : O) (present : occurrence ∈ after.present)
    (where_ : location occurrence = judgments) (context : Nat) (fact : Theorem)
    (observed : action.apply assignment (payload occurrence) = theoremPayload context fact) :
    Licensed initial policy (contexts context) ∧ TheoryDerives policy (contexts context) fact := by
  apply (system.run_preserves initial payload run prior assignment solved occurrence present).2.2 context fact
  exact Prod.ext where_ observed

end System
end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedPublication
