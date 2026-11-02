import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextSemantics

/-!
# Exact-context registered HOL publication on ordinary CMR authority systems

Arbitrary client processes keep their own installed schemas and rights.
Protected theorem output comes only from installed original source commands.
Every used premise is selected in protected space and retains its complete
theorem codec, context identity, hypotheses and axiom dependencies. This is
the same generic schema-publication authority path as the inference catalog.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextPublication

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action)
open InferenceSchemaKernel (Space Value locatedAction protectedOccurrence)
open HOLLightContextActivation
open HOLLightContextSemantics (ValidValue ValidLocated)

abbrev SourceSchema (C : Type*) := Nat ⊕ C
abbrev Inputs (X : Type*) := Array Theorem ⊕ X

def activation (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) {C X : Type*}
    (client : C → X → Option (RuleInstance Value)) : SourceSchema C → Inputs X → Option (RuleInstance Value)
  | .inl source, .inl cache => activate policy contexts entries source cache
  | .inr source, .inr inputs => client source inputs
  | _, _ => none

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO}

structure System (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (C : Type uC) (X : Type uX)
    (I : Type uI) (O : Type uO) (location : O → Space) where
  sources : List Nat
  clientActivation : C → X → Option (RuleInstance Value)
  authority : SchemaPublicationAuthority.System (SourceSchema C) Space I O location (protectedOccurrence location)
  kernelSchemas : (authority.process authority.kernel).schemas = sources.map Sum.inl

def ProtectedValid (policy : AxiomPolicy) (contexts : Nat → TheoryContext) (location : O → Space)
    (payload : O → Tm) (state : Configuration Value O) : Prop :=
  ∀ assignment, locatedAction.Models assignment state.equations →
    ∀ occurrence ∈ state.present, location occurrence = .judgments →
      ValidValue policy contexts (action.apply assignment (payload occurrence))

namespace System

variable [DecidableEq O] {policy : AxiomPolicy} [DecidablePred policy]
    {contexts : Nat → TheoryContext} {entries : Nat → Option (Entry contexts)} {location : O → Space}
    (system : System policy contexts entries C X I O location)

def activate : SourceSchema C → Inputs X → Option (RuleInstance Value) :=
  activation policy contexts entries system.clientActivation

def Step (payload : O → Tm) (actor : I) (before after : Configuration Value O) : Prop :=
  system.authority.Step system.activate locatedAction
    (fun occurrence => (location occurrence, payload occurrence)) actor before after

def Run (payload : O → Tm) (before : Configuration Value O) (actors : List I) (after : Configuration Value O) : Prop :=
  system.authority.Run system.activate locatedAction
    (fun occurrence => (location occurrence, payload occurrence)) before actors after

theorem step_preserves (payload : O → Tm) {actor : I} {before after : Configuration Value O}
    (stepped : system.Step payload actor before after)
    (prior : ProtectedValid policy contexts location payload before) :
    ProtectedValid policy contexts location payload after := by
  obtain ⟨source, installed, inputs, raw, computed, picked, qualified, formed, rfl⟩ := stepped
  intro assignment solved occurrence present protectedHere
  have oldModels := qualified.refines assignment solved
  rcases mem_fire.mp present with survived | produced
  · exact prior assignment oldModels occurrence survived.1 protectedHere
  · have made : occurrence ∈ picked.made := by simpa [Selection.commit] using produced
    by_cases kernelActor : actor = system.authority.kernel
    · subst actor
      rw [system.kernelSchemas] at installed
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp installed
      cases inputs with
      | inr clientInputs => simp [activate, activation] at computed
      | inl cache =>
          change HOLLightContextActivation.activate policy contexts entries source cache = some raw at computed
          have valid := HOLLightContextSemantics.output_valid policy contexts entries source cache computed
            (fun item => (location item, payload item)) qualified assignment solved (by
              intro selected member selectedProtected
              exact prior assignment oldModels selected
                (qualified.occurrences.kept_subset (by simpa [Selection.commit] using member)) selectedProtected)
            occurrence made
          exact valid protectedHere
    · have allowed := formed occurrence made
      rw [system.authority.soleWriter actor kernelActor occurrence protectedHere] at allowed
      cases allowed

theorem run_preserves (payload : O → Tm) {before after : Configuration Value O} {actors : List I}
    (run : system.Run payload before actors after)
    (prior : ProtectedValid policy contexts location payload before) :
    ProtectedValid policy contexts location payload after := by
  induction run with
  | nil => exact prior
  | cons stepped rest earlier => exact earlier (system.step_preserves payload stepped prior)

/-- Exact theorem identity at its actual declaration context, including all
dependencies, is extracted from the actual protected published occurrence. -/
theorem published_theorem_has_source_derivation (payload : O → Tm)
    {before after : Configuration Value O} {actors : List I}
    (run : system.Run payload before actors after)
    (prior : ProtectedValid policy contexts location payload before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment after.equations)
    (occurrence : O) (present : occurrence ∈ after.present) (protectedHere : location occurrence = .judgments)
    (context : Nat) (fact : Theorem)
    (observed : action.apply assignment (payload occurrence) = theoremPayload context fact) :
    TheoryDerives policy (contexts context) fact :=
  system.run_preserves payload run prior assignment solved occurrence present protectedHere context fact observed

end System
end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextPublication
