import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextControls
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextExecution

/-! # An actual protected type-definition firing with two retained outputs -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextExecutionControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open ProofExecution.Registered.Controls
open DefinitionAdapters.ContextControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (action)
open InferenceSchemaKernel (Space Value locatedAction)
open HOLLightContextActivation
open HOLLightContextExecution
open HOLLightContextControls.TypeDefinition

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def requestOccurrence : Occurrence :=
  (0, .requests, requestPayload 0 entry #[identityExistence])

def existenceOccurrence : Occurrence := (1, .judgments, theoremPayload 0 identityExistence)

def initial : Configuration Value Occurrence := ⟨[], {requestOccurrence, existenceOccurrence}⟩

theorem initial_consistent : locatedAction.Consistent initial.equations := ⟨action.identity, by simp [initial]⟩

theorem type_definition_fires :
    ∃ after, (system emptyAxiomPolicy contexts entries [0]).Step payload true initial after ∧
      existenceOccurrence ∈ after.present ∧
      (∃ abstraction ∈ after.present, label abstraction =
        (.judgments, theoremPayload 1 definedType.output.abstractionRepresentationTheorem)) ∧
      (∃ representation ∈ after.present, label representation =
        (.judgments, theoremPayload 1 definedType.output.representationAbstractionTheorem)) := by
  obtain ⟨after, stepped, retained, produced⟩ := activated_command_runs emptyAxiomPolicy contexts entries
    [0] 0 (by simp) #[identityExistence] entry [identityExistence] output activation_computed
    initial initial_consistent requestOccurrence (by simp [initial]) rfl (by
      intro fact member
      have same : fact = identityExistence := by simpa using member
      subst fact
      exact ⟨existenceOccurrence, by simp [initial], rfl⟩)
  exact ⟨after, stepped, retained existenceOccurrence (by simp [initial]) rfl,
    produced _ (by simp [output]), produced _ (by simp [output])⟩

theorem initial_protected_valid : HOLLightContextPublication.ProtectedValid emptyAxiomPolicy contexts location payload initial := by
  intro assignment _ occurrence present protectedHere
  rcases (show occurrence = requestOccurrence ∨ occurrence = existenceOccurrence by simpa [initial] using present) with rfl | rfl
  · change Space.requests = Space.judgments at protectedHere
    cases protectedHere
  · change HOLLightContextSemantics.ValidValue emptyAxiomPolicy contexts
      (action.apply assignment (theoremPayload 0 identityExistence))
    rw [theoremPayload_fixed]
    apply HOLLightContextSemantics.valid_theorem
    exact withExistence_valid identityExistence (by simp [withExistence])

/-- The actual step, final equation model, and protected occurrence jointly
produce the original independent exact-context source derivation. -/
theorem physical_publication_extracts_original_source :
    ∃ after, (system emptyAxiomPolicy contexts entries [0]).Run payload initial [true] after ∧
      TheoryDerives emptyAxiomPolicy (contexts 1) definedType.output.abstractionRepresentationTheorem ∧
      TheoryDerives emptyAxiomPolicy (contexts 1) definedType.output.representationAbstractionTheorem := by
  obtain ⟨after, stepped, _, ⟨abstraction, abstractionPresent, abstractionReadback⟩,
    ⟨representation, representationPresent, representationReadback⟩⟩ := type_definition_fires
  have run : (system emptyAxiomPolicy contexts entries [0]).Run payload initial [true] after :=
    .cons stepped (.nil _)
  obtain ⟨assignment, solved⟩ := run.consistent initial_consistent
  refine ⟨after, run, ?_, ?_⟩
  · apply (system emptyAxiomPolicy contexts entries [0]).published_theorem_has_source_derivation
      payload run initial_protected_valid assignment solved abstraction abstractionPresent
      (congrArg Prod.fst abstractionReadback) 1 _
    change action.apply assignment (label abstraction).2 = _
    rw [abstractionReadback, theoremPayload_fixed]
  · apply (system emptyAxiomPolicy contexts entries [0]).published_theorem_has_source_derivation
      payload run initial_protected_valid assignment solved representation representationPresent
      (congrArg Prod.fst representationReadback) 1 _
    change action.apply assignment (label representation).2 = _
    rw [representationReadback, theoremPayload_fixed]

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextExecutionControls
