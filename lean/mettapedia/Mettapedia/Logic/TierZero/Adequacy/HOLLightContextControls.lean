import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextPublication

/-!
# Exact-context, provenance, existence-premise and physical-space controls
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic
open InferenceSchemaActivation (Tm action)
open InferenceSchemaKernel (Space Value locatedAction)
open HOLLightContextActivation

theorem context_identity_retained {first second : Nat} (different : first ≠ second)
    (left right : Theorem) : theoremPayload first left ≠ theoremPayload second right :=
  fun same => different (theoremPayload_injective same).1

theorem hypothesis_identity_retained (context : Nat) (first second : Theorem)
    (different : first.sequent.hyp ≠ second.sequent.hyp) :
    theoremPayload context first ≠ theoremPayload context second :=
  fun same => different (congrArg (fun fact : Theorem => fact.sequent.hyp) (theoremPayload_injective same).2)

theorem axiom_dependencies_retained (context : Nat) (first second : Theorem)
    (different : first.axioms ≠ second.axioms) : theoremPayload context first ≠ theoremPayload context second :=
  fun same => different (congrArg Theorem.axioms (theoremPayload_injective same).2)

theorem fabricated_context_routing_refused (contexts : Nat → TheoryContext)
    (before after : Nat) (command : Command)
    (different : targetContext (contexts before) command ≠ some (contexts after)) :
    ¬∃ entry : Entry contexts, entry.before = before ∧ entry.after = after ∧ entry.command = command := by
  rintro ⟨entry, rfl, rfl, rfl⟩
  exact different entry.routed

theorem wrong_space_selected_premise_refused {O : Type*} [DecidableEq O]
    (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (source : Nat) (cache : Array Theorem)
    {raw : RuleInstance Value} (computed : activate policy contexts entries source cache = some raw)
    (location : O → Space) (payload : O → Tm) (before : Configuration Value O) (picked : Selection O)
    (occurrence : O) (selected : occurrence ∈ picked.read) (inPublic : location occurrence = .requests) :
    ¬picked.Valid locatedAction (fun item => (location item, payload item)) raw before := by
  intro qualified
  have declared : ∀ value ∈ raw.read, value.1 = Space.judgments := by
    obtain ⟨entry, output, parents, _, _, _, _, rfl⟩ := origin policy contexts entries source cache computed
    intro value member
    obtain ⟨fact, _, rfl⟩ := List.mem_map.mp member
    rfl
  have actual := LocatedSubstitution.declared_read_space action location payload qualified .judgments declared occurrence selected
  rw [inPublic] at actual
  cases actual

namespace TypeDefinition

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

open DefinitionAdapters.ContextControls
open ProofExecution.Registered.Controls

def contexts (identifier : Nat) : TheoryContext := if identifier = 0 then coreContext else definedType.context

def entry : Entry contexts where
  before := 0
  after := 1
  command := typeCommand
  routed := by simp [targetContext, contexts, typeCommand, defined_type_admitted]

def entries (identifier : Nat) : Option (Entry contexts) := if identifier = 0 then some entry else none

def output : Output := ⟨definedType.context,
  [definedType.output.abstractionRepresentationTheorem, definedType.output.representationAbstractionTheorem]⟩

theorem command_checked : typeCommand.check emptyAxiomPolicy coreContext #[identityExistence] = some output := by
  simp [Command.check, typeCommand, defined_type_admitted, defined_type_formation, output]
  rfl

/-- The real source type declaration activates with one selected existence
premise and publishes both independent definition results at the new context. -/
theorem activation_computed : activate emptyAxiomPolicy contexts entries 0 #[identityExistence] =
    some (fromResult 0 entry #[identityExistence] [identityExistence] output) := by
  simp only [activate, show entries 0 = some entry from rfl]
  dsimp only [Bind.bind, Option.bind]
  rw [show entry.command.check emptyAxiomPolicy (contexts entry.before) #[identityExistence] = some output from command_checked]
  rfl

theorem exact_existence_premise :
    (fromResult 0 entry #[identityExistence] [identityExistence] output).read =
      [(.judgments, theoremPayload 0 identityExistence)] := rfl

theorem both_outputs_at_exact_context :
    (fromResult 0 entry #[identityExistence] [identityExistence] output).produce =
      [(.judgments, theoremPayload 1 definedType.output.abstractionRepresentationTheorem),
        (.judgments, theoremPayload 1 definedType.output.representationAbstractionTheorem)] := rfl

theorem missing_existence_refused : activate emptyAxiomPolicy contexts entries 0 #[] = none := by
  rfl

theorem source_type_results_derived :
    TheoryDerives emptyAxiomPolicy definedType.context definedType.output.abstractionRepresentationTheorem ∧
      TheoryDerives emptyAxiomPolicy definedType.context definedType.output.representationAbstractionTheorem := by
  have source := (HOLLightSelectedAdmission.check_sound_selected emptyAxiomPolicy coreContext #[identityExistence]
    typeCommand (by
      intro index member fact found
      have equal : index = 0 := by simpa [Command.parents, typeCommand] using member
      subst index
      have factSame : identityExistence = fact := Option.some.inj found
      subst fact
      exact withExistence_valid identityExistence (by simp [withExistence])) command_checked).2
  exact ⟨source _ (by simp [output]), source _ (by simp [output])⟩

end TypeDefinition
end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextControls
