import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedExecution
import Mettapedia.Logic.TierZero.Adequacy.HOLLightChronologyControls

/-!
# From one root and no theorem assumptions to declaration and weakening

The actual three-firing run first proves the type-existence theorem, then
admits the type declaration, then transports the old theorem to the licensed
new context. Both context tokens remain present. Initial theorem space is
empty; all three requests are ordinary public data.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedRootControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open ProofExecution.Registered.Controls
open DefinitionAdapters.ContextControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (action)
open HOLLightContextActivation (Entry theoremPayload theoremPayload_fixed)
open HOLLightContextControls.TypeDefinition (contexts output command_checked)
open HOLLightContextLicensing
open HOLLightLicensedActivation
open HOLLightLicensedExecution

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def rootEntry : Entry contexts := ⟨0, 0, existenceCommand, rfl⟩
def typeEntry : Entry contexts := HOLLightContextControls.TypeDefinition.entry
def entries : Nat → Option (Entry contexts)
  | 0 => some rootEntry
  | 1 => some typeEntry
  | _ + 2 => none

def rootOutput : Output := ⟨coreContext, [identityExistence]⟩

theorem root_checked : rootEntry.command.check emptyAxiomPolicy (contexts rootEntry.before) #[] = some rootOutput := by
  simp [rootEntry, contexts, existenceCommand, Command.check, existence_replayed, existence_formation, rootOutput]
  exact ⟨existence_formation.2, rfl⟩

def rootRequest : InferenceSchemaActivation.Tm := HOLLightContextActivation.requestPayload 0 rootEntry #[]
def typeRequest : InferenceSchemaActivation.Tm := HOLLightContextActivation.requestPayload 1 typeEntry #[identityExistence]

theorem root_activated : activate emptyAxiomPolicy contexts entries (.inl 0) (.inl #[]) =
    some (ExactRequestExecution.rule (requests, rootRequest)
      [(licenses, available 0)] [(judgments, theoremPayload 0 identityExistence)]) := by
  simp only [activate, commandActivate, HOLLightContextActivation.activate, show entries 0 = some rootEntry from rfl]
  dsimp only [Bind.bind, Option.bind]
  rw [root_checked]
  rfl

def typeOutputs : List Value :=
  [(licenses, available 1), (licenses, included 0 1),
    (judgments, theoremPayload 1 definedType.output.abstractionRepresentationTheorem),
    (judgments, theoremPayload 1 definedType.output.representationAbstractionTheorem)]

theorem type_activated : activate emptyAxiomPolicy contexts entries (.inl 1) (.inl #[identityExistence]) =
    some (ExactRequestExecution.rule (requests, typeRequest)
      [(licenses, available 0), (judgments, theoremPayload 0 identityExistence)] typeOutputs) := by
  simp only [activate, commandActivate, HOLLightContextActivation.activate, show entries 1 = some typeEntry from rfl]
  dsimp only [Bind.bind, Option.bind]
  rw [show typeEntry.command.check emptyAxiomPolicy (contexts typeEntry.before) #[identityExistence] = some output from command_checked]
  rfl

def rootRequestOccurrence : Occurrence := (0, requests, rootRequest)
def typeRequestOccurrence : Occurrence := (1, requests, typeRequest)
def transportRequestOccurrence : Occurrence := (2, requests, weakeningRequest 0 1 identityExistence)
def rootContextOccurrence : Occurrence := (3, licenses, available 0)

def initial : Configuration Value Occurrence :=
  ⟨[], {rootRequestOccurrence, typeRequestOccurrence, transportRequestOccurrence, rootContextOccurrence}⟩

theorem initial_consistent : locatedAction.Consistent initial.equations := ⟨action.identity, by simp [initial]⟩

theorem initial_genesis : HOLLightLicensedGenesis.Genesis 0 location payload initial := by
  intro occurrence present
  simp only [initial, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩

theorem no_initial_theorems (occurrence : Occurrence) (present : occurrence ∈ initial.present) :
    location occurrence ≠ judgments :=
  HOLLightLicensedGenesis.genesis_has_no_theorems 0 location payload initial initial_genesis occurrence present

private theorem private_not_request {occurrence request : Occurrence}
    (privateHere : (label occurrence).1 ≠ requests) (publicHere : (label request).1 = requests) : occurrence ≠ request :=
  fun same => privateHere ((congrArg (fun item : Occurrence => (label item).1) same).trans publicHere)

theorem rooted_three_firings :
    ∃ after, (system emptyAxiomPolicy contexts entries [0, 1]).Run payload initial [true, true, true] after ∧
      rootContextOccurrence ∈ after.present ∧
      (∃ newContext ∈ after.present, label newContext = (licenses, available 1)) ∧
      (∃ proofRow ∈ after.present, label proofRow = (judgments, theoremPayload 1 identityExistence)) := by
  obtain ⟨first, rootStep, keepRoot, rootProduced⟩ := activated_runs emptyAxiomPolicy contexts entries [0, 1]
    (.inl 0) (by simp [HOLLightLicensedPublication.kernelSources]) (.inl #[])
    rootRequest [(licenses, available 0)] [(judgments, theoremPayload 0 identityExistence)] root_activated
    (by intro value member; have same := List.mem_singleton.mp member; rw [same]; decide)
    initial initial_consistent rootRequestOccurrence (by simp [initial]) rfl (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact ⟨rootContextOccurrence, by simp [initial], rfl⟩)
  obtain ⟨existence, existencePresent, existenceReadback⟩ := rootProduced _ (List.mem_singleton_self _)
  have rootPresent : rootContextOccurrence ∈ first.present := keepRoot _ (by simp [initial]) (by
    intro same
    have impossible : (3 : Nat) = 0 := congrArg Prod.fst same
    omega)
  have typePresent : typeRequestOccurrence ∈ first.present := keepRoot _ (by simp [initial]) (by
    intro same
    have impossible : (1 : Nat) = 0 := congrArg Prod.fst same
    omega)
  have firstConsistent : locatedAction.Consistent first.equations := SchemaPublicationAuthority.System.step_consistent rootStep
  obtain ⟨second, typeStep, keepType, typeProduced⟩ := activated_runs emptyAxiomPolicy contexts entries [0, 1]
    (.inl 1) (by simp [HOLLightLicensedPublication.kernelSources]) (.inl #[identityExistence]) typeRequest
    [(licenses, available 0), (judgments, theoremPayload 0 identityExistence)] typeOutputs type_activated
    (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide)
    first firstConsistent typeRequestOccurrence typePresent rfl (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨rootContextOccurrence, rootPresent, rfl⟩
      · exact ⟨existence, existencePresent, existenceReadback⟩)
  obtain ⟨newContext, newContextPresent, newContextReadback⟩ := typeProduced (licenses, available 1) (by simp [typeOutputs])
  obtain ⟨inclusion, inclusionPresent, inclusionReadback⟩ := typeProduced (licenses, included 0 1) (by simp [typeOutputs])
  have existenceRetained : existence ∈ second.present := keepType _ existencePresent (private_not_request (by
    rw [existenceReadback]
    decide) rfl)
  have secondConsistent : locatedAction.Consistent second.equations := SchemaPublicationAuthority.System.step_consistent typeStep
  have transportPresent : transportRequestOccurrence ∈ second.present := keepType _ (keepRoot _ (by simp [initial]) (by
    intro same
    have impossible : (2 : Nat) = 0 := congrArg Prod.fst same
    omega)) (by
      intro same
      have impossible : (2 : Nat) = 1 := congrArg Prod.fst same
      omega)
  obtain ⟨after, transportStep, keepTransport, transported⟩ := activated_runs emptyAxiomPolicy contexts entries [0, 1]
    (.inr false) (by simp [HOLLightLicensedPublication.kernelSources]) (.inr (.inl (0, 1, identityExistence)))
    (weakeningRequest 0 1 identityExistence)
    [(licenses, available 1), (licenses, included 0 1), (judgments, theoremPayload 0 identityExistence)]
    [(judgments, theoremPayload 1 identityExistence)] rfl
    (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide)
    second secondConsistent transportRequestOccurrence transportPresent rfl (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨newContext, newContextPresent, newContextReadback⟩
      · exact ⟨inclusion, inclusionPresent, inclusionReadback⟩
      · exact ⟨existence, existenceRetained, existenceReadback⟩)
  have rootSecond : rootContextOccurrence ∈ second.present := keepType _ rootPresent (by
    intro same
    have impossible : (3 : Nat) = 1 := congrArg Prod.fst same
    omega)
  refine ⟨after, .cons rootStep (.cons typeStep (.cons transportStep (.nil _))),
    keepTransport _ rootSecond (by
      intro same
      have impossible : (3 : Nat) = 2 := congrArg Prod.fst same
      omega), ?_, transported _ (List.mem_singleton_self _)⟩
  exact ⟨newContext, keepTransport _ newContextPresent (private_not_request (by rw [newContextReadback]; decide) rfl), newContextReadback⟩

theorem original_root_licenses_published_result :
    Licensed coreContext emptyAxiomPolicy (contexts 1) ∧
      TheoryDerives emptyAxiomPolicy (contexts 1) identityExistence := by
  obtain ⟨after, run, _, _, ⟨proofRow, present, readback⟩⟩ := rooted_three_firings
  have prior := HOLLightLicensedGenesis.genesis_valid coreContext emptyAxiomPolicy contexts 0 rfl
    location payload initial initial_genesis
  obtain ⟨assignment, solved⟩ := run.consistent initial_consistent
  apply (system emptyAxiomPolicy contexts entries [0, 1]).published_theorem_is_rooted coreContext payload run prior
    assignment solved proofRow present (congrArg Prod.fst readback) 1 identityExistence
  change action.apply assignment (label proofRow).2 = _
  rw [readback, theoremPayload_fixed]

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedRootControls
