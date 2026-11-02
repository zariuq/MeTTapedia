import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedInstallation
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextTableControls
import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedExecution

/-!
# Allocated exact context, installed actual entry and a real protected firing
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedInstallationControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open ProofExecution.Registered.Controls
open DefinitionAdapters.ContextControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightContextActivation (Entry theoremPayload targetContext)
open HOLLightContextControls.TypeDefinition (output command_checked)
open HOLLightLicensedActivation
open HOLLightLicensedExecution

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def contexts := HOLLightContextTable.interpret HOLLightContextTableControls.declared coreContext

theorem before_context : contexts 0 = coreContext := by
  change (HOLLightContextTable.lookup HOLLightContextTableControls.declared 0).getD coreContext = coreContext
  rw [HOLLightContextTableControls.old_and_new_contexts_remain.1]
  rfl

theorem after_context : contexts 1 = definedType.context := by
  change (HOLLightContextTable.lookup HOLLightContextTableControls.declared 1).getD coreContext = definedType.context
  rw [HOLLightContextTableControls.old_and_new_contexts_remain.2]
  rfl

def rootEntry : Entry contexts := ⟨0, 0, existenceCommand, rfl⟩
def entry : Entry contexts :=
  ⟨0, 1, typeCommand, by
    rw [before_context, after_context]
    simp [targetContext, typeCommand, defined_type_admitted]⟩

def priorEntries (id : Nat) : Option (Entry contexts) := if id = 0 then some rootEntry else none
def prior := system emptyAxiomPolicy contexts priorEntries [0]
def installation : HOLLightLicensedInstallation.Installation prior := ⟨1, entry, rfl⟩

theorem client_process_and_rights_retained :
    installation.rebuilt.authority.process false = prior.authority.process false ∧
      (installation.rebuilt.authority.process true).rights = (prior.authority.process true).rights :=
  ⟨installation.client_process_unchanged false (by decide), installation.rights_unchanged true⟩

theorem new_entry_actual_activation :
    activate emptyAxiomPolicy contexts installation.installedEntries (.inl 1) (.inl #[identityExistence]) =
      some (ExactRequestExecution.rule
        (requests, HOLLightContextActivation.requestPayload 1 entry #[identityExistence])
        [(licenses, available 0), (judgments, theoremPayload 0 identityExistence)]
        [(licenses, available 1), (licenses, included 0 1),
          (judgments, theoremPayload 1 definedType.output.abstractionRepresentationTheorem),
          (judgments, theoremPayload 1 definedType.output.representationAbstractionTheorem)]) := by
  have checked : entry.command.check emptyAxiomPolicy (contexts entry.before) #[identityExistence] = some output := by
    change typeCommand.check emptyAxiomPolicy (contexts 0) #[identityExistence] = some output
    rw [before_context]
    exact command_checked
  simp only [activate, commandActivate, HOLLightContextActivation.activate,
    show installation.installedEntries 1 = some entry from installation.installed_entry]
  dsimp only [Bind.bind, Option.bind]
  rw [checked]
  rfl

def requestOccurrence : Occurrence := (0, requests, HOLLightContextActivation.requestPayload 1 entry #[identityExistence])
def rootOccurrence : Occurrence := (1, licenses, available 0)
def proofOccurrence : Occurrence := (2, judgments, theoremPayload 0 identityExistence)
def before : Configuration Value Occurrence := ⟨[], {requestOccurrence, rootOccurrence, proofOccurrence}⟩

theorem newly_installed_entry_fires :
    ∃ after, installation.rebuilt.Step payload true before after ∧
      ∃ occurrence ∈ after.present, label occurrence = (licenses, available 1) := by
  obtain ⟨after, step, _, produced⟩ := activated_runs emptyAxiomPolicy contexts installation.installedEntries [0, 1]
    (.inl 1) (by simp [HOLLightLicensedPublication.kernelSources]) (.inl #[identityExistence])
    (HOLLightContextActivation.requestPayload 1 entry #[identityExistence])
    [(licenses, available 0), (judgments, theoremPayload 0 identityExistence)]
    [(licenses, available 1), (licenses, included 0 1),
      (judgments, theoremPayload 1 definedType.output.abstractionRepresentationTheorem),
      (judgments, theoremPayload 1 definedType.output.representationAbstractionTheorem)]
    new_entry_actual_activation (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide)
    before ⟨action.identity, by simp [before]⟩ requestOccurrence (by simp [before]) rfl (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨rootOccurrence, by simp [before], rfl⟩
      · exact ⟨proofOccurrence, by simp [before], rfl⟩)
  exact ⟨after, step, produced _ (List.mem_cons_self ..)⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedInstallationControls
