import Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalContextRegistry
import Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenseWorld
import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedRootControls

/-! # Source admission creates one canonical context/path record and reuses it -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalContextRegistryControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open ProofExecution.Registered.Controls
open DefinitionAdapters.ContextControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open HOLLightContextControls.TypeDefinition (contexts entry output command_checked)
open HOLLightCanonicalContextRegistry

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def rootStore := initialized 0
def afterStore := record rootStore entry

theorem root_lookup : rootStore.lookup (.inl 0) = some 0 := by decide +kernel

theorem actual_source_admitted : admitCommand emptyAxiomPolicy contexts rootStore entry #[identityExistence] = some (afterStore, output) := by
  simp only [admitCommand, show rootStore.lookup (.inl entry.before) = some 0 from root_lookup]
  dsimp only [Bind.bind, Option.bind]
  rw [show entry.command.check emptyAxiomPolicy (contexts entry.before) #[identityExistence] = some output from command_checked]
  rfl

theorem metadata_slots_are_computed : afterStore.lookup (.inl 0) = some 0 ∧
    afterStore.lookup (.inl 1) = some 1 ∧ afterStore.lookup (.inr (0, 1)) = some 2 ∧ afterStore.rows.card = 3 := by
  decide +kernel

theorem repeated_record_creates_no_rows : (record afterStore entry).rows = afterStore.rows := by decide +kernel

theorem actual_source_admission_preserves_licenses : LicensedStore coreContext emptyAxiomPolicy contexts afterStore := by
  have prior := initialized_licensed coreContext emptyAxiomPolicy contexts 0 rfl
  have sound := admitCommand_sound coreContext emptyAxiomPolicy contexts rootStore prior entry #[identityExistence] (by
    intro index cited fact found
    have sameIndex : index = 0 := by simpa [Command.parents, entry, typeCommand] using cited
    subst index
    have same : identityExistence = fact := Option.some.inj found
    subst fact
    exact withExistence_valid identityExistence (by simp [withExistence])) actual_source_admitted
  exact sound.2.1

theorem registered_context_has_one_physical_witness
    (frame : Finset HOLLightCanonicalLicenseWorld.CoreOccurrence)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    ∃! occurrence, occurrence ∈ HOLLightCanonicalLicenseWorld.world frame afterStore ∧
      HOLLightLicensedActivation.locatedAction.E
        (HOLLightLicensedActivation.locatedAction.apply assignment
          (HOLLightLicensedActivation.licenses, HOLLightCanonicalLicenses.payload (.inl 1)))
        (HOLLightLicensedActivation.locatedAction.apply assignment (HOLLightCanonicalLicenseWorld.label occurrence)) :=
  HOLLightCanonicalLicenseWorld.successful_read_is_unique frame afterStore assignment (.inl 1) 1 metadata_slots_are_computed.2.1

theorem absent_root_context_refused :
    admitCommand emptyAxiomPolicy contexts (CanonicalMetadataStore.Store.empty (K := HOLLightCanonicalLicenses.Key)) entry #[identityExistence] = none := rfl

theorem missing_existence_refused : admitCommand emptyAxiomPolicy contexts rootStore entry #[] = none := rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalContextRegistryControls
