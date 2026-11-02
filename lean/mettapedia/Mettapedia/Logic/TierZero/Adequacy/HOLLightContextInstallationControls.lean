import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextInstallation
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextExecutionControls

/-! # Fresh catalog installation and unused public-cache data controls -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextInstallationControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open ProofExecution.Registered.Controls
open DefinitionAdapters.ContextControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open HOLLightContextActivation
open HOLLightContextExecution
open HOLLightContextControls.TypeDefinition

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def noEntries : Nat → Option (Entry contexts) := fun _ => none

def prior := system emptyAxiomPolicy contexts noEntries []

def installation : HOLLightContextInstallation.Installation prior where
  index := 0
  entry := entry
  fresh := rfl

theorem absent_before_installation : activate emptyAxiomPolicy contexts noEntries 0 #[identityExistence] = none := rfl

theorem actual_lookup_installed : installation.installedEntries 0 = some entry := installation.installed_entry

theorem actual_kernel_catalog_installed :
    Sum.inl 0 ∈ (installation.rebuilt.authority.process true).schemas :=
  installation.installed_in_actual_kernel

theorem client_did_not_gain_the_schema :
    Sum.inl 0 ∉ (installation.rebuilt.authority.process false).schemas := by
  simp [HOLLightContextInstallation.Installation.rebuilt, installation, prior, system]

theorem actual_activation_installed :
    installation.rebuilt.activate (.inl 0) (.inl #[identityExistence]) =
      some (fromResult 0 entry #[identityExistence] [identityExistence] output) := by
  exact activation_computed

/-- The actual newly installed kernel entry executes the existing type
declaration; it is not only a membership fact about an unused catalog. -/
theorem installed_type_definition_fires :
    ∃ after, installation.rebuilt.Step payload true HOLLightContextExecutionControls.initial after ∧
      HOLLightContextExecutionControls.existenceOccurrence ∈ after.present := by
  obtain ⟨after, step, retained, _, _⟩ := HOLLightContextExecutionControls.type_definition_fires
  exact ⟨after, step, retained⟩

theorem unused_public_false_row_changes_no_local_check :
    typeCommand.check emptyAxiomPolicy coreContext #[identityExistence, falseExistence] =
      typeCommand.check emptyAxiomPolicy coreContext #[identityExistence] := rfl

/-- An unused fabricated public-cache row is not a hidden source premise.
Only address zero becomes the protected read of this actual activation. -/
theorem unused_public_false_row_is_not_a_premise :
    ∃ raw, activate emptyAxiomPolicy contexts entries 0 #[identityExistence, falseExistence] = some raw ∧
      raw.read = [(.judgments, theoremPayload 0 identityExistence)] := by
  have checked : entry.command.check emptyAxiomPolicy (contexts entry.before)
      #[identityExistence, falseExistence] = some output :=
    unused_public_false_row_changes_no_local_check.trans command_checked
  refine ⟨fromResult 0 entry #[identityExistence, falseExistence] [identityExistence] output, ?_, rfl⟩
  simp only [activate, show entries 0 = some entry from rfl]
  dsimp only [Bind.bind, Option.bind]
  rw [checked]
  rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextInstallationControls
