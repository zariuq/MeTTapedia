import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotActivation
import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandControls

/-!
# Actual snapshot installation and immediately usable original source catalog

The existing source type declaration supplies the control. It retains the
old context, creates canonical metadata once, publishes both exact outputs,
and installs an entry that the actual later catalog activation executes.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotControls

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open DefinitionAdapters.ContextControls ProofExecution.Registered.Controls
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation
open HOLLightFiniteCommandWitnesses

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def beforeSnapshot : Snapshot := initial DeclarationTable.core
def contextData := HOLLightFiniteContextSource.ofTable DeclarationTable.core
theorem formed : HOLLightFiniteContextData.WellFormed contextData :=
  HOLLightFiniteContextSource.ofTable_wellFormed DeclarationTable.core
def command : Command := withWitnesses typeCommand (HOLLightFiniteWitnesses.witnesses
  (sampleCommand typeCommand HOLLightContextControls.TypeDefinition.output))
def output := HOLLightContextControls.TypeDefinition.output

theorem command_checked : command.check emptyAxiomPolicy coreContext #[identityExistence] = some output :=
  accepted_finite_observation emptyAxiomPolicy coreContext #[identityExistence] typeCommand
    HOLLightContextControls.TypeDefinition.command_checked

theorem decoded_context_checked : command.check emptyAxiomPolicy
    (HOLLightFiniteContextData.toContext contextData formed) #[identityExistence] = some output := by
  have sameContext : HOLLightFiniteContextData.toContext contextData formed = coreContext :=
    HOLLightFiniteContextSource.toContext_ofTable DeclarationTable.core formed
  exact (congrArg (fun sourceContext => command.check emptyAxiomPolicy sourceContext #[identityExistence]) sameContext).trans command_checked

def successorTable := HOLLightFiniteAdmissionTables.outputTable emptyAxiomPolicy
  (HOLLightFiniteContextData.toTable contextData formed) #[identityExistence] command output decoded_context_checked

def prepared : Prepared := updated beforeSnapshot 0 HOLLightFiniteCommandControls.typeData command output successorTable [identityExistence]

theorem original_command_decoded : HOLLightFiniteCommandData.decode HOLLightFiniteCommandControls.typeData = some command :=
  HOLLightFiniteCommandData.decode_encode typeCommand _

theorem preparation_computed : prepare emptyAxiomPolicy beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] = some prepared := by
  exact prepare_of_checked emptyAxiomPolicy beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence]
    contextData formed command output [identityExistence] 0 rfl rfl original_command_decoded decoded_context_checked rfl

theorem unknown_source_before_installation : runActivate emptyAxiomPolicy beforeSnapshot 0 #[identityExistence] = none :=
  unknown_source_cannot_activate _ _ _ _ (initial_source_absent DeclarationTable.core 0)

theorem real_source_installed : lookup prepared.snapshot 0 = some ((0, 1, HOLLightFiniteCommandControls.typeData), command) :=
  HOLLightSnapshotInstallation.installed_lookup beforeSnapshot 0 HOLLightFiniteCommandControls.typeData command output successorTable
    [identityExistence] original_command_decoded

theorem original_context_retained : context prepared.snapshot 0 = some coreContext :=
  HOLLightSnapshotInstallation.old_context_retained beforeSnapshot 0 HOLLightFiniteCommandControls.typeData command output successorTable
    [identityExistence] 0 (initial_context DeclarationTable.core)

theorem exact_new_context : context prepared.snapshot 1 = some definedType.context :=
  HOLLightSnapshotInstallation.target_context_exact emptyAxiomPolicy beforeSnapshot 0 HOLLightFiniteCommandControls.typeData command output
    successorTable [identityExistence] #[identityExistence] (initial_context DeclarationTable.core) command_checked

theorem canonical_metadata_has_three_rows : prepared.snapshot.store.rows.card = 3 := by decide

theorem original_context_license_retained : prepared.snapshot.store.lookup (.inl 0) = some 0 := by decide

theorem installed_source_really_activates : runActivate emptyAxiomPolicy prepared.snapshot 0 #[identityExistence] =
    some (runFromResult prepared.snapshot 0 (0, 1, HOLLightFiniteCommandControls.typeData) #[identityExistence] output [identityExistence]) := by
  simp only [runActivate, real_source_installed, Bind.bind, Option.bind, original_context_retained,
    original_context_license_retained, command_checked]
  rfl

theorem installation_activates : installActivate emptyAxiomPolicy beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] =
    some (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) := by
  rw [installActivate, preparation_computed]
  rfl

theorem missing_existence_cannot_install : prepare emptyAxiomPolicy beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[] = none := by
  cases computed : prepare emptyAxiomPolicy beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[] with
  | none => rfl
  | some result =>
      obtain ⟨_, _, actualCommand, _, _, _, _, _, decoded, _, selected, _⟩ :=
        prepare_origin emptyAxiomPolicy beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[] computed
      have same : actualCommand = command := Option.some.inj (decoded.symm.trans original_command_decoded)
      subst actualCommand
      have noParents : Mettapedia.Logic.DerivationGraph.lookupPremises (#[] : Array Theorem) command.parents = none := rfl
      rw [noParents] at selected
      cases selected

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotControls
