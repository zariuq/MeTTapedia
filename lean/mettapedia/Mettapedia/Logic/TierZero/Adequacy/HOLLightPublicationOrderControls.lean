import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPhysicalControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CompletedOutputOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequiredLocation

/-!
# The existing HOL snapshot client under completed-output rotation

The successful comparison uses the original selected source installation,
all five physical outputs and the original rights. Missing private snapshot
occurrences block the client's actual installation and proof-use rules, even
if a public copy of the payload remains. No runtime default is changed and no
abstract partial-fault state is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightPublicationOrderControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open DefinitionAdapters.ContextControls ProofExecution.Registered.Controls
open InferenceSchemaActivation (action)
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation
open HOLLightSnapshotExecution HOLLightSnapshotControls
open HOLLightSnapshotPhysicalControls

theorem snapshot_is_the_last_output :
    (CompletedOutputOrder.rotateRule
      (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared)).produce =
      (metadataDelta beforeSnapshot prepared.snapshot ++
        prepared.output.theorems.map
          (fun fact => (judgments, HOLLightContextActivation.theoremPayload prepared.after fact))) ++
        [(snapshots, snapshotPayload prepared.snapshot)] := rfl

/-- The unchanged metadata/theorem prefix publishes no private snapshot. -/
theorem preceding_outputs_do_not_recreate_snapshot :
    ∀ value ∈ metadataDelta beforeSnapshot prepared.snapshot ++
      prepared.output.theorems.map
        (fun fact => (judgments, HOLLightContextActivation.theoremPayload prepared.after fact)),
      value.1 ≠ snapshots := by
  intro value member
  rcases List.mem_append.mp member with metadata | theoremOutput
  · obtain ⟨row, _, rfl⟩ := List.mem_map.mp metadata
    change licenses ≠ snapshots
    decide
  · obtain ⟨fact, _, rfl⟩ := List.mem_map.mp theoremOutput
    change judgments ≠ snapshots
    decide

theorem same_complete_five_output_step :
    ∃ picked : Selection Occurrence,
      picked.Valid locatedAction label
        (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) initialWorld ∧
      (CompletedOutputOrder.rotateSelection picked).Valid locatedAction label
        (CompletedOutputOrder.rotateRule
          (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared)) initialWorld ∧
      (CompletedOutputOrder.rotateSelection picked).result label
        (CompletedOutputOrder.rotateRule
          (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared)) initialWorld =
        picked.result label
          (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) initialWorld := by
  obtain ⟨picked, _, valid⟩ := actual_selection_computed
  exact ⟨picked, valid, CompletedOutputOrder.valid_rotates valid,
    CompletedOutputOrder.result_unchanged picked label _ initialWorld⟩

/-- Full take/read/observe/send formation survives the actual output move. -/
theorem completed_rotation_keeps_original_rights :
    ∃ picked : Selection Occurrence,
      (CompletedOutputOrder.rotateSelection picked).Valid locatedAction label
        (CompletedOutputOrder.rotateRule
          (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared)) initialWorld ∧
      InteractionFormation.Formed fullRights label (CompletedOutputOrder.rotateSelection picked)
        (CompletedOutputOrder.rotateRule
          (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared)) := by
  obtain ⟨picked, _, valid⟩ := actual_selection_computed
  exact ⟨picked, CompletedOutputOrder.valid_rotates valid,
    CompletedOutputOrder.formation_rotates
      (install_fully_formed location payload beforeSnapshot 0
        HOLLightFiniteCommandControls.typeData #[identityExistence] prepared picked)⟩

theorem no_snapshot_blocks_actual_installation (world after : Configuration Value Occurrence)
    (missing : ∀ occurrence ∈ world.present, location occurrence ≠ snapshots) :
    ¬ Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step locatedAction label
      (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) world after :=
  RequiredLocation.no_step_of_missing_take_location action location payload _ world after
    (pattern := (snapshots, snapshotPayload beforeSnapshot)) (by simp [installRule]) missing

theorem no_snapshot_blocks_original_proof_use
    (snapshot : Snapshot) (source : Nat) (entry : RawEntry) (cache : Array Theorem)
    (output : Output) (parents : List Theorem) (world after : Configuration Value Occurrence)
    (missing : ∀ occurrence ∈ world.present, location occurrence ≠ snapshots) :
    ¬ Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step locatedAction label
      (runFromResult snapshot source entry cache output parents) world after :=
  RequiredLocation.no_step_of_missing_read_location action location payload _ world after
    (pattern := (snapshots, snapshotPayload snapshot)) (by simp [runFromResult]) missing

def publicSnapshotCopy : Occurrence := (77, requests, snapshotPayload prepared.snapshot)

def publicCopyOnly : Configuration Value Occurrence := ⟨[], {publicSnapshotCopy}⟩

theorem public_copy_is_not_private_snapshot :
    ∀ occurrence ∈ publicCopyOnly.present, location occurrence ≠ snapshots := by
  intro occurrence present
  have same : occurrence = publicSnapshotCopy := by simpa [publicCopyOnly] using present
  subst occurrence
  decide

theorem public_copy_cannot_restore_original_source_use
    (snapshot : Snapshot) (source : Nat) (entry : RawEntry) (cache : Array Theorem)
    (output : Output) (parents : List Theorem) (after : Configuration Value Occurrence) :
    ¬ Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step locatedAction label
      (runFromResult snapshot source entry cache output parents) publicCopyOnly after :=
  no_snapshot_blocks_original_proof_use snapshot source entry cache output parents
    publicCopyOnly after public_copy_is_not_private_snapshot

end Mettapedia.Logic.TierZero.Adequacy.HOLLightPublicationOrderControls
