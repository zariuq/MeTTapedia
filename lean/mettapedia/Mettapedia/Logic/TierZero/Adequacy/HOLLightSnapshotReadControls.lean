import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotReadExecution
import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPhysicalControls

/-!
# Install, then actually fire the installed catalog entry through a persistent read

The public later request is already pending before installation. One ordinary
interaction installs the source; the next reads its actual successor private
snapshot and protected premise. The snapshot and all existing license rows
survive the proof-only firing. Only theorem judgments are newly produced.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotReadControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (action)
open DefinitionAdapters.ContextControls ProofExecution.Registered.Controls
open HOLLightSnapshotData HOLLightSnapshotActivation HOLLightSnapshotExecution HOLLightSnapshotReadExecution
open HOLLightSnapshotControls HOLLightSnapshotPhysicalControls

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def reusedRule : RuleInstance Value := runFromResult prepared.snapshot 0
  (0, 1, HOLLightFiniteCommandControls.typeData) #[identityExistence] output [identityExistence]

theorem actual_install_then_proof_only_firing :
    ∃ first second snapshot,
      InteractionFormation.SchemaStep authority (activate emptyAxiomPolicy) action payload true initialWorld first ∧
      InteractionFormation.SchemaStep authority (activate emptyAxiomPolicy) action payload true first second ∧
      snapshot ∈ first.present ∧ snapshot ∈ second.present ∧
      label snapshot = (snapshots, snapshotPayload prepared.snapshot) ∧ runOccurrence ∉ second.present ∧
      (∀ occurrence ∈ first.present, location occurrence = licenses → occurrence ∈ second.present) := by
  obtain ⟨first, installed, _, _, existencePresent, _, requestPresent, produced⟩ := complete_atomic_publication
  obtain ⟨snapshot, snapshotPresent, snapshotLabel⟩ := produced (snapshots, snapshotPayload prepared.snapshot) (List.mem_cons_self ..)
  have consistent : locatedAction.Consistent first.equations := by
    obtain ⟨source, _, inputs, rule, _, picked, qualified, _, destination⟩ := installed
    rw [destination]
    exact qualified.consistent
  have available : ∀ value ∈ reusedRule.read, ∃ occurrence ∈ first.present, label occurrence = value := by
    intro value member
    have alternatives : value = (snapshots, snapshotPayload prepared.snapshot) ∨
        value = (judgments, HOLLightContextActivation.theoremPayload 0 identityExistence) := by simpa [reusedRule, runFromResult] using member
    rcases alternatives with rfl | rfl
    · exact ⟨snapshot, snapshotPresent, snapshotLabel⟩
    · exact ⟨existenceOccurrence, existencePresent, rfl⟩
  have separate : ∀ occurrence ∈ first.present, label occurrence ∈ reusedRule.read → occurrence ≠ runOccurrence := by
    intro occurrence _ member equal
    subst occurrence
    simp [reusedRule, runFromResult, runOccurrence, label, IndexedOccurrences.label, requests, snapshots, judgments] at member
  obtain ⟨picked, taken, qualified⟩ := ExactRequestExecution.selection locatedAction (requests, runRequest 0 #[identityExistence])
    reusedRule.read reusedRule.produce first consistent runOccurrence requestPresent rfl available separate
  let second := picked.result label reusedRule first
  have fired : InteractionFormation.SchemaStep authority (activate emptyAxiomPolicy) action payload true first second := by
    refine ⟨true, by simp [authority], (prepared.snapshot, Sum.inr (0, #[identityExistence])), reusedRule,
      installed_source_really_activates, picked, qualified, ?_, rfl⟩
    exact run_fully_formed location payload prepared.snapshot 0 (0, 1, HOLLightFiniteCommandControls.typeData)
      #[identityExistence] output [identityExistence] picked
  have snapshotNotRequest : location snapshot ≠ requests := by
    have place : location snapshot = snapshots := congrArg Prod.fst snapshotLabel
    rw [place]
    decide
  refine ⟨first, second, snapshot, installed, fired, snapshotPresent,
    private_occurrence_survives location payload prepared.snapshot 0 (0, 1, HOLLightFiniteCommandControls.typeData)
      #[identityExistence] output [identityExistence] qualified snapshot snapshotPresent snapshotNotRequest,
    snapshotLabel, qualified.consumed_removed (by simp [taken]), ?_⟩
  intro occurrence present atLicenses
  apply private_occurrence_survives location payload prepared.snapshot 0 (0, 1, HOLLightFiniteCommandControls.typeData)
    #[identityExistence] output [identityExistence] qualified occurrence present
  rw [atLicenses]
  decide

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotReadControls
