import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceProofMetadata
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceProofsControls

/-!
# Actual receiver metadata and a mismatched conclusion control

The same two auxiliary proof calls retain source conclusions at their real
cache addresses. Changing only the source-conclusion metadata does not change
the registered proof history, but fails the separate checked-conclusion law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceMetadataControls

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution ExportReplay NumberedSourceProofs NumberedSourceMetadata

theorem initial_checked : ConclusionsChecked NumberedSourceProofsControls.initial.registered
    NumberedSourceProofsControls.initial.sourceConclusions :=
  empty_conclusions_checked _

theorem first_sources_checked : List.Forall₂
    (fun (source : SourceTerm) (claim : Sequent) => source.check = some claim.concl)
    [NumberedSourceProofsControls.firstPrepared.source] NumberedSourceProofsControls.firstPrepared.event.claims := by
  exact NumberedSourceProofMetadata.prepare_source_checks _ _ _
    (Option.some_get NumberedSourceProofsControls.first_prepared_available).symm

theorem first_apply : ExportReplay.apply SourceProfileModels.policy
    NumberedSourceProofsControls.initial.registered NumberedSourceProofsControls.firstPrepared.event =
      some NumberedSourceProofsControls.afterFirst.registered := by
  obtain ⟨candidate,prepared,applied,_,_,_,_⟩ := receive_checked _ _ _ NumberedSourceProofsControls.first_actual_receive
  have expected : prepare? NumberedSourceProofsControls.initial NumberedSourceProofsControls.first =
      some NumberedSourceProofsControls.firstPrepared :=
    (Option.some_get NumberedSourceProofsControls.first_prepared_available).symm
  have same := Option.some.inj (expected.symm.trans prepared)
  exact same ▸ applied

theorem first_checked : ConclusionsChecked NumberedSourceProofsControls.afterFirst.registered
    NumberedSourceProofsControls.afterFirst.sourceConclusions := by
  exact NumberedSourceProofMetadata.receive_preserves_conclusions _ _ _ initial_checked
    NumberedSourceProofsControls.first_actual_receive

theorem second_sources_checked : List.Forall₂
    (fun (source : SourceTerm) (claim : Sequent) => source.check = some claim.concl)
    [NumberedSourceProofsControls.secondPrepared.source] NumberedSourceProofsControls.secondPrepared.event.claims := by
  exact NumberedSourceProofMetadata.prepare_source_checks _ _ _
    (Option.some_get NumberedSourceProofsControls.second_prepared_available).symm

theorem second_apply : ExportReplay.apply SourceProfileModels.policy
    NumberedSourceProofsControls.afterFirst.registered NumberedSourceProofsControls.secondPrepared.event =
      some NumberedSourceProofsControls.afterSecond.registered := by
  obtain ⟨candidate,prepared,applied,_,_,_,_⟩ := receive_checked _ _ _ NumberedSourceProofsControls.second_actual_receive
  have expected : prepare? NumberedSourceProofsControls.afterFirst NumberedSourceProofsControls.second =
      some NumberedSourceProofsControls.secondPrepared :=
    (Option.some_get NumberedSourceProofsControls.second_prepared_available).symm
  have same := Option.some.inj (expected.symm.trans prepared)
  exact same ▸ applied

theorem second_checked : ConclusionsChecked NumberedSourceProofsControls.afterSecond.registered
    NumberedSourceProofsControls.afterSecond.sourceConclusions := by
  exact NumberedSourceProofMetadata.receive_preserves_conclusions _ _ _ first_checked
    NumberedSourceProofsControls.second_actual_receive

theorem actual_replay_checked : ConclusionsChecked NumberedSourceProofsControls.afterSecond.registered
    NumberedSourceProofsControls.afterSecond.sourceConclusions :=
  NumberedSourceProofMetadata.replay_preserves_conclusions _ _ _ initial_checked
    NumberedSourceProofsControls.actual_two_record_replay

theorem actual_input_replay_checked : ConclusionsChecked NumberedSourceProofsControls.afterStream.registered
    NumberedSourceProofsControls.afterStream.sourceConclusions := by
  exact NumberedSourceProofMetadata.replayInput_preserves_conclusions _ _ 0 2
    (empty_conclusions_checked _) (Option.some_get NumberedSourceProofsControls.actual_input_prefix_received).symm

def wrongSource : SourceTerm := .var (.global "wrong_conclusion") Ty.bool

def tampered : Std.TreeMap Nat SourceTerm :=
  NumberedSourceProofsControls.afterFirst.sourceConclusions.insert 37 wrongSource

theorem changed_metadata_is_not_checked :
    ¬ ConclusionsChecked NumberedSourceProofsControls.afterFirst.registered tampered := by
  intro coherent
  have present : tampered[37]? = some wrongSource := Std.TreeMap.getElem?_insert_self
  obtain ⟨position,fact,atAddress,atCache,sourceChecked⟩ := coherent 37 wrongSource present
  have positionSame : position = 0 :=
    Option.some.inj (atAddress.symm.trans NumberedSourceProofsControls.first_output_address)
  subst position
  have factAt : NumberedSourceProofsControls.afterFirst.registered.registered.cache[0]? =
      some NumberedSourceProofsControls.firstPrepared.receipt.conclusion := by decide +kernel
  have factSame := Option.some.inj (atCache.symm.trans factAt)
  subst fact
  have different : wrongSource.check ≠ some NumberedSourceProofsControls.firstPrepared.receipt.conclusion.sequent.concl := by
    decide +kernel
  exact different sourceChecked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceMetadataControls
