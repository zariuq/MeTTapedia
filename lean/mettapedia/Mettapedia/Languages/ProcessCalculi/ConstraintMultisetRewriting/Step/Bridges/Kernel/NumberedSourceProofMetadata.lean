import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceMetadata
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceProofs

/-!
# Checked source conclusions through actual proof reception

The parsing equation earns the source-check law, and the receiving equation
identifies the actual metadata update. A prepared receipt alone is not used
as evidence about the input's source conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceProofMetadata

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution ExportReplay SourceDAGReceive NumberedSourceMetadata

theorem claim_checked (reading : Reading) (raw : Json) (claim : NumberedSourceProofs.Claim)
    (found : NumberedSourceProofs.claim? reading raw = some claim) :
    claim.source.check = some claim.sequent.concl := by
  simp only [NumberedSourceProofs.claim?, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq] at found
  rcases found with ⟨idJson,_,id,_,hypothesesJson,_,rawHypotheses,_,hypotheses,_,
    indexJson,_,index,_,source,sourceAt,conclusion,conclusionAt,sequent,sequentAt,equal⟩
  have checked := conclusionAt
  unfold NumberedSourceProofs.canonical? at checked
  rw [sourceAt] at checked
  simp only [bind, Option.bind] at checked
  have conclusionEq := (Sequent.ofObjectTerms?_eq_some_iff hypotheses conclusion sequent).mp sequentAt
  cases equal
  simpa only [conclusionEq.2.2] using checked

theorem prepare_source_checks (reading : Reading) (raw : Json)
    (prepared : NumberedSourceProofs.Prepared raw)
    (found : NumberedSourceProofs.prepare? reading raw = some prepared) :
    List.Forall₂ (fun source claim => source.check = some claim.concl)
      [prepared.source] prepared.event.claims := by
  unfold NumberedSourceProofs.prepare? at found
  split at found
  · cases found
  · split at found
    · simp only [bind, Option.bind_eq_some_iff] at found
      rcases found with ⟨inputs,_,found⟩
      split at found
      · cases found
      · split at found
        · cases found
        · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at found
          rcases found with ⟨claim,claimAt,equal⟩
          cases equal
          exact .cons (claim_checked _ _ _ claimAt) .nil
    · cases found

theorem receive_data (before after : Reading) (raw : Json)
    (received : NumberedSourceProofs.receive? before raw = some after) :
    ∃ prepared : NumberedSourceProofs.Prepared raw,
      NumberedSourceProofs.prepare? before raw = some prepared ∧
      ExportReplay.apply SourceProfileModels.policy before.registered prepared.event = some after.registered ∧
      after.sourceConclusions =
        ExportCodec.addConclusions before.sourceConclusions prepared.event.sourceIds [prepared.source] := by
  unfold NumberedSourceProofs.receive? at received
  cases prepared : NumberedSourceProofs.prepare? before raw with
  | none => simp only [prepared, bind, Option.bind] at received; cases received
  | some candidate =>
      simp only [prepared, bind, Option.bind] at received
      split at received
      · cases received
      · rename_i state accepted
        have equal := Option.some.inj received
        subst after
        exact ⟨candidate,rfl,accepted,rfl⟩

theorem receive_preserves_conclusions (before after : Reading) (raw : Json)
    (beforeChecked : ConclusionsChecked before.registered before.sourceConclusions)
    (received : NumberedSourceProofs.receive? before raw = some after) :
    ConclusionsChecked after.registered after.sourceConclusions := by
  obtain ⟨prepared,preparedAt,accepted,metadata⟩ := receive_data before after raw received
  rw [metadata]
  exact apply_preserves_conclusions SourceProfileModels.policy _ _ _ _ _ beforeChecked
    (prepare_source_checks before raw prepared preparedAt) accepted

theorem replay_preserves_conclusions (before after : Reading) (raws : List Json)
    (beforeChecked : ConclusionsChecked before.registered before.sourceConclusions)
    (received : NumberedSourceProofs.replay? before raws = some after) :
    ConclusionsChecked after.registered after.sourceConclusions := by
  induction raws generalizing before with
  | nil =>
      simp only [NumberedSourceProofs.replay?, Option.some.injEq] at received
      subst after
      exact beforeChecked
  | cons raw rest ih =>
      cases first : NumberedSourceProofs.receive? before raw with
      | none => simp [NumberedSourceProofs.replay?,first] at received
      | some middle =>
          have remaining : NumberedSourceProofs.replay? middle rest = some after := by
            simpa [NumberedSourceProofs.replay?,first] using received
          exact ih middle (receive_preserves_conclusions before middle raw beforeChecked first) remaining

theorem replayInput_preserves_conclusions (before after : Reading) (index count : Nat)
    (beforeChecked : ConclusionsChecked before.registered before.sourceConclusions)
    (received : NumberedSourceProofs.replayInput? before index count = some after) :
    ConclusionsChecked after.registered after.sourceConclusions := by
  induction count generalizing before index with
  | zero =>
      simp only [NumberedSourceProofs.replayInput?, Option.some.injEq] at received
      subst after
      exact beforeChecked
  | succ count ih =>
      cases first : NumberedSourceProofs.receiveAt? before index with
      | none => simp [NumberedSourceProofs.replayInput?,first] at received
      | some middle =>
          have remaining : NumberedSourceProofs.replayInput? middle (index+1) count = some after := by
            simpa [NumberedSourceProofs.replayInput?,first] using received
          obtain ⟨raw,_,actual⟩ := NumberedSourceProofs.receiveAt_checked before middle index first
          exact ih middle (index+1)
            (receive_preserves_conclusions before middle raw beforeChecked actual) remaining

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceProofMetadata
