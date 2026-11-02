import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllEvidenceComponents

/-!
# Refusal controls for the unchanged native Vector All producer

These statements concern the original bounded producer and replay. A refused
search is not a proof that no typing derivation exists.
-/
set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents
open Presentation RussellTarski
open NativeNaturalVectorFamilies ReplayComponents
local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projection_absent :
    FormationSensitiveElaboration.alignProjection NativeVectorAll.rules NativeVectorAll.choices
      127 contextAPWNV allEvidenceControl allTypeControl natTm = false := by
  rw [choices_for_proof_evaluation]
  decide +kernel

private theorem alignment_absent :
    (FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      127 contextAPWNV allEvidenceControl allTypeControl natTm evidenceCode).isSome = false := by
  exact (FormationSensitiveElaboration.align_success NativeVectorAll.rules NativeVectorAll.choices
    127 contextAPWNV allEvidenceControl allTypeControl natTm evidenceCode).trans projection_absent

private theorem check_application_eq {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument expected : Tm Head n) :
    FormationSensitiveElaboration.check R choices (fuel+1) context (.app function argument) expected =
      (FormationSensitiveElaboration.synth R choices fuel context (.app function argument)).bind
        (fun inferred => FormationSensitiveElaboration.align R choices fuel context (.app function argument)
          inferred.type expected inferred.evidence) := by
  cases choices.normalize fuel expected <;> rfl

private theorem check_absent : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    128 contextAPWNV allEvidenceControl natTm = none := by
  have absent := Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp alignment_absent)
  have prior := evidence_synth_origin
  rw [evidence_application] at prior absent ⊢
  rw [check_application_eq,prior]
  exact absent

private theorem termReplayAccepted_of_none {Head : Type} (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n)
    (produced : FormationSensitiveElaboration.check R choices fuel context term type = none) :
    FormationSensitiveElaboration.termReplayAccepted R decoder choices fuel context term type = false := by
  unfold FormationSensitiveElaboration.termReplayAccepted
  rw [produced]

private theorem replay_refused : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 128 contextAPWNV allEvidenceControl natTm = false :=
  termReplayAccepted_of_none NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    128 contextAPWNV allEvidenceControl natTm check_absent

#print axioms alignment_absent
#print axioms check_absent
#print axioms replay_refused

theorem evidence_at_nat_not_produced :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      128 contextAPWNV allEvidenceControl natTm = none := check_absent

theorem evidence_at_nat_refused : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 128 contextAPWNV allEvidenceControl natTm = false := replay_refused

#print axioms evidence_at_nat_not_produced
#print axioms evidence_at_nat_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents
