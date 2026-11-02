import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentReplay

/-!
# Exact replay factors for dependent introductions

These equations observe the unchanged bounded producer followed by its
independent checker. Formation, component replay and alignment remain
separate required gates. The equations assume only the actual normalization
view and do not assume correctness of arbitrary search choices.

The observation is Boolean acceptance. No equivalence of physical work or
execution cost is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : Choices Head decoder.Code)

theorem lambda_replay_factor (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (body : Tm Head (n+1)) (expected domain : Tm Head n) (codomain : Tm Head (n+1))
    (view : choices.normalize fuel expected = .pi domain codomain) :
    termReplayAccepted R decoder choices (fuel+1) context (.lam body) expected =
      (formationReplayAccepted R decoder choices fuel context (.pi domain codomain) &&
        termReplayAccepted R decoder choices fuel (.snoc context domain) body codomain &&
        alignReplayGuard R decoder choices fuel context (.pi domain codomain) expected) := by
  conv_lhs =>
    unfold termReplayAccepted
    simp only [check, view]
  cases formed : synth R choices fuel context (.pi domain codomain) with
  | none => simp [formed, formationReplayAccepted]
  | some inference =>
    rcases inference with ⟨type,formation⟩
    cases type <;> try simp [formed, formationReplayAccepted]
    case head level =>
      cases checked : check R choices fuel (.snoc context domain) body codomain with
      | none => simp [checked, termReplayAccepted]
      | some bodyCode =>
        simp only [Option.bind_some]
        change alignReplayAccepted R decoder choices fuel context (.lam body)
          (.pi domain codomain) expected (.lamIntro level formation bodyCode) = _
        rw [align_replay_factor]
        simp [StructuralTypingReplay.check, termReplayAccepted, checked, Bool.and_assoc]


theorem pair_replay_factor (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (first second expected domain : Tm Head n) (codomain : Tm Head (n+1))
    (view : choices.normalize fuel expected = .sigma domain codomain) :
    termReplayAccepted R decoder choices (fuel+1) context (.pair first second) expected =
      (formationReplayAccepted R decoder choices fuel context (.sigma domain codomain) &&
        termReplayAccepted R decoder choices fuel context first domain &&
        termReplayAccepted R decoder choices fuel context second (inst0 first codomain) &&
        alignReplayGuard R decoder choices fuel context (.sigma domain codomain) expected) := by
  conv_lhs =>
    unfold termReplayAccepted
    simp only [check, view]
  cases formed : synth R choices fuel context (.sigma domain codomain) with
  | none => simp [formed, formationReplayAccepted]
  | some inference =>
    rcases inference with ⟨type,formation⟩
    cases type <;> try simp [formed, formationReplayAccepted]
    case head level =>
      cases firstChecked : check R choices fuel context first domain with
      | none => simp [firstChecked, termReplayAccepted]
      | some firstCode =>
        cases secondChecked : check R choices fuel context second (inst0 first codomain) with
        | none => simp [secondChecked, termReplayAccepted]
        | some secondCode =>
          simp only [Option.bind_some]
          change alignReplayAccepted R decoder choices fuel context (.pair first second)
            (.sigma domain codomain) expected (.pairIntro level formation firstCode secondCode) = _
          rw [align_replay_factor]
          simp [StructuralTypingReplay.check, termReplayAccepted, firstChecked, secondChecked,
            Bool.and_assoc]

#print axioms pair_replay_factor

#print axioms lambda_replay_factor
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
