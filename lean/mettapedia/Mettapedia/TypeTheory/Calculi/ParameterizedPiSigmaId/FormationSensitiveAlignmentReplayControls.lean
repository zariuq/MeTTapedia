import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentReplay

/-!
# Alignment replay boundaries

Unchanged alignment preserves the input check. A search choice proposing a
cumulative lift does not override the independent policy check. Exhausted
fuel and an abstraction offered as a target type remain refused.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
namespace AlignmentReplayControls

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : Choices Head decoder.Code)

theorem unchanged_guard {n : Nat} (context : Ctx Head n) (type : Tm Head n) :
    alignReplayGuard R decoder choices 1 context type type = true := by
  simp [alignReplayGuard]

theorem zero_fuel_guard {n : Nat} (context : Ctx Head n) (source target : Tm Head n) :
    alignReplayGuard R decoder choices 0 context source target = false := rfl

theorem malformed_target_guard (head : Head) :
    alignReplayGuard R decoder choices 2 .nil (.head head) (.lam (.var 0)) = false := by
  simp [alignReplayGuard,synth]

theorem policy_refuses_proposed_cumulative {n : Nat} (context : Ctx Head n) (first second : Head)
    (different : first ≠ second) (proposed : choices.cumulative first second = true)
    (refused : ¬R.cumulative first second) :
    alignReplayGuard R decoder choices 1 context (.head first) (.head second) = false := by
  simp [alignReplayGuard,different,proposed,refused]

omit [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq] in
theorem proposed_cumulative_is_produced {n : Nat} (context : Ctx Head n) (term : Tm Head n)
    (first second : Head) (different : first ≠ second)
    (proposed : choices.cumulative first second = true) (evidence : Code Head decoder.Code n) :
    (align R choices 1 context term (.head first) (.head second) evidence).isSome = true := by
  simp [align,different,proposed]

theorem proposed_cumulative_replay_refused {n : Nat} (context : Ctx Head n) (term : Tm Head n)
    (first second : Head) (different : first ≠ second)
    (proposed : choices.cumulative first second = true) (refused : ¬R.cumulative first second)
    (evidence : Code Head decoder.Code n) :
    alignReplayAccepted R decoder choices 1 context term (.head first) (.head second) evidence = false := by
  simpa only [policy_refuses_proposed_cumulative R decoder choices context
    first second different proposed refused,Bool.and_false] using
    (align_replay_factor R decoder choices 1 context term (.head first) (.head second) evidence)

#print axioms proposed_cumulative_is_produced
#print axioms proposed_cumulative_replay_refused

end AlignmentReplayControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
