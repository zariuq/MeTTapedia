import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentReplay

/-!
# Exact alignment-code checkpoints

A proved production observation retains the original alignment result.
The independent replay observation identifies the same retained code, and
successful replay entails production. No property of arbitrary search
choices is assumed, and production alone does not establish acceptance.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration

variable {Head : Type} {RootCode : Nat → Type} (R : Rules Head) [DecidableEq Head]

def producedAlignmentCode (choices : Choices Head RootCode) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term source target : Tm Head n) (evidence : Code Head RootCode n)
    (produced : (align R choices fuel context term source target evidence).isSome = true) :
    Code Head RootCode n :=
  (align R choices fuel context term source target evidence).get produced

theorem producedAlignmentCode_origin (choices : Choices Head RootCode) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term source target : Tm Head n) (evidence : Code Head RootCode n)
    (produced : (align R choices fuel context term source target evidence).isSome = true) :
    align R choices fuel context term source target evidence =
      some (producedAlignmentCode R choices fuel context term source target evidence produced) :=
  Option.eq_some_of_isSome produced

theorem zero_fuel_not_aligned (choices : Choices Head RootCode) {n : Nat}
    (context : Ctx Head n) (term source target : Tm Head n) (evidence : Code Head RootCode n) :
    (align R choices 0 context term source target evidence).isSome = false := rfl

theorem unchanged_alignment_retains_code (choices : Choices Head RootCode) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n) (evidence : Code Head RootCode n)
    (produced : (align R choices 1 context term type type evidence).isSome = true) :
    producedAlignmentCode R choices 1 context term type type evidence produced = evidence := by
  unfold producedAlignmentCode
  apply Option.get_of_eq_some
  simp [align]

variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : Choices Head decoder.Code)

theorem alignment_produced_of_replay (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (term source target : Tm Head n) (evidence : Code Head decoder.Code n)
    (accepted : alignReplayAccepted R decoder choices fuel context term source target evidence = true) :
    (align R choices fuel context term source target evidence).isSome = true := by
  unfold alignReplayAccepted at accepted
  cases output : align R choices fuel context term source target evidence with
  | none => simp [output] at accepted
  | some code => rfl

theorem alignReplayAccepted_eq_produced_code (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (term source target : Tm Head n) (evidence : Code Head decoder.Code n)
    (produced : (align R choices fuel context term source target evidence).isSome = true) :
    alignReplayAccepted R decoder choices fuel context term source target evidence =
      StructuralTypingReplay.check R
        (fun code left right => code.check R.headEq decoder.decode left right)
        context term target
        (producedAlignmentCode R choices fuel context term source target evidence produced) := by
  unfold alignReplayAccepted
  rw [producedAlignmentCode_origin R choices fuel context term source target evidence produced]

#print axioms producedAlignmentCode_origin
#print axioms unchanged_alignment_retains_code
#print axioms zero_fuel_not_aligned
#print axioms alignment_produced_of_replay
#print axioms alignReplayAccepted_eq_produced_code

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
