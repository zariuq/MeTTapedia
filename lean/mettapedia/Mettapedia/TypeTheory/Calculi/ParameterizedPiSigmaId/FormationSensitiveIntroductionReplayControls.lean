import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveIntroductionReplay

/-!
# Generic introduction replay boundaries

Exhausted production refuses both introduction forms. In an arbitrary open
context, variable checking produces the original variable code and that same
code replays at the actual lookup type. These are term observations; ambient
context formation remains a separate publication gate.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
namespace IntroductionReplayControls

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : Choices Head decoder.Code)

theorem zero_fuel_lambda_refused {n : Nat} (context : Ctx Head n)
    (body : Tm Head (n+1)) (expected : Tm Head n) :
    termReplayAccepted R decoder choices 0 context (.lam body) expected = false := rfl

theorem zero_fuel_pair_refused {n : Nat} (context : Ctx Head n)
    (first second expected : Tm Head n) :
    termReplayAccepted R decoder choices 0 context (.pair first second) expected = false := rfl

omit [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq] in
theorem variable_origin {n : Nat} (context : Ctx Head n) (index : Fin n) :
    check R choices 3 context (.var index) (Ctx.lookup context index) =
      some (.var : Code Head decoder.Code n) := by
  cases choices.normalize 2 (Ctx.lookup context index) <;> simp [check, synth, align]

theorem variable_replay {n : Nat} (context : Ctx Head n) (index : Fin n) :
    StructuralTypingReplay.check R
      (fun code left right => code.check R.headEq decoder.decode left right)
      context (.var index) (Ctx.lookup context index) (.var : Code Head decoder.Code n) = true := by
  simp [StructuralTypingReplay.check]

theorem variable_accepted {n : Nat} (context : Ctx Head n) (index : Fin n) :
    termReplayAccepted R decoder choices 3 context (.var index) (Ctx.lookup context index) = true := by
  unfold termReplayAccepted
  rw [variable_origin R decoder choices context index]
  exact variable_replay R decoder context index

#print axioms zero_fuel_lambda_refused
#print axioms zero_fuel_pair_refused
#print axioms variable_origin
#print axioms variable_replay
#print axioms variable_accepted
end IntroductionReplayControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
