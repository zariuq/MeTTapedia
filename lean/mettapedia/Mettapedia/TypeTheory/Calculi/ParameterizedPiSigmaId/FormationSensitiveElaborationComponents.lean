import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration

/-!
# Exact component observations of formation-sensitive elaboration

The existing producer and replay are unchanged. Their Boolean acceptance
factors into the independently produced and replayed telescope and term.
Telescope acceptance further factors over its actual declarations. These
equations allow finite evaluation proofs to share already checked components;
neither component alone establishes the full publication judgment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : Choices Head decoder.Code)

/-- The original term producer followed by the original term replay. Ambient
formation is a separate component of full elaboration acceptance. -/
def termReplayAccepted {n : Nat} (fuel : Nat) (ambient : Ctx Head n)
    (term type : Tm Head n) : Bool :=
  match check R choices fuel ambient term type with
  | none => false
  | some evidence => StructuralTypingReplay.check R
      (fun code left right => code.check R.headEq decoder.decode left right)
      ambient term type evidence

/-- The original telescope producer followed by its independent replay. -/
def contextReplayAccepted {n : Nat} (fuel : Nat) (ambient : Ctx Head n) : Bool :=
  match context R choices fuel ambient with
  | none => false
  | some evidence => StructuralTypingReplay.checkContext R
      (fun code left right => code.check R.headEq decoder.decode left right)
      ambient evidence

/-- One actual telescope entry, retaining its inferred universe policy and
formation replay. The producer receives the unchanged ambient telescope. -/
def formationReplayAccepted {n : Nat} (fuel : Nat) (ambient : Ctx Head n)
    (type : Tm Head n) : Bool :=
  match synth R choices fuel ambient type with
  | none => false
  | some inferred => match inferred.type with
      | .head level => decide (R.isUniverse level) && StructuralTypingReplay.check R
          (fun code left right => code.check R.headEq decoder.decode left right)
          ambient type (.head level) inferred.evidence
      | _ => false

private theorem guard_isSome {α : Type} (decision : Bool) (value : α) :
    (if decision = true then some value else none).isSome = decision := by
  cases decision <;> rfl

theorem elaborate_isSome_eq_components {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term type : Tm Head n) :
    (elaborate R decoder choices fuel ambient term type).isSome =
      (contextReplayAccepted R decoder choices fuel ambient &&
        termReplayAccepted R decoder choices fuel ambient term type) := by
  cases contextProduced : context R choices fuel ambient with
  | none => simp [elaborate, contextReplayAccepted, contextProduced]
  | some contextCode =>
      cases termProduced : check R choices fuel ambient term type with
      | none => simp [elaborate, contextReplayAccepted, termReplayAccepted,
          contextProduced, termProduced]
      | some termCode =>
          simp only [elaborate, contextProduced, termProduced, Option.bind_eq_bind,
            Option.bind_some, replay, StructuralTypingReplay.checkJudgment,
            contextReplayAccepted, termReplayAccepted]
          exact guard_isSome _ _

@[simp] theorem contextReplayAccepted_nil (fuel : Nat) :
    contextReplayAccepted R decoder choices fuel .nil = true := rfl

theorem contextReplayAccepted_snoc {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (type : Tm Head n) :
    contextReplayAccepted R decoder choices fuel (.snoc ambient type) =
      (contextReplayAccepted R decoder choices fuel ambient &&
        formationReplayAccepted R decoder choices fuel ambient type) := by
  cases prior : context R choices fuel ambient with
  | none => simp [contextReplayAccepted, context, prior]
  | some priorCode =>
      cases formed : synth R choices fuel ambient type with
      | none => simp [contextReplayAccepted, formationReplayAccepted, context, prior, formed]
      | some inferred =>
          rcases inferred with ⟨inferredType, evidence⟩
          cases inferredType <;> simp [contextReplayAccepted, formationReplayAccepted,
            context, prior, formed, StructuralTypingReplay.checkContext, Bool.and_assoc]

#print axioms elaborate_isSome_eq_components
#print axioms contextReplayAccepted_snoc

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
