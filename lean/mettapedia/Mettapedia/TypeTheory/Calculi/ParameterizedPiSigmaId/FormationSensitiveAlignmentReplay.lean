import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints

/-!
# Exact replay factorization for an alignment continuation

The original alignment producer and its independent checker are unchanged.
Their acceptance factors into the original source-evidence check and a guard
that retains target formation, universe policy, cumulative policy and the
actual conversion-code check. The guard is independent of the input evidence;
it can therefore be checked once while retaining the original source code.
This equation assumes no validity of the search choices.
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

def alignReplayAccepted (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (term source target : Tm Head n) (evidence : Code Head decoder.Code n) : Bool :=
  match align R choices fuel context term source target evidence with
  | none => false
  | some aligned => StructuralTypingReplay.check R
      (fun code left right => code.check R.headEq decoder.decode left right)
      context term target aligned

def conversionReplayAccepted (fuel : Nat) {n : Nat} (source target : Tm Head n) : Bool :=
  match choices.conversion fuel source target with
  | none => false
  | some conversion => conversion.check R.headEq decoder.decode source target

def alignReplayGuard : Nat → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Bool
  | 0, _, _, _, _ => false
  | fuel+1, _, context, source, target =>
    if source = target then true else
      let cumulative := match source,target with
        | .head first,.head second =>
          if choices.cumulative first second then some (decide (R.cumulative first second)) else none
        | _,_ => none
      match cumulative with
      | some permitted => permitted
      | none => match synth R choices fuel context target with
        | none => false
        | some formation => match formation.type with
          | .head level => decide (R.isUniverse level) &&
            StructuralTypingReplay.check R
              (fun code left right => code.check R.headEq decoder.decode left right)
              context target (.head level) formation.evidence &&
            conversionReplayAccepted R decoder choices fuel source target
          | _ => false

theorem align_replay_factor (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (term source target : Tm Head n) (evidence : Code Head decoder.Code n) :
    alignReplayAccepted R decoder choices fuel context term source target evidence =
      (StructuralTypingReplay.check R
        (fun code left right => code.check R.headEq decoder.decode left right)
        context term source evidence && alignReplayGuard R decoder choices fuel context source target) := by
  unfold alignReplayAccepted
  cases fuel with
  | zero => simp [align,alignReplayGuard]
  | succ fuel =>
    have fallback :
        (match (do
            let formation ← synth R choices fuel context target
            match formation.type with
            | .head level => do
              let conversion ← choices.conversion fuel source target
              pure (StructuralTypingReplay.Code.convert source level evidence formation.evidence conversion)
            | _ => none) with
          | none => false
          | some aligned => StructuralTypingReplay.check R
              (fun code left right => code.check R.headEq decoder.decode left right)
              context term target aligned) =
          (StructuralTypingReplay.check R
            (fun code left right => code.check R.headEq decoder.decode left right)
            context term source evidence &&
          (match synth R choices fuel context target with
            | none => false
            | some formation => match formation.type with
              | .head level => decide (R.isUniverse level) &&
                StructuralTypingReplay.check R
                  (fun code left right => code.check R.headEq decoder.decode left right)
                  context target (.head level) formation.evidence &&
                conversionReplayAccepted R decoder choices fuel source target
              | _ => false)) := by
      cases produced : synth R choices fuel context target with
      | none => simp
      | some formation =>
        rcases formation with ⟨type,code⟩
        cases type <;> simp only [Option.bind_eq_bind,Option.bind_some,Bool.and_false]
        case head level =>
          cases converted : choices.conversion fuel source target <;>
            simp [conversionReplayAccepted,converted,StructuralTypingReplay.check,Bool.and_comm,Bool.and_left_comm]
    by_cases same : source = target
    · simp [align,alignReplayGuard,same]
    · cases source <;> cases target <;>
        simp only [align,alignReplayGuard,same,if_false]
      all_goals try exact fallback
      all_goals
        split_ifs <;> simp only [*]
      all_goals first
        | exact fallback
        | simp [StructuralTypingReplay.check]

#print axioms align_replay_factor

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
