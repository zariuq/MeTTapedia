import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mathlib.Tactic

/-! Exact frame properties of successful protocol instructions. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolFrame

theorem execute_preserves_phase {before after : State} (instruction : Instr)
    (accepted : execute before instruction = some (.ok after)) : after.phase = before.phase := by
  cases instruction
  case fvarNew arity destination =>
    by_cases occupied : (before.symbols destination).isSome = true
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
      cases accepted
      rfl
  case constNew binders destination =>
    by_cases occupied : (before.symbols destination).isSome = true
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
      cases accepted
      rfl
  all_goals
    simp only [execute, State.allocate, State.placeSymbol, State.placeTerm, State.placeTheorem,
      State.placeChallenge, State.inProofs, need, bind, Except.bind, pure, Except.pure,
      Option.some.injEq] at accepted
  all_goals repeat' split at accepted
  all_goals cases accepted <;> simp_all
  all_goals try (split_ifs at * <;> simp_all)
  all_goals subst_vars
  all_goals try (split_ifs at * <;> simp_all)
  all_goals (subst_vars; rfl)

def changesChallenges : Instr → Bool
  | .challengeAdd _ _ | .challengeSatisfy _ _ => true
  | _ => false

structure ChallengeFrame (before after : State) : Prop where
  phase : after.phase = before.phase
  slots : after.challenges = before.challenges
  openCount : after.openChallenges = before.openChallenges
  setupCount : after.setupChallenges = before.setupChallenges
  proofCount : after.proofChallenges = before.proofChallenges
  satisfied : after.satisfied = before.satisfied

theorem execute_challenge_frame {before after : State} (instruction : Instr)
    (maintenance : changesChallenges instruction = false)
    (accepted : execute before instruction = some (.ok after)) : ChallengeFrame before after := by
  cases instruction
  case fvarNew arity destination =>
    by_cases occupied : (before.symbols destination).isSome = true
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
      cases accepted
      constructor <;> rfl
  case constNew binders destination =>
    by_cases occupied : (before.symbols destination).isSome = true
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
    · simp [execute, State.allocate, State.placeSymbol, occupied] at accepted
      cases accepted
      constructor <;> rfl
  all_goals
    simp only [changesChallenges] at maintenance
  all_goals try cases maintenance
  all_goals
    simp only [execute, State.allocate, State.placeSymbol, State.placeTerm, State.placeTheorem,
      State.inProofs, need, bind, Except.bind, pure, Except.pure,
      Option.some.injEq] at accepted
  all_goals repeat' split at accepted
  all_goals cases accepted
  all_goals constructor <;> simp_all
  all_goals try (split_ifs at * <;> simp_all)
  all_goals subst_vars
  all_goals try (split_ifs at * <;> simp_all)
  all_goals (subst_vars; rfl)

end Mettapedia.Languages.VibeITP.Spec.ProtocolFrame
