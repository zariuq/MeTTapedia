/-
# Linear authentication for Pure beta-conversion atomic traces

Supplied traces are replayed once through the deterministic beta-aware
elaborator.  The result records whether failure was ordinary rejection, an
effect-claim mismatch, or conversion-fuel exhaustion.
-/

import Mettapedia.GSLT.LanguageDef.Pure.AtomicFixtures
import Mettapedia.GSLT.LanguageDef.Pure.BetaAtomicRefinement

namespace Mettapedia.GSLT.LanguageDef.PureBetaLinearTraceChecker

open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureRefinement
open Mettapedia.GSLT.LanguageDef.PureAtomicFixtures
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement

inductive ReplayStatus where
  | completed
  | effectClaimMismatch
  | actionRejected
  | conversionFuelExhausted
  | malformedClaim
  | budgetExceeded
  deriving DecidableEq, Repr

structure ReplayResult where
  state : State
  status : ReplayStatus
  firstRejectedAt : Option Nat
  deriving Repr

private def effectClaimMatches (core : Core) (action : AtomicAction) :
    Option Nat → Bool
  | none => true
  | some claimed => computedSpineLength? core action == some claimed

def replayFrom :
    List AtomicAction → List (Option Nat) → State → Nat → ReplayResult
  | [], [], state, _ => ⟨state, .completed, none⟩
  | action :: rest, claim :: claims, state, index =>
      if !effectClaimMatches state.core action claim then
        ⟨state, .effectClaimMismatch, some index⟩
      else
        match rawRefineResult state.core action with
        | .rejected => ⟨state, .actionRejected, some index⟩
        | .conversionFuelExhausted =>
            ⟨state, .conversionFuelExhausted, some index⟩
        | .ok next =>
            replayFrom rest claims
              { core := next
                tokensEmitted := state.tokensEmitted + 3
                maxLen := state.maxLen }
              (index + 1)
  | _, _, state, index => ⟨state, .malformedClaim, some index⟩

def replay (goal : Expr) (maxRefinements : Nat) (translation : Translation) :
    ReplayResult :=
  if translation.actions.length ≤ maxRefinements then
    replayFrom translation.actions translation.claimedSpineLengths
      (atomicInitial goal maxRefinements) 0
  else
    ⟨atomicInitial goal maxRefinements, .budgetExceeded, some maxRefinements⟩

def accepted (goal : Expr) (maxRefinements : Nat)
    (translation : Translation) : Bool :=
  let result := replay goal maxRefinements translation
  decide (result.status = .completed) && translation.claimedTerminal &&
    (terminalResult goal result.state.core).isOk

def firstRejectedAt (goal : Expr) (maxRefinements : Nat)
    (translation : Translation) : Option Nat :=
  let result := replay goal maxRefinements translation
  match result.firstRejectedAt with
  | some index => some index
  | none =>
      if accepted goal maxRefinements translation then none
      else some translation.actions.length

theorem replayFrom_completed_rawRunResult :
    ∀ (actions : List AtomicAction) (claims : List (Option Nat))
      (state : State) (index : Nat),
      (replayFrom actions claims state index).status = .completed →
        rawRunResult actions state.core =
          .ok (replayFrom actions claims state index).state.core
  | [], [], state, index, _ => by simp [replayFrom, rawRunResult]
  | [], _ :: _, state, index, hcompleted => by
      simp [replayFrom] at hcompleted
  | _ :: _, [], state, index, hcompleted => by
      simp [replayFrom] at hcompleted
  | action :: rest, claim :: claims, state, index, hcompleted => by
      by_cases hclaim : effectClaimMatches state.core action claim
      · cases hraw : rawRefineResult state.core action with
        | rejected => simp [replayFrom, hclaim, hraw] at hcompleted
        | conversionFuelExhausted =>
            simp [replayFrom, hclaim, hraw] at hcompleted
        | ok next =>
            simp only [replayFrom, hclaim, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, hraw, rawRunResult]
            simp only [replayFrom, hclaim, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, hraw] at hcompleted
            exact replayFrom_completed_rawRunResult rest claims
              { core := next
                tokensEmitted := state.tokensEmitted + 3
                maxLen := state.maxLen }
              (index + 1) hcompleted
      · simp [replayFrom, hclaim] at hcompleted

theorem replay_completed_rawRunResult {goal : Expr} {maxRefinements : Nat}
    {translation : Translation}
    (hcompleted : (replay goal maxRefinements translation).status = .completed) :
    rawRunResult translation.actions (prepare 0 [] goal []) =
      .ok (replay goal maxRefinements translation).state.core := by
  unfold replay at hcompleted ⊢
  by_cases hbudget : translation.actions.length ≤ maxRefinements
  · simp only [hbudget, ↓reduceIte] at hcompleted ⊢
    exact replayFrom_completed_rawRunResult _ _ _ _ hcompleted
  · simp [hbudget] at hcompleted

/-- Linear beta acceptance produces the same successful result as root decoding. -/
theorem accepted_decodeResult {goal : Expr} {maxRefinements : Nat}
    {translation : Translation}
    (haccepted : accepted goal maxRefinements translation = true) :
    ∃ term, decodeResult goal translation.actions = .ok term := by
  unfold accepted at haccepted
  simp only [Bool.and_eq_true] at haccepted
  have hcompleted :
      (replay goal maxRefinements translation).status = .completed :=
    of_decide_eq_true haccepted.1.1
  have hrun := replay_completed_rawRunResult hcompleted
  cases hterminal : terminalResult goal
      (replay goal maxRefinements translation).state.core with
  | rejected =>
      have himpossible := haccepted.2
      rw [hterminal] at himpossible
      contradiction
  | conversionFuelExhausted =>
      have himpossible := haccepted.2
      rw [hterminal] at himpossible
      contradiction
  | ok term =>
      refine ⟨term, ?_⟩
      simp [decodeResult, hrun, hterminal]

/-- Every linearly accepted trace checks in the declarative beta statics. -/
theorem accepted_sound {goal : Expr} {maxRefinements : Nat}
    {translation : Translation}
    (haccepted : accepted goal maxRefinements translation = true) :
    ∃ term,
      Mettapedia.GSLT.LanguageDef.PureBeta.HasType [] term goal := by
  rcases accepted_decodeResult haccepted with ⟨term, hdecode⟩
  exact ⟨term, decodeResult_sound hdecode⟩

example : accepted PureRefinement.identityGoal 1
    ⟨[⟨0, 0⟩], [some 0], true⟩ = true := by decide

example : accepted PureRefinement.identityGoal 1
    ⟨[⟨0, 99⟩], [none], true⟩ = false := by decide

#print axioms replay_completed_rawRunResult
#print axioms accepted_decodeResult
#print axioms accepted_sound

end Mettapedia.GSLT.LanguageDef.PureBetaLinearTraceChecker
