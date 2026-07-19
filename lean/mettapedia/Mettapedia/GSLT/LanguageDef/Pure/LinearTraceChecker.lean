/-
# Linear authentication for supplied Pure atomic traces

External authentication already carries a complete candidate trace.  Replaying
that trace is therefore the completion witness; the checker must not rediscover
the same suffix by exponential bounded search at every prefix.  This module
uses the raw deterministic elaborator, preserves effect attestations and the
atomic budget, and proves that every accepted result satisfies `AtomicAccepted`.
-/

import Mettapedia.GSLT.LanguageDef.Pure.AtomicFixtures

namespace Mettapedia.GSLT.LanguageDef.PureLinearTraceChecker

open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureAtomicFixtures
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureRefinement

structure ReplayResult where
  state : State
  completed : Bool
  firstRejectedAt : Option Nat
  deriving Repr

private def effectClaimMatches (core : Core) (action : AtomicAction) :
    Option Nat → Bool
  | none => true
  | some claimed => computedSpineLength? core action == some claimed

def replayFrom (goal : Expr) :
    List AtomicAction → List (Option Nat) → State → Nat → ReplayResult
  | [], [], state, _ => ⟨state, true, none⟩
  | action :: rest, claim :: claims, state, index =>
      if !effectClaimMatches state.core action claim then
        ⟨state, false, some index⟩
      else
        match rawRefine? goal state.core action with
        | none => ⟨state, false, some index⟩
        | some next =>
            replayFrom goal rest claims
              { core := next
                tokensEmitted := state.tokensEmitted + 3
                maxLen := state.maxLen }
              (index + 1)
  | _, _, state, index => ⟨state, false, some index⟩

def replay (goal : Expr) (maxRefinements : Nat) (translation : Translation) :
    ReplayResult :=
  if translation.actions.length ≤ maxRefinements then
    replayFrom goal translation.actions translation.claimedSpineLengths
      (atomicInitial goal maxRefinements) 0
  else
    ⟨atomicInitial goal maxRefinements, false, some maxRefinements⟩

def accepted (goal : Expr) (maxRefinements : Nat)
    (translation : Translation) : Bool :=
  let result := replay goal maxRefinements translation
  result.completed && translation.claimedTerminal &&
    decide (coreTerminal goal result.state.core)

def firstRejectedAt (goal : Expr) (maxRefinements : Nat)
    (translation : Translation) : Option Nat :=
  let result := replay goal maxRefinements translation
  match result.firstRejectedAt with
  | some index => some index
  | none =>
      if result.completed && translation.claimedTerminal &&
          decide (coreTerminal goal result.state.core) then
        none
      else
        some translation.actions.length

theorem replayFrom_completed_rawRunAtomic (goal : Expr) :
    ∀ (actions : List AtomicAction) (claims : List (Option Nat))
      (state : State) (index : Nat),
      (replayFrom goal actions claims state index).completed = true →
        rawRunAtomic goal actions state.core =
          some (replayFrom goal actions claims state index).state.core
  | [], [], state, index, _ => by simp [replayFrom, rawRunAtomic]
  | [], _ :: _, state, index, hcompleted => by
      simp [replayFrom] at hcompleted
  | _ :: _, [], state, index, hcompleted => by
      simp [replayFrom] at hcompleted
  | action :: rest, claim :: claims, state, index, hcompleted => by
      by_cases hclaim : effectClaimMatches state.core action claim
      · cases hraw : rawRefine? goal state.core action with
        | none => simp [replayFrom, hclaim, hraw] at hcompleted
        | some next =>
            simp only [replayFrom, hclaim, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, hraw, rawRunAtomic]
            simp only [replayFrom, hclaim, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, hraw] at hcompleted
            exact replayFrom_completed_rawRunAtomic goal rest claims
              { core := next
                tokensEmitted := state.tokensEmitted + 3
                maxLen := state.maxLen }
              (index + 1) hcompleted
      · simp [replayFrom, hclaim] at hcompleted

theorem replay_completed_rawRunAtomic {goal : Expr} {maxRefinements : Nat}
    {translation : Translation}
    (hcompleted : (replay goal maxRefinements translation).completed = true) :
    rawRunAtomic goal translation.actions (prepare 0 [] goal []) =
      some (replay goal maxRefinements translation).state.core := by
  unfold replay at hcompleted ⊢
  by_cases hbudget : translation.actions.length ≤ maxRefinements
  · simp only [hbudget, ↓reduceIte] at hcompleted ⊢
    exact replayFrom_completed_rawRunAtomic goal _ _ _ _ hcompleted
  · simp [hbudget] at hcompleted

/-- Linear acceptance is a sound executable decision for raw atomic acceptance. -/
theorem accepted_sound {goal : Expr} {maxRefinements : Nat}
    {translation : Translation}
    (haccepted : accepted goal maxRefinements translation = true) :
    AtomicAccepted goal translation.actions := by
  unfold accepted at haccepted
  simp only [Bool.and_eq_true] at haccepted
  have hrun := replay_completed_rawRunAtomic (goal := goal)
    (maxRefinements := maxRefinements) (translation := translation)
    haccepted.1.1
  have hterminal : coreTerminal goal
      (replay goal maxRefinements translation).state.core := by
    exact of_decide_eq_true haccepted.2
  generalize hcore :
      (replay goal maxRefinements translation).state.core = core at hrun hterminal
  cases core with
  | done term =>
      exact ⟨term, hrun, by simpa [coreTerminal] using hterminal⟩
  | needHole holeId context target frames => simp [coreTerminal] at hterminal
  | needHead holeId context target frames => simp [coreTerminal] at hterminal
  | needSpine holeId context target frames head headType =>
      simp [coreTerminal] at hterminal
  | finished term => simp [coreTerminal] at hterminal

example : accepted PureRefinement.identityGoal 1
    ⟨[⟨0, 0⟩], [some 0], true⟩ = true := by
  decide

example : accepted PureRefinement.identityGoal 1
    ⟨[⟨0, 99⟩], [none], true⟩ = false := by
  decide

#print axioms accepted_sound

end Mettapedia.GSLT.LanguageDef.PureLinearTraceChecker
