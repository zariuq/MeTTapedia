/-
# Dynamic Pure corpus authentication

This module gives generated proof corpora the same trusted boundary as static
Pure examples.  A claim supplies only a prefix-coded goal and an ordered
refinement trace.  Authentication first parses the goal and then runs the
proved beta-eta refinement decoder; malformed syntax and failed traces are
rejected.
-/

import Mettapedia.GSLT.LanguageDef.Pure.BetaEtaAtomicRefinement
import Mettapedia.GSLT.LanguageDef.Pure.Encoding

namespace Mettapedia.GSLT.LanguageDef.PureCorpusAuthentication

open Lean
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement

/-- One dynamically supplied Pure proof claim. -/
structure Claim where
  id : String
  source : String
  goalCode : List Nat
  actions : List AtomicAction
  deriving Repr

/--
Parse the prefix-coded goal and reconstruct its beta-eta normal proof from the
ordered refinement trace.
-/
def reconstruct (claim : Claim) :
    Option (Mettapedia.GSLT.LanguageDef.Pure.Expr × Nf) := do
  let goal ← Mettapedia.GSLT.LanguageDef.Pure.Expr.decode claim.goalCode
  let term ← Mettapedia.GSLT.LanguageDef.PureBetaEtaRefinement.decode
    goal claim.actions
  pure (goal, term)

/-- A corpus claim is accepted exactly when reconstruction succeeds. -/
def accepted (claim : Claim) : Bool :=
  (reconstruct claim).isSome

/-- Every accepted dynamic corpus claim has a checked beta-eta typing witness. -/
theorem reconstruct_sound
    {claim : Claim}
    {goal : Mettapedia.GSLT.LanguageDef.Pure.Expr} {term : Nf}
    (hreconstruct : reconstruct claim = some (goal, term)) :
    ∃ inferred,
      Mettapedia.GSLT.LanguageDef.PureBetaEtaRefinement.HasType [] term inferred ∧
      Mettapedia.GSLT.LanguageDef.PureBetaEta.Conv inferred goal := by
  unfold reconstruct at hreconstruct
  cases hgoal : Mettapedia.GSLT.LanguageDef.Pure.Expr.decode claim.goalCode with
  | none =>
      simp [hgoal] at hreconstruct
  | some decodedGoal =>
      simp only [hgoal] at hreconstruct
      cases hterm :
          Mettapedia.GSLT.LanguageDef.PureBetaEtaRefinement.decode
            decodedGoal claim.actions with
      | none =>
          simp [hterm] at hreconstruct
      | some decodedTerm =>
          simp [hterm] at hreconstruct
          rcases hreconstruct with ⟨rfl, rfl⟩
          exact
            Mettapedia.GSLT.LanguageDef.PureBetaEtaRefinement.decode_sound hterm

/-- Successful reconstruction is equivalent to the executable acceptance bit. -/
theorem accepted_eq_true_iff (claim : Claim) :
    accepted claim = true ↔
      ∃ goal term, reconstruct claim = some (goal, term) := by
  simp [accepted, Option.isSome_iff_exists]

private def parseStringField (json : Lean.Json) (field : String) :
    Except String String :=
  json.getObjVal? field >>= Json.getStr?

private def parseNatField (json : Lean.Json) (field : String) :
    Except String Nat :=
  json.getObjVal? field >>= Json.getNat?

private def parseNatArray (json : Lean.Json) (field : String) :
    Except String (List Nat) := do
  let values ← json.getObjVal? field >>= Json.getArr?
  values.toList.mapM Json.getNat?

private def parseAction (json : Lean.Json) : Except String AtomicAction := do
  let kind ← parseStringField json "kind"
  if kind != "refine" then
    throw s!"unsupported action kind: {kind}"
  pure ⟨← parseNatField json "hole", ← parseNatField json "head"⟩

/-- Parse the common JSON fields emitted by authenticated corpus builders. -/
def parseClaimJson (source : String) (json : Lean.Json) : Except String Claim := do
  let id ← parseStringField json "id"
  let goalCode ← parseNatArray json "goal_code"
  let actionJson ← json.getObjVal? "actions" >>= Json.getArr?
  let actions ← actionJson.toList.mapM parseAction
  pure { id, source, goalCode, actions }

/-- Parse one JSON line and reject malformed input before reconstruction. -/
def parseClaimLine (source line : String) : Except String Claim := do
  let json ← Lean.Json.parse line
  parseClaimJson source json

def identityGoal : Mettapedia.GSLT.LanguageDef.Pure.Expr := .pi .sort .sort

def identityTerm : Nf := .lam .sort (.head 0 [])

def identityClaim : Claim where
  id := "positive.identity"
  source := "fixture"
  goalCode := identityGoal.encode
  actions := [⟨0, 0⟩]

def shiftedHeadClaim : Claim where
  id := "negative.shifted-head"
  source := "fixture"
  goalCode := identityGoal.encode
  actions := [⟨0, 1⟩]

def malformedGoalClaim : Claim where
  id := "negative.malformed-goal"
  source := "fixture"
  goalCode := [2, 0]
  actions := [⟨0, 0⟩]

example : reconstruct identityClaim = some (identityGoal, identityTerm) := by
  rfl

example : accepted identityClaim = true := by rfl

example : reconstruct shiftedHeadClaim = none := by rfl

example : accepted shiftedHeadClaim = false := by rfl

example : reconstruct malformedGoalClaim = none := by rfl

end Mettapedia.GSLT.LanguageDef.PureCorpusAuthentication
