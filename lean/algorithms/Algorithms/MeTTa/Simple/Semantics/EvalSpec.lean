import Algorithms.MeTTa.Simple.Session

/-! QUARANTINED: Original constant-state evaluation spec.
Determinism theorem is real but covers only step?-based evaluation,
not the controlEval? architecture used by the actual evaluator. -/

namespace Algorithms.MeTTa.Simple.Semantics.EvalSpec

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

/-! # Inductive Operational Semantics for MeTTa

The canonical multi-step evaluation relation, built on `Session.step`.

`step` is a computable function, so evaluation is deterministic.
Any two correct implementations must produce the same results.

Session state `s` is constant (valid for safe branches).
-/

mutual
  /-- Multi-step evaluation with bounded fuel. -/
  inductive EvaluatesN (s : Session) : Nat → Pattern → List Pattern → Prop
    | normal (term : Pattern) (fuel : Nat)
        (hStep : Session.step s term = []) :
        EvaluatesN s fuel term [term]
    | reduce (term : Pattern) (fuel : Nat) (reducts results : List Pattern)
        (hStep : Session.step s term = reducts)
        (hReducts : reducts ≠ [])
        (hResults : EvaluatesAllN s fuel reducts results) :
        EvaluatesN s (fuel + 1) term results

  /-- Evaluate a list of terms, concatenating results. -/
  inductive EvaluatesAllN (s : Session) : Nat → List Pattern → List Pattern → Prop
    | nil (fuel : Nat) :
        EvaluatesAllN s fuel [] []
    | cons (fuel : Nat) (term : Pattern) (rest termResults restResults : List Pattern)
        (hTerm : EvaluatesN s fuel term termResults)
        (hRest : EvaluatesAllN s fuel rest restResults) :
        EvaluatesAllN s fuel (term :: rest) (termResults ++ restResults)
end

-- ─── Determinism ──────────────────────────────────────────────────────────

mutual
  theorem evaluatesN_deterministic {s : Session} {fuel : Nat} {term : Pattern}
      {r1 r2 : List Pattern}
      (h1 : EvaluatesN s fuel term r1) (h2 : EvaluatesN s fuel term r2) :
      r1 = r2 := by
    cases h1 with
    | normal _ _ hStep1 =>
      cases h2 with
      | normal _ _ _ => rfl
      | reduce _ _ reducts2 _ hStep2 hReducts2 _ =>
        rw [hStep1] at hStep2; exact absurd hStep2.symm (by simpa using hReducts2)
    | reduce _ _ reducts1 results1 hStep1 hReducts1 hResults1 =>
      cases h2 with
      | normal _ _ hStep2 =>
        rw [hStep2] at hStep1; exact absurd hStep1 (by simpa using hReducts1)
      | reduce _ _ reducts2 results2 hStep2 _hReducts2 hResults2 =>
        have hEq : reducts1 = reducts2 := by rw [← hStep1, hStep2]
        subst hEq
        exact evaluatesAllN_deterministic hResults1 hResults2

  theorem evaluatesAllN_deterministic {s : Session} {fuel : Nat} {terms : List Pattern}
      {r1 r2 : List Pattern}
      (h1 : EvaluatesAllN s fuel terms r1) (h2 : EvaluatesAllN s fuel terms r2) :
      r1 = r2 := by
    cases h1 with
    | nil _ =>
      cases h2 with | nil _ => rfl
    | cons _ term rest termR1 restR1 hTerm1 hRest1 =>
      cases h2 with
      | cons _ _ _ termR2 restR2 hTerm2 hRest2 =>
        have hEqTerm := evaluatesN_deterministic hTerm1 hTerm2
        have hEqRest := evaluatesAllN_deterministic hRest1 hRest2
        subst hEqTerm; subst hEqRest; rfl
end

-- ─── Fuel monotonicity ───────────────────────────────────────────────────

mutual
  theorem evaluatesN_fuel_mono {s : Session} {fuel : Nat} {term : Pattern} {results : List Pattern}
      (h : EvaluatesN s fuel term results) (fuel' : Nat) (hGe : fuel' ≥ fuel) :
      EvaluatesN s fuel' term results := by
    cases h with
    | normal _ _ hStep => exact .normal _ fuel' hStep
    | reduce _ _ reducts _ hStep hReducts hResults =>
      obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
      exact .reduce _ m reducts _ hStep hReducts
        (evaluatesAllN_fuel_mono hResults m (by omega))

  theorem evaluatesAllN_fuel_mono {s : Session} {fuel : Nat} {terms results : List Pattern}
      (h : EvaluatesAllN s fuel terms results) (fuel' : Nat) (hGe : fuel' ≥ fuel) :
      EvaluatesAllN s fuel' terms results := by
    cases h with
    | nil _ => exact .nil fuel'
    | cons _ _ _ termR restR hTerm hRest =>
      exact .cons fuel' _ _ termR restR
        (evaluatesN_fuel_mono hTerm fuel' hGe)
        (evaluatesAllN_fuel_mono hRest fuel' hGe)
end

-- ─── Unbounded evaluation ────────────────────────────────────────────────

def Evaluates (s : Session) (term : Pattern) (results : List Pattern) : Prop :=
  ∃ fuel, EvaluatesN s fuel term results

theorem evaluates_deterministic {s : Session} {term : Pattern} {r1 r2 : List Pattern}
    (h1 : Evaluates s term r1) (h2 : Evaluates s term r2) :
    r1 = r2 := by
  obtain ⟨f1, hf1⟩ := h1
  obtain ⟨f2, hf2⟩ := h2
  exact evaluatesN_deterministic
    (evaluatesN_fuel_mono hf1 (max f1 f2) (Nat.le_max_left _ _))
    (evaluatesN_fuel_mono hf2 (max f1 f2) (Nat.le_max_right _ _))

-- ─── One-step lemmas ─────────────────────────────────────────────────────

theorem evaluatesN_normal (s : Session) (fuel : Nat) (term : Pattern)
    (hStep : Session.step s term = []) :
    EvaluatesN s fuel term [term] :=
  .normal term fuel hStep

theorem evaluatesN_singleton_step (s : Session) (fuel : Nat) (term result : Pattern)
    (results : List Pattern)
    (hStep : Session.step s term = [result])
    (hResult : EvaluatesN s fuel result results) :
    EvaluatesN s (fuel + 1) term results := by
  have hAll : EvaluatesAllN s fuel [result] (results ++ []) :=
    .cons fuel result [] results [] hResult (.nil fuel)
  simp at hAll
  exact .reduce term fuel [result] results hStep (by simp) hAll

end Algorithms.MeTTa.Simple.Semantics.EvalSpec
