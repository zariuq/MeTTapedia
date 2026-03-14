import Algorithms.MeTTa.Simple.Session

/-!
# SessionReferenceTotal — Unconditionally Verified Reference Evaluator

This module exposes the fuel-indexed N-kernel as a public, unconditionally verified
reference backend.  Unlike `SessionReference.evalWithStateCore` (which delegates to
the live `partial def intrinsicStateful` and needs an external `hIntrinsicPres`
hypothesis), the functions here are `def`, not `partial def`, and their
WF-preservation theorems hold unconditionally.

## Coverage note

`totalIntrinsicStateful` covers the branches currently implemented in the N-kernel,
including the generic `.apply ctor args` branch and the explicit `case` / `foldall` /
`forall` control-flow heads. Terms that still miss a corresponding intrinsic case
fall through to `none`, so the total reference backend remains conservative:
it may return `none` where the live runtime returns `some`, but it does not invent
unsupported successful results.
-/

namespace Algorithms.MeTTa.Simple.Backend.SessionReferenceTotal

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

abbrev SessionWF : Session → Prop := Session.WF

/-- Fuel-indexed total reference intrinsic evaluator.
    Returns `none` when the term is not a handled intrinsic or fuel is exhausted.
    Terminates by fuel — no `partial def`, no `sorry`. -/
abbrev totalIntrinsicStateful := Session.intrinsicStatefulN

/-- Fuel-indexed total reference evaluator.
    Terminates by fuel — no `partial def`, no `sorry`. -/
abbrev totalEvalWithStateCore := Session.evalWithStateCoreN

/-- Default fuel policy for the total reference backend.
    Same formula as `Session.referenceProofFuel`. -/
def referenceFuel (s : Session) : Nat :=
  Session.referenceProofFuel s

/-- Public theorem-bearing total reference intrinsic evaluator. -/
def intrinsicStateful (s : Session) (term : Pattern) : Option (Session × List Pattern) :=
  totalIntrinsicStateful (referenceFuel s) s term

/-- Public theorem-bearing total reference evaluator. -/
def evalWithStateCore (s : Session) (term : Pattern) : Session × List Pattern :=
  totalEvalWithStateCore (referenceFuel s) s term

/-- Unconditional session-WF preservation for `totalEvalWithStateCore`. -/
theorem totalEvalWithStateCore_preserves
    (fuel : Nat) (s : Session) (term : Pattern)
    (hs : SessionWF s) :
    SessionWF (totalEvalWithStateCore fuel s term).1 :=
  Session.evalWithStateCoreN_preserves fuel s term hs

/-- Unconditional session-WF preservation for `totalIntrinsicStateful` on `some` results. -/
theorem totalIntrinsicStateful_preserves
    (fuel : Nat) {s : Session} {term : Pattern}
    {s' : Session} {out : List Pattern}
    (h : totalIntrinsicStateful fuel s term = some (s', out))
    (hs : SessionWF s) :
    SessionWF s' :=
  Session.intrinsicStatefulN_preserves fuel h hs

/-- Unconditional session-WF preservation for the public total reference evaluator. -/
theorem evalWithStateCore_preserves
    (s : Session) (term : Pattern)
    (hs : SessionWF s) :
    SessionWF (evalWithStateCore s term).1 := by
  unfold evalWithStateCore referenceFuel
  exact totalEvalWithStateCore_preserves _ _ _ hs

/-- Unconditional session-WF preservation for the public total reference intrinsic evaluator. -/
theorem intrinsicStateful_preserves
    {s : Session} {term : Pattern}
    {s' : Session} {out : List Pattern}
    (h : intrinsicStateful s term = some (s', out))
    (hs : SessionWF s) :
    SessionWF s' := by
  unfold intrinsicStateful referenceFuel at h
  exact totalIntrinsicStateful_preserves
    (fuel := referenceFuel s) (s := s) (term := term) (s' := s') (out := out) h hs

end Algorithms.MeTTa.Simple.Backend.SessionReferenceTotal
