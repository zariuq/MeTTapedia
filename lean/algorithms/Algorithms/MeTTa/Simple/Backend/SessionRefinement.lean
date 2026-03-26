import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Backend.SessionReference

/-! QUARANTINED: FastPathEq/AgreementOn transport layer.
hAgreeRaw was confirmed false (truth audit 2026-03-17).
Pointwise FastPathEq is honest but uninhabited — no theorem instantiates it. -/

namespace Algorithms.MeTTa.Simple.Backend.SessionRefinement

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

abbrev SessionWF : Session → Prop := SessionReference.SessionWF

-- ─── Pointwise fast-path equality ─────────────────────────────────────────
-- The minimal hypothesis the transport layer needs: the optimized evaluator
-- agrees with the reference evaluator FOR THIS SPECIFIC (s, term).
-- The transport layer does not care WHERE this equality came from.
--
-- Former `hAgreeRaw` (global ∀-quantified) was confirmed false (truth audit
-- 2026-03-17, 3rd falsity vector: translateCall + reducible args overlap).

abbrev FastPathEq (s : Session) (term : Pattern) : Prop :=
  Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
    Session.optimizedBackendInterface s term =
  SessionReference.evalWithStateCore s term

-- ─── Predicate-parametric agreement ───────────────────────────────────────
-- For convenience wrappers that quantify over a predicate (e.g., SupportedDeterministic).

def AgreementOn (P : Session → Pattern → Prop) : Prop :=
  ∀ ⦃s : Session⦄ ⦃term : Pattern⦄, P s term → FastPathEq s term

-- ─── Core transport: equality ─────────────────────────────────────────────

/-- evalWithState = SessionReference.evalWithStateCore, given pointwise FastPathEq. -/
theorem evalWithState_eq_reference
    (s : Session) (term : Pattern)
    (hEq : FastPathEq s term) :
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
  -- evalWithState s term = OptimizedEval.evalWithState OBI s term (by rfl)
  -- FastPathEq says OptimizedEval.evalWithState OBI s term = SessionReference.evalWithStateCore s term
  rw [Session.evalWithState_eq_optimizedBackend]
  exact hEq

-- ─── Core transport: WF preservation ──────────────────────────────────────

/-- evalWithState preserves SessionWF, given pointwise FastPathEq. -/
theorem wf_evalWithState
    (hCorePres :
      ∀ (s : Session) (term : Pattern),
        SessionWF s →
        SessionWF (SessionReference.evalWithStateCore s term).1)
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hEq : FastPathEq s term) :
    SessionWF (Session.evalWithState s term).1 := by
  rw [evalWithState_eq_reference s term hEq]
  exact hCorePres s term hs

-- ─── Predicate-parametric convenience wrappers ────────────────────────────

theorem evalWithState_eq_reference_of_agreementOn
    {P : Session → Pattern → Prop}
    (s : Session) (term : Pattern)
    (hP : P s term)
    (hAgree : AgreementOn P) :
    Session.evalWithState s term = SessionReference.evalWithStateCore s term :=
  evalWithState_eq_reference s term (hAgree hP)

theorem wf_evalWithState_of_agreementOn
    {P : Session → Pattern → Prop}
    (hCorePres :
      ∀ (s : Session) (term : Pattern),
        SessionWF s →
        SessionWF (SessionReference.evalWithStateCore s term).1)
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hP : P s term)
    (hAgree : AgreementOn P) :
    SessionWF (Session.evalWithState s term).1 :=
  wf_evalWithState hCorePres s term hs (hAgree hP)

end Algorithms.MeTTa.Simple.Backend.SessionRefinement
