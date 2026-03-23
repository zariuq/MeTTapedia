import Algorithms.MeTTa.Simple.Backend.SessionReference
import Algorithms.MeTTa.Simple.Backend.SessionReferenceAdequacy
import Algorithms.MeTTa.Simple.Backend.SessionReferenceFaithful
import Algorithms.MeTTa.Simple.Backend.SessionReferenceTotal
import Algorithms.MeTTa.Simple.Backend.SessionRefinement

/-! QUARANTINED: Transport theorems depending on SessionRefinement.
Valid conditional theorems but the conditions (FastPathEq) are not instantiated. -/

namespace Algorithms.MeTTa.Simple.Backend.SessionRefinementTotal

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple
open Algorithms.MeTTa.Simple.Backend.SessionRefinement (FastPathEq AgreementOn)

abbrev SessionWF : Session → Prop := SessionReferenceTotal.SessionWF

-- ─── Core equality transport to total reference ───────────────────────────

/-- Transport: evalWithState = total reference, given pointwise fast-path equality
    and a live-to-total reference bridge. -/
theorem evalWithState_eq_total_reference
    (s : Session) (term : Pattern)
    (hRefEq :
      SessionReference.evalWithStateCore s term =
        SessionReferenceTotal.evalWithStateCore s term)
    (hs : SessionWF s)
    (hEq : FastPathEq s term) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term := by
  calc
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
      exact Algorithms.MeTTa.Simple.Backend.SessionRefinement.evalWithState_eq_reference s term hEq
    _ = SessionReferenceTotal.evalWithStateCore s term := hRefEq

/-- Unconditional variant using `reference_eq_total`. -/
theorem evalWithState_eq_total_reference_unconditional
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hEq : FastPathEq s term) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term :=
  evalWithState_eq_total_reference s term
    (SessionReferenceAdequacy.reference_eq_total s term) hs hEq

-- ─── WF transport to total reference ──────────────────────────────────────

/-- WF preservation: evalWithState preserves SessionWF, given pointwise equality. -/
theorem wf_evalWithState
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hEq : FastPathEq s term) :
    SessionWF (Session.evalWithState s term).1 := by
  have hEqTotal := evalWithState_eq_total_reference_unconditional s term hs hEq
  rw [hEqTotal]
  exact SessionReferenceTotal.evalWithStateCore_preserves s term hs

-- ─── Predicate-parametric convenience wrappers ────────────────────────────

theorem evalWithState_eq_total_reference_of_agreementOn
    {P : Session → Pattern → Prop}
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hP : P s term)
    (hAgree : AgreementOn P) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term :=
  evalWithState_eq_total_reference_unconditional s term hs (hAgree hP)

theorem wf_evalWithState_of_agreementOn
    {P : Session → Pattern → Prop}
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hP : P s term)
    (hAgree : AgreementOn P) :
    SessionWF (Session.evalWithState s term).1 :=
  wf_evalWithState s term hs (hAgree hP)

-- ─── Witnessed-faithful variant ───────────────────────────────────────────

/-- Transport via a witnessed-faithful run: if the faithful backend terminates
    with `.done res` and the live reference agrees, transport to total reference. -/
theorem evalWithState_eq_total_reference_of_faithful_done
    (s : Session) (term : Pattern) (res : Session × List Pattern)
    (hdone : SessionReferenceFaithful.evalWithStateCore s term = .done res)
    (hRefDone : SessionReference.evalWithStateCore s term = res)
    (hs : SessionWF s)
    (hEq : FastPathEq s term) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term := by
  have hTotEq : SessionReferenceTotal.evalWithStateCore s term = res :=
    SessionReferenceAdequacy.eval_done_eq_public_totalEvalWithStateCore s term res hdone
  calc
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
      exact Algorithms.MeTTa.Simple.Backend.SessionRefinement.evalWithState_eq_reference s term hEq
    _ = res := hRefDone
    _ = SessionReferenceTotal.evalWithStateCore s term := by symm; exact hTotEq

end Algorithms.MeTTa.Simple.Backend.SessionRefinementTotal
