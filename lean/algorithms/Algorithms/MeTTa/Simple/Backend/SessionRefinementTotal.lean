import Algorithms.MeTTa.Simple.Backend.SessionReference
import Algorithms.MeTTa.Simple.Backend.SessionReferenceAdequacy
import Algorithms.MeTTa.Simple.Backend.SessionReferenceFaithful
import Algorithms.MeTTa.Simple.Backend.SessionReferenceTotal
import Algorithms.MeTTa.Simple.Backend.SessionRefinement

namespace Algorithms.MeTTa.Simple.Backend.SessionRefinementTotal

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

abbrev SessionWF : Session → Prop := SessionReferenceTotal.SessionWF

abbrev DeterministicAcceptedRaw := SessionRefinement.DeterministicAcceptedRaw

/-- Transport the existing live-reference refinement result to the total reference backend
    once a fragment-specific adequacy/equality theorem is available. -/
theorem evalWithState_eq_total_reference_of_live_reference_and_deterministic_agreement
    (hRefEq :
      ∀ (s : Session) (term : Pattern),
        SessionReference.evalWithStateCore s term =
          SessionReferenceTotal.evalWithStateCore s term)
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term := by
  calc
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
      exact
        SessionRefinement.evalWithState_eq_reference_of_deterministic_agreement_raw_guard
          s term hs hAgreeRaw
    _ = SessionReferenceTotal.evalWithStateCore s term := by
      exact hRefEq s term

/-- Covered-term variant of the total-reference transport theorem.
    This avoids requiring a global live-to-total equality assumption when adequacy is
    only available for the current covered term. -/
theorem evalWithState_eq_total_reference_of_covered_agreement_and_deterministic_agreement
    (s : Session) (term : Pattern)
    (hCov : SessionReferenceAdequacy.CoveredByReferenceN term)
    (hRefEqCov :
      SessionReferenceAdequacy.CoveredByReferenceN term →
        SessionReference.evalWithStateCore s term =
          SessionReferenceTotal.evalWithStateCore s term)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term := by
  have hRefEq : SessionReference.evalWithStateCore s term =
      SessionReferenceTotal.evalWithStateCore s term :=
    hRefEqCov hCov
  calc
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
      exact
        SessionRefinement.evalWithState_eq_reference_of_deterministic_agreement_raw_guard
          s term hs hAgreeRaw
    _ = SessionReferenceTotal.evalWithStateCore s term := hRefEq

/-- Transport the existing session-WF result to the total reference backend once
    equality with the live reference backend is available. -/
theorem wf_evalWithState_of_total_reference_and_deterministic_agreement
    (hRefEq :
      ∀ (s : Session) (term : Pattern),
        SessionReference.evalWithStateCore s term =
          SessionReferenceTotal.evalWithStateCore s term)
    (hCorePresTotal :
      ∀ (s : Session) (term : Pattern),
        SessionWF s →
        SessionWF (SessionReferenceTotal.evalWithStateCore s term).1)
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.evalWithState s term).1 := by
  have hCorePresLive :
      ∀ (s : Session) (term : Pattern),
        SessionReference.SessionWF s →
        SessionReference.SessionWF (SessionReference.evalWithStateCore s term).1 := by
    intro s term hs
    have hTot := hCorePresTotal s term hs
    have hEqFst :
        (SessionReference.evalWithStateCore s term).1 =
          (SessionReferenceTotal.evalWithStateCore s term).1 := by
      exact congrArg Prod.fst (hRefEq s term)
    rw [hEqFst]
    simpa [SessionWF] using hTot
  exact
    SessionRefinement.wf_evalWithState_of_reference_and_deterministic_agreement
      hCorePresLive s term hs hAgreeRaw

/-- Covered-term variant of the session-WF transport theorem. -/
theorem wf_evalWithState_of_covered_total_reference_and_deterministic_agreement
    (s : Session) (term : Pattern)
    (hCov : SessionReferenceAdequacy.CoveredByReferenceN term)
    (hRefEqCov :
      SessionReferenceAdequacy.CoveredByReferenceN term →
        SessionReference.evalWithStateCore s term =
          SessionReferenceTotal.evalWithStateCore s term)
    (hCorePresTotal :
      ∀ (s : Session) (term : Pattern),
        SessionWF s →
        SessionWF (SessionReferenceTotal.evalWithStateCore s term).1)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.evalWithState s term).1 := by
  have hEq :
      Session.evalWithState s term =
        SessionReferenceTotal.evalWithStateCore s term := by
    exact
      evalWithState_eq_total_reference_of_covered_agreement_and_deterministic_agreement
        s term hCov hRefEqCov hs hAgreeRaw
  have hEqFst :
      (Session.evalWithState s term).1 =
        (SessionReferenceTotal.evalWithStateCore s term).1 := by
    exact congrArg Prod.fst hEq
  have hTot : SessionWF (SessionReferenceTotal.evalWithStateCore s term).1 :=
    hCorePresTotal s term hs
  rw [hEqFst]
  exact hTot

/-- Witnessed-faithful variant of the total-reference transport theorem.
    Instead of taking a generic covered-term equality premise, this theorem uses an explicit
    successful run of the faithful backend together with a local equality witness from the
    live reference path to that result. -/
theorem evalWithState_eq_total_reference_of_faithful_done_and_deterministic_agreement
    (s : Session) (term : Pattern) (res : Session × List Pattern)
    (hdone : SessionReferenceFaithful.evalWithStateCore s term = .done res)
    (hRefDone : SessionReference.evalWithStateCore s term = res)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term := by
  have hTotEq : SessionReferenceTotal.evalWithStateCore s term = res :=
    SessionReferenceAdequacy.eval_done_eq_public_totalEvalWithStateCore s term res hdone
  calc
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
      exact
        SessionRefinement.evalWithState_eq_reference_of_deterministic_agreement_raw_guard
          s term hs hAgreeRaw
    _ = res := hRefDone
    _ = SessionReferenceTotal.evalWithStateCore s term := by
      symm
      exact hTotEq

/-- Local-equality variant of the total-reference transport theorem.
    This is the clean public surface to use once a fragment-specific adequacy theorem
    supplies equality with the live reference backend; the faithful `.done` witness is
    discharged automatically from the public fuel policy. -/
theorem evalWithState_eq_total_reference_of_local_reference_agreement_and_deterministic_agreement
    (s : Session) (term : Pattern)
    (hRefEq :
      SessionReference.evalWithStateCore s term =
        SessionReferenceTotal.evalWithStateCore s term)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s term = SessionReferenceTotal.evalWithStateCore s term := by
  calc
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
      exact
        SessionRefinement.evalWithState_eq_reference_of_deterministic_agreement_raw_guard
          s term hs hAgreeRaw
    _ = SessionReferenceTotal.evalWithStateCore s term := hRefEq

/-- First fragment-specific refinement transport theorem with the local equality
    witness discharged automatically: `get-atoms` at `maxNodes = 1`. -/
theorem evalWithState_getAtoms_eq_total_reference_of_oneMaxNode_and_deterministic_agreement
    (s : Session) (spaceArg : Pattern)
    (hNodes : s.maxNodes = 1)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s (.apply "get-atoms" [spaceArg]) =
      SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms" [spaceArg]) := by
  have hRefEq :
      SessionReference.evalWithStateCore s (.apply "get-atoms" [spaceArg]) =
        SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms" [spaceArg]) := by
    simpa [SessionReference.evalWithStateCore] using
      SessionReferenceAdequacy.getAtoms_eval_eq_public_total_of_oneMaxNode s spaceArg hNodes
  exact
    evalWithState_eq_total_reference_of_local_reference_agreement_and_deterministic_agreement
      s (.apply "get-atoms" [spaceArg]) hRefEq hs hAgreeRaw

/-- First fragment-specific refinement transport theorem with the local equality
    witness discharged automatically: `get-atoms!` at `maxNodes = 1`. -/
theorem evalWithState_getAtomsBang_eq_total_reference_of_oneMaxNode_and_deterministic_agreement
    (s : Session) (spaceArg : Pattern)
    (hNodes : s.maxNodes = 1)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s (.apply "get-atoms!" [spaceArg]) =
      SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms!" [spaceArg]) := by
  have hRefEq :
      SessionReference.evalWithStateCore s (.apply "get-atoms!" [spaceArg]) =
        SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms!" [spaceArg]) := by
    simpa [SessionReference.evalWithStateCore] using
      SessionReferenceAdequacy.getAtomsBang_eval_eq_public_total_of_oneMaxNode s spaceArg hNodes
  exact
    evalWithState_eq_total_reference_of_local_reference_agreement_and_deterministic_agreement
      s (.apply "get-atoms!" [spaceArg]) hRefEq hs hAgreeRaw

/-- First compositional refinement transport theorem whose local equality witness is
    discharged automatically: three-argument `match` with a `get-atoms!` template on
    the `maxNodes = 1` fragment. -/
theorem evalWithState_match_getAtomsBang_eq_total_reference_of_oneMaxNode_and_deterministic_agreement
    (s : Session) (space pat spaceExpr : Pattern)
    (hNodes : s.maxNodes = 1)
    (hIntr :
      Session.intrinsicStateful s (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) =
        Session.intrinsicStatefulN (SessionReferenceTotal.referenceFuel s - 1) s
          (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]))
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) =
      SessionReferenceTotal.evalWithStateCore s
        (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) := by
  have hRefEq :
      SessionReference.evalWithStateCore s (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) =
        SessionReferenceTotal.evalWithStateCore s
          (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) := by
    simpa [SessionReference.evalWithStateCore] using
      SessionReferenceAdequacy.match_getAtomsBang_eval_eq_public_total_of_oneMaxNode
        s space pat spaceExpr hNodes hIntr
  exact
    evalWithState_eq_total_reference_of_local_reference_agreement_and_deterministic_agreement
      s (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) hRefEq hs hAgreeRaw

/-- Witnessed-faithful variant of the session-WF transport theorem. -/
theorem wf_evalWithState_of_faithful_done_and_deterministic_agreement
    (s : Session) (term : Pattern) (s' : Session) (out : List Pattern)
    (hdone : SessionReferenceFaithful.evalWithStateCore s term = .done (s', out))
    (hRefDone : SessionReference.evalWithStateCore s term = (s', out))
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.evalWithState s term).1 := by
  have hEq :
      Session.evalWithState s term =
        SessionReferenceTotal.evalWithStateCore s term := by
    exact
      evalWithState_eq_total_reference_of_faithful_done_and_deterministic_agreement
        s term (s', out) hdone hRefDone hs hAgreeRaw
  have hEqFst :
      (Session.evalWithState s term).1 =
        (SessionReferenceTotal.evalWithStateCore s term).1 := by
    exact congrArg Prod.fst hEq
  have hTotPair :
      SessionReferenceTotal.evalWithStateCore s term = (s', out) ∧
        SessionReferenceTotal.SessionWF s' := by
    exact SessionReferenceAdequacy.eval_done_eq_total_and_preserves_public s term hdone hs
  have hTotEqFst :
      (SessionReferenceTotal.evalWithStateCore s term).1 = s' := by
    exact congrArg Prod.fst hTotPair.1
  have hTot :
      SessionWF (SessionReferenceTotal.evalWithStateCore s term).1 := by
    rw [hTotEqFst]
    exact hTotPair.2
  rw [hEqFst]
  exact hTot

/-- Local-equality variant of the session-WF transport theorem.
    Like the equality transport above, this is the theorem to target once a small
    adequacy lemma provides live-reference = total-reference for the current term. -/
theorem wf_evalWithState_of_local_reference_agreement_and_deterministic_agreement
    (s : Session) (term : Pattern)
    (hRefEq :
      SessionReference.evalWithStateCore s term =
        SessionReferenceTotal.evalWithStateCore s term)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.evalWithState s term).1 := by
  have hEq :
      Session.evalWithState s term =
        SessionReferenceTotal.evalWithStateCore s term := by
    exact
      evalWithState_eq_total_reference_of_local_reference_agreement_and_deterministic_agreement
        s term hRefEq hs hAgreeRaw
  have hEqFst :
      (Session.evalWithState s term).1 =
        (SessionReferenceTotal.evalWithStateCore s term).1 := by
    exact congrArg Prod.fst hEq
  have hTot :
      SessionWF (SessionReferenceTotal.evalWithStateCore s term).1 :=
    SessionReferenceTotal.evalWithStateCore_preserves s term hs
  rw [hEqFst]
  exact hTot

/-- First fragment-specific WF transport theorem with the local equality witness
    discharged automatically: `get-atoms` at `maxNodes = 1`. -/
theorem wf_evalWithState_getAtoms_of_oneMaxNode_and_deterministic_agreement
    (s : Session) (spaceArg : Pattern)
    (hNodes : s.maxNodes = 1)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.evalWithState s (.apply "get-atoms" [spaceArg])).1 := by
  have hRefEq :
      SessionReference.evalWithStateCore s (.apply "get-atoms" [spaceArg]) =
        SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms" [spaceArg]) := by
    simpa [SessionReference.evalWithStateCore] using
      SessionReferenceAdequacy.getAtoms_eval_eq_public_total_of_oneMaxNode s spaceArg hNodes
  exact
    wf_evalWithState_of_local_reference_agreement_and_deterministic_agreement
      s (.apply "get-atoms" [spaceArg]) hRefEq hs hAgreeRaw

/-- First fragment-specific WF transport theorem with the local equality witness
    discharged automatically: `get-atoms!` at `maxNodes = 1`. -/
theorem wf_evalWithState_getAtomsBang_of_oneMaxNode_and_deterministic_agreement
    (s : Session) (spaceArg : Pattern)
    (hNodes : s.maxNodes = 1)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.evalWithState s (.apply "get-atoms!" [spaceArg])).1 := by
  have hRefEq :
      SessionReference.evalWithStateCore s (.apply "get-atoms!" [spaceArg]) =
        SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms!" [spaceArg]) := by
    simpa [SessionReference.evalWithStateCore] using
      SessionReferenceAdequacy.getAtomsBang_eval_eq_public_total_of_oneMaxNode s spaceArg hNodes
  exact
    wf_evalWithState_of_local_reference_agreement_and_deterministic_agreement
      s (.apply "get-atoms!" [spaceArg]) hRefEq hs hAgreeRaw

end Algorithms.MeTTa.Simple.Backend.SessionRefinementTotal
