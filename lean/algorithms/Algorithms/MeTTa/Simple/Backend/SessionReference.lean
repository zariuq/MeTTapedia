import Algorithms.MeTTa.Simple.Session

namespace Algorithms.MeTTa.Simple.Backend.SessionReference

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

abbrev SessionWF : Session → Prop := Session.WF

abbrev referenceEvalInterface := Session.referenceEvalInterface

abbrev evalWithStateCore := Session.referenceEvalWithStateCore

abbrev evalAuxStateful := Session.referenceEvalAuxStateful

abbrev evalSequenceStateful := Session.referenceEvalSequenceStateful

abbrev runNestedEffectsArgs := Session.referenceRunNestedEffectsArgs

abbrev runNestedEffects := Session.referenceRunNestedEffects

theorem evalWithStateCore_preserves
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        Session.intrinsicStateful s term = some (s', out) →
        SessionWF s →
        SessionWF s')
    (s : Session) (term : Pattern)
    (hs : SessionWF s) :
    SessionWF (evalWithStateCore s term).1 := by
  have hPres :
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.Preservation
        referenceEvalInterface SessionWF := by
    have hIntrinsicPresRef :
        ∀ {s : Session} {term : Pattern} {s' : Session} {out : List Pattern},
          referenceEvalInterface.intrinsicStateful s term = some (s', out) →
          SessionWF s →
          SessionWF s' := by
      intro s term s' out hIntr hs
      simpa [referenceEvalInterface] using hIntrinsicPres s term s' out hIntr hs
    exact
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.preservation_of_intrinsicStateful
        referenceEvalInterface SessionWF hIntrinsicPresRef
  simpa [evalWithStateCore, referenceEvalInterface] using
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore_preserves
      referenceEvalInterface SessionWF hPres s term hs

end Algorithms.MeTTa.Simple.Backend.SessionReference
