import Algorithms.MeTTa.Simple.Session

namespace Algorithms.MeTTa.Simple.Backend.SessionReference

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

abbrev SessionWF : Session → Prop := Session.WF

abbrev referenceEvalInterface := Session.referenceEvalInterface

def evalWithStateCore (s : Session) (term : Pattern) : Session × List Pattern :=
  Session.evalWithStateCoreN (Session.referenceProofFuel s) s term

abbrev evalAuxStateful := Session.referenceEvalAuxStateful

abbrev evalSequenceStateful := Session.referenceEvalSequenceStateful

abbrev runNestedEffectsArgs := Session.referenceRunNestedEffectsArgs

abbrev runNestedEffects := Session.referenceRunNestedEffects

theorem evalWithStateCore_preserves
    (s : Session) (term : Pattern)
    (hs : SessionWF s) :
    SessionWF (evalWithStateCore s term).1 := by
  unfold evalWithStateCore
  exact Session.evalWithStateCoreN_preserves (Session.referenceProofFuel s) s term hs

end Algorithms.MeTTa.Simple.Backend.SessionReference
