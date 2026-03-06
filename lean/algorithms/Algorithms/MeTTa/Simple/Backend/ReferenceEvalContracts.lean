import Algorithms.MeTTa.Simple.Backend.ReferenceEval

namespace Algorithms.MeTTa.Simple.Backend.ReferenceEvalContracts

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend.ReferenceEval

variable {σ : Type}

theorem evalWithStateCore_unfold
    (I : Interface σ) (s : σ) (term : Pattern) :
    evalWithStateCore I s term =
      evalAuxStateful I s (I.maxNodes s) [(term, 0)] [] := rfl

end Algorithms.MeTTa.Simple.Backend.ReferenceEvalContracts
