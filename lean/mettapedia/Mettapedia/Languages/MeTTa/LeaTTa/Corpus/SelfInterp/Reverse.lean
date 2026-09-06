import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Checkpoints.Reverse

/-!
# Self-interpreter reverse check

Finite self-interpreter checks by kernel reduction over `MeTTaIL.eval`.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp

open MeTTaIL

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

theorem self_rev_012 :
    eval pMI 12000 (miRun rulesRev (miRev miList012) (fuel 40)) =
      Cons (S (S Z)) (Cons (S Z) (Cons Z Nil)) := by
  calc
    _ = eval pMI 10500 (Cons (S (S Z)) (Cons (S Z) (Cons Z Nil))) :=
      (eval_add pMI 1500 10500 _).trans
        (congrArg (eval pMI 10500) Checkpoints.Reverse.evaluated)
    _ = _ := eval_fixed_of_normal pMI _ Checkpoints.Reverse.normal 10499

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
