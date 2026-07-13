import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Base

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
  rfl

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
