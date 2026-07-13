import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Base

/-!
# Self-interpreter reverse involution checks

Finite self-interpreter checks by kernel reduction over `MeTTaIL.eval`.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp

open MeTTaIL

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

theorem self_rev_involution_eval_012 :
    eval pMI 12000 (miEval rulesRev (miRev (miRev miList012)) (fuel 40)) =
      MIDone miList012 := by
  rfl

theorem self_rev_involution_decode_012 :
    eval pMI 300 (miDecodeVerdict (MIDone miList012)) =
      Cons Z (Cons (S Z) (Cons (S (S Z)) Nil)) := by
  rfl

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
