import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Base

/-!
# Self-interpreter addition checks

Finite self-interpreter checks by kernel reduction over `MeTTaIL.eval`.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp

open MeTTaIL

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

theorem self_add_0_1 :
    eval pMI 120 (miRun rulesAdd (miAdd miZ miOne) (fuel 6)) = S Z := by
  rfl

theorem self_add_2_1 :
    eval pMI 1000 (miRun rulesAdd (miAdd miTwo miOne) (fuel 10)) = S (S (S Z)) := by
  rfl

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
