import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Base

/-!
# Self-interpreter query and boundary checks

Finite self-interpreter checks by kernel reduction over `MeTTaIL.eval`.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp

open MeTTaIL

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

theorem self_match_query_answer :
    eval pMI 500 (miRun rulesMatchQuery miMatchQuery (fuel 8)) = N (S (S Z)) := by
  rfl

theorem self_match_query_missing_stays :
    eval pMI 500 (miEval rulesMatchQuery miMissingQuery (fuel 8)) =
      MIDone miMissingQuery := by
  rfl

theorem self_nonmatching_query_stays :
    eval pMI 80 (miEval MIRNil (MIApp "missing" (MICons miZ MINil)) (fuel 3)) =
      MIDone (MIApp "missing" (MICons miZ MINil)) := by
  rfl

theorem self_fuel_exhaustion_visible :
    eval pMI 30 (miEval rulesAdd (miAdd miTwo miOne) FZ) =
      MIExhausted (miAdd miTwo miOne) := by
  rfl

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
