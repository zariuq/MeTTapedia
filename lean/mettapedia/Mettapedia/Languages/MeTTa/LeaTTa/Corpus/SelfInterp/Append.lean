import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Base

/-!
# Self-interpreter append and length checks

Finite self-interpreter checks by kernel reduction over `MeTTaIL.eval`.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp

open MeTTaIL

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

theorem self_append_01_2 :
    eval pMI 3000 (miRun rulesAppendLen (miListAppend miList01 miList2) (fuel 20)) =
      Cons Z (Cons (S Z) (Cons (S (S Z)) Nil)) := by
  rfl

theorem self_len_append_01_2 :
    eval pMI 5000 (miRun rulesAppendLen (miLen (miListAppend miList01 miList2)) (fuel 30)) =
      S (S (S Z)) := by
  rfl

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
