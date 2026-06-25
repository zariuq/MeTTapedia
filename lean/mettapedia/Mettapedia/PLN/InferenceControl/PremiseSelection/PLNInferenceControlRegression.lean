import Mettapedia.PLN.InferenceControl.PremiseSelection.SelectorSpec
import Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality
import Mettapedia.PLN.InferenceControl.PremiseSelection.RankingStability
import Mettapedia.PLN.InferenceControl.PremiseSelection.Coverage
import Mettapedia.PLN.InferenceControl.PremiseSelection.BestPLNDraft
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlAlgorithms
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlChainer
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCanary
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples

/-!
# Chapter 13 Regression Target

Single-entry build target for Chapter-13 inference-control coverage:

- selector defaults + checklist linkage
- ranking transfer and stability lemmas
- coverage/submodularity objective theorems
- executable positive/negative canaries

Build command:

```bash
cd /home/zar/claude/Mettapedia/lean/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlRegression
```
-/

namespace Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlRegression

end Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlRegression
