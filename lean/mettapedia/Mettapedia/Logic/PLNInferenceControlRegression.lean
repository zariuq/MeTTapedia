import Mettapedia.Logic.PremiseSelectionSelectorSpec
import Mettapedia.Logic.PremiseSelectionOptimality
import Mettapedia.Logic.PremiseSelectionRankingStability
import Mettapedia.Logic.PremiseSelectionCoverage
import Mettapedia.Logic.PremiseSelectionBestPLNDraft
import Mettapedia.Logic.PLNInferenceControlCore
import Mettapedia.Logic.PLNInferenceControlAlgorithms
import Mettapedia.Logic.PLNInferenceControlChainer
import Mettapedia.Logic.PLNInferenceControlCanary
import Mettapedia.Logic.PLNInferenceControlExamples

/-!
# Chapter 13 Regression Target

Single-entry build target for Chapter-13 inference-control coverage:

- selector defaults + checklist linkage
- ranking transfer and stability lemmas
- coverage/submodularity objective theorems
- executable positive/negative canaries

Build command:

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNInferenceControlRegression
```
-/

namespace Mettapedia.Logic.PLNInferenceControlRegression

end Mettapedia.Logic.PLNInferenceControlRegression
