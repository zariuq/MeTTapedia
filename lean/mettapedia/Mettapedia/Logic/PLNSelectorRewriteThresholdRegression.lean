import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PLNBNLocalMarkovPackages
import Mettapedia.Logic.PLNCanonicalAPI
import Mettapedia.Logic.PLNInferenceControlExamples
import Mettapedia.Logic.PLNMultideductionResidual
import Mettapedia.Logic.PLNTrailFreeDampedConvergence
import Mettapedia.Logic.PremiseSelectionBRGI
import Mettapedia.Logic.PLNSelectorRewriteThresholdExamples

/-!
# Selector→Rewrite→Threshold Positive Regression

Single-entry build target for the Chapter-9 positive (non-counterexample) path:

- BN local-Markov package modules (chain/fork/collider)
- class-packaged d-separation discharge
- multideduction residual decomposition + assumption-indexed agreement endpoint
- damped SP/SPN positive convergence under eventual fresh evidence
- bounded-gap fairness reset bounds for damped SP/SPN dynamics
- finite BRGI object (feasible-set semantics + optimality endpoint)
- concrete Bool selector fixture + composed rewrite/threshold endpoint

Build command:

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNSelectorRewriteThresholdRegression
```
-/

namespace Mettapedia.Logic.PLNSelectorRewriteThresholdRegression

end Mettapedia.Logic.PLNSelectorRewriteThresholdRegression
