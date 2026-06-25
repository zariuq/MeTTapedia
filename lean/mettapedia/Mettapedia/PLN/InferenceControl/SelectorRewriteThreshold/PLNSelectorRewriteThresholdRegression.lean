import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNLocalMarkovPackages
import Mettapedia.PLN.Core.PLNCanonicalAPI
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultideductionResidual
import Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDampedConvergence
import Mettapedia.PLN.InferenceControl.PremiseSelection.BRGI
import Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdExamples

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
cd /home/zar/claude/Mettapedia/lean/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdRegression
```
-/

namespace Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdRegression

end Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdRegression
