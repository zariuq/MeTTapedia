import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.QuantifierCanary
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierSemanticsFin
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyITVBridgeFin
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierWorkedExamplesFin
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzySyllogismCanaryFin

/-!
# Chapter 11 Finite/Counting Regression Target

Single-entry build target for the finite/counting Chapter-11 quantifier semantics,
ITV bridge, worked examples, and fuzzy syllogism canaries.

Build command:

```bash
cd /home/zar/claude/Mettapedia/lean/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.QuantifierRegression
```
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers

end Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
