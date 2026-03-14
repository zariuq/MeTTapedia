import Mettapedia.Logic.PLNFirstOrder.QuantifierCanary
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsFin
import Mettapedia.Logic.PLNFirstOrder.FuzzyITVBridgeFin
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierWorkedExamplesFin
import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismCanaryFin

/-!
# Chapter 11 Finite/Counting Regression Target

Single-entry build target for the finite/counting Chapter-11 quantifier semantics,
ITV bridge, worked examples, and fuzzy syllogism canaries.

Build command:

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNFirstOrder.QuantifierRegression
```
-/

namespace Mettapedia.Logic.PLNFirstOrder

end Mettapedia.Logic.PLNFirstOrder
