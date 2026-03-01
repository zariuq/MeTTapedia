import Mettapedia.Logic.PLNFirstOrder.QuantifierCanary
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.FuzzyITVBridge
import Mettapedia.Logic.PLNFirstOrder.QuantifierWorkedExamples
import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismCanary

/-!
# Chapter 11 Regression Target

Single-entry build target for Chapter-11 quantifier semantics and canaries.

Build command:

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNFirstOrder.QuantifierRegression
```
-/

namespace Mettapedia.Logic.PLNFirstOrder

end Mettapedia.Logic.PLNFirstOrder
