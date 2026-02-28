import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismCanary

/-!
# Chapter 11 Fuzzy-Syllogism Regression Target

Dedicated build target for extended fuzzy-quantifier syllogism checks
(`most ∘ most`, `few ∘ most`, QFM-style monotonicity/conservativity canaries).

Build command:

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNFirstOrder.Chapter11FuzzySyllogismRegression
```
-/

namespace Mettapedia.Logic.PLNFirstOrder

end Mettapedia.Logic.PLNFirstOrder
