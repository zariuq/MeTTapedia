import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzySyllogismCanary

/-!
# Chapter 11 Fuzzy-Syllogism Regression Target

Dedicated build target for extended fuzzy-quantifier syllogism checks
(`most ∘ most`, `few ∘ most`, QFM-style monotonicity/conservativity canaries).

Build command:

```bash
cd /home/zar/claude/Mettapedia/lean/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzySyllogismRegression
```
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers

end Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
