import Mettapedia.Logic.PLNIntensionalWorldModel
import Mettapedia.Logic.IntensionalInheritanceSolomonoffBridge
import Mettapedia.Logic.PLNCanonicalAPI
import Mettapedia.Logic.PLNIntensionalCanary

/-!
# Chapter 12 Regression Target

Single-entry build target for Chapter-12 intensional inheritance:

- WM typed inheritance channels
- Solomonoff log-ratio bridge
- canonical one-call API composition
- executable positive/negative canaries

Build command:

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNIntensionalRegression
```
-/

namespace Mettapedia.Logic.PLNIntensionalRegression

end Mettapedia.Logic.PLNIntensionalRegression
