import Algorithms.MeTTa.PeTTa.Lowering
import Algorithms.MeTTa.Simple.Session

/-!
Legacy bridge from frozen PeTTa lowering into the deprecated `Simple.Session`
runtime. Kept only for compatibility and conformance harnesses that still
exercise the old evaluator.
-/

namespace Algorithms.MeTTa.PeTTa

def toSession (cfg : FrozenPeTTaConfig) : Algorithms.MeTTa.Simple.Session :=
  (Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfg)).withBounds cfg.maxSteps cfg.maxNodes

end Algorithms.MeTTa.PeTTa
