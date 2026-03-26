import Algorithms.MeTTa.HE.Lowering
import Algorithms.MeTTa.Simple.Session

/-!
Legacy bridge from frozen HE lowering into the deprecated `Simple.Session`
runtime. Kept only for compatibility and conformance harnesses that still
exercise the old evaluator.
-/

namespace Algorithms.MeTTa.HE

def toSession (cfg : FrozenHEConfig) : Algorithms.MeTTa.Simple.Session :=
  let s0 := Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfg)
  let s1 := Algorithms.MeTTa.Simple.Session.withSyntax s0 MeTTailCore.MeTTaSyntax.he
  Algorithms.MeTTa.Simple.Session.withBounds s1 cfg.maxSteps cfg.maxNodes

end Algorithms.MeTTa.HE
