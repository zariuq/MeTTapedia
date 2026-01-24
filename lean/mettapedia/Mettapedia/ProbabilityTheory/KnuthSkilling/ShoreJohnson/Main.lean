import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Inference
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.TheoremI
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.SystemIndependence
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Theorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.OperatorAtomBridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KL
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Bridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.PathC
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.SJ3Locality
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KLWitness
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.RatioInvarianceCounterexample
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Integration

/-!
# Shore-Johnson (1980) entrypoint

This entrypoint keeps two threads visible:

1. **SJ axioms and inference formalism** (SJ1--SJ4) leading to sum-form objectives and
   system independence. Core modules:
   `Inference`, `Constraints`, `Objective`, `TheoremI`, `SystemIndependence`,
   `OperatorAtomBridge`, `Theorem`, `KL`.

2. **Path C overlap with Appendix C**. The Shore-Johnson path derives the same
   multiplicative Cauchy/log equation used in the Appendix C variational route.
   See `ShoreJohnson.PathC` and compare with
   `Mettapedia/ProbabilityTheory/KnuthSkilling/Variational/Main.lean`.

Analytic regularity for SJ3 -> locality is packaged in `GradientSeparability` and
`SJ3Locality`. We also include **positive** and **negative** examples of the
ratio-invariance axiom:
- `KLWitness`: KL atom satisfies `DerivRatioInvariant`.
- `RatioInvarianceCounterexample`: quadratic loss fails it.
-/
