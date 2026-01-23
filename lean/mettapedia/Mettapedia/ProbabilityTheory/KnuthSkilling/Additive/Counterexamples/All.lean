import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.BenV2Theorem1
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.CStrict0Fails
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.FreeMonoidNoSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.GoertzelLemma7
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.KSSeparationNotDerivable
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.NewAtomCommutesNotDerivable
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.NoFiniteModel
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.ProductFailsSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.RankObstruction
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.RankObstructionLinear
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.SemidirectNoSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.StrictGap
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.ZQuantizedBEmpty
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.ZQuantizedBNonempty

/-!
# Knuth–Skilling: Counterexamples (Build Target)

This module imports the full suite of formal counterexamples used to clarify which hypotheses
are necessary for the Knuth–Skilling representation theorem development.

Build this file to compile the entire counterexample suite in one go:

```bash
ulimit -Sv 6291456
cd lean-projects/mettapedia
export LAKE_JOBS=1
nice -n 19 lake build Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.All
```

Exploration notes and failed model attempts live separately under
`Mettapedia.ProbabilityTheory.KnuthSkilling.Experimental.RepresentationTheorem.Explorations`.
-/

