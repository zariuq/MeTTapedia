import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Connection
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Neighbors
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Proofs
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Theory

/-!
# Hypercube ↔ Knuth–Skilling (aggregator)

The Knuth–Skilling-centred *slice* of the probability hypercube. It fixes the
master `ProbabilityVertex` (`Mettapedia/ProbabilityTheory/Hypercube/Basic.lean`)
to the K&S vertex and characterises which representation theorems survive under
various order/separation hypotheses (commutativity, density, sandwich-separation,
scale dichotomy).

This aggregator collects the K&S-specific hypercube analysis modules under
`Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/`. They build on the
standalone K&S external (`KnuthSkilling.Core.*`, `KnuthSkilling.Additive.*`) and
the verified Hypercube core (`Hypercube.Basic`, `Hypercube.ThetaSemantics`,
`Hypercube.ScaleDichotomy`).
-/
