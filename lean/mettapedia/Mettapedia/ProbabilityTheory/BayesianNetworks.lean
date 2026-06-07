import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparationSoundness
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationBridge
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingSchedule
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingLiterature
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingBridge
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingExactness
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingTreeSupport
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingBeliefExactness
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingTreeExactness
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingSemiringExamples

/-!
# Bayesian Networks (Entry Point)

This module collects the stable public entry points for the Bayesian-network /
factor-graph / variable-elimination / belief-propagation stack.

The intended public story is:

* graph and BN structure,
* discrete local-Markov and d-separation soundness for CPT joint measures,
* exact factor-graph inference (`VariableElimination`, `ValuationBridge`),
* semiring-generic belief propagation, with the incident-edge schedule surface
  as the preferred exactness API,
* local bridge lemmas and the attached-tree exactness support layer,
* first belief-exactness theorems on small tree fragments and reusable
  attached incoming subtrees,
* a small named tree-exactness family collecting the current fragment
  theorems, rather than a full general loopy-BP exactness claim,
* tiny executable semiring examples that show the same graph yielding
  different messages under different carriers.

Cross-domain bridges from empirical inheritance objects into this stack remain
opt-in from the logic side (`Logic.IntensionalInheritanceAll`), rather than
being re-exported here by default.

Heavier experimental files and large example collections remain opt-in imports.
-/
