import Mettapedia.Logic.HOL.Probabilistic.ModelSpace
import Mettapedia.Logic.HOL.Probabilistic.Semantics
import Mettapedia.Logic.HOL.Probabilistic.WorldModelBridge
import Mettapedia.Logic.HOL.Probabilistic.IndexedSpaces
import Mettapedia.Logic.HOL.Probabilistic.EmpiricalSpecialCase
import Mettapedia.Logic.HOL.Probabilistic.Regression
import Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
import Mettapedia.Logic.HOL.Probabilistic.Flattening
import Mettapedia.Logic.HOL.Probabilistic.BenchmarkBridge
import Mettapedia.Logic.HOL.Probabilistic.HierarchicalRegression
import Mettapedia.Logic.HOL.Probabilistic.BeliefBridge
import Mettapedia.Logic.HOL.Probabilistic.BenchmarkBeliefBridge
import Mettapedia.Logic.HOL.Probabilistic.BeliefRegression

/-!
# Probabilistic HOL Semantics

Public entrypoint for the infinitary-first semantic `ProbHOL` layer:

- measurable index spaces of pointed Henkin models,
- sentence probabilities for closed HOL formulas,
- a thin WM-facing probability/strength lens,
- concrete indexed model spaces, both infinitary and finitary,
- the theorem that the existing empirical HOL-WM semantics is a special case,
- hierarchical and infinite-order uncertainty over measures on those model spaces,
- flattening theorems back to ordinary sentence probabilities,
- and a first concrete guarded-benchmark bridge into that hierarchy,
- a benchmark-facing belief-day/process bridge showing how the guarded carried
  value can be consumed as a semantically justified LI-style price on the
  benchmark query,
- a thin comparison layer to the LI-ready belief/process interface, and
- positive and negative regressions for that semantic-vs-belief bridge.

This semantic layer follows the higher-order probability/Kyburg direction of
the project, including the Kyburg/Giry line already formalized in
`Mettapedia/ProbabilityTheory/HigherOrderProbability/`. It remains distinct
from the logical-induction-ready dynamic belief-process layer, which is
re-exported separately.
-/
