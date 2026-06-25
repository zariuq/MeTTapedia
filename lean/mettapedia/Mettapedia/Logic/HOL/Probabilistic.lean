import Mettapedia.Logic.HOL.Probabilistic.ModelSpace
import Mettapedia.Logic.HOL.Probabilistic.Semantics
import Mettapedia.Logic.HOL.Probabilistic.IndexedSpaces
import Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
import Mettapedia.Logic.HOL.Probabilistic.Flattening

/-!
# Probabilistic HOL Semantics

Public entrypoint for the infinitary-first semantic `ProbHOL` layer:

- measurable index spaces of pointed Henkin models,
- sentence probabilities for closed HOL formulas,
- concrete indexed model spaces, both infinitary and finitary,
- hierarchical and infinite-order uncertainty over measures on those model spaces,
- and flattening theorems back to ordinary sentence probabilities.

This semantic layer follows the higher-order probability/Kyburg direction of
the project, including the Kyburg/Giry line already formalized in
`Mettapedia/ProbabilityTheory/HigherOrderProbability/`. It remains distinct
from the logical-induction-ready dynamic belief-process layer. PLN-facing
empirical, benchmark, belief, and regression bridges are exported from
`Mettapedia.PLN.Bridges.HOL.Probabilistic`.
-/
