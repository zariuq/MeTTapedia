import Mettapedia.GSLT.Distinction.Probabilistic.KantorovichDuality
import Mettapedia.GSLT.Distinction.Probabilistic.LogicalDistance
import Mettapedia.GSLT.Distinction.Probabilistic.System
import Mettapedia.GSLT.Distinction.Probabilistic.FiniteChains
import Mettapedia.GSLT.Distinction.Probabilistic.Completion
import Mettapedia.GSLT.Distinction.Probabilistic.Domination
import Mettapedia.GSLT.Distinction.Probabilistic.Controls
import Mettapedia.GSLT.Distinction.Probabilistic.Causal
import Mettapedia.GSLT.Distinction.Probabilistic.Semiring
import Mettapedia.GSLT.Distinction.Probabilistic.DisjointUnion
import Mettapedia.GSLT.Distinction.Probabilistic.SubDistributionDomination
import Mettapedia.GSLT.Distinction.Probabilistic.CausalAbduction

/-!
# Probabilistic GSLTs and their behavioural metrics

Labelled Markov processes as GSLTs, read against the finite labelled Markov
chains and the Kantorovich metric of `Cybernetics.ApproximateAdequacy`, which
this layer reuses.

* `KantorovichDuality`: on finite spaces, transport duality from Hahn–Banach
  separation, its Kantorovich–Rubinstein form, and the lifting as a supremum
  over the functions the cost bounds.
* `LogicalDistance`: the bisimulation metric (the Kantorovich fixed point) is
  the logical distance of functional expressions (Desharnais, Gupta, Jagadeesan
  and Panangaden), and its `n`-th iterate is the distance of expressions of
  depth at most `n`.
* `System`: probabilistic systems over a GSLT, with finite sub-distributions as
  steps read modulo the equations; the support erasure to a
  `HennessyMilner.System`, through `WeightedObservers.Weighting`; Larsen–Skou
  bisimulation and its logical characterisation; the erasure of bisimulations.
* `FiniteChains`: a finite chain is a probabilistic GSLT; Larsen–Skou
  bisimilarity, probabilistic bisimilarity and distance zero coincide.
* `Completion`: a finite probabilistic GSLT with sub-distributions is completed
  by a stopped state; its behavioural pseudometric is the Kantorovich fixed
  point of the completion, a logical distance, zero exactly on Larsen–Skou
  bisimilarity.
* `Domination`: the possibilistic distance of the support at discount `c · p`
  is at most the Kantorovich distance at discount `c`, for a floor `p` of the
  positive transition probabilities.
* `Controls`: equal supports with different weights, at support distance zero
  and Kantorovich distance at least `c / 4`, not Larsen–Skou bisimilar; the
  inequality attained; the factor `p` needed.
* `Causal`: noisy response-type populations with two random steps; PNS and the
  experimental marginals are two-step expressions, satisfy the Tian–Pearl
  bounds, transport along probabilistic bisimulation and along the metric, and
  along support bisimulation only as far as their positivity.
* `Semiring`: one definition of semiring-weighted GSLTs; the Boolean instance
  and the support homomorphism; the probability instance in both directions;
  observer weights as a separate layer that reads only the erasure.
* `DisjointUnion`: between two chains, the bisimulation metric is the largest
  difference of a functional expression, through their disjoint union.
* `SubDistributionDomination`: domination for systems with refusal, through the
  completion; the zero kernel is discount-free; refusal is invisible to the
  support.
* `CausalAbduction`: abduction over both random steps of a noisy population;
  PN and PS with Tian–Pearl's combined bounds; what unit-resolved data identify,
  and how a second random step breaks it.
-/
