import Mettapedia.Cybernetics.ApproximateAdequacy.ApproxBisimulationLaws
import Mettapedia.Cybernetics.ApproximateAdequacy.SquareIteration
import Mettapedia.Cybernetics.ApproximateAdequacy.Coupling
import Mettapedia.Cybernetics.ApproximateAdequacy.CouplingBound
import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric
import Mettapedia.Cybernetics.ApproximateAdequacy.LogicalCharacterisation
import Mettapedia.Cybernetics.ApproximateAdequacy.MassFunction
import Mettapedia.Cybernetics.ApproximateAdequacy.ProbabilisticSquares
import Mettapedia.Cybernetics.ApproximateAdequacy.Weighting
import Mettapedia.Cybernetics.ApproximateAdequacy.DefectLaws
import Mettapedia.Cybernetics.ApproximateAdequacy.Hosting
import Mettapedia.Cybernetics.ApproximateAdequacy.Combined
import Mettapedia.Cybernetics.ApproximateAdequacy.DeliveryExample
import Mettapedia.Cybernetics.ApproximateAdequacy.RoadMapExample
import Mettapedia.Cybernetics.ApproximateAdequacy.DelayedFailureExample

/-!
# Approximate adequacy of a model of a world

What an approximate model of a world certifies, for six notions, and how the
certificates relate and compose.

* `ApproxBisimulationLaws`: Girard–Pappas approximate bisimulation.  It
  certifies observations along every run within `ε` for every horizon, and
  positive modal formulas up to inflation; errors add under sequential and
  parallel composition.
* `SquareIteration`: approximate update squares.  A square certifies a
  one-step prediction; over `n` steps the error is `δ Σ κ^k`, uniformly
  bounded by `δ / (1 - κ)` exactly under a contraction.
* `Coupling`, `CouplingBound`, `BisimulationMetric`: the behavioural
  pseudometric of Desharnais, Gupta, Jagadeesan and Panangaden on finite
  labelled Markov chains.  Coupling bounds are checkable certificates over any
  ordered field; the metric, defined by iterated Kantorovich liftings, is the
  least of them, a fixed point, zero exactly on probabilistic bisimilarity,
  and a pseudometric.  Every functional expression varies by at most the
  metric; along a plan of `n` actions, expected observations by at most the
  bound over `c ^ n`.
* `MassFunction`: over `ℝ` the finite distributions are Mathlib's `PMF`s on
  a finite type, with the same point masses and supports.
* `LogicalCharacterisation`: on a finite chain at a positive discount, zero
  distance, probabilistic bisimilarity and agreement on every functional
  expression coincide.
* `ProbabilisticSquares`: probabilistic update squares with error `δ`, at
  discount `c < 1` with `c κ ≤ 1`, bound the behavioural distance of every
  world state to its view by `c δ / (1 - c)`; deterministic squares on
  products add their errors.
* `Weighting`: goal-weighted averages certify an expectation bound and a
  Markov tail bound, nothing uniform, nothing off the goal paths, and nothing
  for a new goal that charges a path outside today's support.
* `DefectLaws`: correspondence defects of path maps certify compositional
  reuse of the mind's arrows; composite correspondences multiply and add
  defects; averages compose along the push-forward weighting.
* `Hosting`: exact state-level closeness gives exact theory-level hosting;
  positive state-level error gives no hosting bound for crisp sentences.
* `Combined`: a defect bound together with a drift bound, and its
  composition law.
* `DeliveryExample`, `RoadMapExample`: every notion computed on a delivery
  over a slippery bridge and on the road map under revision.
* `DelayedFailureExample`: discounting forgives a delayed failure that no
  approximate bisimulation below `1` tolerates.
-/
