import Mettapedia.ProbabilityTheory.StochasticInference.Binary
import Mettapedia.ProbabilityTheory.StochasticInference.Readouts
import Mettapedia.ProbabilityTheory.StochasticInference.Propagation
import Mettapedia.ProbabilityTheory.StochasticInference.History

/-!
# Stochastic inference over finite rational models

This entry point supplies finite factors, identified evidence, conditional
readouts, and retained elimination. Import `StochasticInference.ProbLogic`,
`StochasticInference.MarkovLogic`, or `StochasticInference.Counts` for the
corresponding model interfaces. `StochasticInference.ProofSearch` exposes
certified partial Horn search. `StochasticInference.MeasureSemantics` connects
the numerical readouts to Bayesian measure semantics.
`StochasticInference.AnytimeMixtures` bounds unfinished model searches.
`StochasticInference.CachedLearning` supplies retained E-step statistics,
and `StochasticInference.SoftBernoulliLearning` integrates shared rates
from likelihood-scored reports. `StochasticInference.BinaryChangePoint`
filters changing Bernoulli rates. `StochasticInference.ResidualMass`
reads separate caps on unsettled outcome masses. `StochasticInference.Interventions`
constructs truncated products of binary mechanisms, and
`StochasticInference.EvidenceInvariance` gives laws for fixed likelihood
permutations and re-admission of entailed events.
-/
