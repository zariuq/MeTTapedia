import Mettapedia.UniversalAI.GrainOfTruth.Setup
import Mettapedia.UniversalAI.GrainOfTruth.BayesMixtureEnv
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.Main
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ExpectedTotalVariation
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.KLDivergenceBridge
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ThompsonSampling

/-!
# Bayesian learning with a grain of truth: what is proved here

A prior has a grain of truth when it gives the true environment positive
weight (Kalai and Lehrer 1993). This directory develops Bayesian learning over
a countable class of environments under that assumption. This module imports
every module of the directory and declares nothing.

## Proved

* The posterior weight of each environment is a martingale under the mixture
  and converges almost surely (`MeasureTheory/PosteriorMartingale.lean`,
  `MeasureTheory/PosteriorConcentration.lean`).
* The log-likelihood ratio of a wrong environment against the true one is a
  supermartingale under the true environment
  (`MeasureTheory/LikelihoodRatio.lean`).
* If every wrong environment is told apart from the true one, the posterior
  weight of the true environment tends to one almost surely, and the regret
  averaged over the posterior tends to zero for a policy that is optimal in
  the true environment (`MeasureTheory/Main.lean`).
* For every finite lookahead, the expected total-variation distance between
  the predictions of the environments and of the mixture, averaged over the
  posterior, tends to zero in mean under the mixture
  (`MeasureTheory/ExpectedTotalVariation.lean`, `tendsto_integral_F_m_prefix`;
  compare Lemma 5.27 of Leike's thesis, which is stated for the true
  environment and unbounded lookahead).
* Each agent of a multi-agent environment faces a single-agent environment. If
  its policy is asymptotically optimal in mean there, it plays an ε-best
  response with probability tending to one (`Setup.lean`,
  `convergence_to_equilibrium`; the last step of Theorem 7.30 of the thesis).

## Not proved

* That Thompson sampling is asymptotically optimal in mean (Theorem 5.25 of
  the thesis). The sampling policy is defined
  (`MeasureTheory/ThompsonSampling.lean`); the theorem is not stated.
* The class of environments computable with a reflective oracle, that the
  Bayesian mixture over it belongs to it (Proposition 7.18), and that optimal
  policies for it are computable with the oracle (Theorem 7.19). These are
  what turn the hypothesis of `convergence_to_equilibrium` into a theorem.
  Reflective oracles themselves are defined and shown to exist in
  `UniversalAI/ReflectiveOracles/`, also for every family of probabilistic
  machines that call the oracle (`Machines.exists_reflective`: Theorem 7.5);
  the environments computed by such machines are not yet defined.

So the solution to the grain of truth problem of Leike, Taylor and Fallenstein
(Corollary 7.21 and Theorem 7.30 of the thesis) is not formalized here.

## References

- Kalai & Lehrer (1993). "Rational Learning Leads to Nash Equilibrium"
- Leike, Lattimore, Orseau & Hutter (2016). "Thompson Sampling is Asymptotically
  Optimal in General Environments"
- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Leike (2016). PhD Thesis "Nonparametric General Reinforcement Learning"
-/
