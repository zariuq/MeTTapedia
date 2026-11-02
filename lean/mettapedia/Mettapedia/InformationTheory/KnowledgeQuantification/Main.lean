import Mettapedia.InformationTheory.KnowledgeQuantification.Basic
import Mettapedia.InformationTheory.KnowledgeQuantification.Amortization
import Mettapedia.InformationTheory.KnowledgeQuantification.Entropic
import Mettapedia.InformationTheory.KnowledgeQuantification.Hypotheses
import Mettapedia.InformationTheory.KnowledgeQuantification.Resolution
import Mettapedia.InformationTheory.KnowledgeQuantification.Coding
import Mettapedia.InformationTheory.KnowledgeQuantification.Causal
import Mettapedia.InformationTheory.KnowledgeQuantification.ProofSharing

/-!
# Knowledge as standardized compression (entry point)

D. Fanelli, *A theory and methodology to quantify knowledge*, R. Soc. open sci. 6: 181055
(2019), measures knowledge by

`K = n_Y (H(Y) − H(Y | X, τ)) / (n_Y H(Y) + n_X H(X) − log p(τ))`,

the share of all the information in an explanandum `Y`, an input `X` and a theory `τ` that
the explanation compresses.

* `Basic`: `K` of an information budget: the split `K = k η`, the range `[0, 1)`, the odds
  form, the marginal rule and its instances (progress, resolution, cumulation), relative
  Ockham, compression `K > 1 − η`, the two-part code counterexample, bias correction and
  predictive knowledge.
* `Amortization`: limits as uses grow, consilience, and unknown use counts through
  rent-or-buy.
* `Entropic`: `K` of finite distributions with the tree's entropy, divergence, mutual
  information and Bayesian information gain; the mixture identity; `K ≤ 1/2` under direct
  measurement; predictive knowledge; the value of ruling out a hypothesis.
* `Hypotheses`: ruling out the most probable hypothesis can raise uncertainty; the claimed
  symmetry `K(Y; X, T) = K(T; Y, X)` fails.
* `Resolution`: entropy under refinement and coarsening; data processing.
* `Coding`: codebook relativity and its disappearance with use, priors over infinitely many
  theories, Kolmogorov floors, and knowledge as a razor profile beside the two-part code.
* `Causal`: interventional knowledge on structural models; correlation without causation.
* `ProofSharing`: theoretical knowledge of shared and unshared proofs.
-/
