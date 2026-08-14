import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.Core
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.PrecisionBiasedRead
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.CausalInnovationLedger
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.EvidenceMemoryDynamics
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.CausalEvidenceTransport
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ConditionalInformationNovelty
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.EvidentialOpinion
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.PriorNetworkUncertainty
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.FastWeightMemory
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.InContextGradientDescent
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RankOneAssociativeExperts
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ModernHopfieldRetrieval
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.DecayingFastWeightMemory
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RecurrentFastWeightProgrammer
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RecurrentIndependentMechanisms
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.CompetitiveIndependentMechanisms
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.SoftMixtureOfExperts
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.DynamicHypernetwork
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ContinualFeatureReplacement
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.TaskVectorArithmetic
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.LocalizedTaskArithmetic
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.DifferentiablePlasticity
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.NeuromodulatedPlasticity
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.SparseNeuromodulatedMemory
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.NeuralTuringMemory
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ExpertChoiceRouting
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ExpertLoadBalance
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.LossFreeExpertBalancing
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RouterPerturbation
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RetentionEconomics
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.BayesPCNDiffusion
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RoutedTensorTransition
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RoutedTensorTransitionExample
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ActiveSlotRestriction
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.MixedRadixAddressTransition
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.StateCarrier
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.EvidenceTransitionClosure

/-!
# Unified carrier

Umbrella import for the exact-real carrier algebra, provenance-aware
exactly-once innovation, conditional-information novelty, its nontrivial
continuous evidential-opinion and predictive-uncertainty decompositions,
`StateCarrier` instance, retention
economics, BayesPCN diffusion semigroup, active-slot boundary, and source-bound
binary32 transition fixtures.  It also exposes the exact equivalence between
streamed outer-product fast weights and unnormalized linear attention, together
with the delta-rule editability boundary for repeated keys.  The in-context
gradient-descent bridge identifies a residual outer-product memory with the
negative prediction change of one finite-batch linear-regression update.  Its
query-token theorem recovers the updated prediction exactly, while a
contamination fixture exposes why a zero-target query cannot generally join
the key/value set at nonzero initial weight.  Routed rank-one
associative experts add exact atomic matrix/read decomposition, sparse-support
budgets, and the zero-activation, dense-crosstalk, and post-threshold
normalization boundaries.  Modern Hopfield retrieval adds an exponential
score-margin bound on off-target mass and coordinate error, together with
equal-score collision and zero-temperature boundaries.  Recurrent
fast-weight programmers add a second delta-programmed recurrent matrix and a
previous-output-dependent controller projection, with exact feedforward
collapse and nontrivial recurrence fixtures.  Recurrent independent mechanisms
separate sparse activation, local transitions, and sparse communication:
inactive state is preserved exactly, while active mechanisms may still read
dormant memory.  Competitive independent mechanisms specialize this boundary
to winner-only expert learning: distinct winners commute exactly, while
overlapping noncommuting updates remain order-sensitive.  Soft mixtures of
experts provide the complementary continuous router: one shared logit matrix
has distinct token-normalized dispatch and slot-normalized combine semantics,
both with full positive support.  Dynamic hypernetworks generate time-varying
row scales for fixed recurrent matrices, with exact fixed-network endpoints
and an explicit within-row expressivity boundary.  Continual feature
replacement isolates the zero-outgoing-weight reset boundary, the exact raw
and mean-transferred readout disturbance, and the strict maturity gate, while
showing why centered utility alone cannot certify an untransferred reset.
Task-vector arithmetic then makes checkpoint editing's shared-anchor algebra
explicit, including the residual offsets and failure of mixed-anchor
analogies.  Differentiable plasticity
then separates fixed weights,
episode-local Hebbian traces, and learned connection-wise plasticity
coefficients, including exact fixed-network and decay boundaries.
Neuromodulated plasticity adds simple and delayed eligibility-gated writes,
with the old-versus-new eligibility timing boundary pinned explicitly.  Sparse
neuromodulated memory composes that plastic state with an active-set write
boundary, so dormant state is provably untouched.  The decaying
variant recovers the finite weighted-attention expansion and makes chronological
order sensitivity explicit.  Neural Turing
memory adds normalized convex reads, one-hot recovery, commutative batched
erase/add heads, and the exact order defect of incorrectly sequencing complete
write heads.  Loss-free expert balancing adds a causal historical-load
controller, its exact two-expert correction law, and the future-token boundary
of batch-wide expert choice.  Expert-load balance adds the quantitative
coefficient-of-variation certificate and separates importance balance from
token-count balance.  Conditional-information novelty separates geometric
direction from evidence accounting: the Schur complement is positive
semidefinite exactly when the corresponding joint covariance is, exact
duplicates contribute zero, and zero cross-covariance retains full information.
-/
