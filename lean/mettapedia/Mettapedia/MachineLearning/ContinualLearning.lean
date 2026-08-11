import Mettapedia.MachineLearning.ContinualLearning.QuadraticTwoTask
import Mettapedia.MachineLearning.ContinualLearning.EvidenceLedger
import Mettapedia.MachineLearning.ContinualLearning.RetentionSafeUpdate
import Mettapedia.MachineLearning.ContinualLearning.MinimumChangeUpdate
import Mettapedia.MachineLearning.ContinualLearning.FisherRetentionBridge
import Mettapedia.MachineLearning.ContinualLearning.OrthogonalGradientRetention
import Mettapedia.MachineLearning.ContinualLearning.AveragedGradientProjection
import Mettapedia.MachineLearning.ContinualLearning.GradientEpisodicMemory
import Mettapedia.MachineLearning.ContinualLearning.ElasticWeightConsolidation
import Mettapedia.MachineLearning.ContinualLearning.FisherEstimatorBoundary
import Mettapedia.MachineLearning.ContinualLearning.NaturalContinualLearning
import Mettapedia.MachineLearning.ContinualLearning.SynapticIntelligence
import Mettapedia.MachineLearning.ContinualLearning.RiemannianWalk
import Mettapedia.MachineLearning.ContinualLearning.VariationalContinualLearning
import Mettapedia.MachineLearning.ContinualLearning.BayesianGradientDescent
import Mettapedia.MachineLearning.ContinualLearning.OptimalContinualLearning
import Mettapedia.MachineLearning.ContinualLearning.GradientBasedSampleSelection
import Mettapedia.MachineLearning.ContinualLearning.MemoryAwareSynapses
import Mettapedia.MachineLearning.ContinualLearning.ProgressiveNetworks
import Mettapedia.MachineLearning.ContinualLearning.GradientProjectionMemory
import Mettapedia.MachineLearning.ContinualLearning.TrustRegionScaledProjection
import Mettapedia.MachineLearning.ContinualLearning.FactorizedLinearForgetting
import Mettapedia.MachineLearning.ContinualLearning.InterferenceFreeLowRankAdaptation
import Mettapedia.MachineLearning.ContinualLearning.LowRankForgettingGeometry
import Mettapedia.MachineLearning.ContinualLearning.TransferInterferenceBoundary
import Mettapedia.MachineLearning.ContinualLearning.CrossTaskForgettingFlow
import Mettapedia.MachineLearning.ContinualLearning.ContinualBackpropUtility
import Mettapedia.MachineLearning.ContinualLearning.LastLayerResetGeometry
import Mettapedia.MachineLearning.ContinualLearning.OnlineLowRankConsolidation
import Mettapedia.MachineLearning.ContinualLearning.ContinualLowRankRouting
import Mettapedia.MachineLearning.ContinualLearning.SequentialPredictiveContext
import Mettapedia.MachineLearning.ContinualLearning.PackNet
import Mettapedia.MachineLearning.ContinualLearning.MaximallyInterferedRetrieval
import Mettapedia.MachineLearning.ContinualLearning.PathNet
import Mettapedia.MachineLearning.ContinualLearning.HardAttentionToTask
import Mettapedia.MachineLearning.ContinualLearning.ContextDependentGating
import Mettapedia.MachineLearning.ContinualLearning.LatentReplay
import Mettapedia.MachineLearning.ContinualLearning.AdaptiveLayerFreezing
import Mettapedia.MachineLearning.ContinualLearning.MetaTransferCausalStructure
import Mettapedia.MachineLearning.ContinualLearning.SparseMechanismShift
import Mettapedia.MachineLearning.ContinualLearning.FeatureCovarianceRetention
import Mettapedia.MachineLearning.ContinualLearning.TaskOverlapForgetting
import Mettapedia.MachineLearning.ContinualLearning.OrthogonalGradientProjection
import Mettapedia.MachineLearning.ContinualLearning.ApproximateCovarianceRetention
import Mettapedia.MachineLearning.ContinualLearning.ContinualEvaluation
import Mettapedia.MachineLearning.ContinualLearning.ReferenceNormalizedGap
import Mettapedia.MachineLearning.ContinualLearning.DirichletExpertExpansion
import Mettapedia.MachineLearning.ContinualLearning.ReplayMemoryEconomics
import Mettapedia.MachineLearning.ContinualLearning.WidthDiminishingReturns
import Mettapedia.MachineLearning.ContinualLearning.DualTimescaleLookahead
import Mettapedia.MachineLearning.ContinualLearning.RandomFourierOnlineClassifier
import Mettapedia.MachineLearning.ContinualLearning.ModelSoupGeometry
import Mettapedia.MachineLearning.ContinualLearning.StreamingLDACovariance
import Mettapedia.MachineLearning.ContinualLearning.RandomProjectionPrototypeLedger
import Mettapedia.MachineLearning.ContinualLearning.AnalyticIncrementalRidge
import Mettapedia.MachineLearning.ContinualLearning.LowRankTruncationFeasibility
import Mettapedia.MachineLearning.ContinualLearning.TwoStageSketchApproximation
import Mettapedia.MachineLearning.ContinualLearning.InvariantRiskRepresentation
import Mettapedia.MachineLearning.ContinualLearning.InvariantRiskEnvironmentThreshold
import Mettapedia.MachineLearning.ContinualLearning.FeatureCovarianceClassifier
import Mettapedia.MachineLearning.ContinualLearning.ComputeBudgetNormalization
import Mettapedia.MachineLearning.ContinualLearning.AdaptiveContinualMemory
import Mettapedia.MachineLearning.ContinualLearning.FrequencyAwareReplay
import Mettapedia.MachineLearning.ContinualLearning.RealTimeContinualSchedule
import Mettapedia.MachineLearning.ContinualLearning.TaskConfusionBoundary
import Mettapedia.MachineLearning.ContinualLearning.SupermaskTaskInference
import Mettapedia.MachineLearning.ContinualLearning.PromptPoolSelection
import Mettapedia.MachineLearning.ContinualLearning.DecomposedPromptComponents
import Mettapedia.MachineLearning.ContinualLearning.DualPromptAttention
import Mettapedia.MachineLearning.ContinualLearning.HierarchicalPromptLoss
import Mettapedia.MachineLearning.ContinualLearning.GenerativeReplayRisk
import Mettapedia.MachineLearning.ContinualLearning.ReservoirReplaySampling
import Mettapedia.MachineLearning.ContinualLearning.ModeConnectivityObjective
import Mettapedia.MachineLearning.ContinualLearning.TaskFreePlateauGate
import Mettapedia.MachineLearning.ContinualLearning.SharedHeadEvaluation
import Mettapedia.MachineLearning.ContinualLearning.HypernetworkOutputRetention
import Mettapedia.MachineLearning.ContinualLearning.StochasticSemanticMemory
import Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble
import Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge
import Mettapedia.MachineLearning.ContinualLearning.RepetitionProvenance
import Mettapedia.MachineLearning.ContinualLearning.ContrastiveEnergyUpdateSupport
import Mettapedia.MachineLearning.ContinualLearning.PredictionErrorClassification
import Mettapedia.MachineLearning.ContinualLearning.SemanticDriftCompensation
import Mettapedia.MachineLearning.ContinualLearning.LinearRepresentationDiscrepancy
import Mettapedia.MachineLearning.ContinualLearning.HadamardLieGroupUpdate
import Mettapedia.MachineLearning.ContinualLearning.StreamingRegularizedDiscriminant
import Mettapedia.MachineLearning.ContinualLearning.VirtuallyAddressedParameterMemory

/-!
# Continual-learning theory

This umbrella exposes finite quadratic interference, exactly-once evidence
ledgers, nonlinear retention trust regions, minimum-change replay
projections, Fisher/retention geometry, and finite-sequence
orthogonal-gradient retention.  The latter recovers exact no-forgetting in a
fixed-Jacobian linearization, quantifies the loss of that guarantee under
Jacobian drift, and includes a nonlinear counterexample preventing a
first-order orthogonality claim from being used as a finite-update theorem.
The A-GEM projection is exposed with its exact Euclidean minimum, its
idempotence law, and the curvature budget required for finite replay-loss
retention.  Gradient episodic memory adds the full per-task constraint
intersection, proves that averaged feasibility is a strict relaxation, and
solves a nondegenerate two-task projection exactly.  Elastic-weight
consolidation is exposed in additive information
coordinates, including exact multi-task quadratic fusion, its unique
consolidated minimizer, and zero/negative-precision boundaries.
Fisher-estimator boundaries then distinguish the exact categorical
expectation, unbiased model-label sampling, observed-label empirical
contributions, and minibatch-gradient squaring.  The batched quantity is
proved to add every pairwise cross term, with executable cancellation and
amplification fixtures preventing these estimators from being interchanged.
Natural continual learning then applies an invertible positive prior metric
to the complete Laplace-posterior gradient.  Its update is the unique
minimizer of the corresponding local trust Lagrangian and maximizes
linearized gain on its induced metric ball.  It shares fixed points with raw
Laplace-gradient optimization while an anisotropic fixture separates their
finite paths.
Synaptic intelligence contributes an exactly-once gradient/update path
ledger, safe task-boundary normalization, an exact finite-step curvature
remainder, and a shared quadratic-penalty bridge to EWC.
Riemannian Walk then replaces Euclidean path normalization by a local
diagonal-Fisher displacement.  Its online Fisher update preserves its
declared range, its per-step sensitivity is coordinate-rescaling invariant,
and explicit fixtures show that both interval segmentation and continual
averaging retain chronological information.
Variational continual learning contributes the exact finite-dimensional
diagonal-Gaussian linear-regression update.  The Sherman--Morrison mean
formula solves the source normal equation and precision increases by the
source feature-square contribution.  Exact full Gaussian information packets
commute, while an executable two-coordinate fixture proves that projecting
back to a diagonal covariance after every observation can make the mean
order-dependent even when final diagonal precision is identical.  Its
coreset schedule is additionally proved to partition every available packet
exactly once, with explicit double-counting and evidence-loss boundaries.
Bayesian Gradient Descent contributes a finite antithetic-sampling form of
its strong-curvature argument.  Strong gradient monotonicity lower-bounds
every paired sample and hence the aggregate; unit empirical second moment
recovers the source-shaped curvature bound.  The exact uncertainty recursion
is positive and its increase/decrease direction follows the curvature sign,
while a one-sided strongly-convex fixture shows why arbitrary unpaired
samples do not inherit the expectation-level sign guarantee.
Optimal continual learning then exposes a source-definition boundary before
its complexity claims: intersecting all admissible sets that contain a point
does not generally produce the membership-equivalence classes asserted in
the source.  A two-point counterexample refutes that implication.  Equality
of complete task-set membership signatures repairs the construction;
complement closure recovers the displayed intersection as a special case,
and one stored representative of every surviving repaired class is proved
sufficient for all admissible task-intersection queries.
Gradient-based sample selection then proves the exact algebra behind its
pairwise-cosine diversity surrogate and the antitone feasible-cone law for
constraint reduction.  The surrogate is the squared norm of the resultant
normalized gradient, so minimizing it exactly maximizes directional variance
at fixed buffer size.  A nondegenerate two-dimensional counterexample shows
that equal surrogate and variance can nevertheless encode different feasible
cones, while the shifted-cosine score is proved merely nonnegative: antipodal
unit gradients attain zero.
Memory-aware synapses contributes an online output-sensitivity accumulator,
the exact geometry and blind spot of squared-output scalarization, a local
active-unit derivative, and a parameterization-dependence boundary.
Progressive networks contributes exact old-task preservation under arbitrary
ordered new-column updates, a constructive lateral-transfer fixture, the
one-way directionality boundary, and the triangular cost of unshared lateral
connections.
Gradient-projection memory contributes the exact right- and left-projection
equations for fully connected and convolutional layers, the growing
orthogonal-projector algebra, zero/full-memory boundaries, and an executable
counterexample showing why orthonormalized activation bases are essential.
Trust-region scaled projection then preserves the shared-weight action on
every stored basis direction while giving a new task a small task-indexed
coordinate transform of the frozen subspace.  Identity scaling recovers the
shared weight, orthogonal inputs are unchanged, and a nonorthonormal fixture
breaks the intended coordinate action.
Factorized linear forgetting then proves that equal function classes need not
have equal continual-update dynamics.  Orthogonal task rows preserve every
old prediction along an arbitrary finite direct-linear gradient path and
preserve the old feature map of a factorized path, yet output-head motion can
still cause exactly quantified forgetting.  Full column rank makes every
nonzero head displacement strictly forgetting; a noninjective counterexample
shows why that premise is necessary.
Interference-free low-rank adaptation then identifies output-factor training
with a projected dense gradient, bridges the selected row space to the GPM
residual projector, proves exact retention on annihilated linear activations,
and separates that result from merely first-order loss orthogonality.
Low-rank forgetting geometry recovers the source's rigorous smooth Taylor
budget, proves that orthogonality removes only the first-order term, and gives
an exact common-upper-model counterexample showing that first-order angle
data alone cannot determine finite forgetting.
The transfer--interference boundary recovers pairwise gradient alignment as
the first-order term of an exact finite quadratic update. Positive alignment
always admits a safe positive step but does not license arbitrary step sizes;
negative alignment causes strict finite interference at every positive step.
The cross-task forgetting flow supplies the continuous-time complement:
old-task half-squared residual energy changes by the negative pairing of old
residual with the new residual transported through the cross-task kernel.
An operator-norm budget controls its magnitude, while a positive-semidefinite
joint-kernel fixture proves that residual orientation can still reverse its
sign.
Continual-backpropagation utility contributes the exact finite-age exponential
average and its bias correction, exposes the lag in the printed correction
formula, and proves that transferring a removed unit's mean contribution to
the consumer bias preserves the preactivation exactly at that mean. Away from
the mean, the replacement drift is an explicit weight-times-deviation term.
Last-layer reset geometry then proves the exact representation-gradient
perturbation law for a finite linear head, separates equal predictions from
equal upstream credit, and solves the frozen unit-feature relearning recurrence.
The same nondegenerate relearning schedule preserves the strict ordering of
initial head losses, so any benefit from resetting a worse head must pass
through representation learning, path dependence, or another mechanism absent
from the frozen-feature restriction.
Online low-rank consolidation adds the exact merge-and-zero-reset lifecycle,
arbitrary-trigger function preservation, repeated-packet algebra, the boundary
between active and accumulated rank, and nonnegative streaming diagonal
empirical-Fisher penalties.
Continual low-rank routing identifies block-diagonal routing with a mixture of
low-rank experts, proves exact old/fresh forward and gradient decompositions,
recovers the strict gradient-magnitude theorem under its load-bearing alignment
condition, and exposes both anti-alignment and finite-forgetting boundaries.
Sequential predictive context recovers the exact scalar predictive-coding
state-energy law, separates symmetric feedback from a sign-reversed
energy-increasing fixture, identifies the printed context-memory drift as
contraction rather than repulsion, and proves the normalization boundary for
competitive task routing together with safe running error moments.
PackNet contributes an executable parameter-ownership semantics, exact
old-task preservation across arbitrary admissible later traces, monotone
birth-task masks, a hard capacity-exhaustion boundary, and a nonlinear
simultaneous-inference counterexample.
Maximally interfered retrieval contributes the exact finite virtual-loss
score, its first-order alignment term and curvature remainder, a computable
finite-step safety budget, the historical-best baseline relation, and ranking
counterexamples separating gradient conflict from actual finite interference.
PathNet contributes bounded-width routed module paths, exact preservation of
a frozen source computation across arbitrary later routed updates, reusable
frozen overlap, a width-independent active-module bound, and executable
plasticity and no-freezing boundaries.
Hard attention to the task contributes learned logistic masks, monotone
cumulative attention, the exact reverse-minimum gradient gate, arbitrary-trace
preservation at the binary endpoint, soft-mask drift accounting, normalized
remaining-capacity bounds, and out-of-range counterexamples.
Context-dependent gating then gives fixed task masks an exact finite support
semantics. Active connection counts and cross-task overlap factor through the
two endpoint masks, disjoint new-task updates preserve an old masked linear
readout, and the source's eighty-percent unit gate activates exactly four
percent of hidden-to-hidden connections. A shared-bias counterexample prevents
this layer-local result from being promoted to whole-network no-forgetting.
Latent replay makes frozen-representation caching an explicit relation:
authenticated cached activations reproduce every downstream native-replay
update, finite representation drift bounds cache aging and its Lipschitz
downstream effect, and refresh resets the pointwise age error. Fixed weights
with mutable normalization state do not meet the frozen-map premise.
Adaptive layer freezing then puts that boundary under an explicit compute
exchange. Its batch criterion has an exact per-layer recurrence and benefit
threshold; a two-layer fixture separates the globally best Fisher-per-compute
prefix from the current batch's safe choice. Similarity-aware replay is
normalized and order-correct only at positive temperature, while negative
gradient similarities make its effective-use quantity a signed score rather
than a literal frequency.
Compute-budget normalization then gives auxiliary operations a shared integer
work unit and proves that integer division returns the greatest affordable
iteration count exactly when per-iteration work is positive. It recovers the
source's two-thirds distillation and one-half costly-sampling ratios on
divisible budgets, exposes the one-unit overspend caused by rounding
two-thirds of one hundred upward, and characterizes exact allocation of a
fixed horizon across stream steps by divisibility.
Adaptive continual memory then isolates the exact one-nearest-neighbor
consistency core. A newly prepended packet is recalled immediately, and
finite later inserts preserve a stored label when their features differ from
the queried feature. Conflicting duplicate labels, three-neighbor majority
voting, and encoder drift provide executable boundaries to unconditional
fast-adaptation or no-forgetting claims.
Meta-transfer causal structure then recovers the source's finite categorical
unchanged-mechanism score identity and exact two-hypothesis regret derivative.
At a matched positive law every simplex-tangent expected score vanishes, but a
shifted evaluation law need not. The structural gradient is a positive scale
times the online-likelihood gap, so its sign selects the faster-adapting
hypothesis; equal likelihoods provide no signal and zero likelihoods violate
the statistical premise.
Feature-covariance retention proves that a finite real feature matrix and its
uncentered covariance have the same null space, lifts covariance-null updates
through arbitrary-depth square networks and arbitrary deterministic
activations, and exposes both the full-rank loss-of-plasticity boundary and a
conditioning counterexample where tiny covariance residual coexists with unit
output drift.
Task-overlap forgetting factors finite source-task prediction drift through
the overlap of fixed source and target feature bases, extends the identity to
an arbitrary later-task trace, and proves exact orthogonal-subspace
retention.  Its fixtures distinguish overlap from learned coefficient size,
expose cancellation of large intermediate drifts, and show that a stale
zero-overlap certificate fails when the feature map changes.
Orthogonal-gradient projection recovers the multi-direction OGD update,
proves exact annihilation of the stored basis and the sharpened current-task
descent identity, and separates weak from strict descent according to whether
any plastic component survives.  Full memory erases all plasticity, while a
nonorthonormal scalar memory reverses the nominal direction into strict
ascent.
Approximate covariance retention closes the practical truncated-SVD gap with
an exact covariance-energy identity and an observable multi-output bound:
stored-output drift squared is controlled by update one-norm times
coordinatewise covariance residual.  A tight scalar fixture proves that the
residual cannot be interpreted without the update magnitude.
Low-rank truncation feasibility then separates projection from exact
interpolation.  An orthogonal retained-subspace projector gives the unique
representable least-squares prediction and an exact Pythagorean loss
decomposition.  Exact interpolation holds precisely when every target row is
fixed by the projector, with a proper rank-one positive and negative fixture.
Two-stage sketch approximation then separates packetwise truncation from
streaming-sketch error.  Their finite norm budgets compose additively in any
normed additive group, while executable fixtures show both that local errors
may cancel and that a perfect packet approximation cannot control an
uncertified downstream sketch.
Invariant-risk representation then proves the source's fixed-scalar
first-order characterization in real Hilbert spaces.  Any simultaneous
optimum over a continuous linear representation is orthogonal to every
environment gradient, and those equations make scalar classifier one
simultaneously optimal for the predictor-generated rank-one representation.
Opposed transverse affine risks give a nonzero positive fixture, while an
aligned affine gradient gives the negative boundary.
The finite-environment threshold then exposes two further geometric cores.
Strictly fewer scalar environment constraints than nuisance coordinates
always leave a nonzero invisible direction, while an equal-dimensional
identity constraint shows why equality needs additional structure.  For a
declared nonzero minimum-norm base solution, Pythagoras bounds every
nonnegative unit-solution scale by the inverse base norm and makes equality
equivalent to eliminating the orthogonal residual.  Cancellation without
orthogonality supplies the negative boundary.
Continual evaluation formalizes finite-window minimum accuracy, maximal
forgetting and plasticity moves, and the source's WC-ACC lower-bound relation.
Window enlargement is proved monotone in the expected direction, while a
three-update trace proves that task-boundary evaluation can report perfect
retention and miss an interior unit drop completely.
Reference-normalized gaps then isolate the common algebra of stability,
plasticity, and continual-knowledge gaps: positive references recover zero
under exact matching, better pointwise performance monotonically lowers the
gap, strict transfer makes it negative, and a zero-reference fixture exposes
the load-bearing denominator condition.
Dirichlet expert expansion recovers the finite responsibility algebra behind
task-free neural mixture growth. Existing and candidate responsibilities
conserve unit mass, normalization preserves existing pairwise odds, and the
candidate wins exactly when its raw score is maximal. If the candidate is
rejected, conditioning back on existing experts cancels its score exactly and
makes the stored-count update add one example. A two-expert fixture shows that
omitting this second normalization adds only three quarters of an example.
Replay-memory economics then derives an exact one-sample improvement threshold
from the two-task pure-replay expected-forgetting closed form. The same extra
sample improves the expression when retained-task mass dominates
task-dissimilarity, but worsens it on the opposite side; executable fixtures
realize both regimes.
Width diminishing returns then isolates the source power-law width envelope.
Equal multiplicative width expansions have geometrically shrinking absolute
benefit, while simultaneous task/depth load growth is offset exactly when it is
smaller than the corresponding width power. Zero and negative exponents expose
the load-bearing sign premise.
Dual-timescale Lookahead finally isolates the fast/slow update used by DualNet.
It preserves every inner fixed point and, under an explicit pointwise
contraction premise, gives the exact affine rate
`1 - beta + beta * q ^ K`. Zero interpolation discards the fast endpoint, while
an over-relaxed scalar fixture turns a perfect inner contraction into
factor-two expansion.
Random Fourier online classification then recovers the exact normalized
cosine--sine feature geometry and its online class-mean recurrence. The
finite similarity is symmetric, bounded by one, and exactly one on the
diagonal; a full-period phase collision prevents normalization from being
mistaken for injectivity. The online update counts every sample exactly once
and is order-independent on a two-sample fixture.
Frozen random-projection prototype ledgers then recover RanPAC's additive
Gram and class-prototype statistics. Both ledgers are invariant under every
permutation of a fixed projected sample collection, and a positive identity
ridge makes the Gram matrix positive definite without a full-rank data
premise. The scalar closed form uniquely minimizes its regularized squared
error under a positive quadratic coefficient. A changing-projector fixture
breaks raw-order invariance, while a singular negative-ridge fixture exposes
the danger of totalized division.
Analytic incremental ridge regression then proves ACIL's complete matrix
recursion.  An explicit two-sided inverse contract turns the batch Schur
inverse into a Woodbury inverse of the enlarged normal matrix; the residual
head correction is exactly the joint ridge head and satisfies the enlarged
normal equation.  Fixed-feature sufficient statistics commute without a
class-disjointness premise.  Changing the ridge or a position-indexed feature
map breaks the equivalence, singular matrices fail the inverse contract, and
a scalar recovery theorem prevents exemplar-free inverse statistics from
being promoted to a privacy theorem without an additional threat model.
Feature-covariance classification then isolates FeCAM's exact probabilistic
boundary. Positive-semidefinite precision gives a nonnegative Mahalanobis
quadratic and identity precision recovers Euclidean distance. With shared
positive precision and equal priors, Gaussian-density ranking is exactly
Mahalanobis ranking. Class-dependent precision requires its Gaussian
normalizer: a scalar fixture reverses the Mahalanobis-only decision, and two
positive-definite unit-diagonal correlation matrices have different
determinants. Correlation normalization alone therefore does not recover a
complete heterogeneous Gaussian Bayes classifier.
DualPrompt attention finally separates prompt tuning from prefix tuning at
the exact scalar-attention boundary. Prompt tuning adds output-query
positions, whereas prefix tuning leaves their count unchanged. A nonempty
key--value prefix changes a token output by its softmax-mass share times the
difference between the separately normalized prefix and token outputs, and
therefore preserves the old output exactly only when those outputs agree.
Hierarchical prompt loss then turns the correct-class probability factorization
into exact additive negative-log loss. Nonnegative bounds on within-task,
task-identity, and task-adaptive loss give a maximum envelope, while a small
complete loss forces every component below the same budget. A strict fixture
corrects the source appendix's substitution of upper bounds as equalities.
Generative replay finally separates the distributional and target-substitution
errors hidden inside replay equivalence. The train--test risk gap is exactly the
retained old-data weight times their sum. Perfect input generation removes only
the first term; teacher agreement or exact cancellation is still required.
Reservoir replay then proves the horizon-free marginal invariant used by Dark
Experience Replay. Uniform admission followed by uniform conditional eviction
maps every old and new item to the same capacity-over-stream-length marginal,
propagates through any finite continuation, and preserves expected occupancy.
A biased-eviction fixture shows that the admission probability alone is
insufficient.
Mode-connectivity objectives finally expose the exact linear-path boundary.
Convex endpoint losses control their complete segment, but low endpoints alone
do not: a nonconvex barrier has zero endpoint loss and unit midpoint loss.
Finite-grid path penalties split into endpoint and interior terms, while a
two-task quadratic proves that a unique aggregate minimizer need not minimize
either component task.
Task-free plateau gating then models the two sequential tests used to trigger
importance consolidation without declared task boundaries. A plateau with no
simultaneous peak disarms the gate and cannot repeat; a later peak rearms it.
A threshold-order theorem excludes overlap, while an executable fixture shows
that overlapping independent `if` tests can consolidate and immediately
rearm on the same observation.
Virtually addressed parameter memory then separates immutable stored
competence from mutable accessibility. Positive temperature scaling preserves
hard winners while candidate insertion dilutes every old softmax weight and
can displace an old hard route. Resource-bounded recall carries an explicit
address-cost and optimization debit, and its exact regularization path trades
raw task energy monotonically for cheaper addresses. Functional success is
formalized as an input--memory competence relation, connected to the existing
projection-aware WM-PLN accounting and its exact leave-one-witness coverage
decomposition. Frozen PathNet evaluation and low-rank consolidation instantiate
the shared storage-invariance interface, while an executable example proves
that accessibility can remain strictly below availability.
-/
