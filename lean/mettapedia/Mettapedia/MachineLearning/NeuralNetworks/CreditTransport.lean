import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Core
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ResourceSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Equivalence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Counterexamples
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ExactReverse
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.Predictive
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.PrimalDual
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.BroadcastProxy
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TargetPerturbation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TemporalEquilibrium
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.HolomorphicPhase
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ContinuousHolomorphic
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ImplicitEquilibrium
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ImplicitHolomorphicEquilibrium
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.SplittingOptimizer
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.VerifierFlow
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceAdjoint
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ResidualLagrangian
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ParameterLagrangian
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ForwardComposition
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.HilbertGradient
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceExtensionality
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ExistingInstances
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualContinuation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ContinuationTaskBias
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MechanismTelemetry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActiveFrontierSettling
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DynamicFrontierTrace
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearTiedProxy
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CompositeTaskCurvature
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LogitLossCurvature
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrecisionSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OperatorClassification
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OperatorSplitting
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearResolvent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearForwardBackward
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactForwardBackward
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ResolverResidual
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ProspectiveResidualSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ErrorCoordinateResidualSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualStability
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LocalAmortizedInitialization
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedCreditReadout
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedSettlingTrace
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OptimizerTransport
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NeuralCertificateReplay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SpectralPolynomialAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SafeguardedCompositeBlock
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DeepErrorCoordinateAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CurvatureDriftAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MaskedThreeSiteLayout
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegionalErrorCoordinateContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegionalLinearizationCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LocalRegionalCertificateExistence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearReadoutGradientTransport
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CompositionalJacobianBounds
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionEvaluationError
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionReplayChain
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteCoordinateErrorCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionExpressionCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegisteredUnaryExpressionCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalExpressionCertificateChecker
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalExpEnclosureCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalRangeReducedExpEnclosureCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalActivationEnclosureCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalRangeReducedActivationEnclosureCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalUnaryWireCertificateChecker
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalMixedExpressionCertificateChecker
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RuntimeCenterTransport
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SiLUTransitionBounds
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteMatrixOperatorBounds
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedCheckpointGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ReplayGeometryBridge
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayBatchCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayCoverageCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplayChunkedGeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedActivationReplaySite1Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineSiLUReplaySite1Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AddMaskReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32HiddenStageReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedHiddenStageReplaySite1Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReadoutReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReadoutReplayBatchGeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageResidualReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedThreeHiddenStageResidualReplayInvocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.JacobianRemainderContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ParameterTracking
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FixedPointSensitivity
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.VaryingScheduleTracking
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualFixedPointSensitivity
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ContinuationKKTSensitivity
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ThirdFamilyGateFixtures

/-!
# Credit-transport calculus

This umbrella exposes the typed transition-system semantics, multidimensional
resource accounting, equivalence lattice, valid refinement arrows, finite
counterexamples separating invalid converses, and the first exact-reverse,
predictive, primal-dual, broadcast, learned-proxy, inverse-target, forward-
derivative, function-evaluation, temporal-eligibility, equilibrium, reversible-
echo, finite-phase, auxiliary-splitting, detached-objective,
implicit-equilibrium, continuous-contour, optimizer-transport, and verifier-flow
instances. It also exposes the metric-free, occurrence-aware residual-Lagrangian
derivation of exact reverse covector recursion and tied-parameter task
derivatives on heterogeneous finite DAGs, together with the derived Hilbert
adjoint-gradient presentation, typed occurrence-reindexing invariance, and the
exact active/inactive mask partition. Concrete shared-residual and tied-
recurrence instances connect those identities to executable scalar evaluators.
The settling layer includes global and local fixed-point sensitivity, finite
parameter tracking, exact varying-schedule drift convolutions, explicit
neighborhood-overlap boundaries, and an exact positive-leak instance of the
scalar primal-then-dual transition. Residual-certified amortized settling also
transports state error through a declared Lipschitz credit readout, so an
adaptive stopping threshold controls the parameter-update signal rather than
only the hidden solver state. Work-normalized truncation then turns a certified
finite-credit error ball into an observable positive-alignment gate using the
finite credit's own norm, retains equilibrium mismatch as a separate residual-
budget term, and compares uniform task-decrease guarantees under fixed plus
per-sweep work. Positive and negative fixtures show respectively when extra
cheap rounds improve the bound and when fixed overhead reverses that
conclusion; neither theorem substitutes guaranteed loss decrease for realized
verifier yield.
Proof-carrying settling traces keep certificate assumptions outside measured
rows, reconstruct every derived error, alignment, descent, and work field, and
reject understated radii or nonmonotone accepted energies.  The optimizer
boundary is explicit: positive uniform norm clipping preserves alignment, but
adaptive coordinate scaling, stale moments, and decoupled weight decay need a
separate transport-error certificate before raw local credit licenses the
actual parameter displacement.
Fixed-checkpoint neural replay is typed at that boundary: tensor-resolved rows
reconstruct the raw-to-optimizer transport distance and the sign convention of
the displacement, while prospective and deep error-coordinate rows separately
reconstruct the final energy-gradient norm divided by precision.  Agreement
with a longer finite settling depth is explicitly not equilibrium evidence;
the emitted algebraic residual becomes an equilibrium-distance certificate
only after method-specific curvature or monotonicity and readout bounds are
supplied.
Conditional acceleration begins only after curvature accounting.  A task with
declared lower curvature bound `-rho` plus a `precision`-strongly-convex
penalty has modulus `precision - rho`; positive precision alone is therefore
not a convexity certificate.  An exact two-mode quadratic fixture then proves
the accelerated slow-mode recurrence, its closed form, strict improvement over
plain settling after four sweeps, annihilation of the high mode, and reduction
to plain settling at zero momentum.  Negative-curvature and persistent-oracle-
error fixtures keep nonconvex expansion and approximation floors outside that
positive theorem.  The spectrum-wide polynomial rung then proves a simultaneous
two-sweep contraction for every finite SPD mode in a declared interval, transports
it through an explicit linear-isometric diagonalization, and packages the result
as a contraction certificate with inherited inexact-solver error floor.  Its
two-mode endpoint fixture attains the uniform factor, while the first scheduled
sweep expands the high mode; only the composed solver is certified.  General
nonlinear acceleration still requires its own invariant-region, smoothness,
curvature, and oracle-error certificates.
The nonlinear readout side now has a compositional certificate calculus.
Forward motion, Jacobian norm, and Jacobian variation compose through addition
and the chain rule, with intermediate-region preservation stated explicitly.
The exact three-error-site residual shape—one fixed base, three masked linear
injections, two nonlinear transitions, and a final affine readout—therefore
yields recursive source bounds that feed the nonlinear pullback certificate.
A scalar fixture proves that dropping the inner forward rate from the
Jacobian-variation chain rule is unsound.  The registered hidden-transition
shape is also certified directly: affine maps followed by coordinatewise SiLU
on finite Euclidean states have explicit regional derivative and derivative-
variation bounds, and the subsequent zero-one node mask is nonexpansive with
constant Jacobian.  Trained linear operator norms, an admitted invariant
region, and downstream task/readout bounds remain separate premises.
Finite checkpoint matrices now have an auditable conservative bridge: their
Euclidean operator norm is bounded by the finite sum of all entry magnitudes.
The bound is deliberately reducible to entrywise arithmetic; a two-dimensional
all-ones fixture proves that the largest entry alone is not a sound substitute.
Runtime-audited intermediate centers are not silently identified with exact
real evaluation of this recurrence.  A separately certified center mismatch
enlarges each transported hidden-state ball additively, and the complete
three-site `R/J/H` budget is recovered on those audited balls.  A unit fixture
proves that dropping this mismatch is unsound even when the exact transported
radius is zero.
Finite-precision evaluation error is factored one level further: local error
at a stage and mismatch already present in its input compose as
`localError + rate * inputError`.  The corresponding one-, two-, and
three-stage theorems turn independently certified local arithmetic errors into
the center-mismatch bounds above.  Separate counterexamples show that neither
input mismatch nor local evaluation error may be omitted.
Finite coordinatewise interval bounds then discharge each Euclidean local
error by summing their nonnegative radii.  A two-coordinate fixture proves
that taking only the largest coordinate radius is not sound.
The scalar expression-certificate layer replays the remaining local bound
composition through variables, constants, addition, multiplication, Boolean
masks, and explicitly certified unary maps.  Exact-value ranges are checked by
a separate indexed derivation.  Multiplication retains its operand-error
cross term, and under-sized global certificates are uninhabitable by
soundness.  Its source-facing unary vocabulary is finite: square, sigmoid, and
SiLU carry exact real semantics with proved regional output and pairwise-rate
bounds.  A separate rational wire checker validates the algebraic subset by
kernel reduction and exports a real error theorem; registered unary wire nodes
are rejected until their source-specific floating-point evaluation enclosure
is supplied.
Raw IEEE-754 binary32 checkpoint words have an exact real-valued bridge as
well: finite words are decoded without decimal rounding, flat tensors receive
an explicit `[output, input]` row-major matrix view, and the decoded matrix
inherits the entrywise operator-norm bound.  Infinity and NaN words are
excluded by the source type, while an asymmetric fixture proves that tensor
layout cannot be inferred from shape alone.
Concrete replay certificates extend that bridge through the audited hidden
transition `(SiLU(affine(center)) + error) * mask`.  Exact binary32 word
equalities connect affine output to activation input, activation and recorded
error to addition, addition to the Boolean mask, and each masked center to the
next stage's affine input.  The third center is likewise connected to the
final affine residual readout.  The resulting theorems transport all four
local replay budgets through explicit point-pair rates.  They do not infer global
regularity, identify backend accumulation order, or turn endpoint provenance
hashes into kernel evidence; an independently valid but miswired stage is
rejected by the executable checker.
One authenticated trained-checkpoint affine invocation is also exposed here.
Its kernel theorem certifies exact decoded-real arithmetic among the supplied
binary32 words and a pointwise nonzero error budget.  Checkpoint, ledger,
invocation, endpoint, and generated-source identity remain the responsibility
of the separately hash-pinned verifier.  This single affine replay is not a
backend accumulation model, uniform regional bound, hidden-stage replay, or
complete-network replay.
For the implemented three-site deep error-coordinate solver, the active-space
boundary is stricter still: the full stored tensors contain inactive padding
directions that affect neither the task readout nor the masked precision penalty.
A nonzero padding-only fixture therefore refutes strong monotonicity on the full
storage space.  On the compacted active three-site product, an explicit modal
task-gradient certificate lifts the spectrum-wide two-rate contraction and its
uniform inexact-block error floor.  A six-mode endpoint fixture carries both
curvature endpoints at every site and attains the exact `4/7` contraction factor.
Binding this quadratic reference certificate to the nonlinear trained adapter
still requires active-coordinate extraction, local curvature and remainder
bounds.  Composite-step acceptance is exposed separately: a complete
accelerated endpoint is accepted only when it passes the declared energy
tolerance, otherwise execution falls back to a baseline map.  Selection
preserves geometric convergence toward a common target under separate
target-contraction certificates, without claiming pairwise contraction across
different selector branches.
When curvature changes between the two scheduled sweeps, the terminal factor
differs from the fixed-curvature polynomial by two ordered first-order terms
and one quadratic interaction.  A pointwise drift certificate now adds that
exact envelope to the fixed-spectrum contraction factor and lifts the result
through the same active-state isometry.  The unchanged-curvature fixture
recovers the exact `4/7` block, while a finite second-sweep curvature jump makes
the nominally accelerated mode expansive.  Sampled local Ritz values remain
diagnostics rather than uniform spectral or drift certificates.
Constraint release is connected to task loss only through an explicit feasible repair,
with lower-boundedness and repair regularity exposed as necessary premises.
Approximate credit is connected to finite task descent through a conservative
four-error norm certificate and a sharper directional-curvature trust region;
positive first-order alignment alone remains insufficient.  The nonlinear
shared-parameter lift now takes the Fréchet derivative of every tied use at the
actual parameter point, sums all adjoint-Jacobian local credits, identifies the
exact aggregate proxy error, and bounds it by the complete derivative-weighted
occurrence budget.  This aggregate recovers the occurrence-aware KKT gradient
for exact node credit and licenses a finite task step only through the existing
curvature-aware descent certificate.  Local errors may cancel or reinforce, so
neither a single occurrence nor an unpropagated proxy norm is a sound substitute.
The field-generic implicit-equilibrium layer is shared by complex contour
readout and real KKT continuation.  At a hard KKT endpoint, dual leak produces
multiplier-only forcing; inverse-Jacobian conditioning and multiplier magnitude
jointly bound the local branch response, and neither factor is silently
discarded.
Statistical and penalty precision remain distinct typed quantities.  The
operator layer derives affine integrability from circulation, separates
Euclidean and metric-gradient certificates from monotonicity, and extends the
classification to proof-carrying resolvent and forward--backward steps.  A
global Hilbert-space lift derives firm nonexpansiveness, implicit-solve
uniqueness, and the fixed-point/zero correspondence from nonlinear
monotonicity.  Nonlinear forward--backward composition preserves the explicit
map's contraction factor, exposes exact zeros of the summed operators, and
therefore inherits finite-step initializer and stopping certificates.  Its
positive fixture is genuinely nonlinear, while matched skew and anti-monotone
fixtures separate stable implicit dynamics from scalar-potential and
unlicensed forward dynamics.  A uniformly inexact resolvent is tracked without
identifying it with the exact solver: per-step approximation errors accumulate
geometrically, induce an explicit error floor, and enter a sound residual
stopping rule.  A sharp biased-solver fixture shows that nonzero approximation
error can move the fixed point even when every step remains uniformly close.
For monotone resolvents, the observable equation residual of each proposed
implicit output bounds its distance from the exact solve.  This converts
per-solve residuals into pointwise stopping certificates and a time-ordered
finite-trajectory error budget without first assuming global solver accuracy.
For prospective quadratic-penalty settling on the active latent subspace, the
implicit-equation residual is exactly the final energy gradient divided by
penalty precision whenever precision is nonzero.  Monotonicity of the scaled
task gradient is a separate premise for turning that residual into distance
from equilibrium, and energy descent alone is proved insufficient to recover
the endpoint gradient.  Deep error-coordinate settling has the same exact
zero-input equation on its active product space: its final energy gradient
divided by precision is an algebraic resolver residual.  More generally, a
`rho`-hypomonotone task gradient is licensed when quadratic precision strictly
exceeds `rho`: the final energy-gradient norm divided by `precision - rho`
bounds equilibrium distance and the stationary state is unique.  A mildly
concave fixture attains this corrected bound, while equality of precision and
negative curvature leaves multiple stationary states.
The third-family admission layer keeps eight candidate mechanisms unnamed
unless ten independent mathematical, implementation, prior-art, and empirical
obligations are all confirmed.  Exact fixtures prove that chord escape can
remain SPD-preconditioned BP, additive branches can collapse to BP, warm
starts can alter finite trajectories without changing a contractive endpoint,
and fixed-map escape can remain variable-metric transport.  The skew fixture
is classified as known optimizer geometry after exact credit and carries both
a certified descending step and a large-step ascent boundary.
-/
