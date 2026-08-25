import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Core
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ResourceSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Equivalence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Counterexamples
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ExactReverse
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.Predictive
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.PrimalDual
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.BroadcastProxy
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FeedbackAlignmentDynamics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FeedbackAlignmentDegeneracy
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PEPITAAntialignment
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectRandomTargetProjection
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SignalPropagationForwardUnlock
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AutoencoderTargetPropagation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OneStepMetaGradient
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SoftHebbNormDynamics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NoPropLocalLearning
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.GradientIsolation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AgnosticEquilibriumLyapunov
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TemperatureScaledLocalGoodness
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ForwardForwardObjectiveDecomposition
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ForwardForwardLocalGoodness
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TargetPerturbation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DifferenceTargetPropagation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TemporalEquilibrium
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.EquilibriumPropagationErrorBudget
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.HolomorphicPhase
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ContinuousHolomorphic
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ImplicitEquilibrium
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ImplicitHolomorphicEquilibrium
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.SplittingOptimizer
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.VerifierFlow
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceAdjoint
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.GradientRouting
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ResidualLagrangian
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ParameterLagrangian
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ForwardComposition
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.HilbertGradient
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceExtensionality
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ExistingInstances
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualContinuation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ContinuationTaskBias
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TruncatedNeumannResidual
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CyclicEPCRefinement
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SCCHybridEquivalence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PhantomGradientAlignment
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TransportedDirectionAlignment
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActiveFrontierSettling
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActiveFrontierContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DynamicFrontierTrace
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FrontierHysteresis
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ChromaticSchedule
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.BoundedStaleEpoch
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ShapeBucketPacking
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LagrangianBoundary
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearTiedProxy
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CompositeTaskCurvature
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LogitLossCurvature
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrecisionSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OperatorClassification
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OperatorSplitting
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearResolvent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.EnergyDecrementStopping
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearForwardBackward
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PeacemanRachfordContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactForwardBackward
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactContractionSchedule
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactFirstOrderOracle
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PartialStrongConvexityPL
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactPrimalGradientRate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectKolenPollackAlignment
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ResolverResidual
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ProspectiveResidualSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CarrierOutputPC
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MultiSiteErrorCoordinatePC
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TwoLayerLocalCreditSeparation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ErrorCoordinateResidualSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualStability
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LocalAmortizedInitialization
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedCreditReadout
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CarrierCutHybridDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SettledCreditClosedForm
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NondimensionalSettlingSchedule
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ShootingStructure
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RealizedScheduledCredit
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SettledCreditSpectralGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.BlockSettlingStability
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteSolverSubstitution
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PreconditionedBranchStableContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.GuardedFiniteAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RetrievalAddressedAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.UnifiedMemoryInteraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryLocalPCEnergy
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RealizedDisplacementAdmission
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryVectorPC
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MetricDependentSteepestDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MinimumInterferenceCredit
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalCreditAdvantage
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CoordinatewiseNormalizedTransport
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OutputLatentCreditGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CarrierCutSettlingContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.UniformBlockExpectedDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ImportanceSampledCoordinateDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WeightedStrongConvexity
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.GammaImportanceSampling
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PointwiseCoordinateReplay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedPointwiseReplay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32PointwiseCoordinateReplay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32WorkNormalizedPointwiseReplay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FrozenConeSpecialization
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedSettlingTrace
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OptimizerTransport
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamFirstMomentTransport
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CyclicalLearningRateGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.EdgeOfStabilityFeedback
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdaptiveRestartDiagnostics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WeightAveragingPrediction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CentralFlowProjection
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CoordinatewiseLearnedOptimizer
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NeuralCertificateReplay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SpectralPolynomialAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ChebyshevInertialIteration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RobustNoisyConvergence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SafeguardedCompositeBlock
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SafeguardedAndersonConvergence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AndersonGainGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegularizedResidualMixing
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactMoreauGradient
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FixedRestartRate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DeepErrorCoordinateAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CurvatureDriftAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TimeOrderedSpectralInsertion
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
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedIntervalEvaluation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedRoundingErrorComposition
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedDivisionSafety
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedCorrectRounding
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedElementaryApproximation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SymbolicTaylorRoundoff
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
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AffineFixedPointAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ReplayGeometryBridge
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayBatchCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayCoverageCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AddMaskReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32HiddenStageReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReadoutReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageResidualReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.JacobianRemainderContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ParameterTracking
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FixedPointSensitivity
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.VaryingScheduleTracking
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualFixedPointSensitivity
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ContinuationKKTSensitivity
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SPDPreconditionedUpdateChord

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
Occurrence-level gradient routing extends that recursion with one scalar per
edge use, has a unique weighted reverse solution, recovers ordinary reverse
mode under unit routes, and reduces to direct task credit under zero routes.
Routes in the unit interval cannot amplify an individual pullback; parallel-
edge and negative-route fixtures separate routing from node masking and record
the boundary of that local norm guarantee.
Gradient isolation is represented independently by a forward map paired with
its declared reverse pullback.  Inserting a stop-gradient boundary preserves
an arbitrary composite forward computation while annihilating all upstream
declared credit.  Replacing it by reverse identity preserves the original
pullback instead, and a scalar fixture separates the two boundaries.  This
semantics deliberately does not identify an arbitrary declared pullback with
the analytic derivative of its forward map.
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
For an error-coordinate primary solve followed by cycle-local refinement, a
shared linearized resolvent now separates two finite paths.  Explicit cycle
unrolling truncates the original transfer operator, whereas damped refinement
truncates its convex combination with the identity.  They share the declared
fixed point and coincide without damping, but an exact scalar fixture separates
their damped finite iterates.  Omitted-power identities give the finite error
crossover, pairwise credit budget, and positive-alignment gate.  An
energy-decrement stop controls credit only after charging residual decrease,
contraction margin, readout sensitivity, and equilibrium mismatch.  Active-
frontier and dense-work fixtures reverse the refine-versus-unroll cost ordering;
matrix-multiplication count alone likewise does not order charged execution
cost.  Componentwise numerical tolerance and credit-direction equivalence are
separated by counterexamples in both directions.
The damping certificate is now explicitly one-sided.  A cycle norm bound at
least one makes the derived convex-combination upper bound inconclusive; it
does not prove the exact damped operator is noncontractive.  The signed scalar
operator `-2 I` has norm factor two but becomes the zero map under one-third
damping.  A genuine no-rescue theorem instead assumes a nonzero positive real
eigenmode with eigenvalue at least one, which remains noncontractive under every
nonnegative damping fraction.  Large gradients, flat trajectory credit, and a
depth-fit decay rate are therefore telemetry rather than uniform operator
certificates.
Finite phantom-gradient readout now has a separate Hilbert-space certificate.
Lower and upper transport bounds for the exact implicit Jacobian turn a
pointwise inverse-approximation error into an explicit inner-product margin
against the exact gradient.  For damped Neumann readout, the inverse residual
is exactly the omitted power of the damped equilibrium operator, yielding a
geometric alignment budget at finite depth.  Zero upstream credit and equality
at the threshold are explicit negative boundaries: neither permits a strict
alignment claim.  Positive alignment remains distinct from finite task
descent, which still requires the curvature and step-size premises exposed by
the directional-descent layer.
Frozen-cone specialization is represented by an actual residualizing
transformation on semiring-polynomial expressions.  Static inputs are
substituted, static-only cones are constant-folded, and mixed cones retain
their dynamic dependencies.  The residual program preserves both values and
formal partial derivatives for every dynamic state.  A counterfixture shows
that freezing a dynamic dependency can agree at one observed state while
breaking both later values and credit.
Proof-carrying settling traces keep certificate assumptions outside measured
rows, reconstruct every derived error, alignment, descent, and work field, and
reject understated radii or nonmonotone accepted energies.  The optimizer
boundary is explicit: positive uniform norm clipping preserves alignment, but
adaptive coordinate scaling, stale moments, and decoupled weight decay need a
separate transport-error certificate before raw local credit licenses the
actual parameter displacement.  Transported cosine and transported norm ratio
are therefore recorded separately: an explicit positive scalar family has
perfect raw and transported cosine for every scale, including a fixture whose
transported norm is less than one percent of the matched BP norm.
The decay algebra is refined separately.  Standard unpreconditioned SGD
recovers exact equivalence between per-step weight decay and a learning-rate-
adjusted scalar quadratic penalty.  A fixed diagonal preconditioner instead
requires a scale-adjusted coordinate penalty; unequal diagonal entries rule
out any single scalar penalty, and a changed preconditioner rules out one
fixed coordinatewise penalty across both steps.  Thus AdamW-style decoupling
cannot be silently reinterpreted as ordinary L2 regularization during a
mechanism comparison.
Adam's moment algebra is audited at the same optimizer boundary.  First and
second moments transport under positive gradient scaling by factors `c` and
`c²`, and bias correction preserves those factors.  With zero stabilizer the
bias-corrected direction is exactly invariant under every positive scale.
With the practical fixed positive stabilizer, scaling instead corresponds to
inverse-rescaling that stabilizer, so exact invariance generally fails.
Negative scaling reverses the direction, while time zero and a zero
second-moment/zero-stabilizer denominator remain explicit degenerate
boundaries.  Raw-credit comparisons therefore require matched incoming
moments, time indices, bias correction, and stabilizers before they can be
transported to Adam displacement claims.
Fixed-checkpoint neural replay is typed at that boundary: tensor-resolved rows
reconstruct the raw-to-optimizer transport distance and the sign convention of
the displacement, while prospective and deep error-coordinate rows separately
reconstruct the final energy-gradient norm divided by precision.  Agreement
with a longer finite settling depth is explicitly not equilibrium evidence;
the emitted algebraic residual becomes an equilibrium-distance certificate
only after method-specific curvature or monotonicity and readout bounds are
supplied.
For strongly convex inexact first-order oracles, the unconstrained primal
gradient step now has a Hilbert-space distance/objective recurrence and a
geometric best-iterate rate whose oracle error appears as one additive floor
rather than accumulating with the iteration count.  The recurrence is exposed
as a trace certificate so neural settling diagnostics can discharge it without
claiming that every measured update satisfies the oracle hypotheses.
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
An arbitrary-degree Chebyshev inertial cycle is also recovered exactly from
the transformed roots of the interval polynomial.  Every nonzero inertial
weight preserves precisely the original fixed points, one complete cycle has
the normalized Chebyshev spectral gain, and repeated complete cycles inherit
the certified geometric rate.  Individual factors may expand, zero weight may
mask a non-fixed point, and nonlinear factor order need not commute.
A complementary integral-quadratic layer isolates the trace theorem behind
matrix-IQC analyses without trusting an external semidefinite solver.  Finite
nonnegative combinations of hard discounted supplies remain hard; a one-step
storage inequality then telescopes to a geometric rate even when storage rises
at an intermediate step.  Additive solver noise composes with the same
telescope: arbitrary noise accumulates through the chronological discount
kernel, while constant or uniformly bounded noise yields an explicit
robustness floor.  A faster noiseless rate can still have a worse noise floor,
so rate alone cannot select an accelerated profile.
Fixed restart has a separate objective-gap theorem: a complete inner block
with a subquadratic endpoint bound, combined with strong convexity, contracts
by `8L / (mu * k^2)`, and repeated blocks inherit a geometric rate when that
factor is below one.  This certifies a fixed block interval only; observable
adaptive restart triggers remain conditional rather than being inferred from
the rate theorem.
Direct Kolen--Pollack alignment has an exact schedule-independent core as
well.  When a shape-matched forward object and transposed feedback object
receive the same time-varying innovation and decay, their gap is multiplied
by `1 - learningRate` on every step and converges throughout the sharp scalar
interval `0 < learningRate < 2`.  An asymmetric-innovation fixture shows why
that result cannot be propagated through dimension-mismatched hidden layers
without an additional approximation certificate.
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
Asymmetric endpoint intervals provide a complementary exact-value layer.
Addition and the exact four-corner multiplication hull satisfy the interval
inclusion property, an indexed certificate reconstructs inclusion for the
shared scalar-expression language, and finite input splitting transports
tilewise bounds back to the original domain.  The repeated-variable fixture
`2*x-x` records the dependency effect: splitting narrows its enclosure but
does not silently recover an algebraic simplification.
Approximation and rounding error are then composed at this asymmetric
interval boundary.  Absolute errors add through an explicit intermediate
value.  Relative errors use a zero-safe multiplicative witness, and two
stages retain the product of their local errors.  Independently valid
evaluation paths may be intersected.  Fixtures prove that dropping the
relative cross term is unsound and that division by a zero reference loses
information that the multiplicative predicate preserves.  No theorem here
identifies an unauthenticated runtime operation with IEEE-754 rounding.
Division receives an additional executable rational safety certificate.
It checks both the ideal denominator interval and its absolute-error-expanded
machine interval, then transports a replay error bound to nonzeroness of both
denominators over the reals.  Equality at the separation margin, improper
intervals, and the real-range-only failure are explicit negative fixtures.
Correct-rounding cells add a distinct final-result layer.  For an authenticated
monotone higher-to-target rounding map, an executable endpoint checker proves
that every value in the certified interval rounds to one oracle-bound target.
A nonmonotone interior counterexample shows why endpoint equality alone is
insufficient, while an explicit-list checker proves that sampled candidate
success cannot replace complete-domain validation.
Elementary-function approximations receive a two-phase certificate matching
the Dandelion decomposition: a certified elementary-to-Taylor error and a
residual polynomial error add to a checked uniform budget.  A separate compact
interval theorem bounds every value from endpoint samples and derivative-based
confidence intervals covering all critical points.  Under-sized composed
budgets and endpoint-only extrema checks are explicit negative fixtures; no
Taylor generator, root oracle, or runtime elementary implementation is assumed.
Symbolic Taylor round-off forms provide the complementary floating-point
reduction.  A finite family of bounded error coordinates contributes its common
radius times the `L1` sensitivity, and a rigorously bounded higher-order
remainder is retained.  An executable rational certificate checks the global
sensitivity, remainder, and total budgets.  Separately maximizing every
sensitivity is proved sound but can be strictly looser than the
correlation-preserving bound; deleting the remainder is explicitly unsound.
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
For stabilized Anderson acceleration, accepted proposals may be noncontractive:
a summable accepted-step error budget and the fallback decrease instead form a
quasi-Fejer trace.  The resulting finite-horizon budget yields summability of
fallback decreases, vanishing residual, and convergence of squared distance to
every fixed point.  A semantic residual binding plus a sequentially compact
invariant set then recover convergence of the full state sequence to a fixed
point.  The polynomial safeguard is proved summable only above exponent one;
the harmonic boundary supplies a matching negative result.  These results
license convergence monitoring, not a rate improvement.
The complementary depth-one Anderson geometry is exact: least-squares
projection removes the residual component along the latest residual
difference, minimizes the residual over every scalar coefficient, and has a
strict gain precisely when that component is nonzero.  For nonlinear maps the
saved first-order residual supplies an exact remainder budget and a quadratic
local radius; spending the full budget recovers the baseline rather than a
strict improvement.  A scalar affine map reaches its fixed point in one
nondegenerate Anderson step, while repeated history exposes the denominator
boundary.
Regularized residual mixing supplies a complementary coefficient-stability
certificate.  Any regularized affine mixture that beats uniform averaging has
squared coefficient norm at most `(1 + 1 / regularization) / history`, provided
the declared residual scale bounds the uniform mixture.  The actual
two-history scalar solver is constructed and proved globally optimal by an
exact completed-square identity.  With zero regularization, identical
residual columns permit optimal affine mixtures of arbitrarily large
coefficient norm, so residual reduction alone cannot justify extrapolation
stability.
When curvature changes between the two scheduled sweeps, the terminal factor
differs from the fixed-curvature polynomial by two ordered first-order terms
and one quadratic interaction.  A pointwise drift certificate now adds that
exact envelope to the fixed-spectrum contraction factor and lifts the result
through the same active-state isometry.  The unchanged-curvature fixture
recovers the exact `4/7` block, while a finite second-sweep curvature jump makes
the nominally accelerated mode expansive.  Sampled local Ritz values remain
diagnostics rather than uniform spectral or drift certificates.
For an arbitrary finite-memory schedule, a directed perturbation from one
spectral fibre to another now has an exact time-ordered insertion response.
The coupled triangular execution is affine in the perturbation scale, so its
nonzero finite-difference quotient is exactly that response.  Two scalar
realizations can share both fixed terminal products while having different
insertion responses; a terminal residual polynomial therefore does not
determine curvature-drift sensitivity.
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
unlicensed forward dynamics.  Scaled monotone resolvents are also connected
to Peaceman--Rachford splitting: reflection is nonexpansive for a monotone
operator and strictly contractive at every positive rate for a strongly
monotone Lipschitz operator.  Fixed reflected states decode exactly to zeros
of the operator sum.  Zero-rate and period-two endpoint fixtures expose the
strict boundaries.  A uniformly inexact resolvent is tracked without
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
The shooting-structure layer separates coarse recurrent condensation from
multi-site lifting.  It proves finite-speed support for simultaneous local
credit, exact reverse credit for an output-to-input ordered sweep, and the
matching-manifold equality between lifted and condensed trajectories.  Exact
counterexamples show that local lifting alone does not imply global coercivity,
operator norm does not determine conditioning, parameter-dependent Schur
condensation can change stationary sets, and sweep completeness need not move
cosine monotonically toward backpropagation.  A valid orthogonal-capture
special case and exact staged AC residual schedules expose the hypotheses a
frozen-checkpoint admission probe must measure.
The realized-schedule layer lifts that scalar schedule theory to actual
finite-parameter credit vectors.  Pairwise-orthogonal sweep contributions
give an exact identity between squared cosine and captured credit energy, and
therefore monotone prefix alignment.  Legal staggered DAG fixtures realize the
positive law, while a signed-cancellation DAG proves that prefix cosine can
decrease and later recover when orthogonality fails.  For ranked tensor DAGs,
a complete frozen reverse-power sweep is exactly the finite BP resolvent and
therefore reproduces every occurrence-level BP credit.  The corresponding
moving-state reverse-rank sweep is deliberately kept separate: agreement is
licensed only when the state stays frozen and the realized local force is
complete, and an executable chain fixture crosses that boundary.
The third-family admission layer keeps eight candidate mechanisms unnamed
unless ten independent mathematical, implementation, prior-art, and empirical
obligations are all confirmed.  Exact fixtures prove that chord escape can
remain SPD-preconditioned BP, additive branches can collapse to BP, warm
starts can alter finite trajectories without changing a contractive endpoint,
and fixed-map escape can remain variable-metric transport.  The skew fixture
is classified as known optimizer geometry after exact credit and carries both
a certified descending step and a large-step ascent boundary.
-/
