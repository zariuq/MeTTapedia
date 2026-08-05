import Mettapedia.MachineLearning.NeuralNetworks.Architecture.TypedRelationGraph
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RowIndexedRotary
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.EncoderEquivariance
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.GSLTGraphCompiler
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ObservationalEquivalence
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.AcceptedBehavior
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.EquilibriumObservation
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RoutingExpansion
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.SeparatedSoftmax
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LogitPriorAdjustment
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.SlidingWindowPrior
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ClassBalancedBayes
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ExecutionSemantics
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.AutonomousExecution
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.FiniteDirectionality
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.PhaseHandoffTracking
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ReZeroIgnition
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ResidualTransport
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.FixupScale
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.HighwayGateBoundary
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LayerNormalizationBoundary
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.PrePostLayerNormBoundary
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RectifierVarianceTransport
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.MeanFieldSignalDepth
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.TransientChaosGeometry
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ConvolutionalModeDepth
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.DepthwiseResidualScaling
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.DepthwiseUpdateScaling
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.MaximalUpdateScaling
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ScaledDotProductAttention
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.SliceAttentionEquivariance
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.NeuralFunctionalAttentionEquivariance
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.SwitchRoutingBalanceBoundary
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.SwitchHeadCostBoundary
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.GroupedExpertCapacity
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.BatchNormalizationDependence
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.BatchNormalizationGradientProjection
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LowRankAdaptation
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Recurrent
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.RecurrentPolicy
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.RecurrentPolicyProvenance
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Workspace
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Belief
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Carom
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.TrainingSelector
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.TrainingSelectorFixtures

/-!
# Neural-network state-carrier architecture

This import surface collects typed relation-graph compilation, the abstract
state-carrier calculus, observational-equivalence, execution-semantics, and
routing-expansion boundaries, observable equilibrium, checker-mediated
accepted behavior, and the recurrent, workspace, belief, and routed CAROM
instances. The recurrent instance includes its typed state-input, source-summary,
teacher-forced scan, incremental-step, and shared legal-policy-port semantics.
It also exposes exact low-rank adaptation semantics: training/deployment
equivalence, the rank-budget boundary, and the asymmetric update-zero
initialization that keeps one factor's first update live.
Coupled highway gates are treated as transform/carry interpolation with exact
endpoints and a pairwise propagation budget.  The scalar theory retains the
input-dependent gate derivative: a pointwise zero gate has identity Jacobian
only when the gate is locally flat or the transform agrees with the input.
Finite logistic biases approach but never attain the exact carry endpoint.
Layer normalization is formalized over every nonempty finite width, with exact
centering, unit-variance, shift-invariance, and positive-rescaling laws.  Its
boundaries are explicit: negative scale reverses direction, zero variance
requires totalization, and a positive numerical stabilizer breaks exact scale
invariance.
Batch normalization reuses the same finite-population core along the example
axis.  Its additional boundaries are cross-example training dependence,
batch-size-one signal erasure, strict variance attenuation under a positive
stabilizer, and exact identity restoration only when the gain includes that
stabilizer.
For exact positive-variance normalization, the activation-gradient pullback
is also decomposed into the original squared norm minus its constant-batch and
normalized-activation components, followed by the gain-to-standard-deviation
scale.  Either nonzero removed component gives strict projection decrease,
while a nonzero gradient tangent to both directions is unchanged.
Group-local expert caps compose into a global per-expert capacity bound.
The converse is false: an aggregate cap alone permits one routing group to
overflow while another is idle.
Mean-field signal depth is exposed as an exact finite scalar transport law:
subcritical multipliers contract, the critical multiplier preserves, and
supercritical multipliers expand every nonzero linearized residual.  Its
correlation-depth threshold is constructive for any finite requested horizon.
The independent-mask dropout boundary records both strict loss of identical-
input correlation under nondegenerate variance and the zero-moment exception.
The associated finite metric/curvature recurrence has an exact product law:
curvature squared times Euclidean metric increases by precisely the nonlinear
curvature-injection term. Positive injection gives strict layerwise growth;
zero injection conserves the product even under expanding linear transport.
The curvature fixed point and its finite-depth error are also closed form.
For normalized convolutional variance kernels, every unit-phase spatial mode
has gain norm at most one.  A point-mass kernel preserves every mode at
criticality, while a diffuse two-site kernel preserves the constant mode and
annihilates the alternating mode; average criticality alone therefore does not
certify spatial-mode transport.
Depthwise residual scaling is separated from its geometric assumptions.
Uniform inverse-square-root coefficients preserve the exact quadratic budget
for orthonormal branch directions, but their fully aligned effect grows with
depth.  Uniform inverse-depth coefficients reverse this tradeoff, and no
single scalar coefficient preserves both unit budgets beyond depth one.
Paired branch-and-update scaling sharpens this boundary.  When both effective
coefficients scale inversely with square-root depth, aligned training updates
have an exactly depth-independent coherent effect, while orthonormal update
directions have a quadratic budget decaying as inverse depth.  Holding the
effective update scale constant makes the coherent squared effect grow
linearly; for a nonzero branch amplitude, coherent invariance uniquely forces
the paired inverse-square-root update scale.
Width scaling has an analogous exact finite boundary in a two-layer linear
network.  Expanding the simultaneous update gives four dot-product terms.
Under standard squared-norm statistics the output grows strictly with width;
under maximal-update statistics and reciprocal layerwise rates, any two
positive-width networks have the same one-step output.  Rational width-four
fixtures share zero initial output and separate to five versus two after one
unit update.
-/
