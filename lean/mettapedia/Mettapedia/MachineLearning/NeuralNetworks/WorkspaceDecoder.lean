import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FiniteDampedSettling
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FixedAddressFrontier
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FixedAddressFrontierProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedChildInitialization
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedChildInitializationProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CarrierDecisionPipeline
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CarrierDecisionPipelineProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.LinearSettling
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedRegisters
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Predictions
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.DEQBridge
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.KalmanCorrespondence
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.StateSpaceScan
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefState
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Selectivity
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefWorldModel
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefStateProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.SequentialSelectivity
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.MatrixBelief
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.GaussianBeliefPropagation
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.SelectiveBeliefContract
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NaturalEvidenceCoordinates
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.WeightedEvidenceDynamics
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.SelectiveBeliefProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FusionExpressivity
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.OverlapCalibration
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NonstationaryFusion
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.DistortionCalibration
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FusionBoundaryProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.WeightedEvidenceProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Carom
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CaromProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutation
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearCommutation
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromSymmetricComposition
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearJointGrowth
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromTwoPopulationCompiler
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromGLVLocalDirectionality
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromGLVSaddleProduct
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromGLVTransitionLearning
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromPathCompleteStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromPathCompleteLift
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromContinuousChannel
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromAutonomousSemiflow
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutingNilpotentStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromJointNilpotentStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromScalarShiftStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromBalancedScalarShiftStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromBlockStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromSimultaneousBlocks
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromHermitianWordStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromHermitianDirectSum
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutingHermitianStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromRealSchurStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromInheritance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromProvenance

/-!
# Typed workspace-decoder formal scope

This umbrella module exposes the generic gated workspace dynamics, exact
positive-depth simultaneous settling traces, the shared fixed-address
workspace/belief frontier transition and packed-row boundary, the common
typed-hole metadata map, carrier-specific ideal child initialization and
natural-coordinate packet invariants, the common decision/readout waist and
checker-owned score support, the linear settling and finite-depth
mismatch results, the sealed typed-register adapter,
the preregistered prediction layer, the linear deep-equilibrium bridge, and the
Kalman, affine-scan, belief-state, selectivity, and certified world-model layers.
It also exposes sequential Riccati selectivity, matrix Gaussian information,
the weighted-evidence selective-decoder contract, its exact count embedding
and derived coordinate chart, the expressivity and calibration boundaries of
hardwired fusion, derived forgetting under nonstationarity, linear measurement
recalibration, and machine-checked transport accounting.
The Gaussian-information layer additionally exposes exact leave-one-edge
message cavities, their properness boundary, and scalar factor elimination by
Schur complement with an independently derived completion-of-squares
semantics.
It also exports the exact CAROM recurrent-write reduction, its certified
linear settling and legal-action inheritance, metric and interference scope
boundaries, and the separated within-action/across-action recurrence model.
The routed extension adds simplex mixtures, command opacity and immutable
evidence registers, the exact affine commutation boundary, switched-system
stability and divergence results, nonlinear near-identity command-order bounds
under explicit derivative regularity, uniform nonlinear arbitrary-schedule
stability from one coercive regional Lyapunov certificate with an invariant
region and observation margin, exact group-valued adjoint reversal and
time-symmetric method--adjoint and palindromic compositions with explicit
noncommuting and commuting boundaries,
finite-word nonlinear growth factors with a submultiplicative composition law,
arbitrary repeated-block schedule bounds, and explicit one-step and
switching counterexamples,
an exact two-population graph compiler with one state cell per vertex and one
transition cell per edge, together with an injective-address recovery theorem
and a noninjective collision that creates a spurious transition,
the local generalized Lotka--Volterra invasion-rate boundary for compiled
itineraries, including exact expansion, contraction-dominance, transverse
stability, graph-edge correspondence, and logarithmic linearized exit time,
phase-indexed path-complete regional stability
with changing centers and a certified finite observation itinerary, a local
forward graph lift that preserves finite-word path completeness and transports
regional certificates without weakening their rate, and a
continuous phase-flow contract composing entry, transverse attraction,
positive dwell, observation, exit, activation, and an absorbing halt, with an
explicit two-phase exponential channel, plus a shared-semiflow realization
theorem and a smooth autonomous vector-field fixture with transverse
contraction, nonconstant observations, and observable halt, a
constructed common quadratic metric
for finite jointly nilpotent command families, a finite joint-extinction
budget for pairwise commuting individually nilpotent commands, a shared
strict metric for scalar contractions with jointly nilpotent residuals,
its balanced extension covering every strict real scalar radius below one,
finite dependent block assembly of local common metrics, simultaneous
generalized-eigenspace scalar-plus-transient decomposition for commuting
families, strict positive Hermitian word metrics for every simultaneous
complex block whose command character lies inside the unit disk, finite
Hermitian product assembly and exact non-orthogonal coordinate transport,
a global common Hermitian contraction energy for commuting complex families
under a strict active-character disk bound, its spectral-radius specialization,
and an exact complexification/restriction theorem producing a positive real
quadratic energy and arbitrary-schedule bound for finite commuting real Schur
families, and
route/temperature/schedule-independent legal-action safety inheritance.

All settling, entropy-limit, implicit-gradient, Bayesian, and scan conclusions
are explicitly scoped by their stated linear, linear-Gaussian, or nonlinear
regularity hypotheses.  Arbitrary trained nonlinear workspace-decoder
performance remains outside the formal claims exported here.
-/
