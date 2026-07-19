import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics
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
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromInheritance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromProvenance

/-!
# Typed workspace-decoder formal scope

This umbrella module exposes the generic gated workspace dynamics, the linear
settling and finite-depth mismatch results, the sealed typed-register adapter,
the preregistered prediction layer, the linear deep-equilibrium bridge, and the
Kalman, affine-scan, belief-state, selectivity, and certified world-model layers.
It also exposes sequential Riccati selectivity, matrix Gaussian information,
the weighted-evidence selective-decoder contract, its exact count embedding
and derived coordinate chart, the expressivity and calibration boundaries of
hardwired fusion, derived forgetting under nonstationarity, linear measurement
recalibration, and machine-checked transport accounting.
It also exports the exact CAROM recurrent-write reduction, its certified
linear settling and legal-action inheritance, metric and interference scope
boundaries, and the separated within-action/across-action recurrence model.
The routed extension adds simplex mixtures, command opacity and immutable
evidence registers, the exact affine commutation boundary, switched-system
stability and divergence results, and route/temperature/schedule-independent
legal-action safety inheritance.

All settling, entropy-limit, implicit-gradient, Bayesian, and scan conclusions
are explicitly linear or linear-Gaussian.  Arbitrary trained nonlinear
workspace decoders remain outside the formal claims exported here.
-/
