import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Model
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Attention
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.RankReachability
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.OnlineRegret
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.AdapterReachability
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Cadence
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.DerivedCadence
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.BeliefInstantiation
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Consolidation
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Crown

/-!
# Two-timescale adaptation

Theory for bounded fast-state adaptation followed by periodic weight
consolidation: concrete linear-attention and belief-register instances,
rank-budget and Jacobian-local adapter reachability, online dynamic regret,
the softmax approximation boundary, exact capacity
deadlines, cadence derived from counted updates and evidence loss, evidence
de-duplication, update ordering, retention, and the boundary where weight
updates are unnecessary.
-/
