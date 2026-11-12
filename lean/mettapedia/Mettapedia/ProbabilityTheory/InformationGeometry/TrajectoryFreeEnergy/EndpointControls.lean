import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.EndpointBridge
import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Controls

/-!
# An unreachable endpoint has infinite bridge cost

The finite history space here records no movement: initial and terminal
observations are the same coordinate. A changed, supported endpoint law has
finite static divergence but cannot preserve the prescribed initial law.
The extended bridge and residual costs are infinite. Leaving the law
unchanged gives a zero-cost feasible bridge.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.EndpointControls

open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference
open Controls (fair desiredCost)

def target : Prob Bool := gibbs fair desiredCost 1 (by norm_num)

theorem target_supported : SupportedBy target fair.1 := gibbs_supported fair desiredCost 1 (by norm_num)

theorem impossible_endpoint : IsEmpty (EndpointBridge.Feasible fair id fair id target) := by
  refine ⟨fun feasible => ?_⟩
  have same : target = fair := feasible.2.2.2.symm.trans feasible.2.2.1
  apply Controls.fixed_initial_law_violated
  simpa only [Prob.coarsen_id, target] using same

theorem static_finite_bridge_infinite :
    SupportedBy target fair.1 ∧ ENNReal.ofReal (klSum target.1 fair.1) < ⊤ ∧
      EndpointBridge.cost fair id fair id target = ⊤ :=
  ⟨target_supported, ENNReal.ofReal_lt_top,
    EndpointBridge.cost_infinite_of_infeasible fair id fair id target impossible_endpoint⟩

theorem dynamic_remainder_infinite : EndpointBridge.residual fair id fair id target = ⊤ :=
  EndpointBridge.residual_infinite_of_infeasible fair id fair id target impossible_endpoint

theorem unchanged_endpoint_zero : EndpointBridge.cost fair id fair id fair = 0 := by
  let feasible : EndpointBridge.Feasible fair id fair id fair :=
    ⟨fair, (fun _ positive => positive), Prob.coarsen_id fair, Prob.coarsen_id fair⟩
  apply le_antisymm _ bot_le
  calc
    EndpointBridge.cost fair id fair id fair ≤ ENNReal.ofReal (klSum feasible.1.1 fair.1) := iInf_le _ feasible
    _ = 0 := by rw [klSum_self_eq_zero fair.1 fair.2.1, ENNReal.ofReal_zero]

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.EndpointControls
