import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridge
import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicyRegression

/-!
# Fixpoint-SP/SPN Bridge Regression

Concrete fixtures for the orbit-to-closure bridge.
-/

namespace Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridgeRegression

open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDampedConvergence
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridge
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicy
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicyRegression
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeightedOverlapRegression

abbrev PointedKripke :=
  Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicyRegression.PointedKripke
abbrev PolicyWeightedState :=
  Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridge.PolicyWeightedState
abbrev PolicyModalQuery :=
  Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridge.PolicyModalQuery

def alwaysFresh : Nat → Bool := fun _ => true

theorem alwaysFresh_eventual :
    ∃ N, ∀ n, N ≤ n → alwaysFresh n = true := by
  refine ⟨0, ?_⟩
  intro n _hn
  simp [alwaysFresh]

theorem fixture_orbit_pair_two_in_closure :
    (2, true) ∈
      leastRuleClosure (State := OrbitState) (Query := OrbitQuery)
        (orbitRules alwaysFresh true) (0 : OrbitState) (orbitSeed false) := by
  have hMem :
      (2, dampedOrbit alwaysFresh true false 2) ∈
        leastRuleClosure (State := OrbitState) (Query := OrbitQuery)
          (orbitRules alwaysFresh true) (0 : OrbitState) (orbitSeed false) :=
    orbit_pair_mem_leastRuleClosure alwaysFresh true false 2
  simpa [alwaysFresh, dampedOrbit, dampedSPNStep, spnStep] using hMem

theorem fixture_eventualFresh_to_closure_endpoint :
    ∃ M, ∀ n, M ≤ n →
      (n, true) ∈
        leastRuleClosure (State := OrbitState) (Query := OrbitQuery)
          (orbitRules alwaysFresh true) (0 : OrbitState) (orbitSeed false) := by
  exact
    dampedOrbit_eventualFresh_to_fixpointClosure_endpoint
      alwaysFresh true false alwaysFresh_eventual

theorem fixture_policy_eventualFresh_endpoint_add_of_compatible_trustedAll
    (pkA pkB : PointedKripke) (qPolicy : PolicyModalQuery) :
    ∃ M, ∀ n, M ≤ n →
      (n, true) ∈
        leastRuleClosure (State := OrbitState) (Query := OrbitQuery)
          (orbitRules alwaysFresh true)
          (BinaryWorldModel.evidence (State := PolicyWeightedState) (Query := PolicyModalQuery)
            ((leftState pkA) + (rightDisjointState pkB)) qPolicy)
          (orbitSeed false) := by
  exact
    dampedOrbit_eventualFresh_to_fixpointClosure_endpoint_policy_add_of_compatible_trustedAll
      (W₁ := leftState pkA) (W₂ := rightDisjointState pkB) (qPolicy := qPolicy)
      (hcompat := disjoint_compatible pkA pkB)
      (freshAt := alwaysFresh) (freshState := true) (x0 := false)
      alwaysFresh_eventual

end Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridgeRegression
