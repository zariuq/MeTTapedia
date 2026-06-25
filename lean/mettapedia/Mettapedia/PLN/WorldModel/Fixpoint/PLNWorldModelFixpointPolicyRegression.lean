import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicy
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeightedOverlapRegression

/-!
# Policy-Aware Fixpoint Closure Regression

Concrete disjoint/overlap fixtures lifted to the policy-aware fixpoint adapter.
-/

namespace Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicyRegression

open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeighted
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeightedOverlap
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeightedOverlapRegression
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicy

abbrev ModalQuery := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeighted.ModalQuery
abbrev WeightedState := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeighted.WeightedState
abbrev PointedKripke := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeighted.PointedKripke
abbrev PolicyRuleSet := Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicy.PolicyRuleSet

def fixtureSeed : Set ModalQuery := ∅
def fixtureRules : PolicyRuleSet := (∅ :
  Set (Mettapedia.PLN.WorldModel.PLNWorldModel.WMConsequenceRuleOn WeightedState ModalQuery))

theorem disjoint_compatible
    (pkA pkB : PointedKripke) :
    compatible (leftState pkA) (rightDisjointState pkB) := by
  intro s hsL hsR
  have hsA : "srcA" = s := by
    simpa [sourceInState, leftState, wpLeft] using hsL
  have hsB : "srcB" = s := by
    simpa [sourceInState, rightDisjointState, wpRightDisjoint] using hsR
  have hEq : "srcA" = "srcB" := by
    calc
      "srcA" = s := hsA
      _ = "srcB" := hsB.symm
  simp at hEq

theorem overlap_not_compatible
    (pkA pkB : PointedKripke) :
    ¬ compatible (leftState pkA) (rightOverlapState pkB) := by
  intro hcompat
  have hsL : sourceInState "srcA" (leftState pkA) := by
    simp [sourceInState, leftState, wpLeft]
  have hsR : sourceInState "srcA" (rightOverlapState pkB) := by
    simp [sourceInState, rightOverlapState, wpRightOverlap]
  exact hcompat "srcA" hsL hsR

theorem fixture_policy_state_disjoint_eq_add
    (pkA pkB : PointedKripke) :
    policyRevisedState trustedAll (leftState pkA) (rightDisjointState pkB) =
      (leftState pkA) + (rightDisjointState pkB) := by
  exact
    policyRevisedState_eq_add_of_compatible_trustedAll
      (hcompat := disjoint_compatible pkA pkB)

theorem fixture_policy_state_overlap_eq_left
    (pkA pkB : PointedKripke) :
    policyRevisedState trustedAll (leftState pkA) (rightOverlapState pkB) =
      leftState pkA := by
  exact
    policyRevisedState_eq_left_of_not_compatible_trustedAll
      (hcompat := overlap_not_compatible pkA pkB)

theorem fixture_policy_closure_disjoint_eq_baseClosure
    (pkA pkB : PointedKripke) :
    policyLeastRuleClosure fixtureRules trustedAll
        (leftState pkA) (rightDisjointState pkB) fixtureSeed =
      leastRuleClosure (State := WeightedState) (Query := ModalQuery)
        fixtureRules ((leftState pkA) + (rightDisjointState pkB)) fixtureSeed := by
  exact
    policyLeastRuleClosure_eq_add_of_compatible_trustedAll
      fixtureRules (leftState pkA) (rightDisjointState pkB) fixtureSeed
      (disjoint_compatible pkA pkB)

theorem fixture_policy_closure_overlap_eq_leftClosure
    (pkA pkB : PointedKripke) :
    policyLeastRuleClosure fixtureRules trustedAll
        (leftState pkA) (rightOverlapState pkB) fixtureSeed =
      leastRuleClosure (State := WeightedState) (Query := ModalQuery)
        fixtureRules (leftState pkA) fixtureSeed := by
  exact
    policyLeastRuleClosure_eq_left_of_not_compatible_trustedAll
      fixtureRules (leftState pkA) (rightOverlapState pkB) fixtureSeed
      (overlap_not_compatible pkA pkB)

end Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointPolicyRegression
