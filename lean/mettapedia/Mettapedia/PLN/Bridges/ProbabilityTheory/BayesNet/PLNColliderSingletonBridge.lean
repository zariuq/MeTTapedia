import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules
import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation

/-!
# Collider Singleton Bridge (Thin Module)

This module deliberately uses `abbrev` re-exports only, to avoid re-elaborating
heavy collider theorems in wrapper proofs.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNColliderSingletonBridge

open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

variable
  [Fintype Three]
  [DecidableEq Three]
  [∀ v : Three, Fintype (colliderBN.stateSpace v)]
  [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
  [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace]
  [∀ v : Three, MeasurableSingletonClass (colliderBN.stateSpace v)]
  [∀ v : Three, Nonempty (colliderBN.stateSpace v)]
  [DecidableRel colliderBN.graph.edges]

/-- Short-name re-export for the collider link-to-prop `.toReal` equality. -/
abbrev sinkLinkEqPropToReal :=
  Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules.xi_sink_queryStrength_toReal_eq_of_colliderBN

/-- Short-name re-export for singleton prop `.toReal` = marginal probability. -/
abbrev singletonPropToReal :=
  Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation.BNWorldModel.queryStrength_singleton_prop_toReal
    (bn := colliderBN)

end Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNColliderSingletonBridge
