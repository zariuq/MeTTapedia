import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCore
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLRules
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSoundness
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLConsequence
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLLinkBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLProbabilisticBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCredalBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCanary
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLSetBridgeRegression
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNProbHOLPlannerBridgeRegression
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNRegimeMixtureRegression

/-!
# Higher-Order HOL Regression Surface

Aggregates the initial HO PLN layer built over the real Church/Henkin HOL
semantics, the enriched HO PLN rule surface, the real HOL world-model
bridge, the direct `Set -> HOL -> WM` higher-order regression fixtures, and the
planner-facing bridge from semantic `ProbHOL` into mixed-mode higher-order
guarded planning, together with the finite regime-mixture theorem/regression
surface for direct-vs-soft-vs-reveal Chapter-11 reasoning.
-/
