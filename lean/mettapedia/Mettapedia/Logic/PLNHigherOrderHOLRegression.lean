import Mettapedia.Logic.PLNHigherOrderHOLCore
import Mettapedia.Logic.PLNHigherOrderHOLRules
import Mettapedia.Logic.PLNHigherOrderHOLSoundness
import Mettapedia.Logic.PLNHigherOrderHOLConsequence
import Mettapedia.Logic.PLNHigherOrderHOLLinkBridge
import Mettapedia.Logic.PLNHigherOrderHOLCanary
import Mettapedia.Logic.PLNWorldModelHOLSetBridgeRegression
import Mettapedia.Logic.PLNProbHOLPlannerBridgeRegression
import Mettapedia.Logic.PLNRegimeMixtureRegression

/-!
# Higher-Order HOL Regression Surface

Aggregates the initial HO PLN layer built over the real Church/Henkin HOL
semantics, the enriched HO PLN rule surface, the real HOL world-model
bridge, the direct `Set -> HOL -> WM` higher-order regression fixtures, and the
planner-facing bridge from semantic `ProbHOL` into mixed-mode higher-order
guarded planning, together with the finite regime-mixture theorem/regression
surface for direct-vs-soft-vs-reveal Chapter-11 reasoning.
-/
