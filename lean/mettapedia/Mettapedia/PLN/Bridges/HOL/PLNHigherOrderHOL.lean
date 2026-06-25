import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLRegression
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCredalBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDeductionBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInductionAbductionITVBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNIndependencePointApproximation
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNAlgorithmicAbductionBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNBayesInversionBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRavenInductionBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRavenAbductionBridge
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNContextGuardBridge
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNTypedSemanticLayerBridge
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNTypedSemanticLayerAssocPatBridge
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts

/-!
# Higher-Order PLN Over Real HOL

Public entrypoint for the soundness-first HO PLN layer built on:

- real Church-style HOL derivability,
- Henkin semantics,
- the classical Henkin soundness/completeness path for the underlying HOL
  substrate,
- the real HOL world-model bridge,
- the credal/QFM predicate-rule bridge for higher-order PLN truth values,
- and the no-independence deduction interval transport from HOL strengths into
  the shared PLN deduction ITV surface, including the source-rule and sink-rule
  induction/abduction interval lifts.
-/
