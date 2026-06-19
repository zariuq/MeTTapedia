import Mettapedia.Logic.PLNHigherOrderHOLRegression
import Mettapedia.Logic.PLNHigherOrderHOLCredalBridge
import Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge
import Mettapedia.Logic.PLNInductionAbductionITVBridge
import Mettapedia.Logic.PLNIndependencePointApproximation
import Mettapedia.Logic.PLNAlgorithmicAbductionBridge
import Mettapedia.Logic.PLNBayesInversionBridge
import Mettapedia.Logic.PLNRavenInductionBridge
import Mettapedia.Logic.PLNRavenAbductionBridge
import Mettapedia.Logic.PLNContextGuardBridge
import Mettapedia.Logic.PLNHigherOrderHOLCompletenessTightness
import Mettapedia.Logic.PLNHigherOrderHOLDefinableCuts

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
