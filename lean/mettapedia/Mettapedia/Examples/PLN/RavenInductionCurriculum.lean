import Mathlib.Tactic
import Mettapedia.Examples.PLN.ClassicExamples
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRavenInductionBridge

/-!
# Raven induction curriculum example

This wrapper is the teachable raven cell for the PLN curriculum.  The rule
facts come from `RuleFamilies.FirstOrder.RavenAsymmetricInduction` and
`RuleFamilies.FirstOrder.PLNRavenInductionBridge`; the older
`ClassicExamples` raven entry is kept as provenance for the PLN v0.9 example it
supersedes.
-/

namespace Mettapedia.Examples.PLN.RavenInductionCurriculum

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence
open Mettapedia.PLN.RuleFamilies.FirstOrder
open Mettapedia.PLN.RuleFamilies.FirstOrder.RavenInductionBridge
open Mettapedia.PLN.RuleFamilies.FirstOrder.RavenAsymmetricInduction

/-! ## Positive case: ravens support `raven -> black` -/

/-- The concrete `5` raven observations aggregate to the closed-form forward
evidence imported from the rule-family module. -/
theorem five_ravens_forward_aggregate :
    aggregateEvidence ravenBlackContribution positiveExampleDataset =
      ravenBlackEvidence 5 := by
  simpa [positiveExampleDataset] using
    aggregate_ravenBlack_ravenObservationDataset 5 95

/-- Five observed black ravens make the forward count-strength exactly `1`. -/
theorem five_ravens_forward_strength :
    (toStrength (ravenBlackEvidence 5)).toReal = (1 : ℝ) :=
  ravenBlackStrength_toReal_eq_one 5 (by norm_num)

/-! ## Negative case: other black objects dilute `black -> raven` -/

/-- The same dataset gives inverse evidence with `95` black non-ravens. -/
theorem five_ravens_inverse_aggregate :
    aggregateEvidence blackRavenContribution positiveExampleDataset =
      blackRavenEvidence 5 95 := by
  simpa [positiveExampleDataset] using
    aggregate_blackRaven_ravenObservationDataset 5 95

/-- In the concrete dataset, the inverse strength is the observed base rate,
not the forward certainty. -/
theorem five_ravens_inverse_strength :
    (toStrength (blackRavenEvidence 5 95)).toReal = (1 / 20 : ℝ) :=
  (ravenInduction_bayesInversion_values_canary).2.1

/-- Negative example: the inverse link is not the forward link when other black
objects are present. -/
theorem inverse_not_forward_strength :
    (toStrength (blackRavenEvidence 5 95)).toReal ≠
      (toStrength (ravenBlackEvidence 5)).toReal :=
  ravenInduction_inverse_ne_forward_canary

/-- More black non-ravens increase confidence in the inverse estimate while
lowering its strength.  This is the confidence-cap side of the example:
well-evidenced inverse data can still be weak. -/
theorem inverse_confidence_grows_with_more_black_nonravens :
    toConfidence (1 : ℝ≥0∞) (blackRavenEvidence 5 95) ≤
      toConfidence (1 : ℝ≥0∞) (blackRavenEvidence 5 995) :=
  confidence_blackRaven_monotone
    (1 : ℝ≥0∞) (by norm_num) (by simp) 5 95 995 (by norm_num)

/-- The corresponding strength comparison goes the other way. -/
theorem inverse_strength_drops_with_more_black_nonravens :
    toStrength (blackRavenEvidence 5 995) ≤
      toStrength (blackRavenEvidence 5 95) :=
  strength_blackRaven_antitone 5 95 995 (by norm_num) (by norm_num)

/-! ## Provenance link to the older PLN v0.9 example -/

/-- The older PeTTa-style `ClassicExamples` batch check is retained as
provenance; this file supersedes its raven entry as the curriculum proof
wrapper. -/
def olderClassicExampleBatchCheck : Bool :=
  Mettapedia.Examples.PLN.ClassicExamples.plnExampleAllPass

end Mettapedia.Examples.PLN.RavenInductionCurriculum
