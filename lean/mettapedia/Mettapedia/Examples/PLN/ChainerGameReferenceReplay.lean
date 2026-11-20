import Mettapedia.Examples.PLN.ChainerGameReferenceControls
import Mettapedia.Examples.PLN.ProofWriterEvidenceReplay
import Lean.Data.Json.FromToJson

/-! # Export exact rational reference controls -/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.ChainerGameReferenceReplay

open Lean ChainerGameReferenceControls
open ProofWriterEvidenceReplay (readout initial premiseGivenProof)
open Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout (Masses)

private def ratio (q : ℚ) : Json := toJson (q.num, q.den)

private def optionalRatio (q : Option ℚ) : Json := q.elim Json.null ratio

private def named (names : List String) (values : List (Option ℚ)) : Json :=
  Json.mkObj (names.zip (values.map optionalRatio))

private def sharedEvidence : Json :=
  named ["prior", "independent", "shared_reliability", "replayed",
    "alternative_given_proof_independent", "alternative_given_proof_shared"]
    ([readout false [], readout false initial, readout true initial,
      readout true (initial ++ [.sharedPremise]), premiseGivenProof false 2,
      premiseGivenProof true 2].map (fun mass => mass.bind Masses.posterior?))

def reference : Json := Json.mkObj [
  ("version", toJson (1 : Nat)),
  ("shared_evidence", sharedEvidence),
  ("explaining_away", named ["prior", "hard_alarm", "hard_alarm_and_rival", "soft_alarm",
    "soft_alarm_and_rival"] explainingAway),
  ("lures", named ["given_separator", "separator_and_lure", "only_lure"] lureReadouts),
  ("interventions", named ["confounded_observed", "confounded_do", "direct_do"] causalReadouts),
  ("but_for", named ["confounded", "direct"] butForReadouts),
  ("storm_persistence", named ["base", "carry"] persistenceReadouts),
  ("cross_region", named ["base", "second_leg"] crossRegionReadouts),
  ("regime", named ["changing", "stationary", "two_reports", "newest_withdrawn", "oldest_withdrawn"]
    regimeReadouts),
  ("late_evidence", toJson (lateEvidenceReadouts.map (fun value =>
    value.elim Json.null (fun (lo, hi) => .arr #[ratio lo, ratio hi])))),
  ("budget_allocation", toJson (allocationScores.map ratio)),
  ("concepts", toJson learnedParity),
  ("active_probing", toJson (probeScores.map ratio))]

end Mettapedia.Examples.PLN.ChainerGameReferenceReplay

def main : IO Unit :=
  IO.println Mettapedia.Examples.PLN.ChainerGameReferenceReplay.reference.pretty
