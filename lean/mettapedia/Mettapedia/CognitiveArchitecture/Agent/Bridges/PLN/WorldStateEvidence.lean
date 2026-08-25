import Mettapedia.CognitiveArchitecture.Agent.WorldState
import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-!
# Agent world-state evidence bridge for PLN

The architecture-neutral agent state permits any evidence revision discipline.
This bridge proves the additional law obtained when its evidence coordinate is
an additive PLN world model.  Keeping the specialization here prevents the
general context and compaction theory from depending on PLN.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.Bridges.PLN.WorldStateEvidence

open Mettapedia.CognitiveArchitecture.Agent.WorldState
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-- PLN extraction sees evidence revision as addition, while the other agent
coordinates remain outside that algebra. -/
theorem extract_reviseEvidence
    {Operational Evidence Commitment Context Capability Query Ev : Type*}
    [EvidenceType Evidence] [AddCommMonoid Ev]
    [AdditiveWorldModel Evidence Query Ev]
    (s : AgentState Operational Evidence Commitment Context Capability)
    (delta : Evidence) (q : Query) :
    AdditiveWorldModel.extract
        (State := Evidence) (Query := Query) (Ev := Ev)
        (reviseEvidence s delta).evidence q =
      AdditiveWorldModel.extract
          (State := Evidence) (Query := Query) (Ev := Ev) s.evidence q +
        AdditiveWorldModel.extract
          (State := Evidence) (Query := Query) (Ev := Ev) delta q := by
  exact AdditiveWorldModel.extract_add' s.evidence delta q

end Mettapedia.CognitiveArchitecture.Agent.Bridges.PLN.WorldStateEvidence

#print axioms Mettapedia.CognitiveArchitecture.Agent.Bridges.PLN.WorldStateEvidence.extract_reviseEvidence
