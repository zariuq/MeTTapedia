import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceFixtures

example : packetSupport first (.p0, .t0) = ⟨1, 0⟩ := by
  rfl

example :
    (aggregatePacketEvidence [first, first] (.p0, .t0)).pos = 2 := by
  change (packetSupport first (.p0, .t0) + packetSupport first (.p0, .t0)).pos = 2
  rw [show packetSupport first (.p0, .t0) = ⟨1, 0⟩ by rfl]
  rfl

example :
    (packetExperimentEvidence ({first, first} : Multiset Packet) (.p0, .t0)).pos = 2 := by
  simp [packetExperimentEvidence, experimentEvidence, packetExperimentQuery,
    packetExperimentChannel, SourcePacket.claim, queryOf, queryHolds, first]

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceFixtures
