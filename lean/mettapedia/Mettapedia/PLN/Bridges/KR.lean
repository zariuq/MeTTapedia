import Mettapedia.PLN.Bridges.KR.ConceptClosure
import Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary
import Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge
import Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge
import Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge

/-!
# PLN ↔ KR bridges

Interfaces between PLN-native closure machinery and knowledge-representation
concept structures.
-/

namespace Mettapedia.PLN.Bridges.KR

universe u

/-- Proof-carrying package for the current PLN/KR bridge surface.

The package keeps concept formation, formed-concept closure, de Finetti
readouts, control canaries, and stamped-provenance Revision guards visible as
one bridge layer. -/
structure PLNKRBridgeProfile (Stamp : Type u) [DecidableEq Stamp] where
  conceptFullInheritanceClosure :
    Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.CredalConceptFullInheritanceClosureBridgeProfile
  conceptFormationITV :
    Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge.ConceptFormationITVBridgeProfile
  conceptFormationControlCanary :
    Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary.ConceptFormationControlCanaryProfile.{0}
  conceptFormationDeFinettiPrefix :
    Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge.ConceptFormationDeFinettiPrefixBridgeProfile
  revisionStampedWitness :
    Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge.RevisionStampedWitnessBridgeProfile
      (Stamp := Stamp)

/-- Public profile for the current PLN/KR bridge layer. -/
noncomputable def plnKRBridgeProfile (Stamp : Type u) [DecidableEq Stamp] :
    PLNKRBridgeProfile Stamp where
  conceptFullInheritanceClosure :=
    Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.credalConceptFullInheritanceClosureBridgeProfile
  conceptFormationITV :=
    Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge.conceptFormationITVBridgeProfile
  conceptFormationControlCanary :=
    Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary.conceptFormationControlCanaryProfile
  conceptFormationDeFinettiPrefix :=
    Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge.conceptFormationDeFinettiPrefixBridgeProfile
  revisionStampedWitness :=
    Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge.revisionStampedWitnessBridgeProfile

end Mettapedia.PLN.Bridges.KR
