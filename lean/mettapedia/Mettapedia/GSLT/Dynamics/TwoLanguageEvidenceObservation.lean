import Mettapedia.Evidence.TwoLanguage
import Mettapedia.GSLT.Dynamics.ObservationTransport

/-!
# Two-language evidence along operational observation transport

A GSLT operational translation maps proof-relevant events. Observation
disciplines pull back along that map without changing their witness container;
two-language evidential layers pull back by interpreting source evidence
through the same event map. This module packages both structures and proves
their naturality squares together.

The construction does not identify evidence with an observation value. Events
remain the evidence language, collected histories remain proof-relevant
witnesses, and any scalar degree remains a readout chosen by the evidential
layer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.TwoLanguageEvidenceObservation

open Mettapedia.Evidence
open Mettapedia.GSLT.Dynamics

universe uWorld uDegree uBelief uEvent uSourceEvent uContainer uValue

/-- A common event language observed operationally and used evidentially. -/
structure EvidentialObservation
    (World : Type uWorld) (Degree : Type uDegree)
    (Belief : Type uBelief) (Event : Type uEvent) where
  observation : ObservationDiscipline.{uEvent, uContainer, uValue} Event
  evidence : TwoLanguageLayer World Degree Belief Event

namespace EvidentialObservation

variable {World : Type uWorld} {Degree : Type uDegree}
  {Belief : Type uBelief} {Event : Type uEvent}

/-- Pull both operational observation and evidential support back along one
event translation. -/
def pullback {SourceEvent : Type uSourceEvent}
    (eventMap : SourceEvent → Event)
    (target : EvidentialObservation World Degree Belief Event) :
    EvidentialObservation World Degree Belief SourceEvent where
  observation :=
    ObservationTransport.ObservationDiscipline.pullback
      eventMap target.observation
  evidence := target.evidence.pullbackEvidence eventMap

/-- Operational observations commute with event translation. -/
theorem pullback_observe {SourceEvent : Type uSourceEvent}
    (eventMap : SourceEvent → Event)
    (target : EvidentialObservation World Degree Belief Event)
    (events : List SourceEvent) :
    (target.pullback eventMap).observation.observe events =
      target.observation.observe (events.map eventMap) :=
  rfl

/-- Evidential degrees commute with the same event translation. -/
theorem pullback_degree {SourceEvent : Type uSourceEvent}
    (eventMap : SourceEvent → Event)
    (target : EvidentialObservation World Degree Belief Event)
    (belief : Belief) (available : Set SourceEvent) :
    (target.pullback eventMap).evidence.degree belief available =
      target.evidence.degree belief (eventMap '' available) :=
  TwoLanguageLayer.pullbackEvidence_degree
    target.evidence eventMap belief available

/-- The paired naturality law: translation commutes independently with the
proof-relevant operational observation and with its evidential readout. -/
theorem pullback_naturality {SourceEvent : Type uSourceEvent}
    (eventMap : SourceEvent → Event)
    (target : EvidentialObservation World Degree Belief Event)
    (events : List SourceEvent) (belief : Belief)
    (available : Set SourceEvent) :
    (target.pullback eventMap).observation.observe events =
        target.observation.observe (events.map eventMap) ∧
      (target.pullback eventMap).evidence.degree belief available =
        target.evidence.degree belief (eventMap '' available) :=
  ⟨pullback_observe eventMap target events,
    pullback_degree eventMap target belief available⟩

#print axioms pullback_observe
#print axioms pullback_degree
#print axioms pullback_naturality

end EvidentialObservation

end Mettapedia.GSLT.Dynamics.TwoLanguageEvidenceObservation
