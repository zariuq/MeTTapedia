import Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
import Mettapedia.GSLT.LanguageDef.GSLTILOperationalEquipment

/-!
# Tight code transport and loose dependent interaction

The dependent reflective protocol supplies two different kinds of operational
arrow, and the distinction is structural.

The exact command-code comparison preserves one endpoint step at a time in
both directions.  It therefore gives tight operational translations and the
canonical represented companion routes of the GSLT-IL equipment.

The interaction itself is different.  From the initial state there are two
proof-relevant enabled events with different response-selected targets.  The
loose route retaining those events is not representable by one function.  It
belongs to the relational horizontal layer of the equipment rather than the
functional tight layer.

Thus exact reflection of command syntax does not collapse operational choice.
The same inhabited protocol exhibits both the represented and genuinely loose
parts of the equipment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolEquipment

open Mettapedia.GSLT
open Mettapedia.Computability.ReflectiveCode
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.ExactCodeProtocolPolynomial
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ExactCodeModalityModel

namespace Comparison

open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
open Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalEquipment

/-! ## Tight exact-code translations -/

/-- Encoding exact command codes preserves each endpoint step directly. -/
def encodingTranslation : Tight (lts query) (lts codedQuery) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := fun step =>
    step_preserves query CommandCode representation representation_beta step

/-- Decoding exact command codes reflects each endpoint step directly. -/
def decodingTranslation : Tight (lts codedQuery) (lts query) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := fun step =>
    step_reflects query CommandCode representation step

/-- Encoding followed by decoding has the identity endpoint map. -/
theorem encoding_then_decoding :
    tightComp encodingTranslation decodingTranslation = tightId (lts query) :=
  OperationalTranslation.ext rfl

/-- Decoding followed by encoding has the identity endpoint map. -/
theorem decoding_then_encoding :
    tightComp decodingTranslation encodingTranslation =
      tightId (lts codedQuery) :=
  OperationalTranslation.ext rfl

/-- Exact encoding has the canonical proof-relevant companion route. -/
def encodingCompanion : LooseRoute (lts query) (lts codedQuery) :=
  companionRoute encodingTranslation

/-- The encoding companion is represented by its selected direct map. -/
def encodingCompanionRepresentation : Representation encodingCompanion :=
  companionRepresentation encodingTranslation

/-- Exact decoding likewise has a represented companion route. -/
def decodingCompanion : LooseRoute (lts codedQuery) (lts query) :=
  companionRoute decodingTranslation

def decodingCompanionRepresentation : Representation decodingCompanion :=
  companionRepresentation decodingTranslation

/-! ## The genuinely loose interaction route -/

/-- A loose route retains the exact enabled event and its target equality.
It is defined for every protocol state, including states with no command. -/
def enabledEventRoute : LooseRoute (lts codedQuery) (lts codedQuery) :=
  fun source target =>
    { event : (interaction codedQuery).Enabled source // event.target = target }

/-- The false response gives one retained route occurrence. -/
def unitRouteWitness :
    enabledEventRoute Phase.start Phase.unitDone :=
  ⟨unitEvent, rfl⟩

/-- The true response gives a different retained route occurrence. -/
def boolRouteWitness :
    enabledEventRoute Phase.start Phase.boolDone :=
  ⟨boolEvent, rfl⟩

/-- Response-dependent branching prevents exact functional representation of
the enabled-event route.  The contradiction is at the target level, so it
does not depend on merely having multiple proofs of one endpoint. -/
theorem enabledEventRoute_not_representable :
    ¬ Nonempty (Representation enabledEventRoute) := by
  rintro ⟨represented⟩
  have deterministic := represented.deterministic Phase.start
  have sameOutcome :
      (⟨Phase.unitDone, unitRouteWitness⟩ :
          Sigma fun target => enabledEventRoute Phase.start target) =
        ⟨Phase.boolDone, boolRouteWitness⟩ :=
    deterministic.allEq _ _
  have impossible : Phase.unitDone = Phase.boolDone :=
    congrArg Sigma.fst sameOutcome
  cases impossible

/-- The connected protocol inhabits both strata of the operational
equipment: exact code transport is represented, while interaction choice is
genuinely loose. -/
theorem tight_code_loose_interaction_boundary :
    Nonempty (Representation encodingCompanion) /\
      Nonempty (Representation decodingCompanion) /\
      Nonempty (enabledEventRoute Phase.start Phase.unitDone) /\
      Nonempty (enabledEventRoute Phase.start Phase.boolDone) /\
      ¬ Nonempty (Representation enabledEventRoute) :=
  ⟨⟨encodingCompanionRepresentation⟩,
    ⟨decodingCompanionRepresentation⟩,
    ⟨unitRouteWitness⟩,
    ⟨boolRouteWitness⟩,
    enabledEventRoute_not_representable⟩

/-- The material code layer remains visible while the endpoint translations
are inverse.  Operational equivalence therefore does not identify the command
representations definitionally. -/
theorem material_code_and_operational_equivalence :
    (representation Phase.start).quote QueryCommand.ask =
        ExactCodeLayer.mk QueryCommand.ask /\
      tightComp encodingTranslation decodingTranslation = tightId (lts query) /\
      tightComp decodingTranslation encodingTranslation =
        tightId (lts codedQuery) :=
  ⟨quoted_ask_has_one_code_layer,
    encoding_then_decoding,
    decoding_then_encoding⟩

end Comparison

#print axioms Comparison.encodingTranslation
#print axioms Comparison.decodingTranslation
#print axioms Comparison.encoding_then_decoding
#print axioms Comparison.decoding_then_encoding
#print axioms Comparison.encodingCompanionRepresentation
#print axioms Comparison.enabledEventRoute_not_representable
#print axioms Comparison.tight_code_loose_interaction_boundary
#print axioms Comparison.material_code_and_operational_equivalence

end Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolEquipment
