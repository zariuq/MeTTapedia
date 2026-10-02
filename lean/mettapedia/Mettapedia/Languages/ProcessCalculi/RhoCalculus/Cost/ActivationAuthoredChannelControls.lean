import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredWholeInversion
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedControls

/-!
# Actual authored and concrete channel comparison controls

The base-colored canonical matcher can distinguish wrapped zero from an
empty wrapped collection even when the existing parser returns the same
concrete rho location. This is a failure of reflection, not a counterexample
to preservation of a successful authored channel test.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredChannelControls

open ActivationGenerated ActivationLocatedControls
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def wrappedNilChannel : Pattern :=
  .apply "$cost:wrapped-constructor:NQuote" [.apply "$cost:wrapped-constructor:PZero" []]

def collectionNilChannel : Pattern :=
  .apply "$cost:wrapped-constructor:NQuote" [.collection .hashBag [] none]

theorem wrapped_nil_image : NameImage 0 wrappedNilChannel (.quote .nil) := .quote .zero

theorem collection_nil_image : NameImage 0 collectionNilChannel (.quote .nil) := .quote (.collection .nil)

/-- Both existing parser graphs return the same concrete location, whereas
the source-selected matcher keeps their distinct wrapped unit layouts. -/
theorem runtime_equal_authored_distinct :
    NameImage 0 wrappedNilChannel (.quote .nil) ∧
    NameImage 0 collectionNilChannel (.quote .nil) ∧
    canonicalEquivalent baseRhoDeclaration wrappedNilChannel collectionNilChannel = false := by
  exact ⟨wrapped_nil_image, collection_nil_image, by decide +kernel⟩

def senderSource : Pattern := .apply "$cost:base-constructor:POutput"
  [nilChannelSource, .apply "$cost:wrapped-constructor:PZero" []]

def senderChannel : Pattern := .apply "$cost:wrapped-constructor:NQuote"
  [.apply "$cost:apparatus-constructor:signed" [senderSource, unitSource]]

def unitPaddedChannel : Pattern := .apply "$cost:wrapped-constructor:NQuote"
  [.apply "$cost:apparatus-constructor:signed"
    [.collection .hashBag [.apply "$cost:base-constructor:PZero" [], senderSource] none, unitSource]]

theorem sender_channel_image : NameImage 0 senderChannel
    (.quote (.signed (.send nilChannelLocation .nil) unitTyped.val)) :=
  .quote (.signed unitTyped unit_accepted (.send .baseZeroQuote .zero))

theorem unit_padded_channel_image : NameImage 0 unitPaddedChannel
    (.quote (.signed (.par .nil (.send nilChannelLocation .nil)) unitTyped.val)) :=
  .quote (.signed unitTyped unit_accepted (.pair .zero (.send .baseZeroQuote .zero)))

/-- A nonliteral successful source test removes the declared base unit
inside a signed quoted sender, and the actual concrete locations agree. -/
theorem successful_channel_match_preserves_location :
    canonicalEquivalent baseRhoDeclaration unitPaddedChannel senderChannel = true ∧
    (literalEncodeName (.quote (.signed (.par .nil (.send nilChannelLocation .nil)) unitTyped.val))).normalize =
      (literalEncodeName (.quote (.signed (.send nilChannelLocation .nil) unitTyped.val))).normalize := by
  exact ⟨by decide +kernel, rfl⟩

theorem wrong_external_location_literal_readout :
    (literalEncodeTerm (locatedContact channel
      (.signed (.par (.recv nilChannelLocation (.drop (.bvar 0)))
        (.send nilChannelLocation .nil)) unitTyped.val) (.cons unitTyped.val .empty))).components =
      [.signed (.par (.recv occurrenceNilLocation (.drop (.bvar 0)))
        (.send occurrenceNilLocation .nil)) [literalAuthorityKey unitSource],
       .purse (literalEncodeName channel) [[literalAuthorityKey unitSource]]] := by
  change [RawCostTerm.signed _ (encodeCostSig (unitTyped.val.map literalAuthorityKey)),
    RawCostTerm.purse (literalEncodeName channel) [encodeCostSig (unitTyped.val.map literalAuthorityKey)]] = _
  rw [unitTyped.property.1, literalEncodeSig_singleton]
  rfl

/-- The authored funding constructor has no channel coordinate. An actual
R1 firing therefore still parses when its concrete funding location differs
from the matched channels. The located runtime correctly rejects that purse. -/
theorem actual_authored_step_wrong_external_location :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage
      (receiverSource nilChannelSource boundBodySource zeroSource unitSource emptySource)
      (receiverContractum boundBodySource zeroSource emptySource) ∧
    ConfigImage channel
      (receiverSource nilChannelSource boundBodySource zeroSource unitSource emptySource)
      (locatedContact channel
        (.signed (.par (.recv nilChannelLocation (.drop (.bvar 0)))
          (.send nilChannelLocation .nil)) unitTyped.val) (.cons unitTyped.val .empty)) ∧
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv occurrenceNilLocation (.drop (.bvar 0)))
        (.send occurrenceNilLocation .nil)) [literalAuthorityKey unitSource],
       .purse (literalEncodeName channel) [[literalAuthorityKey unitSource]]] = [] := by
  refine ⟨actual_receiver_step _ _ _ _ _, ?_, ?_⟩
  · exact .contact (.signed unitTyped unit_accepted
      (.pair (.recv .baseZeroQuote (.drop (.bvar (by decide +kernel))))
        (.send .baseZeroQuote .zero))) (.cons unitTyped unit_accepted .empty)
  · exact locatedWhole_wrong_location_blocked _ _ canonical_channel_distinct _ []

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredChannelControls
