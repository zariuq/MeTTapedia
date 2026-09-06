import Mettapedia.Languages.Megalodon.DefinitionConversionKernel
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.InferenceABTWireRefinement

/-!
# Exact wire refinement for the Megalodon definition canary

The retained-definition specimen is checked in the logical presentation and
then transported through the exact CeTTa carrier.  The physical runtime model
uses the same decoded presentation, goal, proof tree, constructor vocabulary,
and side-condition semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.DefinitionConversionWireRefinement

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering
open Mettapedia.GSLT.LanguageDef.InferenceCettaExecutionRefinement
open Mettapedia.Languages.Megalodon.DefinitionConversionKernel

/-- The exact CeTTa goal carrier loses no binding or constructor data. -/
theorem definition_identity_goal_roundtrip :
    decodePattern (encodePattern definitionIdentityGoal) =
      some definitionIdentityGoal :=
  decodePattern_encodePattern definitionIdentityGoal

/-- The exact CeTTa proof carrier loses no rule, argument, or child data. -/
theorem definition_identity_article_roundtrip :
    decodeRawProof (encodeRawProof definitionIdentityArticle) =
      some definitionIdentityArticle :=
  decodeRawProof_encodeRawProof definitionIdentityArticle

/-- The checker-facing definition presentation round-trips with its rooted
conversion declaration and generic side conditions intact. -/
theorem definition_presentation_roundtrip :
    Mettapedia.GSLT.LanguageDef.InferenceCettaWire.decodeRuntimeInferenceLanguage
        (Mettapedia.GSLT.LanguageDef.InferenceCettaWire.encodeDefinition
          DefinitionConversionKernel.definition) =
      some (RuntimeInferenceLanguage.ofDefinition DefinitionConversionKernel.definition) :=
  Mettapedia.GSLT.LanguageDef.InferenceCettaWire.decodeRuntimeInferenceLanguage_encodeDefinition
    DefinitionConversionKernel.definition

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Every fixed application carried by the concrete article belongs to the
declared definition-conversion constructor vocabulary. -/
theorem definition_identity_payloads_valid :
    (RuntimeInferenceLanguage.ofDefinition DefinitionConversionKernel.definition).proofPayloadsValid
        definitionIdentityArticle = true := by
  exact definition_identity_closed_payload

/-- Logical acceptance of the exact retained-definition article is complete
for the closed-payload runtime model consumed by CeTTa. -/
theorem definition_identity_packet_accepted :
    checkPacket
        (encodeRuntimeInferenceLanguage
          (RuntimeInferenceLanguage.ofDefinition DefinitionConversionKernel.definition))
        (encodePattern definitionIdentityGoal)
        (encodeRawProof definitionIdentityArticle) = some true := by
  rw [checkPacket_encode]
  apply congrArg some
  exact RuntimeInferenceLanguage.checkRaw_complete
    validated definitionIdentityGoal definitionIdentityArticle
    definition_identity_article_accepted
    definition_identity_payloads_valid

/-- The accepted retained-definition packet lowers every authenticated rule
node to the support-indexed ABT carrier while retaining the exact article. -/
theorem definition_identity_packet_has_abt_derivation :
    ∃ derivation : ABTDerivation validated definitionIdentityGoal,
      ABTDerivation.erase derivation = definitionIdentityArticle := by
  exact
    Mettapedia.GSLT.LanguageDef.InferenceABTWireRefinement.Cetta.checkPacket_acceptance_has_abt_derivation
      validated definitionIdentityGoal definitionIdentityArticle
      definition_identity_packet_accepted

/-- The same retained-definition article is replayed by the direct physical
schema walk at every proof node and retains its exact chronological erasure. -/
theorem definition_identity_packet_has_physical_abt_derivation :
    ∃ derivation : PhysicalABTDerivation
        validated definitionIdentityGoal,
      PhysicalABTDerivation.erase derivation =
        definitionIdentityArticle := by
  exact
    Mettapedia.GSLT.LanguageDef.InferenceABTWireRefinement.Cetta.checkPacket_acceptance_has_physical_abt_derivation
      validated definitionIdentityGoal definitionIdentityArticle
      definition_identity_packet_accepted

/-- The same exact article cannot be replayed at the distinct synthesized
endpoint after crossing the physical carrier. -/
theorem definition_identity_wrong_packet_rejected :
    checkPacket
        (encodeRuntimeInferenceLanguage
          (RuntimeInferenceLanguage.ofDefinition DefinitionConversionKernel.definition))
        (encodePattern definitionIdentityWrongGoal)
        (encodeRawProof definitionIdentityArticle) = some false := by
  rw [checkPacket_encode]
  cases runtimeResult :
      (RuntimeInferenceLanguage.ofDefinition DefinitionConversionKernel.definition).checkRaw
        definitionIdentityWrongGoal definitionIdentityArticle with
  | false => rfl
  | true =>
      have genericResult :=
        (RuntimeInferenceLanguage.checkRaw_iff_generic_of_payloadsValid validated
          definitionIdentityWrongGoal definitionIdentityArticle
          definition_identity_payloads_valid).mp runtimeResult
      rw [definition_identity_wrong_goal_rejected] at genericResult
      simp at genericResult

end Mettapedia.Languages.Megalodon.DefinitionConversionWireRefinement
