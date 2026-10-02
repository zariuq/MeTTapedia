import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedRHS
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedControls

/-!
# A discriminating normalization-aware generated firing control

Reflective normalization changes the literal quoted payload in this actual
authored firing. The funded declarative endpoint retains its literal payload.
Their erasures agree by the established rho structural observer, while exact
configuration equality fails. No free dequotation step is added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalizationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated

def quote (code : Pattern) : Pattern := .apply (costWrappedConstructorName "NQuote") [code]
def drop (name : Pattern) : Pattern := .apply (costWrappedConstructorName "PDrop") [name]
def zero : Pattern := .apply (costWrappedConstructorName "PZero") []

def literalPayload : Pattern := drop (quote (drop (quote zero)))
def normalizedPayload : Pattern := drop (quote zero)
def interpretedLiteral : CostTerm LiteralAuthority := .drop (.quote (.drop (.quote .nil)))
def interpretedNormalized : CostTerm LiteralAuthority := .drop (.quote .nil)

def source : Pattern := activationSource nilChannelSource literalPayload
  ActivationGeneratedControls.unitSignature ActivationGeneratedControls.emptyStack
def target : Pattern := .apply costContactConstructorName
  [.collection .hashBag [normalizedPayload] none,
   .apply costFundingConstructorName [ActivationGeneratedControls.emptyStack]]

def sourceTerm : CostTerm LiteralAuthority := decodedActivationSource nilChannelLocation
  interpretedLiteral {ActivationGeneratedControls.unitSignature} .empty
def literalTarget : CostTerm LiteralAuthority := locatedContact nilChannelLocation interpretedLiteral .empty
def normalizedTarget : CostTerm LiteralAuthority := locatedContact nilChannelLocation interpretedNormalized .empty

theorem literal_payload_image : GeneratedCodeImage 0 literalPayload interpretedLiteral := by
  exact ⟨checkHasType_sound (by decide +kernel), 12, by decide +kernel⟩

theorem source_image : GeneratedConfigImage nilChannelLocation source sourceTerm := by
  exact ⟨checkHasType_sound (by decide +kernel), nilChannelLocation_free,
    nilChannelLocation_supported, 20, by decide +kernel⟩

theorem target_typed : HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
    target (.base costWrappedSortName) := checkHasType_sound (by decide +kernel)

theorem actual_declared_normalization_firing :
    rewriteAt (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage 1 source = [target] := by
  decide +kernel

theorem actual_endpoints_decode_independently :
    (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported 20 source).map
      (fun decoded => decoded.val.components) = some sourceTerm.components ∧
    (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported 20 target).map
      (fun decoded => decoded.val.components) = some normalizedTarget.components := by
  decide +kernel

theorem actual_funded_endpoint_is_literal :
    CostStep sourceTerm.components nilChannelLocation {ActivationGeneratedControls.unitSignature}
      literalTarget.components :=
  decoded_activation_step nilChannelLocation interpretedLiteral
    {ActivationGeneratedControls.unitSignature} .empty (Multiset.singleton_ne_zero _)

theorem literal_target_equality_fails : literalTarget.components ≠ normalizedTarget.components := by
  decide +kernel

theorem no_literal_costStep_to_normalized_endpoint
    (location : CostName LiteralAuthority) (spend : CostSig LiteralAuthority) :
    ¬CostStep sourceTerm.components location spend normalizedTarget.components := by
  intro step
  generalize sourceEq : sourceTerm.components = sourceConfig at step
  generalize targetEq : normalizedTarget.components = targetConfig at step
  cases step with
  | @wholeRecvSend frame available residual channel body sent signature positive cover =>
    have redexMember : (.signed (.par (.recv location body) (.send location sent)) spend) ∈
        sourceTerm.components := by
      rw [sourceEq]
      simp
    simp [sourceTerm, decodedActivationSource, locatedContact, CostTerm.components] at redexMember
    rcases redexMember with ⟨⟨⟨rfl, rfl⟩, _sameLocation, rfl⟩, rfl⟩
    have contractumMember : interpretedLiteral ∈ normalizedTarget.components := by
      rw [targetEq]
      simp [CostTerm.commSubst, CostTerm.substitute, CostTerm.lift_zero,
        interpretedLiteral, CostTerm.components]
    simp [normalizedTarget, locatedContact, CostTerm.components, interpretedLiteral,
      interpretedNormalized] at contractumMember
  | @wholeSendRecv frame available residual channel body sent signature positive cover =>
    have redexMember : (.signed (.par (.send location sent) (.recv location body)) spend) ∈
        sourceTerm.components := by
      rw [sourceEq]
      simp
    simp [sourceTerm, decodedActivationSource, locatedContact, CostTerm.components] at redexMember
  | @split frame available residual channel body sent recvSignature sendSignature recvPositive sendPositive cover =>
    have redexMember : (.signed (.recv location body) recvSignature) ∈ sourceTerm.components := by
      rw [sourceEq]
      simp
    simp [sourceTerm, decodedActivationSource, locatedContact, CostTerm.components] at redexMember

theorem actual_contractum_observer_matches_funded_endpoint
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (eraseGenerated target) (literalTarget.erase encoding) := by
  have targetEqual : target = activationContractum literalPayload
      ActivationGeneratedControls.emptyStack := by decide +kernel
  rw [targetEqual]
  exact activation_contractum_erasure literal_payload_image
    ActivationGeneratedControls.emptyStack encoding

theorem unit_and_product_authority_remain_distinct :
    ({ActivationGeneratedControls.unitSignature} : CostSig LiteralAuthority) ≠
      {ActivationGeneratedControls.productSignature} := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalizationControls
