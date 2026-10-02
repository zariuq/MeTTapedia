import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedRHS
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSubstitution

/-!
# Authored whole activation with arbitrary admitted receiver code

The actual generated matcher and source-selected reflective RHS are compared
with the existing located whole funding rule. Receiver bodies range over the
existing closed anonymous-binder decoder domain. Target observations use pure
structural congruence; literal configurations and keys remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def receiverBindings (channel body payload signature tail : Pattern) : Bindings :=
  [(rhoCIGSLT.costStackTailVariable, tail),
   (rhoCIGSLT.costSignatureVariable, signature),
   (costSourceSchemaName "q", payload),
   (costSourceSchemaName "rest", .collection .hashBag [] none),
   (costSourceSchemaName "p", body),
   (costSourceSchemaName "n", channel)]

def receiverSource (channel body payload signature tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [.collection .hashBag
        [.apply (costBaseConstructorName "PInput")
          [channel, .lambda none (body)],
         .apply (costBaseConstructorName "POutput") [channel, payload]] none,
       signature],
     .apply costFundingConstructorName
       [.apply costTokenStackConsConstructorName [signature, tail]]]

theorem actual_receiver_match (channel body payload signature tail : Pattern) :
    receiverBindings channel body payload signature tail ∈
      matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile
        rhoCIGSLT.costWholeRedexRewrite (receiverSource channel body payload signature tail) := by
  rw [matchPatternForRuleUsing, baseRhoDeclaration_selected]
  change receiverBindings channel body payload signature tail ∈
    matchPatternWith (canonicalEquivalent baseRhoDeclaration)
      (.apply costContactConstructorName
        [.apply costSignedConstructorName
          [.collection .hashBag
            [.apply (costBaseConstructorName "PInput")
              [.fvar (costSourceSchemaName "n"), .lambda none (.fvar (costSourceSchemaName "p"))],
             .apply (costBaseConstructorName "POutput")
              [.fvar (costSourceSchemaName "n"), .fvar (costSourceSchemaName "q")]]
            (some (costSourceSchemaName "rest")),
           .fvar rhoCIGSLT.costSignatureVariable],
         .apply costFundingConstructorName
           [.apply costTokenStackConsConstructorName
             [.fvar rhoCIGSLT.costSignatureVariable, .fvar rhoCIGSLT.costStackTailVariable]]]) _
  simp [receiverSource, receiverBindings, matchPatternWith, matchArgsWith,
    matchBagWith, mergeBindingsWith, canonicalEquivalent,
    costSourceSchemaName, costSourceSchemaTag, CIGSLT.costSignatureVariable,
    CIGSLT.costStackTailVariable, costAdministrativeSchemaName,
    costAdministrativeSchemaTag]

def receiverContractum (body payload tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.collection .hashBag
      [substituteReflective wrappedRhoDeclaration 0 (generatedReplacement payload) body] none,
     .apply costFundingConstructorName [tail]]

theorem actual_receiver_rhs (channel body payload signature tail : Pattern) :
    applyBindingsForRuleUsing rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeRedexRewrite (receiverBindings channel body payload signature tail)
      = receiverContractum body payload tail := by
  unfold applyBindingsForRuleUsing
  rw [wrappedRhoDeclaration_selected]
  change applyBindingsReflective wrappedRhoDeclaration
      (receiverBindings channel body payload signature tail)
      (.apply costContactConstructorName
        [.collection .hashBag
          [.subst (.fvar (costSourceSchemaName "p"))
            (.apply (costWrappedConstructorName "NQuote") [.fvar (costSourceSchemaName "q")])]
          (some (costSourceSchemaName "rest")),
         .apply costFundingConstructorName [.fvar rhoCIGSLT.costStackTailVariable]]) = _
  have quoteName : wrappedRhoDeclaration.quoteConstructor =
      "$cost:wrapped-constructor:NQuote" := rfl
  simp [quoteName, receiverBindings, receiverContractum, generatedReplacement, applyBindingsReflective,
    applyBindingsReflectiveList, normalizeReflectiveReplacement,
    costSourceSchemaName, costSourceSchemaTag, CIGSLT.costSignatureVariable,
    CIGSLT.costStackTailVariable, costAdministrativeSchemaName,
    costAdministrativeSchemaTag, costWrappedConstructorName, costWrappedConstructorTag]

theorem actual_receiver_step (channel body payload signature tail : Pattern) :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage (receiverSource channel body payload signature tail)
      (receiverContractum body payload tail) := by
  refine ⟨1, .rule (rule := rhoCIGSLT.costWholeRedexRewrite)
    (initialBindings := receiverBindings channel body payload signature tail)
    (finalBindings := receiverBindings channel body payload signature tail)
    List.mem_cons_self (actual_receiver_match channel body payload signature tail)
    (.nil _) (actual_receiver_rhs channel body payload signature tail)⟩

def decodedReceiverSource (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority)
    (tail : CostStack LiteralAuthority) : CostTerm LiteralAuthority :=
  locatedContact location (.signed (.par (.recv location body) (.send location payload)) signature)
    (.cons signature tail)

theorem receiver_source_decodes (fuel : Nat)
    (bodySource payloadSource signatureSource tailSource : Pattern)
    (body : DecodedCode 1 bodySource) (payload : DecodedCode 0 payloadSource) (signature : TypedSignature signatureSource)
    (tail : DecodedStack tailSource)
    (bodyParsed : code? (fuel + 2) 1 bodySource = some body)
    (payloadParsed : code? (fuel + 2) 0 payloadSource = some payload)
    (signatureParsed : signature? signatureSource = some signature)
    (tailParsed : stack? (fuel + 5) tailSource = some tail) :
    (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported (fuel + 7)
      (receiverSource nilChannelSource bodySource payloadSource signatureSource tailSource)).map Subtype.val =
      some (decodedReceiverSource nilChannelLocation body.val payload.val signature.val tail.val) := by
  have payloadValue : (code? (fuel + 2) 0 payloadSource).map Subtype.val = some payload.val :=
    congrArg (Option.map Subtype.val) payloadParsed
  have signatureValue : (signature? signatureSource).map Subtype.val = some signature.val :=
    congrArg (Option.map Subtype.val) signatureParsed
  have tailValue : (stack? (fuel + 5) tailSource).map Subtype.val = some tail.val :=
    congrArg (Option.map Subtype.val) tailParsed
  have channelValue : (name? (fuel + 2) 0 nilChannelSource).map Subtype.val =
      some nilChannelLocation := name_base_zero_quote_readout (fuel + 1) 0
  have bodyValue : (code? (fuel + 2) 1 bodySource).map Subtype.val = some body.val :=
    congrArg (Option.map Subtype.val) bodyParsed
  have receiveValue : (proc? (fuel + 3) 0
      (.apply "$cost:base-constructor:PInput"
        [nilChannelSource, .lambda none bodySource])).map
      Subtype.val = some (.recv nilChannelLocation body.val) := by
    have readout := proc_recv_readout (fuel + 2) 0 nilChannelSource
      bodySource
    simp only [Nat.add_assoc] at readout
    rw [readout, channelValue, bodyValue]
    rfl
  have sendValue : (proc? (fuel + 3) 0
      (.apply "$cost:base-constructor:POutput" [nilChannelSource, payloadSource])).map Subtype.val =
      some (.send nilChannelLocation payload.val) := by
    have readout := proc_send_readout (fuel + 2) 0 nilChannelSource payloadSource
    simp only [Nat.add_assoc] at readout
    rw [readout, channelValue, payloadValue]
    rfl
  let receiveSource : Pattern := .apply "$cost:base-constructor:PInput"
    [nilChannelSource, .lambda none bodySource]
  let sendSource : Pattern := .apply "$cost:base-constructor:POutput" [nilChannelSource, payloadSource]
  let coreSource : Pattern := .collection .hashBag [receiveSource, sendSource] none
  let signedSource : Pattern := .apply "$cost:apparatus-constructor:signed" [coreSource, signatureSource]
  let stackSource : Pattern := .apply "$cost:apparatus-constructor:token-stack-cons" [signatureSource, tailSource]
  have coreValue : (proc? (fuel + 4) 0 coreSource).map Subtype.val =
      some (.par (.recv nilChannelLocation body.val) (.send nilChannelLocation payload.val)) := by
    have readout := proc_pair_readout (fuel + 3) 0 receiveSource sendSource
    simp only [Nat.add_assoc] at readout
    rw [readout, receiveValue, sendValue]
    rfl
  have signedValue : (code? (fuel + 5) 0 signedSource).map Subtype.val =
      some (.signed (.par (.recv nilChannelLocation body.val)
        (.send nilChannelLocation payload.val)) signature.val) := by
    have readout := code_signed_readout (fuel + 4) 0 coreSource signatureSource
    simp only [Nat.add_assoc] at readout
    rw [readout, signatureValue, coreValue]
    rfl
  have configValue : (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported
      (fuel + 6) signedSource).map Subtype.val =
      some (.signed (.par (.recv nilChannelLocation body.val)
        (.send nilChannelLocation payload.val)) signature.val) := by
    have readout := config_signed_readout nilChannelLocation nilChannelLocation_free
      nilChannelLocation_supported (fuel + 5) coreSource signatureSource
    simp only [Nat.add_assoc] at readout
    rw [readout, signedValue]
  have stackValue : (stack? (fuel + 6) stackSource).map Subtype.val =
      some (.cons signature.val tail.val) := by
    have readout := stack_cons_readout (fuel + 5) signatureSource tailSource
    simp only [Nat.add_assoc] at readout
    rw [readout, signatureValue, tailValue]
    rfl
  have readout := config_contact_readout nilChannelLocation nilChannelLocation_free
    nilChannelLocation_supported (fuel + 6) signedSource stackSource
  simp only [Nat.add_assoc] at readout
  change (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported (fuel + 7)
    (.apply "$cost:apparatus-constructor:contact"
      [signedSource, .apply "$cost:apparatus-constructor:funding" [stackSource]])).map Subtype.val = _
  rw [readout, configValue, stackValue]
  rfl

theorem decoded_receiver_step (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority)
    (tail : CostStack LiteralAuthority) (positive : signature.RuntimeValid) :
    CostStep (decodedReceiverSource location body payload signature tail).components
      location signature (locatedContact location (body.commSubst payload) tail).components := by
  simpa [decodedReceiverSource, locatedContact, CostTerm.components,
    LocatedPurse.configComponents, LocatedPurse.toTerm] using
    CostStep.wholeRecvSend (context := 0) (body := body) (payload := payload)
      positive (LocatedTokenCover.singleHead location signature positive tail)

theorem receiver_contractum_erasure {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (payloadSafe : payload.BinderSafe) (tailSource : Pattern)
    (location : CostName LiteralAuthority) (tail : CostStack LiteralAuthority)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (eraseGenerated (receiverContractum bodySource payloadSource tailSource))
      ((locatedContact location (body.commSubst payload) tail).erase encoding) := by
  exact collectionCongruence_of_forall₂ .hashBag none
    (.cons (.trans _ _ _ (.par_singleton _)
      (bodyImage.substitute_erasure payloadImage payloadSafe encoding)) (.cons (.refl _) .nil))

/-- Actual parser success fixes the common source; the two independently
specified firing relations are compared through the existing pure observer. -/
theorem receiver_firing_comparison (fuel : Nat)
    (bodySource payloadSource signatureSource tailSource : Pattern)
    (body : DecodedCode 1 bodySource) (payload : DecodedCode 0 payloadSource)
    (signature : TypedSignature signatureSource) (tail : DecodedStack tailSource)
    (bodyParsed : code? (fuel + 2) 1 bodySource = some body)
    (payloadParsed : code? (fuel + 2) 0 payloadSource = some payload)
    (signatureParsed : signature? signatureSource = some signature)
    (tailParsed : stack? (fuel + 5) tailSource = some tail)
    (sourceTyped : HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (receiverSource nilChannelSource bodySource payloadSource signatureSource tailSource)
      (.base costWrappedSortName))
    (encoding : SignatureNameEncoding LiteralAuthority) :
    GeneratedConfigImage nilChannelLocation
      (receiverSource nilChannelSource bodySource payloadSource signatureSource tailSource)
      (decodedReceiverSource nilChannelLocation body.val payload.val signature.val tail.val) ∧
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage
      (receiverSource nilChannelSource bodySource payloadSource signatureSource tailSource)
      (receiverContractum bodySource payloadSource tailSource) ∧
    CostStep (decodedReceiverSource nilChannelLocation body.val payload.val signature.val tail.val).components
      nilChannelLocation signature.val
      (locatedContact nilChannelLocation (body.val.commSubst payload.val) tail.val).components ∧
    StructuralCongruence (eraseGenerated (receiverContractum bodySource payloadSource tailSource))
      ((locatedContact nilChannelLocation (body.val.commSubst payload.val) tail.val).erase encoding) := by
  refine ⟨⟨sourceTyped, nilChannelLocation_free, nilChannelLocation_supported, fuel + 7,
      receiver_source_decodes fuel bodySource payloadSource signatureSource tailSource
        body payload signature tail bodyParsed payloadParsed signatureParsed tailParsed⟩,
    actual_receiver_step nilChannelSource bodySource payloadSource signatureSource tailSource,
    decoded_receiver_step nilChannelLocation body.val payload.val signature.val tail.val signature.positive, ?_⟩
  exact receiver_contractum_erasure
    (code_parser_image (congrArg (Option.map Subtype.val) bodyParsed))
    (code_parser_image (congrArg (Option.map Subtype.val) payloadParsed))
    payload.property.2.1 tailSource nilChannelLocation tail.val encoding

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
