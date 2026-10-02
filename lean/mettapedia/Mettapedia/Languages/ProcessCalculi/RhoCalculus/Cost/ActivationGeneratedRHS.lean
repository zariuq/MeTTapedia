import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedRefinement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReadout

/-!
# An authored reflective activation contractum family

The source-selected whole rule is applied to explicit matcher bindings for a
receiver returning its argument by Drop. Its actual reflective RHS normalizes
the communicated wrapped code. Apparatus erasure compares that contractum
with the existing funded activation endpoint for every admitted payload.
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

def activationBindings (channel payload signature tail : Pattern) : Bindings :=
  [(rhoCIGSLT.costStackTailVariable, tail),
   (rhoCIGSLT.costSignatureVariable, signature),
   (costSourceSchemaName "q", payload),
   (costSourceSchemaName "rest", .collection .hashBag [] none),
   (costSourceSchemaName "p", .apply (costWrappedConstructorName "PDrop") [.bvar 0]),
   (costSourceSchemaName "n", channel)]

def activationSource (channel payload signature tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [.collection .hashBag
        [.apply (costBaseConstructorName "PInput")
          [channel, .lambda none (.apply (costWrappedConstructorName "PDrop") [.bvar 0])],
         .apply (costBaseConstructorName "POutput") [channel, payload]] none,
       signature],
     .apply costFundingConstructorName
       [.apply costTokenStackConsConstructorName [signature, tail]]]

abbrev baseRhoDeclaration :=
  costBaseReflectivePresentationDecl rhoReflectivePresentation.toReflectivePresentationDecl

theorem baseRhoDeclaration_selected :
    matchingPresentationForRule? rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeRedexRewrite = some baseRhoDeclaration := by
  decide +kernel

theorem actual_activation_match (channel payload signature tail : Pattern) :
    activationBindings channel payload signature tail ∈
      matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile
        rhoCIGSLT.costWholeRedexRewrite (activationSource channel payload signature tail) := by
  rw [matchPatternForRuleUsing, baseRhoDeclaration_selected]
  change activationBindings channel payload signature tail ∈
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
  simp [activationSource, activationBindings, matchPatternWith, matchArgsWith,
    matchBagWith, mergeBindingsWith, canonicalEquivalent,
    costSourceSchemaName, costSourceSchemaTag, CIGSLT.costSignatureVariable,
    CIGSLT.costStackTailVariable, costAdministrativeSchemaName,
    costAdministrativeSchemaTag]

def activationContractum (payload tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.collection .hashBag [normalizeReflective wrappedRhoDeclaration payload] none,
     .apply costFundingConstructorName [tail]]

theorem actual_activation_rhs (channel payload signature tail : Pattern) :
    applyBindingsForRuleUsing rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeRedexRewrite (activationBindings channel payload signature tail)
      = activationContractum payload tail := by
  unfold applyBindingsForRuleUsing
  rw [wrappedRhoDeclaration_selected]
  change applyBindingsReflective wrappedRhoDeclaration
      (activationBindings channel payload signature tail)
      (.apply costContactConstructorName
        [.collection .hashBag
          [.subst (.fvar (costSourceSchemaName "p"))
            (.apply (costWrappedConstructorName "NQuote") [.fvar (costSourceSchemaName "q")])]
          (some (costSourceSchemaName "rest")),
         .apply costFundingConstructorName [.fvar rhoCIGSLT.costStackTailVariable]]) = _
  have quoteName : wrappedRhoDeclaration.quoteConstructor =
      costWrappedConstructorName "NQuote" := rfl
  have dropName : wrappedRhoDeclaration.dropConstructor =
      costWrappedConstructorName "PDrop" := rfl
  simp [activationBindings, activationContractum, applyBindingsReflective,
    applyBindingsReflectiveList, normalizeReflectiveReplacement, substituteReflective,
    substituteNameMark, normalizeReflective,
    costSourceSchemaName, costSourceSchemaTag, CIGSLT.costSignatureVariable,
    CIGSLT.costStackTailVariable, costAdministrativeSchemaName,
    costAdministrativeSchemaTag, quoteName, dropName,
    costWrappedConstructorName, costWrappedConstructorTag]

theorem actual_activation_step (channel payload signature tail : Pattern) :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage (activationSource channel payload signature tail)
      (activationContractum payload tail) := by
  refine ⟨1, .rule (rule := rhoCIGSLT.costWholeRedexRewrite)
    (initialBindings := activationBindings channel payload signature tail)
    (finalBindings := activationBindings channel payload signature tail)
    List.mem_cons_self (actual_activation_match channel payload signature tail)
    (.nil _) (actual_activation_rhs channel payload signature tail)⟩

def decodedActivationSource (location : CostName LiteralAuthority)
    (payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority)
    (tail : CostStack LiteralAuthority) : CostTerm LiteralAuthority :=
  locatedContact location
    (.signed (.par (.recv location (.drop (.bvar 0))) (.send location payload)) signature)
    (.cons signature tail)

def nilChannelSource : Pattern :=
  .apply (costBaseConstructorName "NQuote") [.apply (costBaseConstructorName "PZero") []]

def nilChannelLocation : CostName LiteralAuthority := .quote .nil

theorem nilChannelLocation_free : nilChannelLocation.purseInventory = 0 := rfl
theorem nilChannelLocation_supported : nilChannelLocation.RuntimeSupported := trivial

theorem activation_source_decodes (fuel : Nat)
    (payloadSource signatureSource tailSource : Pattern)
    (payload : DecodedCode 0 payloadSource) (signature : TypedSignature signatureSource)
    (tail : DecodedStack tailSource)
    (payloadParsed : code? (fuel + 2) 0 payloadSource = some payload)
    (signatureParsed : signature? signatureSource = some signature)
    (tailParsed : stack? (fuel + 5) tailSource = some tail) :
    (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported (fuel + 7)
      (activationSource nilChannelSource payloadSource signatureSource tailSource)).map Subtype.val =
      some (decodedActivationSource nilChannelLocation payload.val signature.val tail.val) := by
  have payloadValue : (code? (fuel + 2) 0 payloadSource).map Subtype.val = some payload.val :=
    congrArg (Option.map Subtype.val) payloadParsed
  have signatureValue : (signature? signatureSource).map Subtype.val = some signature.val :=
    congrArg (Option.map Subtype.val) signatureParsed
  have tailValue : (stack? (fuel + 5) tailSource).map Subtype.val = some tail.val :=
    congrArg (Option.map Subtype.val) tailParsed
  have channelValue : (name? (fuel + 2) 0 nilChannelSource).map Subtype.val =
      some nilChannelLocation := name_base_zero_quote_readout (fuel + 1) 0
  have bodyValue : (code? (fuel + 2) 1
      (.apply "$cost:wrapped-constructor:PDrop" [.bvar 0])).map Subtype.val =
      some (.drop (.bvar 0)) := by
    have readout := code_drop_readout (fuel + 1) 1 (.bvar 0)
    simp only [Nat.add_assoc] at readout
    rw [readout, name_bvar_readout fuel 1 0]
    rfl
  have receiveValue : (proc? (fuel + 3) 0
      (.apply "$cost:base-constructor:PInput"
        [nilChannelSource, .lambda none (.apply "$cost:wrapped-constructor:PDrop" [.bvar 0])])).map
      Subtype.val = some (.recv nilChannelLocation (.drop (.bvar 0))) := by
    have readout := proc_recv_readout (fuel + 2) 0 nilChannelSource
      (.apply "$cost:wrapped-constructor:PDrop" [.bvar 0])
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
    [nilChannelSource, .lambda none (.apply "$cost:wrapped-constructor:PDrop" [.bvar 0])]
  let sendSource : Pattern := .apply "$cost:base-constructor:POutput" [nilChannelSource, payloadSource]
  let coreSource : Pattern := .collection .hashBag [receiveSource, sendSource] none
  let signedSource : Pattern := .apply "$cost:apparatus-constructor:signed" [coreSource, signatureSource]
  let stackSource : Pattern := .apply "$cost:apparatus-constructor:token-stack-cons" [signatureSource, tailSource]
  have coreValue : (proc? (fuel + 4) 0 coreSource).map Subtype.val =
      some (.par (.recv nilChannelLocation (.drop (.bvar 0))) (.send nilChannelLocation payload.val)) := by
    have readout := proc_pair_readout (fuel + 3) 0 receiveSource sendSource
    simp only [Nat.add_assoc] at readout
    rw [readout, receiveValue, sendValue]
    rfl
  have signedValue : (code? (fuel + 5) 0 signedSource).map Subtype.val =
      some (.signed (.par (.recv nilChannelLocation (.drop (.bvar 0)))
        (.send nilChannelLocation payload.val)) signature.val) := by
    have readout := code_signed_readout (fuel + 4) 0 coreSource signatureSource
    simp only [Nat.add_assoc] at readout
    rw [readout, signatureValue, coreValue]
    rfl
  have configValue : (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported
      (fuel + 6) signedSource).map Subtype.val =
      some (.signed (.par (.recv nilChannelLocation (.drop (.bvar 0)))
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

theorem decoded_activation_step (location : CostName LiteralAuthority)
    (payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority)
    (tail : CostStack LiteralAuthority) (positive : signature.RuntimeValid) :
    CostStep (decodedActivationSource location payload signature tail).components
      location signature (locatedContact location payload tail).components := by
  simpa [decodedActivationSource, locatedContact, CostTerm.components,
    LocatedPurse.configComponents, LocatedPurse.toTerm, CostTerm.commSubst,
    CostTerm.substitute, CostTerm.lift_zero] using
    CostStep.wholeRecvSend (context := 0) (body := .drop (.bvar 0)) (payload := payload)
      positive (LocatedTokenCover.singleHead location signature positive tail)

theorem activation_contractum_observer_congruence (payloadSource : Pattern)
    (payload : CostTerm LiteralAuthority) (tail : Pattern)
    (encoding : SignatureNameEncoding LiteralAuthority)
    (correspondence : StructuralCongruence (payload.erase encoding) (eraseGenerated payloadSource)) :
    StructuralCongruence (eraseGenerated (activationContractum payloadSource tail))
      (.collection .hashBag [payload.erase encoding, .collection .hashBag [] none] none) := by
  have normalization := eraseGenerated_normalizeReflective payloadSource
  change StructuralCongruence
    (.collection .hashBag
      [.collection .hashBag [eraseGenerated (normalizeReflective wrappedRhoDeclaration payloadSource)] none,
       .collection .hashBag [] none] none)
    (.collection .hashBag [payload.erase encoding, .collection .hashBag [] none] none)
  exact collectionCongruence_of_forall₂ .hashBag none
    (.cons (.trans _ _ _ (.par_singleton _)
      (.trans _ _ _ normalization (.symm _ _ correspondence))) (.cons (.refl _) .nil))

theorem activation_contractum_erasure {payloadSource : Pattern}
    {payload : CostTerm LiteralAuthority} (image : GeneratedCodeImage 0 payloadSource payload)
    (tail : Pattern) (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (eraseGenerated (activationContractum payloadSource tail))
      (.collection .hashBag [payload.erase encoding, .collection .hashBag [] none] none) :=
  activation_contractum_observer_congruence payloadSource payload tail encoding
    (image.erase_structural encoding)

/-- Both firings share an independently decoded actual source. The actual
generated RHS and funded endpoint are compared by the pure structural observer;
this statement does not assert literal decoding equality of their targets. -/
theorem activation_firing_comparison (fuel : Nat)
    (payloadSource signatureSource tailSource : Pattern)
    (payload : DecodedCode 0 payloadSource) (signature : TypedSignature signatureSource)
    (tail : DecodedStack tailSource)
    (payloadParsed : code? (fuel + 2) 0 payloadSource = some payload)
    (signatureParsed : signature? signatureSource = some signature)
    (tailParsed : stack? (fuel + 5) tailSource = some tail)
    (sourceTyped : HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (activationSource nilChannelSource payloadSource signatureSource tailSource)
      (.base costWrappedSortName))
    (encoding : SignatureNameEncoding LiteralAuthority) :
    GeneratedConfigImage nilChannelLocation
      (activationSource nilChannelSource payloadSource signatureSource tailSource)
      (decodedActivationSource nilChannelLocation payload.val signature.val tail.val) ∧
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage
      (activationSource nilChannelSource payloadSource signatureSource tailSource)
      (activationContractum payloadSource tailSource) ∧
    CostStep (decodedActivationSource nilChannelLocation payload.val signature.val tail.val).components
      nilChannelLocation signature.val (locatedContact nilChannelLocation payload.val tail.val).components ∧
    StructuralCongruence (eraseGenerated (activationContractum payloadSource tailSource))
      ((locatedContact nilChannelLocation payload.val tail.val).erase encoding) := by
  refine ⟨⟨sourceTyped, nilChannelLocation_free, nilChannelLocation_supported, fuel + 7,
      activation_source_decodes fuel payloadSource signatureSource tailSource
        payload signature tail payloadParsed signatureParsed tailParsed⟩,
    actual_activation_step nilChannelSource payloadSource signatureSource tailSource,
    decoded_activation_step nilChannelLocation payload.val signature.val tail.val signature.positive, ?_⟩
  exact activation_contractum_observer_congruence payloadSource payload.val tailSource encoding
    (payload.property.2.2.2 encoding)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
