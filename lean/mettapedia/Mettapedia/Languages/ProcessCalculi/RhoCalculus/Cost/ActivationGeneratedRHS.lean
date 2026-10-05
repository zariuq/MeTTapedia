import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReceiver

/-!
# The receiver that returns what it receives

The receiver `PDrop [bvar 0]` as an instance of the general receiver of
`ActivationGeneratedReceiver`. What is particular to it is one computation: the generated
substitution into this body is the normalization of the payload (`receiverContractum_drop`), and
the communication result of its runtime term is the payload (`CostTerm.drop_bvar_commSubst`).
Apparatus erasure compares the contractum with the funded endpoint for every admitted payload.
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

theorem actual_activation_match (channel payload signature tail : Pattern) :
    activationBindings channel payload signature tail ∈
      matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile
        rhoCIGSLT.costWholeRedexRewrite (activationSource channel payload signature tail) :=
  actual_receiver_match channel (.apply (costWrappedConstructorName "PDrop") [.bvar 0]) payload signature tail

def activationContractum (payload tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.collection .hashBag [normalizeReflective wrappedRhoDeclaration payload] none,
     .apply costFundingConstructorName [tail]]

/-- The generated substitution into the body `PDrop [bvar 0]` is the normalization of the
payload. -/
theorem receiverContractum_drop (payload tail : Pattern) :
    receiverContractum (.apply (costWrappedConstructorName "PDrop") [.bvar 0]) payload tail =
      activationContractum payload tail := by
  have quoteName : wrappedRhoDeclaration.quoteConstructor =
      "$cost:wrapped-constructor:NQuote" := rfl
  have dropName : wrappedRhoDeclaration.dropConstructor =
      costWrappedConstructorName "PDrop" := rfl
  simp [receiverContractum, activationContractum, substituteReflective, generatedReplacement,
    substituteNameMark, normalizeReflective, quoteName, dropName, costWrappedConstructorName,
    costWrappedConstructorTag]

theorem actual_activation_rhs (channel payload signature tail : Pattern) :
    applyBindingsForRuleUsing rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeRedexRewrite (activationBindings channel payload signature tail)
      = activationContractum payload tail :=
  (actual_receiver_rhs channel _ payload signature tail).trans (receiverContractum_drop payload tail)

theorem actual_activation_step (channel payload signature tail : Pattern) :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage (activationSource channel payload signature tail)
      (activationContractum payload tail) :=
  receiverContractum_drop payload tail ▸ actual_receiver_step channel _ payload signature tail

def decodedActivationSource (location : CostName LiteralAuthority)
    (payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority)
    (tail : CostStack LiteralAuthority) : CostTerm LiteralAuthority :=
  locatedContact location
    (.signed (.par (.recv location (.drop (.bvar 0))) (.send location payload)) signature)
    (.cons signature tail)

/-- The body `PDrop [bvar 0]` is read at depth one with any fuel above one. -/
theorem drop_body_decodes (fuel : Nat) :
    ∃ body : DecodedCode 1 (.apply (costWrappedConstructorName "PDrop") [.bvar 0]),
      code? (fuel + 2) 1 (.apply (costWrappedConstructorName "PDrop") [.bvar 0]) = some body ∧
        body.val = .drop (.bvar 0) :=
  Option.map_eq_some_iff.mp ((code?_val _ _ _).trans rfl)

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
  obtain ⟨body, bodyParsed, bodyValue⟩ := drop_body_decodes fuel
  have decodes := receiver_source_decodes fuel _ payloadSource signatureSource tailSource body payload
    signature tail bodyParsed payloadParsed signatureParsed tailParsed
  rw [bodyValue] at decodes
  exact decodes

theorem CostTerm.drop_bvar_commSubst (payload : CostTerm LiteralAuthority) :
    (CostTerm.drop (.bvar 0)).commSubst payload = payload := by
  simp [CostTerm.commSubst, CostTerm.substitute, CostTerm.lift_zero]

theorem decoded_activation_step (location : CostName LiteralAuthority)
    (payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority)
    (tail : CostStack LiteralAuthority) (positive : signature.RuntimeValid) :
    CostStep (decodedActivationSource location payload signature tail).components
      location signature (locatedContact location payload tail).components := by
  have fired := decoded_receiver_step location (.drop (.bvar 0)) payload signature tail positive
  rw [CostTerm.drop_bvar_commSubst] at fired
  exact fired

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

/-- `receiver_firing_comparison` for the receiver that returns what it receives. The targets are
compared by the pure structural observer; literal equality of their readouts is not asserted. -/
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
  obtain ⟨body, bodyParsed, bodyValue⟩ := drop_body_decodes fuel
  have comparison := receiver_firing_comparison fuel _ payloadSource signatureSource tailSource body
    payload signature tail bodyParsed payloadParsed signatureParsed tailParsed sourceTyped encoding
  rw [bodyValue, CostTerm.drop_bvar_commSubst, receiverContractum_drop] at comparison
  exact comparison

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
