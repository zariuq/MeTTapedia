import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReceiver
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalizationControls

/-!
# Nested receiver and admission controls

The receiver retains an inner binder while substituting the outer channel.
The communicated payload has a genuine quote/drop normalization change.
An additional copying control exercises collection readout and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReceiverControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open ActivationGeneratedControls

def nestedBody : Pattern := .apply costSignedConstructorName
  [.apply (costBaseConstructorName "PInput") [nilChannelSource, .lambda none
    (.apply costSignedConstructorName
      [.apply (costBaseConstructorName "POutput") [.bvar 1, dropZero], unitSignature])],
   unitSignature]

def interpretedNested : CostTerm LiteralAuthority :=
  .signed (.recv nilChannelLocation
    (.signed (.send (.bvar 1) (.drop (.bvar 0))) {unitSignature})) {unitSignature}

def nestedSource : Pattern := receiverSource nilChannelSource nestedBody
  ActivationGeneratedNormalizationControls.literalPayload unitSignature emptyStack

def openedNested : CostTerm LiteralAuthority :=
  .signed (.recv nilChannelLocation
    (.signed (.send (.quote ActivationGeneratedNormalizationControls.interpretedLiteral)
      (.drop (.bvar 0))) {unitSignature})) {unitSignature}

theorem nested_body_image : GeneratedCodeImage 1 nestedBody interpretedNested :=
  ⟨checkHasType_sound (by decide +kernel), 16, by decide +kernel⟩

theorem nested_source_typed : HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
    nestedSource (.base costWrappedSortName) := checkHasType_sound (by decide +kernel)

theorem nested_binder_substitution_is_exact :
    interpretedNested.commSubst ActivationGeneratedNormalizationControls.interpretedLiteral =
      openedNested := by
  decide +kernel

theorem nested_actual_authored_firing :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage nestedSource
      (receiverContractum nestedBody ActivationGeneratedNormalizationControls.literalPayload emptyStack) :=
  actual_receiver_step nilChannelSource nestedBody
    ActivationGeneratedNormalizationControls.literalPayload unitSignature emptyStack

theorem nested_actual_source_decodes :
    (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported 24 nestedSource).map
      Subtype.val = some (decodedReceiverSource nilChannelLocation interpretedNested
        ActivationGeneratedNormalizationControls.interpretedLiteral {unitSignature} .empty) := by
  decide +kernel

theorem nested_actual_funded_firing :
    CostStep (decodedReceiverSource nilChannelLocation interpretedNested
      ActivationGeneratedNormalizationControls.interpretedLiteral {unitSignature} .empty).components
      nilChannelLocation {unitSignature} (locatedContact nilChannelLocation openedNested .empty).components := by
  rw [←nested_binder_substitution_is_exact]
  exact decoded_receiver_step nilChannelLocation interpretedNested
    ActivationGeneratedNormalizationControls.interpretedLiteral {unitSignature} .empty
    (Multiset.singleton_ne_zero _)

theorem nested_rhs_observer_comparison (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence
      (eraseGenerated (receiverContractum nestedBody
        ActivationGeneratedNormalizationControls.literalPayload emptyStack))
      ((locatedContact nilChannelLocation openedNested .empty).erase encoding) := by
  rw [←nested_binder_substitution_is_exact]
  exact receiver_contractum_erasure nested_body_image.structural_image
    ActivationGeneratedNormalizationControls.literal_payload_image.structural_image
    ActivationGeneratedNormalizationControls.literal_payload_image.binderSafe
    emptyStack nilChannelLocation .empty encoding

theorem copying_body_image : GeneratedCodeImage 1 copyBody interpretedBody :=
  ⟨checkHasType_sound (by decide +kernel), 14, by decide +kernel⟩

theorem nonempty_payload_image : GeneratedCodeImage 0 inner interpretedInner :=
  ⟨checkHasType_sound (by decide +kernel), 14, by decide +kernel⟩

theorem copying_rhs_observer_comparison (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (eraseGenerated (receiverContractum copyBody inner emptyStack))
      (interpretedTarget.erase encoding) := by
  have opened : interpretedBody.commSubst interpretedInner =
      .par interpretedInner (.par interpretedInner .nil) := by decide +kernel
  simpa only [interpretedTarget, location, nilChannelLocation, opened] using
    receiver_contractum_erasure copying_body_image.structural_image
      nonempty_payload_image.structural_image nonempty_payload_image.binderSafe
      emptyStack nilChannelLocation .empty encoding

theorem dangling_outer_name_rejected :
    (code? 14 1 (.apply (costWrappedConstructorName "PDrop") [.bvar 1])).isNone = true := by
  decide +kernel

theorem named_receiver_binder_rejected :
    (code? 14 1 (.apply costSignedConstructorName
      [.apply (costBaseConstructorName "PInput") [nilChannelSource, .lambda (some "x") dropZero],
       unitSignature])).isNone = true := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReceiverControls
