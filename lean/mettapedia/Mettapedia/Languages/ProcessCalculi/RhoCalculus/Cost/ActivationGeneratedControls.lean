import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationVerticalBraid
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientBorrow

/-!
# Nontrivial generated-code interpretation controls

The declared asynchronous rule duplicates a sealed nonempty COMM payload.
The source and actual declared reduct are decoded independently, and the
existing CostStep relates their decoded configurations. Exact signature and
location controls delimit the interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveEngine

def unitSignature : Pattern := .apply costSignatureUnitConstructorName []
def productSignature : Pattern := .apply costSignatureProductConstructorName [unitSignature, unitSignature]
def emptyStack : Pattern := .apply costTokenStackEmptyConstructorName []
def channel : Pattern := .apply (costBaseConstructorName "NQuote") [.apply (costBaseConstructorName "PZero") []]
def zero : Pattern := .apply (costWrappedConstructorName "PZero") []
def dropZero : Pattern := .apply (costWrappedConstructorName "PDrop") [.bvar 0]
def copyBody : Pattern := .collection .hashBag [dropZero, dropZero] none

def core (body sent : Pattern) : Pattern := .collection .hashBag
  [.apply (costBaseConstructorName "PInput") [channel, .lambda none body],
   .apply (costBaseConstructorName "POutput") [channel, sent]] none

def inner : Pattern := .apply costSignedConstructorName [core zero zero, unitSignature]

def source : Pattern := .apply costContactConstructorName
  [.apply costSignedConstructorName [core copyBody inner, unitSignature],
   .apply costFundingConstructorName
     [.apply costTokenStackConsConstructorName [unitSignature, emptyStack]]]

def target : Pattern := .apply costContactConstructorName
  [.collection .hashBag [.collection .hashBag [inner, inner] none] none,
   .apply costFundingConstructorName [emptyStack]]

def location : CostName LiteralAuthority := .quote .nil
theorem location_free : location.purseInventory = 0 := rfl
theorem location_supported : location.RuntimeSupported := trivial

def interpretedInner : CostTerm LiteralAuthority :=
  .signed (.par (.recv location .nil) (.send location .nil)) {unitSignature}
def interpretedBody : CostTerm LiteralAuthority :=
  .par (.drop (.bvar 0)) (.par (.drop (.bvar 0)) .nil)
def interpretedSource : CostTerm LiteralAuthority :=
  locatedContact location
    (.signed (.par (.recv location interpretedBody) (.send location interpretedInner)) {unitSignature})
    (.cons {unitSignature} .empty)
def interpretedTarget : CostTerm LiteralAuthority :=
  locatedContact location (.par interpretedInner (.par interpretedInner .nil)) .empty

theorem source_typed : HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
    source (.base costWrappedSortName) := checkHasType_sound (by decide +kernel)

theorem target_typed : HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
    target (.base costWrappedSortName) := checkHasType_sound (by decide +kernel)

/-- This is the actual declared reduction, including reflective COMM substitution. -/
theorem actual_generated_copying :
    rewriteAt (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage 1 source = [target] := by
  decide +kernel

/-- The decoder reads the independently authored source and target configurations. -/
theorem actual_generated_endpoints_decoded :
    (config? location location_free location_supported 16 source).map
      (fun decoded => decoded.val.components) = some interpretedSource.components ∧
    (config? location location_free location_supported 16 target).map
      (fun decoded => decoded.val.components) = some interpretedTarget.components := by
  decide +kernel

theorem actual_decoded_copying :
    CostStep interpretedSource.components location {unitSignature} interpretedTarget.components := by
  have positive : ({unitSignature} : CostSig LiteralAuthority).RuntimeValid :=
    Multiset.singleton_ne_zero _
  have actual := CostStep.wholeRecvSend (context := 0)
    (body := interpretedBody) (payload := interpretedInner) positive
    (LocatedTokenCover.singleHead location {unitSignature} positive .empty)
  simpa [interpretedSource, interpretedTarget, locatedContact, interpretedBody,
    CostTerm.commSubst, CostTerm.substitute, CostTerm.components,
    LocatedPurse.configComponents, LocatedPurse.toTerm, add_assoc] using actual

/-- Literal unit syntax is positive; its product is a different exact authority. -/
theorem opaque_signature_controls :
    (signature? unitSignature).map Subtype.val = some {unitSignature} ∧
    (signature? productSignature).map Subtype.val = some {productSignature} ∧
    ({unitSignature} : CostSig LiteralAuthority) ≠ {productSignature} ∧
    ({unitSignature} : CostSig LiteralAuthority).RuntimeValid := by
  refine ⟨?_, ?_, ?_, Multiset.singleton_ne_zero _⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Funding and unsealed output syntax are rejected as communicated code;
the source core also rejects an unresolved or nonempty internal remainder. -/
theorem decoder_domain_controls :
    (code? 8 0 (.apply costFundingConstructorName [emptyStack])).isSome = false ∧
    (code? 8 0 (.apply (costWrappedConstructorName "POutput") [channel, zero])).isSome = false ∧
    (proc? 8 0 (.collection .hashBag
      [.apply (costBaseConstructorName "PInput") [channel, .lambda none zero],
       .apply (costBaseConstructorName "POutput") [channel, zero],
       .apply (costBaseConstructorName "PZero") []] none)).isSome = false ∧
    (proc? 8 0 (.collection .hashBag
      [.apply (costBaseConstructorName "PInput") [channel, .lambda none zero],
       .apply (costBaseConstructorName "POutput") [channel, zero]] (some "rest"))).isSome = false ∧
    (name? 8 0 (.apply (costWrappedConstructorName "NQuote") [dropZero])).isSome = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedControls

