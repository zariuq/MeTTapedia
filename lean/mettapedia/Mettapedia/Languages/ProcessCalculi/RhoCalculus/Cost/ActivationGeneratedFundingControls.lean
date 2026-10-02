import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedFunding
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedControls

/-!
# Exact isolated funding admission controls

These controls separate accepted generated syntax from exact operational
authority: a well-typed purse head can still fail to fund a different literal
signature, and a stack-only funding interpretation retains its chosen location.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedFundingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated ActivationGeneratedControls

def wrongHead : Pattern := .apply costContactConstructorName
  [.apply costSignedConstructorName [core copyBody inner, unitSignature],
   .apply costFundingConstructorName
     [.apply costTokenStackConsConstructorName [productSignature, emptyStack]]]

def emptyFunding : Pattern := .apply costContactConstructorName
  [.apply costSignedConstructorName [core copyBody inner, unitSignature],
   .apply costFundingConstructorName [emptyStack]]

def otherLocation : CostName LiteralAuthority := .quote (.signed .nil {unitSignature})
theorem otherLocation_free : otherLocation.purseInventory = 0 := rfl
theorem otherLocation_supported : otherLocation.RuntimeSupported := by
  exact ⟨trivial, Multiset.singleton_ne_zero _⟩

theorem admitted_source_decodes :
    (fundedPair? location location_free location_supported 16 source).map Subtype.val =
      some interpretedSource := by
  decide +kernel

theorem admitted_source_has_actual_step :
    GeneratedConfigImage location source interpretedSource ∧
      ∃ spend target, CostStep interpretedSource.components location spend target ∧
        target.ResourceSeparated := by
  obtain ⟨decoded, accepted, same⟩ := Option.map_eq_some_iff.mp admitted_source_decodes
  have result := fundedPair_sound location location_free location_supported 16 source decoded accepted
  simpa only [same] using result

theorem well_typed_wrong_head_is_decodable :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] wrongHead
      (.base costWrappedSortName) ∧
    (config? location location_free location_supported 16 wrongHead).isSome = true := by
  exact ⟨checkHasType_sound (by decide +kernel), by decide +kernel⟩

theorem exact_funding_rejections :
    (fundedPair? location location_free location_supported 16 wrongHead).isSome = false ∧
    (fundedPair? location location_free location_supported 16 emptyFunding).isSome = false ∧
    (fundedPair? otherLocation otherLocation_free otherLocation_supported 16 source).isSome = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedFundingControls
