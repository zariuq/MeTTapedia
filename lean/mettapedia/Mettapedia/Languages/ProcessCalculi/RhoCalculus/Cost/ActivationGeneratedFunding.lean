import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

/-!
# Source admission for isolated generated whole funding

The admission reads a generated pattern, checks its authored wrapped sort,
and then compares exact decoded channel locations and the literal purse head.
A successful result enables an actual positive CostStep. This is source
enablement; general target-substitution adequacy is a separate comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def wholeFundedAt (location : CostName LiteralAuthority) : CostTerm LiteralAuthority → Bool
  | .par (.signed (.par (.recv recvLocation _body) (.send sendLocation _payload)) signature)
      (.purse purseLocation (.cons head _tail)) =>
      decide (recvLocation = location ∧ sendLocation = location ∧
        purseLocation = location ∧ head = signature)
  | .par (.signed (.par (.send sendLocation _payload) (.recv recvLocation _body)) signature)
      (.purse purseLocation (.cons head _tail)) =>
      decide (recvLocation = location ∧ sendLocation = location ∧
        purseLocation = location ∧ head = signature)
  | _ => false

theorem wholeFundedAt_enables (location : CostName LiteralAuthority)
    (term : CostTerm LiteralAuthority) (supported : term.RuntimeSupported)
    (matching : wholeFundedAt location term = true) :
    ∃ spend target, CostStep term.components location spend target := by
  unfold wholeFundedAt at matching
  split at matching
  · rename_i _source recvLocation body sendLocation payload signature purseLocation head tail
    have same := of_decide_eq_true matching
    obtain ⟨recvEq, sendEq, purseEq, headEq⟩ := same
    simp only [recvEq, sendEq, purseEq, headEq] at supported ⊢
    have positive : signature.RuntimeValid := supported.1.2
    exact ⟨signature, _, by
      simpa [CostTerm.components, LocatedPurse.configComponents, LocatedPurse.toTerm] using
        CostStep.wholeRecvSend (context := 0) (body := body) (payload := payload) positive
          (LocatedTokenCover.singleHead location signature positive tail)⟩
  · rename_i _source sendLocation payload recvLocation body signature purseLocation head tail
    have same := of_decide_eq_true matching
    obtain ⟨recvEq, sendEq, purseEq, headEq⟩ := same
    simp only [recvEq, sendEq, purseEq, headEq] at supported ⊢
    have positive : signature.RuntimeValid := supported.1.2
    exact ⟨signature, _, by
      simpa [CostTerm.components, LocatedPurse.configComponents, LocatedPurse.toTerm] using
        CostStep.wholeSendRecv (context := 0) (body := body) (payload := payload) positive
          (LocatedTokenCover.singleHead location signature positive tail)⟩
  · contradiction

/-- A real syntax decoder with exact isolated authority checks. -/
def fundedPair? (location : CostName LiteralAuthority)
    (locationFree : location.purseInventory = 0) (locationSupported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) : Option (DecodedConfig source) := do
  let decoded ← config? location locationFree locationSupported fuel source
  if checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] source
      (.base costWrappedSortName) && wholeFundedAt location decoded.val then
    some decoded
  else none

theorem fundedPair_sound (location : CostName LiteralAuthority)
    (locationFree : location.purseInventory = 0) (locationSupported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) (decoded : DecodedConfig source)
    (accepted : fundedPair? location locationFree locationSupported fuel source = some decoded) :
    GeneratedConfigImage location source decoded.val ∧
      ∃ spend target, CostStep decoded.val.components location spend target ∧
        target.ResourceSeparated := by
  cases parsed : config? location locationFree locationSupported fuel source with
  | none => simp [fundedPair?, parsed] at accepted
  | some actual =>
    unfold fundedPair? at accepted
    rw [parsed] at accepted
    change (if (checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] source
        (.base costWrappedSortName) && wholeFundedAt location actual.val) = true
      then some actual else none) = some decoded at accepted
    split at accepted
    · rename_i checks
      have equal : actual = decoded := Option.some.inj accepted
      subst decoded
      obtain ⟨typed, matching⟩ := Bool.and_eq_true_iff.mp checks
      have image : GeneratedConfigImage location source actual.val :=
        ⟨checkHasType_sound typed, locationFree, locationSupported, fuel,
          by simp only [parsed, Option.map_some]⟩
      obtain ⟨spend, target, step⟩ :=
        wholeFundedAt_enables location actual.val actual.property.2.2.1 matching
      exact ⟨image, spend, target, step,
        step.preserves_resourceSeparated actual.property.1⟩
    · contradiction

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
