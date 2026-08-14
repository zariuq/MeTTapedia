import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportTwoAvailabilitySubstitution

/-!
# Canary for two-regime reflective substitution callbacks

The exposed and sealed callbacks must be inhabited only by occurrences of
their corresponding regime.  Name indexing alone cannot establish that fact
when each embedding is total over every frame occurrence.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open WellSorted

/-- A name-indexed sealed callback is still contradictory for an exposed
free-variable value with nonempty output support if its sealed embedding is
total over all occurrences. -/
theorem nameIndexedSealedCallback_totalEmbedding_impossible
    {language : LanguageDef} {source target : FreeTypeContext}
    {typingSupport outputSupport : ContextSupport.Support}
    {profile : ReflectionProfile}
    (assignment : SupportedAssignment language source target typingSupport)
    {callerBinderImage : TypeExpr → TypeExpr}
    {pattern : Pattern} {RootSealed : String → Type}
    (occurrence : CostStaticFVarOccurrence pattern)
    (embedSealed : (point : CostStaticFVarOccurrence pattern) →
      RootSealed point.name)
    (valueSafeSealed : ∀ {name type}
      (lookup : source name = some type), RootSealed name →
      (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
        [] callerBinderImage)
    {u : String} {type : TypeExpr}
    (lookup : source occurrence.name = some type)
    (valueShape : assignment.assignment occurrence.name = .fvar u)
    (supportNonempty : outputSupport u ≠ []) :
    False := by
  have safe := valueSafeSealed lookup (embedSealed occurrence)
  have packaged : ∃ fvarTyped : HasType language target
      (typingSupport occurrence.name) (Pattern.fvar u) type,
      fvarTyped.ReflectiveSupportSafeAt profile outputSupport []
        callerBinderImage :=
    valueShape ▸ ⟨assignment.typed lookup, safe⟩
  obtain ⟨fvarTyped, fvarSafe⟩ := packaged
  cases fvarSafe with
  | fvar _ _ shape =>
      obtain ⟨inner, innerEquality⟩ := shape
      exact supportNonempty
        (List.append_eq_nil_iff.mp innerEquality.symm).2

/-- Empty output support is the benign boundary of the negative canary: an
assigned free variable is reflectively safe at the sealed availability. -/
theorem fvar_safeAt_sealed_of_emptySupport
    {language : LanguageDef} {target : FreeTypeContext}
    {typingSupport : ContextSupport.Support}
    {profile : ReflectionProfile} {callerBinderImage : TypeExpr → TypeExpr}
    {u : String} {type : TypeExpr}
    {typed : HasType language target (typingSupport u) (.fvar u) type}
    (lookup : target u = some type) :
    typed.ReflectiveSupportSafeAt profile (fun _ => []) [] callerBinderImage := by
  exact .fvar lookup [] ⟨[], by simp⟩

end Mettapedia.GSLT.LanguageDef
