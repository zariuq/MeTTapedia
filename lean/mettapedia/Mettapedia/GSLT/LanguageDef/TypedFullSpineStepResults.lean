import Mettapedia.GSLT.LanguageDef.TypedFullSpineRecovery

/-!
# Typed binder-local step results

For a scoped step whose target is a metavariable applied to its complete
local-binder spine, every selected executable premise event preserves the
typed assignment invariant. The oracle must supply typed outputs at the
declared result sort. Event ordinals remain part of the selected result;
this theorem neither collapses nor invents them.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

set_option autoImplicit false

/-- A selected binder-local event with a full-spine metavariable target
retains the sorts and two-part contexts of every stored assignment value.
The source instantiation and oracle-output typing contracts are explicit. -/
theorem stepResults_fvar_fullSpine_preserves_types {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies : List TypeExpr) (index : Nat)
    (source : Pattern) (name : String) (resultType : TypeExpr)
    (oracle : StepOracle Evidence)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (event : PremiseEvent Evidence) (instantiated : Pattern)
    (before : AssignmentHasTypes language free spec ambient initial)
    (declared : dependencies? spec name = some dependencies)
    (arguments : arguments? rule spec name (.premise index 0 1) [] =
      some (fullSpine dependencies.length))
    (namedType : free name = some resultType)
    (sourceResult : instantiateAt? rule spec ambient.length
      (.premise index 0 0) [] dependencies.length initial source =
        some instantiated)
    (outputs : ∀ evidence candidate,
      (evidence, candidate) ∈ oracle (dependencies.length + ambient.length)
        instantiated →
      HasType language free (dependencies ++ ambient) candidate resultType)
    (selected : (event, final) ∈ stepResults oracle rule spec
      ambient.length index dependencies.length source (.fvar name) initial) :
    AssignmentHasTypes language free spec ambient final := by
  simp only [stepResults, sourceResult] at selected
  by_cases hsource : instantiated.isWellScopedAt
      (dependencies.length + ambient.length) = true
  · simp only [hsource, if_true, List.mem_flatMap] at selected
    obtain ⟨⟨⟨evidence, candidate⟩, ordinal⟩, oracleMember,
      resultMember⟩ := selected
    have candidateTyped := outputs evidence candidate
      (List.fst_mem_of_mem_zipIdx oracleMember)
    by_cases hcandidate : candidate.isWellScopedAt
        (dependencies.length + ambient.length) = true
    · simp only [hcandidate, if_true, List.mem_map] at resultMember
      obtain ⟨completed, matchMember, resultEq⟩ := resultMember
      have finalEq : completed = final := (Prod.mk.inj resultEq).2
      subst final
      have captureResult : capture? rule spec ambient.length
          dependencies.length (.premise index 0 1) [] initial name candidate =
          some completed := by
        simpa only [matchAt, Option.mem_toList] using matchMember
      exact capture?_fullSpine_preserves_types language free rule spec
        ambient dependencies (.premise index 0 1) [] initial completed name
        candidate resultType before declared arguments namedType candidateTyped
        captureResult
    · simp [hcandidate] at resultMember
  · simp [hsource] at selected

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
