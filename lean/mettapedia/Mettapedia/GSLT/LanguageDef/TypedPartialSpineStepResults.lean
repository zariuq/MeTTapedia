import Mettapedia.GSLT.LanguageDef.TypedPartialSpineRecovery
import Mettapedia.GSLT.LanguageDef.TypedFullSpineStepResults

/-!
# Typed binder-local step results on partial occurrence spines

A selected event from an ordered scoped step premise carries its ordinal and
evidence. When its target is a contextual metavariable on a sort-compatible
partial variable spine, the actual matcher either rejects a dependency on an
omitted binder or stores a value of the declared sort. No separate support
assumption is needed: successful recovery supplies it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

/-- A selected binder-local event with a partial occurrence spine preserves
the type and exact contexts of every stored assignment. The step oracle's
result-typing obligation is explicit and the event ordinal is retained. -/
theorem stepResults_fvar_partialSpine_preserves_types {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies locals : List TypeExpr) (index : Nat)
    (source : Pattern) (name : String) (resultType : TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (oracle : StepOracle Evidence)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (event : PremiseEvent Evidence) (instantiated : Pattern)
    (before : AssignmentHasTypes language free spec ambient initial)
    (declared : dependencies? spec name = some dependencies)
    (atSite : arguments? rule spec name (.premise index 0 1) [] =
      some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : PartialSortedSpine dependencies locals indices)
    (namedType : free name = some resultType)
    (sourceResult : instantiateAt? rule spec ambient.length
      (.premise index 0 0) [] locals.length initial source =
        some instantiated)
    (outputs : ∀ evidence candidate,
      (evidence, candidate) ∈ oracle (locals.length + ambient.length)
        instantiated →
      HasType language free (locals ++ ambient) candidate resultType)
    (selected : (event, final) ∈ stepResults oracle rule spec
      ambient.length index locals.length source (.fvar name) initial) :
    AssignmentHasTypes language free spec ambient final := by
  simp only [stepResults, sourceResult] at selected
  by_cases sourceScoped : instantiated.isWellScopedAt
      (locals.length + ambient.length) = true
  · simp only [sourceScoped, if_true, List.mem_flatMap] at selected
    obtain ⟨⟨⟨evidence, candidate⟩, ordinal⟩, oracleMember,
      resultMember⟩ := selected
    have candidateTyped := outputs evidence candidate
      (List.fst_mem_of_mem_zipIdx oracleMember)
    by_cases candidateScoped : candidate.isWellScopedAt
        (locals.length + ambient.length) = true
    · simp only [candidateScoped, if_true, List.mem_map] at resultMember
      obtain ⟨completed, matchMember, resultEq⟩ := resultMember
      have finalEq : completed = final := (Prod.mk.inj resultEq).2
      subst final
      have captureResult : capture? rule spec ambient.length
          locals.length (.premise index 0 1) [] initial name candidate =
          some completed := by
        simpa only [matchAt_fvar, Option.mem_toList] using matchMember
      exact capture?_partialSortedSpine_preserves_types_from_success
        language free rule spec ambient dependencies locals
        (.premise index 0 1) [] initial completed name candidate
        resultType arguments indices before declared atSite spineCheck spine
        namedType candidateTyped captureResult
    · simp [candidateScoped] at resultMember
  · simp [sourceScoped] at selected

/-- Selection itself supplies successful source instantiation. Oracle outputs
must be typed for whichever source the current assignment instantiates. -/
theorem stepResults_fvar_partialSpine_preserves_types_of_selected
    {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies locals : List TypeExpr) (index : Nat)
    (source : Pattern) (name : String) (resultType : TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (oracle : StepOracle Evidence)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (event : PremiseEvent Evidence)
    (before : AssignmentHasTypes language free spec ambient initial)
    (declared : dependencies? spec name = some dependencies)
    (atSite : arguments? rule spec name (.premise index 0 1) [] =
      some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : PartialSortedSpine dependencies locals indices)
    (namedType : free name = some resultType)
    (outputs : ∀ instantiated evidence candidate,
      (evidence, candidate) ∈ oracle (locals.length + ambient.length)
        instantiated →
      HasType language free (locals ++ ambient) candidate resultType)
    (selected : (event, final) ∈ stepResults oracle rule spec
      ambient.length index locals.length source (.fvar name) initial) :
    AssignmentHasTypes language free spec ambient final := by
  cases sourceResult : instantiateAt? rule spec ambient.length
      (.premise index 0 0) [] locals.length initial source with
  | none => simp [stepResults, sourceResult] at selected
  | some instantiated =>
      exact stepResults_fvar_partialSpine_preserves_types
        language free rule spec ambient dependencies locals index source
        name resultType arguments indices oracle initial final event
        instantiated before declared atSite spineCheck spine namedType
        sourceResult (outputs instantiated) selected

#print axioms stepResults_fvar_partialSpine_preserves_types
#print axioms stepResults_fvar_partialSpine_preserves_types_of_selected

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
