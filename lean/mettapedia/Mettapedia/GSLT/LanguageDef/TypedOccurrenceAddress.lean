import Mettapedia.GSLT.LanguageDef.WellSortedOccurrence
import Mettapedia.GSLT.LanguageDef.RestAwareTyping
import Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress

/-!
# Authored types at executable occurrence addresses

The executable address decoder yields the existing one-hole context for an
ordinary schema variable. A typing derivation then descends along that exact
context. The resulting binder prefix has exactly the depth counted by the
runtime address reader; no first-occurrence depth is inferred or guessed.
Collection-rest slots require a separate typed address construction.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress

set_option autoImplicit false

/-- Typed zipper descent adds precisely one type per crossed binder, counting
the body of an explicit substitution and every multi-binder component. -/
theorem TypedAt.focusBound_length
    {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {context : OneHoleContext}
    {bound focusBound : List TypeExpr} {type result : TypeExpr}
    (selected : TypedAt language free focus context bound type
      focusBound result) :
    focusBound.length = binderCount context + bound.length := by
  induction selected with
  | here _ => simp [binderCount]
  | application _ _ _ _ _ _ _ inductionHypothesis =>
      simpa [binderCount] using inductionHypothesis
  | lambda _ inductionHypothesis =>
      simpa [binderCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using inductionHypothesis
  | multiLambda _ inductionHypothesis =>
      simpa [binderCount, List.length_append, List.length_replicate,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using inductionHypothesis
  | substBody _ _ inductionHypothesis =>
      simpa [binderCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using inductionHypothesis
  | substReplacement _ _ inductionHypothesis =>
      simpa [binderCount] using inductionHypothesis
  | collection _ _ inductionHypothesis =>
      simpa [binderCount] using inductionHypothesis
  | collectionConstructor _ _ _ _ inductionHypothesis =>
      simpa [binderCount] using inductionHypothesis

/-- An actual decoded fvar address in a typed authored pattern has the
authored fvar sort and a binder prefix whose length matches the executable
depth count. The prefix types are retained as data for checking supplied
dependency arguments. -/
theorem HasType.typedAtAddress
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    {path : List Nat} {name : String} {context : OneHoleContext}
    (decoded : termZipperAt? pattern path = some (name, context)) :
    ∃ focusBound result binderPrefix,
      TypedAt language free (.fvar name) context bound type
        focusBound result ∧
      free name = some result ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = binderCount context ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        pattern path 0 = some binderPrefix.length := by
  obtain ⟨focusBound, result, selected, lookup⟩ :=
    typed.selected_fvar (termZipperAt?_selects decoded)
  obtain ⟨binderPrefix, prefixEq⟩ := selected.ambient_suffix
  have prefixLength : binderPrefix.length = binderCount context := by
    have lengthEq := selected.focusBound_length
    rw [prefixEq, List.length_append] at lengthEq
    omega
  refine ⟨focusBound, result, binderPrefix, selected, lookup,
    prefixEq, prefixLength, ?_⟩
  simpa [prefixLength] using termZipperAt?_depth decoded 0

/-- A computed name-and-depth summary can be refined to the full authored
typed zipper and binder-sort list. This is the bridge for concrete rule rows
whose executable address data is checked by computation. -/
theorem HasType.typedAtAddress_of_summary
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    {path : List Nat} {name : String} {depth : Nat}
    (summary : (termZipperAt? pattern path).map
      (fun entry => (entry.1, binderCount entry.2)) =
        some (name, depth)) :
    ∃ context focusBound result binderPrefix,
      termZipperAt? pattern path = some (name, context) ∧
      TypedAt language free (.fvar name) context bound type
        focusBound result ∧
      free name = some result ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = depth ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        pattern path 0 = some depth := by
  cases decoded : termZipperAt? pattern path with
  | none => simp [decoded] at summary
  | some entry =>
      rcases entry with ⟨actualName, context⟩
      simp only [decoded, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at summary
      obtain ⟨nameEq, depthEq⟩ := summary
      subst actualName
      obtain ⟨focusBound, result, binderPrefix, selected, lookup,
          prefixEq, prefixLength, runtimeDepth⟩ :=
        typed.typedAtAddress decoded
      have preciseLength : binderPrefix.length = depth :=
        prefixLength.trans depthEq
      refine ⟨context, focusBound, result, binderPrefix, rfl,
        selected, lookup, prefixEq, preciseLength, ?_⟩
      simpa [preciseLength] using runtimeDepth

end Mettapedia.GSLT.LanguageDef.WellSorted

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress

set_option autoImplicit false

/-- A rest-aware schema derivation supplies the same typed ordinary term
occurrences after forgetting only its extra rest premises. -/
theorem HasType.typedAtAddress
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    {path : List Nat} {name : String} {context : OneHoleContext}
    (decoded : termZipperAt? pattern path = some (name, context)) :
    ∃ focusBound result binderPrefix,
      TypedAt language free (.fvar name) context bound type
        focusBound result ∧
      free name = some result ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = binderCount context ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        pattern path 0 = some binderPrefix.length :=
  typed.forget.typedAtAddress decoded

theorem HasType.typedAtAddress_of_summary
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    {path : List Nat} {name : String} {depth : Nat}
    (summary : (termZipperAt? pattern path).map
      (fun entry => (entry.1, binderCount entry.2)) =
        some (name, depth)) :
    ∃ context focusBound result binderPrefix,
      termZipperAt? pattern path = some (name, context) ∧
      TypedAt language free (.fvar name) context bound type
        focusBound result ∧
      free name = some result ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = depth ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        pattern path 0 = some depth :=
  typed.forget.typedAtAddress_of_summary summary

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
