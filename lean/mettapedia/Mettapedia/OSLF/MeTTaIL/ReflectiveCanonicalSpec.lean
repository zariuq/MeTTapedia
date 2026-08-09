import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.MatchWithSpec
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Relational specification of rule-aware reflective matching

This module gives the declaration-selected matcher a proof-only relational
meaning.  A selected reflective rule uses the equivalence-parameterized
relation; missing or ambiguous declarations use the established structural
`MatchRel`.  Neither branch is defined by executable-result membership.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Reflection

/-- Independent relational meaning of profile-indexed rule matching. -/
def MatchForRuleRelUsing
    (profile : ReflectionProfile) (rule : RewriteRule) (term : Pattern)
    (bindings : Bindings) : Prop :=
  match matchingPresentationForRule? profile rule with
  | some declaration =>
      MatchRelWith (canonicalEquivalent declaration) rule.left term bindings
  | none => MatchRel rule.left term bindings

/-- The core relation is the reflection-free instance. -/
def MatchForRuleRel
    (_language : LanguageDef) (rule : RewriteRule) (term : Pattern)
    (bindings : Bindings) : Prop :=
  MatchForRuleRelUsing .empty rule term bindings

theorem matchPatternForRuleUsing_iff_matchForRuleRelUsing
    {profile : ReflectionProfile} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings} :
    bindings ∈ matchPatternForRuleUsing profile rule term ↔
      MatchForRuleRelUsing profile rule term bindings := by
  cases selected : matchingPresentationForRule? profile rule with
  | none =>
      simp only [matchPatternForRuleUsing, MatchForRuleRelUsing, selected]
      exact matchPattern_iff_matchRel
  | some declaration =>
      simp only [matchPatternForRuleUsing, MatchForRuleRelUsing, selected]
      exact matchPatternWith_iff_matchRelWith

/-- Core rule matching has exactly the original structural meaning. -/
theorem matchPatternForRule_iff_matchForRuleRel
    {language : LanguageDef} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings} :
    bindings ∈ matchPatternForRule language rule term ↔
      MatchForRuleRel language rule term bindings := by
  exact matchPatternForRuleUsing_iff_matchForRuleRelUsing

/-- When a profile selects no unique reflective declaration, rule-aware
matching has exactly the original structural relational meaning. -/
theorem matchPatternForRuleUsing_iff_matchRel_of_no_presentation
    {profile : ReflectionProfile} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings}
    (missing : matchingPresentationForRule? profile rule = none) :
    bindings ∈ matchPatternForRuleUsing profile rule term ↔
      MatchRel rule.left term bindings := by
  rw [matchPatternForRuleUsing_iff_matchForRuleRelUsing]
  simp [MatchForRuleRelUsing, missing]

/-- A uniquely selected reflective declaration gives the parameterized
relational matcher compiled from that declaration. -/
theorem matchPatternForRuleUsing_iff_matchRelWith_of_presentation
    {profile : ReflectionProfile} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings} {declaration : ReflectivePresentationDecl}
    (selected : matchingPresentationForRule? profile rule = some declaration) :
    bindings ∈ matchPatternForRuleUsing profile rule term ↔
      MatchRelWith (canonicalEquivalent declaration) rule.left term bindings := by
  rw [matchPatternForRuleUsing_iff_matchForRuleRelUsing]
  simp [MatchForRuleRelUsing, selected]

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
