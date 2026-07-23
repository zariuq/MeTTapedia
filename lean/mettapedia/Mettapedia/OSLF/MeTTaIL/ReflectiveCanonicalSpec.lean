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

/-- Independent relational meaning of `matchPatternForRule`. -/
def MatchForRuleRel
    (lang : LanguageDef) (rule : RewriteRule) (term : Pattern)
    (bindings : Bindings) : Prop :=
  match matchingPresentationForRule? lang rule with
  | some declaration =>
      MatchRelWith (canonicalEquivalent declaration) rule.left term bindings
  | none => MatchRel rule.left term bindings

theorem matchPatternForRule_iff_matchForRuleRel
    {lang : LanguageDef} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings} :
    bindings ∈ matchPatternForRule lang rule term ↔
      MatchForRuleRel lang rule term bindings := by
  cases selected : matchingPresentationForRule? lang rule with
  | none =>
      simp only [matchPatternForRule, MatchForRuleRel, selected]
      exact matchPattern_iff_matchRel
  | some declaration =>
      simp only [matchPatternForRule, MatchForRuleRel, selected]
      exact matchPatternWith_iff_matchRelWith

/-- When no unique reflective declaration is selected, rule-aware matching
has exactly the original structural relational meaning. -/
theorem matchPatternForRule_iff_matchRel_of_no_presentation
    {lang : LanguageDef} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings}
    (missing : matchingPresentationForRule? lang rule = none) :
    bindings ∈ matchPatternForRule lang rule term ↔
      MatchRel rule.left term bindings := by
  rw [matchPatternForRule_iff_matchForRuleRel]
  simp [MatchForRuleRel, missing]

/-- A uniquely selected reflective declaration gives the parameterized
relational matcher compiled from that declaration. -/
theorem matchPatternForRule_iff_matchRelWith_of_presentation
    {lang : LanguageDef} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings} {declaration : ReflectivePresentationDecl}
    (selected : matchingPresentationForRule? lang rule = some declaration) :
    bindings ∈ matchPatternForRule lang rule term ↔
      MatchRelWith (canonicalEquivalent declaration) rule.left term bindings := by
  rw [matchPatternForRule_iff_matchForRuleRel]
  simp [MatchForRuleRel, selected]

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
