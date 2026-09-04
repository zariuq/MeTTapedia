import Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory

/-!
# Falsification controls for structural presentation coproducts

These finite examples show that the hypotheses used by the exact operational
coproduct theorem are load-bearing.  A bare metavariable rewrite crosses a
perfectly disjoint symbol boundary, and a constructor-rooted rewrite crosses
when the constructor images collide.  Rooted rules over disjoint constructor
images remain silent on the other component.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralCoproductCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct

private def prefixedSymbols (tag : String) : LanguageDefSymbolMap where
  sort := fun name => tag ++ "sort:" ++ name
  constructor := fun name => tag ++ "constructor:" ++ name
  relation := fun name => tag ++ "relation:" ++ name
  equation := fun name => tag ++ "equation:" ++ name
  rewrite := fun name => tag ++ "rewrite:" ++ name

private def unrootedRule : RewriteRule where
  name := "unrooted"
  typeContext := []
  premises := []
  left := .fvar "value"
  right := .apply "result" []

/-- Constructor-image disjointness does not stop a bare metavariable rule
from inventing a cross-component transition. -/
theorem unrooted_rule_crosses_disjoint_images :
    applyRule
        (mapRewriteRule (prefixedSymbols "right:") unrootedRule)
        (mapPattern (prefixedSymbols "left:") (.apply "input" [])) =
      [.apply "right:constructor:result" []] := by
  simp [applyRule, mapRewriteRule, mapPattern, prefixedSymbols, unrootedRule,
    matchPattern, applyBindings]

private def rootedRule : RewriteRule where
  name := "rooted"
  typeContext := []
  premises := []
  left := .apply "input" []
  right := .apply "result" []

private def collidingLeftSymbols : LanguageDefSymbolMap :=
  prefixedSymbols "shared:"

private def collidingRightSymbols : LanguageDefSymbolMap :=
  prefixedSymbols "shared:"

/-- Constructor-rootedness alone does not prevent interference when the two
constructor images collide. -/
theorem rooted_rule_crosses_colliding_images :
    applyRule
        (mapRewriteRule collidingRightSymbols rootedRule)
        (mapPattern collidingLeftSymbols (.apply "input" [])) =
      [.apply "shared:constructor:result" []] := by
  simp [applyRule, mapRewriteRule, mapPattern, collidingLeftSymbols,
    collidingRightSymbols, prefixedSymbols, rootedRule, matchPattern,
    matchArgs, applyBindings]

/-- Both hypotheses together exclude the same cross-component rule. -/
theorem rooted_rule_is_silent_on_disjoint_image :
    applyRule
        (mapRewriteRule (prefixedSymbols "right:") rootedRule)
        (mapPattern (prefixedSymbols "left:") (.apply "input" [])) = [] := by
  simp [applyRule, mapRewriteRule, mapPattern, prefixedSymbols, rootedRule,
    matchPattern]

theorem rootedRule_is_constructorRooted : ConstructorRooted rootedRule := by
  exact ⟨"input", [], rfl⟩

#print axioms unrooted_rule_crosses_disjoint_images
#print axioms rooted_rule_crosses_colliding_images
#print axioms rooted_rule_is_silent_on_disjoint_image

end Mettapedia.GSLT.LanguageDef.StructuralCoproductCanary
