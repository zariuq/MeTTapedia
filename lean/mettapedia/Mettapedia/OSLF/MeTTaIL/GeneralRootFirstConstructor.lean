import Mettapedia.OSLF.MeTTaIL.GeneralRootConstructor

/-! A fixed constructor in a rule's first argument is retained by an
actual root match. These nested head constraints distinguish request and
answer variants without relying on rule order.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch GeneralPremise

theorem matches_constructor_eq {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {initial final : Assignment}
    {schemaLabel sourceLabel : String} {schemas inputs : List Pattern}
    (matched : Matches rule spec ambient site path depth initial (.apply schemaLabel schemas) (.apply sourceLabel inputs) final) :
    schemaLabel = sourceLabel := by
  cases matched
  rfl

theorem rootFiring_first_constructor_eq {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {rule : RewriteRule} {ordinal : Nat} {label schemaLabel sourceLabel : String}
    {schemas inputs restSchemas restInputs : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {history : List Event}
    (declared : environment.language.rewrites[ordinal]? = some rule)
    (schema : rule.left = .apply label (.apply schemaLabel schemas :: restSchemas))
    (firing : GeneralPremise.RootFiring environment bound type
      (.apply label (.apply sourceLabel inputs :: restInputs)) ordinal trace captured completed history target) :
    schemaLabel = sourceLabel := by
  cases firing with
  | fire actual _ _ _ matching _ _ _ _ =>
    have same := Option.some.inj (actual.symm.trans declared)
    subst same
    have matched := matching.matching
    rw [schema] at matched
    cases matched with
    | constructor arguments =>
      cases arguments with
      | cons first _ => exact matches_constructor_eq first

#print axioms matches_constructor_eq
#print axioms rootFiring_first_constructor_eq

end Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads
