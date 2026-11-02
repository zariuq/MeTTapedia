import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads

/-! Actual scoped root firings preserve an authored constructor head.
This classifies enabled declarations without assuming that only an
expected rule family can match the source.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch GeneralPremise

theorem rootFiring_constructor {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {rule : RewriteRule} {ordinal : Nat} {label : String} {arguments : List Pattern} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (declared : environment.language.rewrites[ordinal]? = some rule)
    (schema : rule.left = .apply label arguments)
    (firing : GeneralPremise.RootFiring environment bound type source ordinal trace captured completed history target) :
    ∃ inputs, source = .apply label inputs := by
  cases firing with
  | fire actual _ _ _ matching _ _ _ _ =>
    have same := Option.some.inj (actual.symm.trans declared)
    subst same
    have matched := matching.matching
    rw [schema] at matched
    cases matched with
    | constructor _ => exact ⟨_, rfl⟩

theorem rootFiring_constructor_eq {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {rule : RewriteRule} {ordinal : Nat} {schemaLabel sourceLabel : String}
    {arguments inputs : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (declared : environment.language.rewrites[ordinal]? = some rule)
    (schema : rule.left = .apply schemaLabel arguments)
    (firing : GeneralPremise.RootFiring environment bound type (.apply sourceLabel inputs) ordinal
      trace captured completed history target) : schemaLabel = sourceLabel := by
  obtain ⟨_, same⟩ := rootFiring_constructor declared schema firing
  exact (Pattern.apply.inj same).1.symm

#print axioms rootFiring_constructor
#print axioms rootFiring_constructor_eq

theorem rootFiring_potentialChild {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {rule : RewriteRule} {ordinal : Nat} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (declared : environment.language.rewrites[ordinal]? = some rule)
    (firing : GeneralPremise.RootFiring environment bound type source ordinal trace captured completed history target) :
    potentialChild source rule = true := by
  cases source with
  | apply label inputs =>
    cases firing with
    | fire actual _ _ _ matching _ _ _ _ =>
      have same := Option.some.inj (actual.symm.trans declared)
      subst same
      rcases matches_constructor_head matching.matching with ⟨name, shape⟩ | ⟨arguments, shape⟩ <;>
        (dsimp only at shape; simp [potentialChild, shape])
  | _ => rfl

#print axioms rootFiring_potentialChild

end Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads
