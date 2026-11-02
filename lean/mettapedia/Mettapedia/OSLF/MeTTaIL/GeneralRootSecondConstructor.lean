import Mettapedia.OSLF.MeTTaIL.GeneralRootFirstConstructor

/-! The second argument's declared constructor is preserved by an actual
root firing. This distinguishes continuation forms independently of rule order.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch GeneralPremise

theorem rootFiring_second_constructor_eq {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {rule : RewriteRule} {ordinal : Nat} {label schemaLabel sourceLabel : String}
    {firstSchema firstInput : Pattern} {schemas inputs restSchemas restInputs : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {history : List Event}
    (declared : environment.language.rewrites[ordinal]? = some rule)
    (schema : rule.left = .apply label (firstSchema :: .apply schemaLabel schemas :: restSchemas))
    (firing : GeneralPremise.RootFiring environment bound type
      (.apply label (firstInput :: .apply sourceLabel inputs :: restInputs)) ordinal trace captured completed history target) :
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
      | cons _ tail =>
        cases tail with
        | cons second _ => exact matches_constructor_eq second

def secondConstructor? : Pattern → Option (String × String)
  | .apply outer (_ :: .apply inner _ :: _) => some (outer, inner)
  | _ => none

theorem secondConstructor_shape {pattern : Pattern} {outer inner : String}
    (read : secondConstructor? pattern = some (outer, inner)) :
    ∃ first arguments rest, pattern = .apply outer (first :: .apply inner arguments :: rest) := by
  cases pattern with
  | apply label arguments =>
    cases arguments with
    | nil => cases read
    | cons first later =>
      cases later with
      | nil => cases read
      | cons second rest =>
        cases second <;> simp only [secondConstructor?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at read
        obtain ⟨rfl, rfl⟩ := read
        exact ⟨_, _, _, rfl⟩
  | _ => cases read

theorem rootFiring_second_constructor_readout {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {rule : RewriteRule} {ordinal : Nat} {label inputLabel : String}
    {firstInput : Pattern} {inputs restInputs : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {history : List Event}
    (declared : environment.language.rewrites[ordinal]? = some rule)
    (shaped : (secondConstructor? rule.left).isSome = true)
    (firing : GeneralPremise.RootFiring environment bound type
      (.apply label (firstInput :: .apply inputLabel inputs :: restInputs)) ordinal trace captured completed history target) :
    secondConstructor? rule.left = some (label, inputLabel) := by
  obtain ⟨⟨outer, inner⟩, read⟩ := Option.isSome_iff_exists.mp shaped
  obtain ⟨first, arguments, rest, shape⟩ := secondConstructor_shape read
  have outerSame := rootFiring_constructor_eq declared shape firing
  subst outer
  have innerSame := rootFiring_second_constructor_eq declared shape firing
  subst inner
  exact read

#print axioms rootFiring_second_constructor_eq
#print axioms secondConstructor_shape
#print axioms rootFiring_second_constructor_readout

end Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads
