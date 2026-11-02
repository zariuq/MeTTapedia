import Mettapedia.OSLF.MeTTaIL.GeneralRootFirstConstructor

/-! Constructor metadata for the first argument of an authored root rule.
An actual firing supplies the observed outer and first-argument labels.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch GeneralPremise

def firstConstructor? : Pattern → Option (String × String)
  | .apply outer (.apply inner _ :: _) => some (outer, inner)
  | _ => none

theorem firstConstructor_shape {pattern : Pattern} {outer inner : String}
    (read : firstConstructor? pattern = some (outer, inner)) :
    ∃ arguments rest, pattern = .apply outer (.apply inner arguments :: rest) := by
  cases pattern with
  | apply label arguments =>
    cases arguments with
    | nil => cases read
    | cons first rest =>
      cases first <;> simp only [firstConstructor?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at read
      obtain ⟨rfl, rfl⟩ := read
      exact ⟨_, _, rfl⟩
  | _ => cases read

theorem rootFiring_first_constructor_readout {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {rule : RewriteRule} {ordinal : Nat} {label inputLabel : String}
    {inputs restInputs : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {history : List Event}
    (declared : environment.language.rewrites[ordinal]? = some rule)
    (shaped : (firstConstructor? rule.left).isSome = true)
    (firing : GeneralPremise.RootFiring environment bound type
      (.apply label (.apply inputLabel inputs :: restInputs)) ordinal trace captured completed history target) :
    firstConstructor? rule.left = some (label, inputLabel) := by
  obtain ⟨⟨outer, inner⟩, read⟩ := Option.isSome_iff_exists.mp shaped
  obtain ⟨arguments, rest, shape⟩ := firstConstructor_shape read
  have outerSame := rootFiring_constructor_eq declared shape firing
  subst outer
  have innerSame := rootFiring_first_constructor_eq declared shape firing
  subst inner
  exact read

#print axioms firstConstructor_shape
#print axioms rootFiring_first_constructor_readout

end Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads
