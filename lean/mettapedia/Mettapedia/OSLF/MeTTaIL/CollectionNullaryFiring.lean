import Mettapedia.OSLF.MeTTaIL.GeneralPremiseNullaryTransport
import Mettapedia.OSLF.MeTTaIL.CanonicalFiring
import Mettapedia.OSLF.MeTTaIL.StructuralDescentDepth

/-!
# Replaying nullary-guarded firings at prepared collection presentations

The recursive matcher supplies an ordinary witness at its reconstructed
presentation, with canonical captures. Guard transport preserves the complete
premise history; the existing substitution comparison transports the result.
No set-free condition is imposed on the supplied recursive match.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching CanonicalBags

theorem Interpreted.PremisesHold.nullary_history_depth {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {history : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (guards : NullaryGuards premises) : StructuralDescent.eventsDepth history = 0 := by
  cases held with
  | nil => simp only [StructuralDescent.eventsDepth]
  | @cons context premise premises initial middle final event history first rest =>
    obtain ⟨relation, same⟩ := guards premise List.mem_cons_self
    subst premise
    have tail := rest.nullary_history_depth
      (fun p member => guards p (List.mem_cons_of_mem _ member))
    cases first with
    | query _ => simp only [StructuralDescent.eventsDepth, StructuralDescent.eventDepth, tail, Nat.max_self]
termination_by premises.length
decreasing_by all_goals simp_all [List.length_cons]

theorem Interpreted.RootFiring.nullary_history_depth {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat} {rule : RewriteRule}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (guards : NullaryGuards rule.premises) : StructuralDescent.eventsDepth history = 0 := by
  cases fired with
  | fire declared _ _ _ _ _ premises _ _ =>
    have same := Option.some.inj (declared.symm.trans selected)
    subst rule
    exact premises.nullary_history_depth guards

theorem Interpreted.RootFiring.replay_nullary {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source other : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace replay : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (binderOk : BinderLawsFor [] environment.reflection rule)
    (guards : NullaryGuards rule.premises) (sameSource : Same source other)
    (matching : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
      rule.left other replay (canonAssignment captured)) :
    ∃ target', GeneralPremise.RootFiring environment bound type other index replay (canonAssignment captured)
        (canonAssignment completed) history target' ∧ Same target target' := by
  cases fired with
  | @fire bound type source target index originalRule originalSpec trace captured completed history
      declared prescribed admitted sourceTyped originalMatching capturedTyped premises reduced targetTyped =>
    have ruleSame : originalRule = rule := Option.some.inj (declared.symm.trans selected)
    have specSame : originalSpec = spec := Option.some.inj (prescribed.symm.trans specified)
    cases ruleSame
    cases specSame
    obtain ⟨target', reduced', sameTarget⟩ := instantiateWith?_same rule spec bound.length
      (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      (binderOperation_same _ rule binderOk) rule.right .right [] 0 completed (canonAssignment completed)
      target (assignSame_canon completed) reduced
    refine ⟨target', ?_, sameTarget⟩
    exact .fire selected specified admitted
      (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameSource) sourceTyped)
      matching (typedAssignment_canon capturedTyped) (premises.nullary_canon guards capturedTyped)
      reduced' (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameTarget) targetTyped)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
