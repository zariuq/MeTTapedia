import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCollectionInputTransport
import Mettapedia.OSLF.MeTTaIL.CanonicalFiring

/-!
# Source firing transport for canonical provider queries

The query contract checks object input templates, actual modes and canonical
provider rows. It retains output captures, provider occurrences and complete
histories while the recursive matcher reconstructs an ordinary presentation.
Whole-variable input guards remain a specialization.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching CanonicalBags

theorem Interpreted.RootFiring.replay_collection_inputs {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source other : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace replay : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (binderOk : BinderLawsFor [] environment.reflection rule)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CollectionInputGuards environment.provider ⟨index, rule, spec, bound, 0, 0⟩ rule.premises)
    (sameSource : Same source other)
    (matching : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
      rule.left other replay (canonAssignment captured)) :
    ∃ target', GeneralPremise.RootFiring environment bound type other index replay (canonAssignment captured)
        (canonAssignment completed) history target' ∧ Same target target' := by
  cases fired with
  | @fire bound type source target index actualRule actualSpec trace captured completed history
      declared prescribed admitted sourceTyped originalMatching capturedTyped premises reduced targetTyped =>
    have ruleSame : actualRule = rule := Option.some.inj (declared.symm.trans selected)
    have specSame : actualSpec = spec := Option.some.inj (prescribed.symm.trans specified)
    cases ruleSame
    cases specSame
    obtain ⟨target', reduced', sameTarget⟩ := instantiateWith?_same rule spec bound.length
      (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      (binderOperation_same _ rule binderOk) rule.right .right [] 0 completed (canonAssignment completed)
      target (assignSame_canon completed) reduced
    refine ⟨target', ?_, sameTarget⟩
    exact .fire selected specified admitted
      (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameSource) sourceTyped)
      matching (typedAssignment_canon capturedTyped)
      (premises.collection_inputs_canon finite rows guarded).2 reduced'
      (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameTarget) targetTyped)

theorem Interpreted.RootFiring.collection_inputs_history_depth {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {history : List Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (guarded : CollectionInputGuards environment.provider ⟨index, rule, spec, bound, 0, 0⟩ rule.premises) :
    StructuralDescent.eventsDepth history = 0 := by
  cases fired with
  | fire declared prescribed _ _ _ _ premises _ _ =>
    cases Option.some.inj (declared.symm.trans selected)
    cases Option.some.inj (prescribed.symm.trans specified)
    exact premises.collection_inputs_history_depth guarded

/-! Mode-parametric queries retain the same complete source history. -/

theorem Interpreted.RootFiring.replay_canonical_queries {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source other : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace replay : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (binderOk : BinderLawsFor [] environment.reflection rule)
    (increasing : IncreasingSpines rule spec)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CanonicalQueryGuards environment.provider ⟨index, rule, spec, bound, 0, 0⟩ rule.premises)
    (sameSource : Same source other)
    (matching : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
      rule.left other replay (canonAssignment captured)) :
    ∃ target', GeneralPremise.RootFiring environment bound type other index replay (canonAssignment captured)
        (canonAssignment completed) history target' ∧ Same target target' := by
  cases fired with
  | @fire bound type source target index actualRule actualSpec trace captured completed history
      declared prescribed admitted sourceTyped originalMatching capturedTyped premises reduced targetTyped =>
    have ruleSame : actualRule = rule := Option.some.inj (declared.symm.trans selected)
    have specSame : actualSpec = spec := Option.some.inj (prescribed.symm.trans specified)
    cases ruleSame
    cases specSame
    obtain ⟨target', reduced', sameTarget⟩ := instantiateWith?_same rule spec bound.length
      (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      (binderOperation_same _ rule binderOk) rule.right .right [] 0 completed (canonAssignment completed)
      target (assignSame_canon completed) reduced
    refine ⟨target', ?_, sameTarget⟩
    exact .fire selected specified admitted
      (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameSource) sourceTyped)
      matching (typedAssignment_canon capturedTyped)
      (premises.canonical_query_transport increasing finite rows guarded) reduced'
      (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameTarget) targetTyped)

theorem Interpreted.RootFiring.canonical_queries_history_depth {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {history : List Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (guarded : CanonicalQueryGuards environment.provider ⟨index, rule, spec, bound, 0, 0⟩ rule.premises) :
    StructuralDescent.eventsDepth history = 0 := by
  cases fired with
  | fire declared prescribed _ _ _ _ premises _ _ =>
    cases Option.some.inj (declared.symm.trans selected)
    cases Option.some.inj (prescribed.symm.trans specified)
    exact premises.canonical_query_history_depth guarded

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
