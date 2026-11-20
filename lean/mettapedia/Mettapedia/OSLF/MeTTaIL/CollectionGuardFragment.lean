import Mettapedia.OSLF.MeTTaIL.CollectionNullaryFiring
import Mettapedia.OSLF.MeTTaIL.CollectionInputFiring

/-!
# Checked guard fragments for collection source coverage

Nullary queries need no representation premise on provider values. Mixed
input/output queries use canonical finite provider rows, checked object input
templates and ordinary traced output matching. Complete premise histories
and output assignments are preserved at every ambient context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching CanonicalBags

inductive CollectionGuardFragment (provider : ProviderSnapshot) (context : Context) (premises : List Premise) : Prop
  | nullary (guards : NullaryGuards premises)
  | queries (finite : provider.dynamicRelations = []) (rows : CanonicalProviderRows provider)
      (guards : CanonicalQueryGuards provider context premises)

def checkCollectionGuardFragment (provider : ProviderSnapshot) (context : Context) (premises : List Premise) : Bool :=
  checkNullaryGuards premises || (provider.dynamicRelations.isEmpty && checkCanonicalProviderRows provider &&
    checkCanonicalQueryGuards provider context premises)

theorem checkCollectionGuardFragment_iff (provider : ProviderSnapshot) (context : Context) (premises : List Premise) :
    checkCollectionGuardFragment provider context premises = true ↔ CollectionGuardFragment provider context premises := by
  simp only [checkCollectionGuardFragment, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff,
    checkNullaryGuards_iff, checkCanonicalProviderRows_iff, checkCanonicalQueryGuards_iff]
  constructor
  · rintro (nullary | ⟨⟨finite, rows⟩, guards⟩)
    · exact .nullary nullary
    · exact .queries finite rows guards
  · intro fragment
    cases fragment with
    | nullary guards => exact .inl guards
    | queries finite rows guards => exact .inr ⟨⟨finite, rows⟩, guards⟩

theorem checkCollectionInputs_recontext (context : Context) (bound : List TypeExpr) (ruleIndex index : Nat)
    (arguments : List Pattern) :
    checkCollectionInputs { context with bound, ruleIndex } index arguments =
      checkCollectionInputs context index arguments := by
  induction arguments generalizing index with
  | nil => rfl
  | cons argument arguments ih =>
    cases argument <;> simp only [checkCollectionInputs, Context.site, ih]

theorem checkCollectionInputGuard_recontext (provider : ProviderSnapshot) (context : Context)
    (bound : List TypeExpr) (ruleIndex : Nat) (premise : Premise) :
    checkCollectionInputGuard provider { context with bound, ruleIndex } premise =
      checkCollectionInputGuard provider context premise := by
  cases premise <;> simp only [checkCollectionInputGuard, checkCollectionInputs_recontext]

theorem checkCollectionInputGuards_recontext (provider : ProviderSnapshot) (context : Context)
    (bound : List TypeExpr) (ruleIndex : Nat) (premises : List Premise) :
    checkCollectionInputGuards provider { context with bound, ruleIndex } premises =
      checkCollectionInputGuards provider context premises := by
  induction premises generalizing context with
  | nil => rfl
  | cons premise premises ih =>
    simp only [checkCollectionInputGuards, checkCollectionInputGuard_recontext]
    exact congrArg (fun tail => checkCollectionInputGuard provider context premise && tail) (ih context.next)

theorem checkCanonicalQueryArguments_recontext (context : Context) (bound : List TypeExpr) (ruleIndex index : Nat)
    (arguments : List Pattern) (modes : List RelationArgMode) :
    checkCanonicalQueryArguments { context with bound, ruleIndex } index arguments modes =
      checkCanonicalQueryArguments context index arguments modes := by
  induction arguments generalizing index modes with
  | nil => cases modes <;> rfl
  | cons argument arguments ih =>
    cases modes with
    | nil => rfl
    | cons mode modes =>
      cases mode <;> simp only [checkCanonicalQueryArguments, Context.site, ih]

theorem checkCanonicalQueryGuard_recontext (provider : ProviderSnapshot) (context : Context)
    (bound : List TypeExpr) (ruleIndex : Nat) (premise : Premise) :
    checkCanonicalQueryGuard provider { context with bound, ruleIndex } premise =
      checkCanonicalQueryGuard provider context premise := by
  cases premise <;> simp only [checkCanonicalQueryGuard, checkCanonicalQueryArguments_recontext]

theorem checkCanonicalQueryGuards_recontext (provider : ProviderSnapshot) (context : Context)
    (bound : List TypeExpr) (ruleIndex : Nat) (premises : List Premise) :
    checkCanonicalQueryGuards provider { context with bound, ruleIndex } premises =
      checkCanonicalQueryGuards provider context premises := by
  induction premises generalizing context with
  | nil => rfl
  | cons premise premises ih =>
    simp only [checkCanonicalQueryGuards, checkCanonicalQueryGuard_recontext]
    exact congrArg (fun tail => checkCanonicalQueryGuard provider context premise && tail) (ih context.next)

theorem CollectionGuardFragment.recontext {provider : ProviderSnapshot} {context : Context}
    {premises : List Premise} (fragment : CollectionGuardFragment provider context premises)
    (bound : List TypeExpr) (ruleIndex : Nat) :
    CollectionGuardFragment provider { context with bound, ruleIndex } premises := by
  apply (checkCollectionGuardFragment_iff _ _ _).mp
  have checked := (checkCollectionGuardFragment_iff _ _ _).mpr fragment
  simpa only [checkCollectionGuardFragment, checkCanonicalQueryGuards_recontext] using checked

theorem Interpreted.RootFiring.replay_collection_guards {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source other : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace replay : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (binderOk : BinderLawsFor [] environment.reflection rule)
    (guards : CollectionGuardFragment environment.provider ⟨index, rule, spec, bound, 0, 0⟩ rule.premises)
    (increasing : IncreasingSpines rule spec)
    (sameSource : Same source other)
    (matching : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
      rule.left other replay (canonAssignment captured)) :
    ∃ target', GeneralPremise.RootFiring environment bound type other index replay (canonAssignment captured)
        (canonAssignment completed) history target' ∧ Same target target' := by
  cases guards with
  | nullary guards => exact fired.replay_nullary selected specified binderOk guards sameSource matching
  | queries finite rows guards =>
    exact fired.replay_canonical_queries selected specified binderOk increasing finite rows guards sameSource matching

theorem Interpreted.RootFiring.collection_guards_history_depth {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {history : List Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (guards : CollectionGuardFragment environment.provider ⟨index, rule, spec, bound, 0, 0⟩ rule.premises) :
    StructuralDescent.eventsDepth history = 0 := by
  cases guards with
  | nullary guards => exact fired.nullary_history_depth selected guards
  | queries _ _ guards => exact fired.canonical_queries_history_depth selected specified guards

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
