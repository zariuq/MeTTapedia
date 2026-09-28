import Mettapedia.GSLT.LanguageDef.TypedOrderedRootPremiseActions

/-!
# Typed projection of contextual captures to root premises

The root premise interpreter uses an ordinary binding list. Its entries are
obtained from contextual captures only when the capture has no local
dependencies. A successful projection retains the exact body and its
declaration-derived sort in the caller's ambient context. This supplies the
freshness premise's output-typing action without an external oracle contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

/-- A root projection cannot consume a contextual capture with a nonempty
local dependency context. -/
theorem instantiateValue?_root_requires_empty_dependencies
    (value : ContextualValue) (ambient : Nat) (result : Pattern)
    (projected : instantiateValue? value ambient 0 [] = some result) :
    value.dependencies = [] := by
  by_contra nonempty
  have lengthPositive : value.dependencies.length ≠ 0 := by
    simpa using nonempty
  simp [instantiateValue?] at projected
  exact lengthPositive projected.2.1.symm

/-- A successful projection from a typed contextual capture has exactly its
declared type at the root, including ambient open variables. -/
theorem instantiateValue?_root_has_type
    (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (dependencies : List TypeExpr)
    (resultType : TypeExpr) (value : ContextualValue)
    (typed : ContextualValueHasType language free dependencies ambient
      resultType value) (result : Pattern)
    (projected : instantiateValue? value ambient.length 0 [] = some result) :
    HasType language free ambient result resultType := by
  obtain ⟨dependenciesEq, ambientEq, bodyTyped⟩ := typed
  have empty := instantiateValue?_root_requires_empty_dependencies
    value ambient.length result projected
  have depsEmpty : dependencies = [] := dependenciesEq.symm.trans empty
  subst dependencies
  cases value with
  | mk actualDependencies actualAmbient body =>
      simp only at ambientEq bodyTyped empty projected
      subst actualDependencies
      subst actualAmbient
      have identity : occurrenceAssignment 0 0 [] = Pattern.bvar := by
        funext index
        simp [occurrenceAssignment]
      simp [instantiateValue?, identity,
        Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id] at projected
      rcases projected with ⟨_, rfl⟩
      simpa using bodyTyped

/-- Every root binding selected from a successful projection comes from a
typed contextual capture with the same name and result. -/
theorem projectRoot?_has_types
    (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (root : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (typed : AssignmentHasTypes language free spec ambient assignment)
    (projected : projectRoot? ambient.length assignment = some root) :
    RootOutputsHaveTypes language free ambient root := by
  induction assignment generalizing root with
  | nil =>
      simp [projectRoot?] at projected
      subst root
      intro name result member
      cases member
  | cons entry tail ih =>
      rcases entry with ⟨entryName, entryValue⟩
      cases entryResult : instantiateValue? entryValue ambient.length 0 [] with
      | none =>
          simp [projectRoot?, entryResult] at projected
      | some value =>
          cases tailResult : projectRoot? ambient.length tail with
          | none =>
              change (List.mapM (fun x : String × ContextualValue =>
                (instantiateValue? x.2 ambient.length 0 []).bind
                  fun result => some (x.1, result)) tail) = none at tailResult
              simp [projectRoot?, entryResult, tailResult] at projected
          | some remaining =>
              change (List.mapM (fun x : String × ContextualValue =>
                (instantiateValue? x.2 ambient.length 0 []).bind
                  fun result => some (x.1, result)) tail) =
                  some remaining at tailResult
              simp [projectRoot?, entryResult, tailResult] at projected
              subst root
              intro name result member
              rcases List.mem_cons.mp member with first | later
              · cases first
                obtain ⟨dependencies, resultType, _, declaredType,
                  valueTyped⟩ := typed entryName entryValue (by simp)
                exact ⟨resultType, declaredType,
                  instantiateValue?_root_has_type language free ambient
                    dependencies resultType entryValue valueTyped value
                    entryResult⟩
              · exact ih remaining (by
                  intro otherName otherValue oldMember
                  exact typed otherName otherValue (by simp [oldMember]))
                  tailResult name result later

/-- The actual freshness interpreter returns only the projected root
bindings, whose typing follows from the contextual assignment. -/
theorem freshness_root_output_action
    (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (relEnv : RelationEnv) (condition : FreshnessCondition) :
    RootPremiseOutputAction language free spec ambient relEnv
      (.freshness condition) := by
  intro initial root raw typed projected selected
  have same := premiseStepWithEnv_freshness_mem selected
  subst raw
  exact projectRoot?_has_types language free spec ambient initial root
    typed projected

/-- Freshness has a type action for every authored rule, without an assumed
premise-output typing condition. It may reject, but cannot corrupt a typed
assignment when it succeeds. -/
theorem freshness_preserves_assignment_types {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (index : Nat) (condition : FreshnessCondition) :
    PremiseTypeAction language free rule spec ambient oracle relEnv
      index (.freshness condition) :=
  freshness_typeAction language free rule spec ambient oracle relEnv
    index condition
      (freshness_root_output_action language free spec ambient relEnv
        condition)

#print axioms instantiateValue?_root_has_type
#print axioms projectRoot?_has_types
#print axioms freshness_preserves_assignment_types

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
