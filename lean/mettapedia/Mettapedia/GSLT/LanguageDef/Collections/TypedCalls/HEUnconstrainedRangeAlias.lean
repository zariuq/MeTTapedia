import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias

/-!
# Operator lookup after an unconstrained schematic range selection

A wildcard demand does not constrain a fresh result variable. The subsequent
whole-arrow lookup introduces another fresh result variable and links the two
unvalued classes. This is an actual source merge, not a numeric-range rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEUnconstrainedRangeAlias

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Eval Spec.Eval.Completed

theorem empty_class (bindings : Bindings) (left right : String)
    (leftFresh : left ∉ specBindingVars bindings) (rightFresh : right ∉ specBindingVars bindings)
    (different : left ≠ right) :
    (bindings.addEquality left right).classValues left = [] := by
  unfold Bindings.classValues
  rw [EqualityClosure.eqClassOrdered_addEquality_of_fresh
    (HEFreshRangeAlias.fresh_not_in_equalities bindings left leftFresh)
    (HEFreshRangeAlias.fresh_not_in_equalities bindings right rightFresh) different]
  change [left, right].filterMap bindings.lookup = []
  simp [HEFreshRangeFrame.fresh_lookup bindings left leftFresh,
    HEFreshRangeFrame.fresh_lookup bindings right rightFresh]

theorem source_merge (bindings : Bindings) (left right : String)
    (leftFresh : left ∉ specBindingVars bindings) (rightFresh : right ∉ specBindingVars bindings)
    (different : left ≠ right) :
    MergeRel equalityGroundedSemantic bindings (Bindings.empty.addEquality left right)
      (bindings.addEquality left right) := by
  apply MergeRel.mk (order := [.equality left right])
  · simp [constraints, Bindings.empty, Bindings.addEquality, List.eraseDups_cons]
  · exact .equality (.consistent (empty_class bindings left right leftFresh rightFresh different) trivial) .nil

theorem arrow_source_match (bindings : Bindings) (spine : List String) (left right : String)
    (leftFresh : left ∉ specBindingVars bindings) (rightFresh : right ∉ specBindingVars bindings)
    (different : left ≠ right) :
    TypeMatchRel (HEFreshRangeAlias.arrowWith spine left) (HEFreshRangeAlias.arrowWith spine right)
      bindings (bindings.addEquality left right) :=
  .structural (by simp [HEFreshRangeAlias.arrowWith, Atom.undefinedType])
    (by simp [HEFreshRangeAlias.arrowWith, Atom.atomType])
    (by simp [HEFreshRangeAlias.arrowWith, Atom.undefinedType])
    (by simp [HEFreshRangeAlias.arrowWith, Atom.atomType])
    (HEFreshRangeAlias.arrow_match spine left right)
    (source_merge bindings left right leftFresh rightFresh different)

theorem arrow_policy_match (before : Frame) (policy : Policy) (spine : List String) (left right : String)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (different : left ≠ right) :
    policy.matching.Rel (HEFreshRangeAlias.arrowWith spine left) (HEFreshRangeAlias.arrowWith spine right)
      before.bindings (before.bindings.addEquality left right) ∧
      ∃ valuation, TypeBindingSatisfied valuation (before.bindings.addEquality left right) := by
  have matched := arrow_source_match before.bindings spine left right leftFresh rightFresh different
  have model := HEFreshRangeAlias.alias_model before left right rightFresh
  refine ⟨?_, model⟩
  cases matching : policy.matching with
  | raw => exact matched
  | finite => exact ⟨matched, model⟩

namespace Controls

theorem unconstrained_if_arrow_keeps_caller_alias (policy : Policy) :
    policy.matching.Rel (HEFreshRangeAlias.arrowWith ["->", "Bool", "Atom", "Atom"] "range")
      (HEFreshRangeAlias.arrowWith ["->", "Bool", "Atom", "Atom"] "query")
      Spec.Eval.Completed.Controls.representedAliasFrame.bindings
      (Spec.Eval.Completed.Controls.representedAliasFrame.bindings.addEquality "range" "query") :=
  (arrow_policy_match Spec.Eval.Completed.Controls.representedAliasFrame policy
    ["->", "Bool", "Atom", "Atom"] "range" "query" (by decide) (by decide) (by decide)).1

theorem fresh_alias_does_not_mean_number :
    TypeBindingSatisfied (fun _ => .symbol "String") (Bindings.empty.addEquality "range" "query") ∧
    (Bindings.empty.addEquality "range" "query").classValues "range" = [] := by
  constructor
  · simp [TypeBindingSatisfied, Bindings.empty, Bindings.addEquality]
  · exact empty_class Bindings.empty "range" "query" (by decide) (by decide) (by decide)

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEUnconstrainedRangeAlias
