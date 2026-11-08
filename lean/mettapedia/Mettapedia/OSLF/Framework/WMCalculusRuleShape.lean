import Mettapedia.OSLF.Framework.WMCalculusDenotationalSoundness

/-!
# Well-formed WM rules

A rewrite rule is *well formed* when every metavariable of its right side is
bound by its left side or by a premise row (`rightNamesBound`).  This is the
dangling-variable condition of the language validator
(`LanguageDef.validateRulePatterns`), computed with the structural name
function `patternNames`, which agrees with `Pattern.freeFvarNames` on
first-order patterns (`patternNames_eq_freeFvarNames`).  A right-side
metavariable that nothing binds survives substitution as a free name, so the
reduct names whatever that name happens to denote.

Every rule of every vertex, every congruence rule and the budget rule
`ruleZeroLeakage` pass the check (`fullWithCong_wellFormed`,
`extWithCong_wellFormed`, `zeroLeakage_wellFormed`), and every relation is
queried with one arity (`maximal_relationArities_unique`).  The rules as they
stood before their premises were added fail both checks; those controls are in
`WMCalculusCounterexamples`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusRuleShape

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusPatternDenotation
open Mettapedia.OSLF.Framework.WMCalculusDenotationalSoundness

/-- The metavariables a premise binds when it succeeds: the arguments of a
relation query, matched against the returned row, and the target of a
congruence premise. -/
def premiseOutputNames : Premise → List String
  | .relationQuery _ args => patternNamesList args
  | .congruence _ target => patternNames target
  | .freshness _ => []
  | .scopedStep _ => []
  | .forAll _ _ _ => []

/-- Every right-side metavariable is bound by the left side or by a premise
row. -/
def rightNamesBound (rule : RewriteRule) : Bool :=
  (patternNames rule.right).all fun name =>
    (patternNames rule.left).contains name ||
      (rule.premises.flatMap premiseOutputNames).contains name

/-- The relation calls of a list of rules, with their arities. -/
def relationCalls (rules : List RewriteRule) : List (String × Nat) :=
  rules.flatMap fun rule => rule.premises.filterMap fun premise =>
    match premise with
    | .relationQuery relation args => some (relation, args.length)
    | _ => none

/-- Each relation name occurs with one arity. -/
def aritiesUnique (calls : List (String × Nat)) : Bool :=
  calls.all fun call => calls.all fun other => call.1 != other.1 || call.2 == other.2

theorem maximalRules_wellFormed :
    ∀ rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites,
      rightNamesBound rule = true := by
  decide +kernel

theorem congruenceRules_wellFormed :
    ∀ rule ∈ allCongruenceRules ++ combinedExtensionCongruenceRules,
      rightNamesBound rule = true := by
  decide +kernel

theorem zeroLeakage_wellFormed : rightNamesBound ruleZeroLeakage = true := by
  decide +kernel

/-- Every rule of every full vertex, with or without its congruence rules, is
well formed. -/
theorem fullWithCong_wellFormed (v : WMFullVertex) :
    ∀ rule ∈ (wmFullVertexLanguageDefWithCong v).rewrites, rightNamesBound rule = true := by
  intro rule member
  simp only [wmFullVertexLanguageDefWithCong, List.mem_append] at member
  rcases member with member | member
  · exact maximalRules_wellFormed rule (fullRules_in_maximal v rule member)
  · exact congruenceRules_wellFormed rule (List.mem_append_left _ member)

/-- So is every rule of every six-axis vertex. -/
theorem extWithCong_wellFormed (v : WMExtVertex) :
    ∀ rule ∈ (wmExtVertexLanguageDefWithCong v).rewrites, rightNamesBound rule = true := by
  intro rule member
  simp only [wmExtVertexLanguageDefWithCong, List.mem_append] at member
  rcases member with member | member
  · exact maximalRules_wellFormed rule (extRules_in_maximal v rule member)
  · apply congruenceRules_wellFormed rule
    simp only [allCongruenceRules, List.mem_append]
    exact Or.inl (Or.inl member)

/-- Every relation the maximal vertex queries has one arity. -/
theorem maximal_relationArities_unique :
    aritiesUnique (relationCalls (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites) =
      true := by
  decide +kernel

/-! ## Premises under the empty relation environment -/

/-- Of the 37 rules of the maximal vertex, 20 have no premise and 17 have
relation premises. -/
theorem maximal_premise_counts :
    ((wmFullVertexLanguageDef wmFullVertexMaximal).rewrites.filter
        fun rule => rule.premises.isEmpty).length = 20 ∧
      ((wmFullVertexLanguageDef wmFullVertexMaximal).rewrites.filter
        fun rule => !rule.premises.isEmpty).length = 17 := by
  decide +kernel

/-- A premise list that starts with a relation query other than the built-in
`eq`. -/
def startsWithEnvironmentRelation : List Premise → Bool
  | .relationQuery relation _ :: _ => relation != "eq"
  | _ => false

/-- Every rule of the maximal vertex either has no premise or starts with a
relation query that only the relation environment answers. -/
theorem maximal_premises_start_with_relation :
    ∀ rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites,
      (rule.premises.isEmpty || startsWithEnvironmentRelation rule.premises) = true := by
  decide +kernel

/-- Under the empty relation environment a premise list that starts with such
a relation query accepts no bindings. -/
theorem applyPremises_empty_of_environmentRelation (lang : LanguageDef)
    (bindings : Bindings) {premises : List Premise}
    (starts : startsWithEnvironmentRelation premises = true) :
    applyPremisesWithEnv RelationEnv.empty lang premises bindings = [] := by
  cases premises with
  | nil => simp [startsWithEnvironmentRelation] at starts
  | cons premise rest =>
      cases premise <;> simp only [startsWithEnvironmentRelation, Bool.false_eq_true] at starts
      rename_i relation args
      have first : premiseStepWithEnv RelationEnv.empty lang bindings
          (.relationQuery relation args) = [] := by
        simp only [premiseStepWithEnv, relationQueryStep, RelationEnv.empty, List.append_nil]
        unfold builtinRelationTuples
        split
        · simp_all
        · rfl
      simp only [applyPremisesWithEnv, List.foldl_cons, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, first]
      clear first
      induction rest with
      | nil => rfl
      | cons premise rest ih => simpa only [List.foldl_cons, List.flatMap_nil] using ih

/-- **No rule with a premise fires under the empty relation environment**: the
premise-free rules are the only ones that do. -/
theorem maximal_premises_refuse_empty :
    ∀ rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites, rule.premises ≠ [] →
      ∀ (lang : LanguageDef) (bindings : Bindings),
        applyPremisesWithEnv RelationEnv.empty lang rule.premises bindings = [] := by
  intro rule member nonempty lang bindings
  have shape := maximal_premises_start_with_relation rule member
  cases hpremises : rule.premises with
  | nil => exact absurd hpremises nonempty
  | cons premise rest =>
      rw [hpremises] at shape
      simp only [List.isEmpty_cons, Bool.false_or] at shape
      exact applyPremises_empty_of_environmentRelation lang bindings shape

#print axioms maximalRules_wellFormed
#print axioms congruenceRules_wellFormed
#print axioms zeroLeakage_wellFormed
#print axioms fullWithCong_wellFormed
#print axioms extWithCong_wellFormed
#print axioms maximal_relationArities_unique
#print axioms maximal_premise_counts
#print axioms maximal_premises_start_with_relation
#print axioms applyPremises_empty_of_environmentRelation
#print axioms maximal_premises_refuse_empty

end Mettapedia.OSLF.Framework.WMCalculusRuleShape
