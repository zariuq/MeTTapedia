import Mettapedia.GSLT.LanguageDef.TypedOrderedPremiseExecution

/-!
# Root premise actions in ordered scoped execution

The existing root premise machine supplies freshness and relation-query
results. Its output typing contract is enough to make either premise an
action on typed contextual assignments. This connects the root adapter to
the same ordered fold used by binder-local step premises. The oracle contract
is indexed by the current assignment: later root premises may consume values
produced by earlier scoped premises.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

/-- The typing contract for root outputs can depend on the assignment
available at this position in an ordered rule. -/
def RootPremiseOutputAction
    (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (relEnv : RelationEnv) (premise : Premise) : Prop :=
  ∀ initial root raw,
    AssignmentHasTypes language free spec ambient initial →
    projectRoot? ambient.length initial = some root →
    raw ∈ premiseStepWithEnv relEnv language root premise →
    RootOutputsHaveTypes language free ambient raw

/-- A freshness premise uses the typed root adapter inside the actual
ordered executor. It cannot silently change the context of a stored value. -/
theorem freshness_typeAction {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (index : Nat) (condition : FreshnessCondition)
    (outputs : RootPremiseOutputAction language free spec ambient
      relEnv (.freshness condition)) :
    PremiseTypeAction language free rule spec ambient oracle relEnv
      index (.freshness condition) := by
  intro initial final event before selected
  exact rootResults_preserves_types language free spec ambient relEnv
    index (.freshness condition) initial final event before
    (fun root raw projected found =>
      outputs initial root raw before projected found)
    selected

/-- A relation query may introduce or repeat captures. The root adapter
checks repeated values and retains both declared dependency and ambient
contexts, so its action composes with binder-local steps. -/
theorem relationQuery_typeAction {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (index : Nat) (relation : String)
    (arguments : List Pattern)
    (outputs : RootPremiseOutputAction language free spec ambient
      relEnv (.relationQuery relation arguments)) :
    PremiseTypeAction language free rule spec ambient oracle relEnv
      index (.relationQuery relation arguments) := by
  intro initial final event before selected
  exact rootResults_preserves_types language free spec ambient relEnv
    index (.relationQuery relation arguments) initial final event before
    (fun root raw projected found =>
      outputs initial root raw before projected found)
    selected

/-- A root query may supply values used by a subsequent binder-local step.
The selected history is the executor's history, including both premise
positions and the step evidence. -/
theorem relationQuery_then_scopedStep_preserves_types {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (index : Nat) (relation : String)
    (arguments : List Pattern) (step : ScopedStepPremise)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (history : List (PremiseEvent Evidence))
    (outputs : RootPremiseOutputAction language free spec ambient
      relEnv (.relationQuery relation arguments))
    (stepAction : PremiseTypeAction language free rule spec ambient
      oracle relEnv (index + 1) (.scopedStep step))
    (before : AssignmentHasTypes language free spec ambient initial)
    (selected : (final, history) ∈ runPremises oracle relEnv language
      rule spec ambient.length index
      [.relationQuery relation arguments, .scopedStep step] initial) :
    AssignmentHasTypes language free spec ambient final ∧
      history.length = 2 := by
  constructor
  · exact runPremises_preserves_assignment_types language free rule spec
      ambient oracle relEnv index
      [.relationQuery relation arguments, .scopedStep step]
      initial final history
      ⟨relationQuery_typeAction language free rule spec ambient oracle
        relEnv index relation arguments outputs, stepAction, trivial⟩
      before selected
  · simpa using runPremises_history_length oracle relEnv language rule spec
      ambient.length index [.relationQuery relation arguments, .scopedStep step]
      initial final history selected

/-- The base executor does not yet implement collection quantification.
Its empty result is a negative control: a vacuous type action for this case
would not establish support for quantified premises. -/
theorem quantified_premise_has_no_results {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat)
    (collection parameter : String) (body : Premise)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment) :
    premiseResults oracle relEnv language rule spec ambient index
      (.forAll collection parameter body) initial = [] := by
  by_cases occurrence : hasOccurrenceAt spec index = true
  · simp [premiseResults, rootResults, occurrence]
  · cases projected : projectRoot? ambient initial with
    | none => simp [premiseResults, rootResults, occurrence, projected]
    | some root =>
        simp [premiseResults, rootResults, occurrence, projected,
          premiseStepWithEnv]

#print axioms freshness_typeAction
#print axioms relationQuery_typeAction
#print axioms relationQuery_then_scopedStep_preserves_types
#print axioms quantified_premise_has_no_results

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
