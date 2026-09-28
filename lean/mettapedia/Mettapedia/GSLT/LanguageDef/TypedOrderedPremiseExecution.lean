import Mettapedia.GSLT.LanguageDef.TypedPartialSpineStepResults

/-!
# Ordered premise typing

An authored premise's type action is an obligation on its actual executable
results. These obligations compose along the executor's ordered list without
discarding event histories. For a scoped-step target on a sorted partial
variable spine, the obligation follows from the typed capture theorem and a
typed output contract for the step oracle. Other premise forms require their
own actions before this theorem applies to a mixed rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

/-- Every returned event of this authored premise preserves assignment typing.
The index is part of the contract because occurrence sites are indexed by
premise position. -/
def PremiseTypeAction {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (index : Nat) (premise : Premise) : Prop :=
  ∀ initial final event,
    AssignmentHasTypes language free spec ambient initial →
    (event, final) ∈ premiseResults oracle relEnv language rule spec
      ambient.length index premise initial →
    AssignmentHasTypes language free spec ambient final

/-- One action contract for each premise in source order. -/
def OrderedPremiseTypeActions {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) : Nat → List Premise → Prop
  | _, [] => True
  | index, premise :: rest =>
      PremiseTypeAction language free rule spec ambient oracle relEnv
        index premise ∧
      OrderedPremiseTypeActions language free rule spec ambient oracle
        relEnv (index + 1) rest

/-- Ordered execution composes the per-premise actions while retaining the
exact selected history and final assignment. -/
theorem runPremises_preserves_assignment_types {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (index : Nat) (premises : List Premise)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (history : List (PremiseEvent Evidence))
    (actions : OrderedPremiseTypeActions language free rule spec ambient
      oracle relEnv index premises)
    (before : AssignmentHasTypes language free spec ambient initial)
    (selected : (final, history) ∈ runPremises oracle relEnv language
      rule spec ambient.length index premises initial) :
    AssignmentHasTypes language free spec ambient final := by
  induction premises generalizing index initial final history with
  | nil =>
      simp only [runPremises, List.mem_singleton, Prod.mk.injEq] at selected
      rcases selected with ⟨same, _⟩
      exact same ▸ before
  | cons premise rest ih =>
      change PremiseTypeAction language free rule spec ambient oracle relEnv
          index premise ∧
        OrderedPremiseTypeActions language free rule spec ambient oracle
          relEnv (index + 1) rest at actions
      simp only [runPremises, List.mem_flatMap, List.mem_map] at selected
      obtain ⟨⟨event, completed⟩, eventMember,
        ⟨next, tail⟩, tailMember, finalEq⟩ := selected
      have middle := actions.1 initial completed event before eventMember
      have last := ih (index := index + 1) (initial := completed)
        (final := next) (history := tail) actions.2 middle tailMember
      exact (Prod.mk.inj finalEq).1 ▸ last

/-- A scoped step premise with a metavariable target on a sorted partial
spine has the required action. The oracle's output-typing contract is stated
at the premise's own declared result sort. -/
theorem scopedStep_fvar_partialSpine_typeAction {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies : List TypeExpr) (index : Nat)
    (step : ScopedStepPremise) (name : String)
    (arguments : List Pattern) (indices : List Nat)
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (target : step.target = .fvar name)
    (declared : dependencies? spec name = some dependencies)
    (atSite : arguments? rule spec name (.premise index 0 1) [] =
      some arguments)
    (spineCheck : variableSpine? step.binders.length arguments = some indices)
    (spine : PartialSortedSpine dependencies step.binders indices)
    (namedType : free name = some step.resultType)
    (outputs : ∀ instantiated evidence candidate,
      (evidence, candidate) ∈ oracle
        (step.binders.length + ambient.length) instantiated →
      HasType language free (step.binders ++ ambient) candidate
        step.resultType) :
    PremiseTypeAction language free rule spec ambient oracle relEnv
      index (.scopedStep step) := by
  intro initial final event before selected
  by_cases wellScoped : step.isWellScopedAt ambient.length = true
  · simp only [premiseResults, wellScoped, if_true] at selected
    rw [target] at selected
    exact stepResults_fvar_partialSpine_preserves_types_of_selected
      language free rule spec ambient dependencies step.binders index
      step.source name step.resultType arguments indices oracle initial
      final event before declared atSite spineCheck spine namedType
      outputs selected
  · simp [premiseResults, wellScoped] at selected

#print axioms runPremises_preserves_assignment_types
#print axioms scopedStep_fvar_partialSpine_typeAction

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
