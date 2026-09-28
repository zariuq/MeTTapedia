import Mettapedia.OSLF.Syntax.CanonicalCompiledRuleShapeAdmission
import Mettapedia.OSLF.Syntax.LambdaAuthoredTypingComparison

/-!
# Actual four-rule lambda firings enter the result-sorted rule presentation

The whole authored declaration compiles at every lambda context. Intrinsic
source and target terms have the declaration-derived authored type. Together
these facts lift every raw listed shape between encoded terms to the sorted
operational rule polynomial without changing its constructor label.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredResultSortedShapes

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.Binding.LambdaAuthoredCanonicalFreeComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredTypingComparison
open Mettapedia.OSLF.Binding.CanonicalCompiledRuleShapeAdmission
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory rewriteAt)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)

/-- Canonically compiled rule shapes between intrinsically scoped lambda
endpoints lift to the authored result-sorted operational presentation. -/
noncomputable def liftEncodedShape {Γ : Ctx sig}
    (source target : Term sig Γ .term)
    (shape : RuleSkeleton RuleHistory RelationEnv.empty language
      (contextTypes Γ).length (encodeTerm source) (encodeTerm target)) :
    ResultSortedScopedOperationalPresentation.RuleShape
      RelationEnv.empty language FreeTypeContext.empty
      (contextTypes Γ) (.base "Term")
      (encodeTerm source) (encodeTerm target) :=
  lift_listed_shape RelationEnv.empty language FreeTypeContext.empty
    (contextTypes Γ) (.base "Term") _
    (all_rules_compile (contextTypes Γ)) shape
    (encodeTerm_hasType source) (encodeTerm_hasType target)

/-- Sorting adds premise-context and endpoint certificates without changing
the selected authored rule constructor. -/
theorem liftEncodedShape_raw {Γ : Ctx sig}
    (source target : Term sig Γ .term)
    (shape : RuleSkeleton RuleHistory RelationEnv.empty language
      (contextTypes Γ).length (encodeTerm source) (encodeTerm target)) :
    (liftEncodedShape source target shape).raw = shape := by
  exact lift_listed_shape_raw RelationEnv.empty language
    FreeTypeContext.empty (contextTypes Γ) (.base "Term") _
    (all_rules_compile (contextTypes Γ)) shape
    (encodeTerm_hasType source) (encodeTerm_hasType target)

/-- The actual two-level left-application firing has a corresponding
result-sorted constructor at precisely its encoded source and target. -/
theorem beta_under_appL_has_sorted_shape {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    ∃ shape : ResultSortedScopedOperationalPresentation.RuleShape
        RelationEnv.empty language FreeTypeContext.empty
        (contextTypes Γ) (.base "Term")
        (encodeTerm (appT (appT (lamT body) argument) outer))
        (encodeTerm (appT (inst body argument) outer)),
      shape.raw.ruleIndex = 2 := by
  have hlen : (contextTypes Γ).length = Γ.length := by
    simp [contextTypes]
  have executed :
      (.fire 2 [.step 0 0 (.fire 0 [])],
        encodeTerm (appT (inst body argument) outer)) ∈
      rewriteAt RelationEnv.empty language 2 (contextTypes Γ).length
        (encodeTerm (appT (appT (lamT body) argument) outer)) := by
    rw [hlen]
    exact beta_under_appL body argument outer
  obtain ⟨shape, _, historyEq, _⟩ :=
    runtime_has_shape_with_history RelationEnv.empty language 1
      (contextTypes Γ).length
      (encodeTerm (appT (appT (lamT body) argument) outer))
      (encodeTerm (appT (inst body argument) outer))
      (.fire 2 [.step 0 0 (.fire 0 [])]) executed
  refine ⟨liftEncodedShape _ _ shape, ?_⟩
  rw [liftEncodedShape_raw]
  injection historyEq with indexEq _
  exact indexEq.symm

/-- The distinct right-application event also admits the canonical sorted
constructor, with its own rule and child position retained by erasure. -/
theorem beta_under_appR_has_sorted_shape {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    ∃ shape : ResultSortedScopedOperationalPresentation.RuleShape
        RelationEnv.empty language FreeTypeContext.empty
        (contextTypes Γ) (.base "Term")
        (encodeTerm (appT outer (appT (lamT body) argument)))
        (encodeTerm (appT outer (inst body argument))),
      shape.raw.ruleIndex = 3 := by
  have hlen : (contextTypes Γ).length = Γ.length := by
    simp [contextTypes]
  have executed :
      (.fire 3 [.step 0 0 (.fire 0 [])],
        encodeTerm (appT outer (inst body argument))) ∈
      rewriteAt RelationEnv.empty language 2 (contextTypes Γ).length
        (encodeTerm (appT outer (appT (lamT body) argument))) := by
    rw [hlen]
    exact beta_under_appR body argument outer
  obtain ⟨shape, _, historyEq, _⟩ :=
    runtime_has_shape_with_history RelationEnv.empty language 1
      (contextTypes Γ).length
      (encodeTerm (appT outer (appT (lamT body) argument)))
      (encodeTerm (appT outer (inst body argument)))
      (.fire 3 [.step 0 0 (.fire 0 [])]) executed
  refine ⟨liftEncodedShape _ _ shape, ?_⟩
  rw [liftEncodedShape_raw]
  injection historyEq with indexEq _
  exact indexEq.symm

#print axioms liftEncodedShape
#print axioms liftEncodedShape_raw
#print axioms beta_under_appL_has_sorted_shape
#print axioms beta_under_appR_has_sorted_shape

end Mettapedia.OSLF.Binding.LambdaAuthoredResultSortedShapes
