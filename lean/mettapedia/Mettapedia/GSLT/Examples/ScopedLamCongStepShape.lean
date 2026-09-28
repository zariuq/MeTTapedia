import Mettapedia.OSLF.Syntax.ScopedStepShapes
import Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame

/-!
# An authored lambda firing has an oracle-independent scoped shape

The actual LamCong firing yields a rule shape with a child in the lambda's
one-variable context. The shape remains after forgetting the selected beta
evidence; an escaping target cannot inhabit any such shape.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedLamCongStepShape

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.Binding.ScopedStepShapes
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame

/-- The successful firing contributes an admissible shape at the correct
authored premise site, independently of the beta oracle's witness. -/
theorem authored_lamCong_has_step_shape :
    ∃ (spec : RuleBindingSpec) (captured completed : Assignment)
      (shape : StepShape lamCongRule spec 0 0 localStep.binders.length
        localStep.source localStep.target captured completed),
      lamCongRule.bindings = some spec ∧
      admittedFor lamCongRule spec = true ∧
      shape.childJudgment.1 = 1 := by
  obtain ⟨firing, spec, captured, completed, event, child,
      declared, admitted, _, _, _, _, childValid⟩ :=
    lamCong_firing_has_scoped_child
  let shape := shapeOfAdmitted childValid
  refine ⟨spec, captured, completed, shape, declared, admitted, ?_⟩
  simp [StepShape.childJudgment, localStep]

/-- A candidate referring to a second local variable cannot be an
admissible child shape under one declared binder. -/
theorem escaping_target_has_no_shape
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (source target : Pattern) (initial final : Assignment) :
    ¬ ∃ shape : StepShape rule spec 0 0 1
      source target initial final, shape.childTarget = .bvar 1 := by
  rintro ⟨shape, targetEq⟩
  have scopedEvidence := shape.targetScoped
  rw [targetEq] at scopedEvidence
  have escaping : (Pattern.bvar 1).isWellScopedAt 1 = false := by
    decide +kernel
  rw [escaping] at scopedEvidence
  cases scopedEvidence

/-- The authored LamCong shape itself admits two distinct selections with
the same endpoint. The selection ordinal is additional event information,
not a property of the oracle-independent shape. -/
theorem authored_shape_supports_distinct_occurrences :
    ∃ (spec : RuleBindingSpec) (captured completed : Assignment)
      (shape : StepShape lamCongRule spec 0 0 localStep.binders.length
        localStep.source localStep.target captured completed)
      (oracle : Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.StepOracle Unit)
      (first second : StepSelection oracle shape),
      first.ordinal = 0 ∧ second.ordinal = 1 ∧ first ≠ second := by
  obtain ⟨spec, captured, completed, shape, _, _, _⟩ :=
    authored_lamCong_has_step_shape
  obtain ⟨oracle, first, second, firstOrdinal, secondOrdinal,
      distinct⟩ := duplicate_selections_distinct shape ()
  exact ⟨spec, captured, completed, shape, oracle, first, second,
    firstOrdinal, secondOrdinal, distinct⟩

end Mettapedia.GSLT.Examples.ScopedLamCongStepShape
