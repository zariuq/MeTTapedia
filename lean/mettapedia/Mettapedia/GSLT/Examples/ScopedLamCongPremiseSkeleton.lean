import Mettapedia.OSLF.Syntax.ScopedPremiseSkeleton
import Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame
import Mettapedia.GSLT.Examples.ScopedLamCongStepShape

/-!
# The authored LamCong premise has one oracle-independent child

The successful open-variable firing projects to an ordered premise skeleton.
Its only recursive child lives in the context of the lambda binder; the
firing and its selected event remain available separately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedLamCongPremiseSkeleton

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepShapes
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame
open Mettapedia.GSLT.Examples.ScopedLamCongStepShape

/-- The actual conditional firing has exactly one recursive child in the
premise's one-variable context after forgetting the selected beta evidence. -/
theorem authored_lamCong_has_one_skeleton_child :
    ∃ (firing : RuleFiring Unit) (spec : RuleBindingSpec)
      (captured completed : Assignment)
      (shape : RunSkeleton Unit RelationEnv.empty language
        lamCongRule spec 0 0 [.scopedStep localStep]
        captured completed),
      lamCongRule.bindings = some spec ∧
      admittedFor lamCongRule spec = true ∧
      firing ∈ applyRuleWithOracle betaOracle RelationEnv.empty language
        0 lamCongRule wrappedRedex ∧
      firing.target = wrappedTarget ∧
      ∃ childSource childTarget,
        shape.children = [(1, childSource, childTarget)] := by
  obtain ⟨firing, spec, captured, completed, event, child,
      declared, admitted, selected, targetEq, _, _, childValid⟩ :=
    lamCong_firing_has_scoped_child
  have wellScoped : localStep.isWellScopedAt 0 = true := by
    decide +kernel
  let stepShape := shapeOfAdmitted childValid
  let shape : RunSkeleton Unit RelationEnv.empty language
      lamCongRule spec 0 0 [.scopedStep localStep]
      captured completed :=
    .cons (.scopedStep wellScoped child.ordinal stepShape) .nil
  refine ⟨firing, spec, captured, completed, shape,
    declared, admitted, selected, targetEq,
    stepShape.childSource, stepShape.childTarget, ?_⟩
  simp [shape, RunSkeleton.children,
    PremiseSkeleton.child?, StepShape.childJudgment, localStep]

/-- The same authored scoped child judgment permits two distinct ordinal
labels. A free operational algebra can therefore retain two equal-endpoint
firings as different constructors. -/
theorem authored_lamCong_distinct_occurrence_labels :
    ∃ (spec : RuleBindingSpec) (captured completed : Assignment)
      (first second : PremiseSkeleton Unit RelationEnv.empty language
        lamCongRule spec 0 0 (.scopedStep localStep) captured completed),
      first.child? = second.child? ∧ first ≠ second := by
  obtain ⟨spec, captured, completed, stepShape, _, _, _⟩ :=
    authored_lamCong_has_step_shape
  have wellScoped : localStep.isWellScopedAt 0 = true := by
    decide +kernel
  let first : PremiseSkeleton Unit RelationEnv.empty language
      lamCongRule spec 0 0 (.scopedStep localStep) captured completed :=
    .scopedStep wellScoped 0 stepShape
  let second : PremiseSkeleton Unit RelationEnv.empty language
      lamCongRule spec 0 0 (.scopedStep localStep) captured completed :=
    .scopedStep wellScoped 1 stepShape
  refine ⟨spec, captured, completed, first, second, rfl, ?_⟩
  exact PremiseSkeleton.scopedStep_ordinals_distinct
    (Evidence := Unit) (relEnv := RelationEnv.empty) (lang := language)
    wellScoped stepShape (by decide)

end Mettapedia.GSLT.Examples.ScopedLamCongPremiseSkeleton
