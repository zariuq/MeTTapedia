import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperScheduleComposition

/-!
# Four-block history interchange of the actual contextual tensor

The sequential tensor executions and the tensor of the local sequential
composites are related in the existing native trace quotient. The bridge
uses admitted schedule interpretation, its composition theorem and the
proved correspondence with TensorPlan.realize.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

def PlacementIso.ofEq {left right : State S O} {p q : ContextPlacement left right} (same : p = q) : PlacementIso p q :=
  same ▸ PlacementIso.refl p

def TensorPlan.sequentialExecution {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    {afterFirst : helperStep.Run first.last} {afterSecond : helperStep.Run second.last}
    {place : ContextPlacement left right} (before : TensorPlan place first second)
    (after : TensorPlan (TensorPlan.realize before).target afterFirst afterSecond) : helperStep.Run place.state :=
  let one := TensorPlan.realize before
  let two := TensorPlan.realize after
  one.execution.append (helperTransport.moveRun (helperTransport.symm one.resultIso) two.execution)

theorem TensorPlan.four_block {left right : State S O} {place : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right}
    {afterFirst : helperStep.Run first.last} {afterSecond : helperStep.Run second.last}
    (before : TensorPlan place first second)
    (after : TensorPlan (TensorPlan.realize before).target afterFirst afterSecond)
    (whole : TensorPlan place (first.append afterFirst) (second.append afterSecond)) :
    helperTransport.TraceEquiv place.state (before.sequentialExecution after) (TensorPlan.realize whole).execution := by
  let initial := Schedule.leftFirst first second
  let later := Schedule.leftFirst afterFirst afterSecond
  let one := Schedule.Plan.ofDomain place initial ((tensor_plan_iff_domain place first second).mp ⟨before⟩)
  let originalTarget := (TensorPlan.realize before).target
  let originalAfter := Schedule.Plan.ofDomain originalTarget later
    ((tensor_plan_iff_domain originalTarget afterFirst afterSecond).mp ⟨after⟩)
  have targetEq : Schedule.target place initial = originalTarget :=
    (Schedule.target_leftFirst place first second).trans (ContextPlacement.tensor_target place first second before).symm
  let mapping := PlacementIso.ofEq targetEq
  let two := Schedule.Plan.map mapping.symm later originalAfter
  let joined := one.append place initial later two
  let oneResult := one.realize place initial
  let twoResult := two.realize (Schedule.target place initial) later
  let nativeOne := TensorPlan.realize before
  let nativeTwo := TensorPlan.realize after
  have beforeSimilar := Schedule.Plan.tensor_similar place first second one before
  have afterSimilar := Transport.Similar.trans (Schedule.Plan.natural mapping later two originalAfter)
    (Schedule.Plan.tensor_similar originalTarget afterFirst afterSecond originalAfter after)
  have suffixes := Transport.Similar.trans
    (Transport.Similar.symm (Transport.Similar.moveRun (helperTransport.symm oneResult.resultIso) twoResult.execution))
    (Transport.Similar.trans afterSimilar
      (Transport.Similar.moveRun (helperTransport.symm nativeOne.resultIso) nativeTwo.execution))
  have sequentialSimilar := Transport.Similar.append beforeSimilar suffixes
  have composition := Schedule.Plan.append_similar place initial later one two
  have wholeTrace := Schedule.tensor_schedule_trace place (first.append afterFirst) (second.append afterSecond) whole
    (Schedule.append initial later) joined
  exact .symm _ _ (.trans _ _ _ wholeTrace
    (.trans _ _ _ (.rel _ _ (.inr composition)) (.rel _ _ (.inr sequentialSimilar))))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
