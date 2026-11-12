import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorInterchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorPlanData

/-!
# Exact composition domain of the two native tensor stages

Once the first tensor stage is admitted, admission of its second stage is
equivalent to the aggregate domain of the two concatenated local programs.
Consequently four-block interchange needs no separately assumed whole-tensor
plan: that plan is constructed from the two admitted stages.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

theorem outputs_append {source : State S O} (run : helperStep.Run source) (later : helperStep.Run run.last) :
    outputs (run.append later) = outputs run ∪ outputs later := by
  simp only [outputs, Step.Run.word_append, List.map_append, List.toFinset_append]

theorem TensorPlan.after_domain_iff_whole {left right : State S O} {place : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right}
    (before : TensorPlan place first second)
    (afterFirst : helperStep.Run first.last) (afterSecond : helperStep.Run second.last) :
    TensorDomain (TensorPlan.realize before).target afterFirst afterSecond ↔
      TensorDomain place (first.append afterFirst) (second.append afterSecond) := by
  obtain ⟨work, firstFresh, secondFresh, crossFresh⟩ :=
    (tensor_domain_iff_symmetric place first second).mp ((tensor_plan_iff_domain place first second).mp ⟨before⟩)
  rw [tensor_domain_iff_symmetric, tensor_domain_iff_symmetric, before.target_solvable_iff]
  simp only [Step.Run.word_append, List.append_eq_nil_iff, outputs_append, present_last,
    Finset.disjoint_union_left, Finset.disjoint_union_right]
  rw [disjoint_comm (a := outputs first) (b := outputs afterSecond),
    disjoint_comm (a := outputs afterFirst) (b := outputs second)]
  tauto

def TensorPlan.compose {left right : State S O} {place : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right}
    {afterFirst : helperStep.Run first.last} {afterSecond : helperStep.Run second.last}
    (before : TensorPlan place first second)
    (after : TensorPlan (TensorPlan.realize before).target afterFirst afterSecond) :
    TensorPlan place (first.append afterFirst) (second.append afterSecond) :=
  TensorPlan.ofDomain _ _ _ ((before.after_domain_iff_whole afterFirst afterSecond).mp
    ((tensor_plan_iff_domain _ _ _).mp ⟨after⟩))

theorem TensorPlan.four_block_compose {left right : State S O} {place : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right}
    {afterFirst : helperStep.Run first.last} {afterSecond : helperStep.Run second.last}
    (before : TensorPlan place first second)
    (after : TensorPlan (TensorPlan.realize before).target afterFirst afterSecond) :
    helperTransport.TraceEquiv place.state (before.sequentialExecution after)
      (TensorPlan.realize (before.compose after)).execution := before.four_block after (before.compose after)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
