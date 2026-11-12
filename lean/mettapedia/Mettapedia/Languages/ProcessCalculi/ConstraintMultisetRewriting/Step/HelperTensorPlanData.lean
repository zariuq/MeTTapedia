import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorDomain

/-! # Constructing actual helper tensor plans from their exact domain -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

def RebasePlan.ofAggregate {left right : State S O} (place : ContextPlacement left right) (run : helperStep.Run left)
    (checked : (run.word = [] ∨ (Frames.contextual S).Solvable place.state.knowledge) ∧ OutputsAvoid run right.present) :
    RebasePlan S O place run :=
  ContextualRunInterpretation.Plan.ofChecks contextualRunInterpretation place run
    ((shared_checks_iff place run).mpr ((rebase_checks_iff_aggregate place run).mpr checked))

def TensorPlan.ofDomain {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) (domain : TensorDomain place first second) :
    TensorPlan place first second := by
  obtain ⟨work, firstFresh, secondFresh⟩ := domain
  let leftPlan := RebasePlan.ofAggregate place first ⟨work.imp And.left id, firstFresh⟩
  let one := RebasePlan.realize place first leftPlan
  have solved : (Frames.contextual S).Solvable one.target.swap.state.knowledge ↔
      (Frames.contextual S).Solvable place.state.knowledge :=
    one.target.swapIso.solvable_iff.trans (RebasePlan.target_solvable_iff place first leftPlan)
  have later : second.word = [] ∨ (Frames.contextual S).Solvable one.target.swap.state.knowledge :=
    work.elim (fun empty => Or.inl empty.2) (fun initial => Or.inr (solved.mpr initial))
  exact ⟨leftPlan, RebasePlan.ofAggregate one.target.swap second ⟨later, secondFresh⟩⟩

theorem TensorPlan.target_solvable_iff {left right : State S O} {place : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right} (plan : TensorPlan place first second) :
    (Frames.contextual S).Solvable (TensorPlan.realize plan).target.state.knowledge ↔
      (Frames.contextual S).Solvable place.state.knowledge := by
  let one := RebasePlan.realize place first plan.leftPlan
  let two := RebasePlan.realize one.target.swap second plan.rightPlan
  exact two.target.swapIso.solvable_iff.trans
    ((RebasePlan.target_solvable_iff one.target.swap second plan.rightPlan).trans
      (one.target.swapIso.solvable_iff.trans (RebasePlan.target_solvable_iff place first plan.leftPlan)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
