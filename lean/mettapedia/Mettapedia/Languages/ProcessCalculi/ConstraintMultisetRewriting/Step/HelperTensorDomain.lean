import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunResources

/-!
# Symmetric definedness of the contextual-helper tensor

The selected left-then-right construction has a symmetric domain: initial
joint consistency when work occurs, fresh outputs against each other's old
resources, and disjoint output identities. The initial resource stores may
overlap. This profile therefore permits either selected order without making
one of them an ambient evaluation policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O]

theorem tensor_domain_iff_symmetric {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) :
    TensorDomain placed first second ↔
      (((first.word = [] ∧ second.word = []) ∨ (Frames.contextual S).Solvable placed.state.knowledge) ∧
        Disjoint (outputs first) right.present ∧ Disjoint (outputs second) left.present ∧
          Disjoint (outputs first) (outputs second)) := by
  rw [TensorDomain, outputsAvoid_iff_disjoint, outputsAvoid_iff_disjoint,
    present_last first, Finset.disjoint_union_right]
  rw [disjoint_comm (a := outputs second) (b := outputs first)]

theorem tensor_domain_swap {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) :
    TensorDomain placed first second ↔ TensorDomain placed.swap second first := by
  rw [tensor_domain_iff_symmetric, tensor_domain_iff_symmetric,
    placed.swapIso.solvable_iff, disjoint_comm (a := outputs second) (b := outputs first)]
  tauto

theorem reversed_plan_exists {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) (defined : TensorDomain placed first second) :
    Nonempty (TensorPlan placed.swap second first) :=
  (tensor_plan_iff_domain placed.swap second first).mpr ((tensor_domain_swap placed first second).mp defined)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
