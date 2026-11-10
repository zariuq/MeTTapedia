import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventAccount
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventEvaluationControls
import Mathlib.Algebra.FreeMonoid.Basic

/-! # Accounts retain event identity unless their grading forgets it

The existing evaluator produces two different admitted candidates with the
same nonidentity store effect. Word grading distinguishes them. A coarser
monoid homomorphism deliberately retains only the per-event cost.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.AccountControls

open Evaluation.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls (Store)

def wordGrade (_ : Store) (firing : Bool) : FreeMonoid Bool := FreeMonoid.of firing
def cost : FreeMonoid Bool →* Nat := FreeMonoid.lift (fun _ => 2)

theorem branch_account (label : Bool) :
    alternatives.pathAccount wordGrade ((branch label).run.eventPath alternatives) = FreeMonoid.of label := by
  rw [← Run.account_eq_pathAccount]
  rfl

theorem same_endpoints_distinct_accounts :
    (branch true).run.last = (branch false).run.last ∧
    alternatives.pathAccount wordGrade ((branch true).run.eventPath alternatives) ≠
      alternatives.pathAccount wordGrade ((branch false).run.eventPath alternatives) := by
  refine ⟨rfl, ?_⟩
  rw [branch_account, branch_account]
  exact fun same => Bool.noConfusion (FreeMonoid.of_injective same)

theorem regraded_cost_agrees (label : Bool) :
    alternatives.pathAccount (fun state firing => cost (wordGrade state firing))
      ((branch label).run.eventPath alternatives) = 2 := by
  rw [pathAccount_regrade, branch_account]
  rfl

theorem forgotten_label_not_recoverable :
    ¬ ∃ recover : Nat → Bool, ∀ label,
      recover (alternatives.pathAccount (fun state firing => cost (wordGrade state firing))
        ((branch label).run.eventPath alternatives)) = label := by
  rintro ⟨recover, exactLabel⟩
  have yes := exactLabel true
  have no := exactLabel false
  rw [regraded_cost_agrees] at yes no
  exact Bool.noConfusion (yes.symm.trans no)

#print axioms same_endpoints_distinct_accounts
#print axioms forgotten_label_not_recoverable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.AccountControls
