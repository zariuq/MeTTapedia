import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Readouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Controls.Progress

/-!
# Delivered success through computation and initialization

The two-instruction implementation has an intermediate state representing
source success before its result is delivered. The boot implementation adds
another phase. The delivery laws compose through those actual phases;
reporting success during boot instead violates reflection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Readouts

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational LoweringCanary
open Bridges.Readouts Controls.Progress

def sourceSuccess (_ : Unit) (state : Bool) : Prop := state = true
def middleSuccess (_ : Unit) (state : TargetState) : Prop := state = .finish
def deliveredSuccess (_ : Unit) (state : BootState) : Prop := state = .ready .finish

theorem lowering_delivery : Delivery correspondence sourceSuccess middleSuccess := by
  constructor
  · intro origin current related index observed
    change current = .finish at observed
    subst current
    exact related
  · intro origin current related index observed
    change origin = true at observed
    cases current with
    | start =>
        have zero : origin = false := related
        exact False.elim (Bool.false_ne_true (zero.symm.trans observed))
    | middle => exact ⟨.finish, .step TargetStep.second (.refl _), rfl⟩
    | finish => exact ⟨.finish, .refl _, rfl⟩

theorem boot_delivery : Delivery bootCorrespondence middleSuccess deliveredSuccess := by
  constructor
  · intro origin current related index observed
    change current = .ready .finish at observed
    subst current
    exact related
  · intro origin current related index observed
    change origin = .finish at observed
    cases current with
    | initial =>
        have same : TargetState.finish = .start := observed.symm.trans related
        cases same
    | ready state =>
        have same : state = .finish := (related : origin = state).symm.trans observed
        subst state
        exact ⟨.ready .finish, .refl _, rfl⟩

theorem staged_delivery : Delivery composed sourceSuccess deliveredSuccess :=
  lowering_delivery.comp boot_delivery

theorem success_reachable_iff :
    (∃ after, PositiveBlocks.source.MultiStep false after ∧ after = true) ↔
      ∃ after, booted.MultiStep BootState.initial after ∧ after = .ready .finish :=
  staged_delivery.reachable_iff composed_start ()

theorem delivered_after_three_instructions :
    completed.length = 3 ∧ deliveredSuccess () (.ready .finish) :=
  ⟨completed_has_three_steps, rfl⟩

/-- An initialization marker is not a delivered successful result. -/
theorem early_success_has_no_delivery :
    ¬ Delivery composed sourceSuccess
      (fun _ state => state = BootState.initial ∨ state = .ready .finish) := by
  intro invalid
  have wrong : sourceSuccess () false := invalid.reflects composed_start () (Or.inl rfl)
  exact Bool.false_ne_true wrong

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Readouts

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Readouts.staged_delivery
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Readouts.early_success_has_no_delivery
