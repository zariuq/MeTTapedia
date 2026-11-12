import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperSchedules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorDomain

/-!
# Every helper interleaving has the same exact admission domain

The domain is the existing tensor domain: initial joint consistency when work
occurs and the required cross-component output freshness. No additional order
test is needed for this profile. Empty raw schedules retain their identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

namespace ContextPlacement

theorem domain_left_iff {left right : State S O} (place : ContextPlacement left right)
    (f : Firing left) (allowed : helperStep.Admits f) (rest : helperStep.Run f.after) (other : helperStep.Run right) :
    TensorDomain place (.cons f allowed rest) other ↔
      helperStep.Admits (s := place.state) (place.leftFiring f) ∧ TensorDomain (place.afterLeft f) rest other := by
  rw [place.admitted_left_iff f allowed]
  simp only [TensorDomain, Step.Run.word, List.cons_ne_nil, false_and, false_or, outputsAvoid_cons]
  rw [place.after_left_solvable_iff f]
  tauto

theorem domain_right_iff {left right : State S O} (place : ContextPlacement left right)
    (g : Firing right) (allowed : helperStep.Admits g) (other : helperStep.Run left) (rest : helperStep.Run g.after) :
    TensorDomain place other (.cons g allowed rest) ↔
      helperStep.Admits (s := place.state) (place.rightFiring g) ∧ TensorDomain (place.afterRight g) other rest := by
  have admission := helperTransport.admits_move place.swapIso (place.swap.leftFiring g)
  rw [place.move_from_swap g] at admission
  exact (tensor_domain_swap place other (.cons g allowed rest)).trans
    ((place.swap.domain_left_iff g allowed rest other).trans
      (and_congr admission.symm (tensor_domain_swap (place.swap.afterLeft g) rest other)))

end ContextPlacement

namespace Schedule

def Plan.ofDomain : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (schedule : Schedule first second),
    TensorDomain place first second → Plan place schedule
  | _, _, _, _, place, .done _ _, _ => .done place
  | _, _, _, _, place, .left f allowed tail, domain =>
      .left (place.domain_left_iff f allowed _ _ |>.mp domain).1
        (ofDomain (place.afterLeft f) tail (place.domain_left_iff f allowed _ _ |>.mp domain).2)
  | _, _, _, _, place, .right g allowed tail, domain =>
      .right (place.domain_right_iff g allowed _ _ |>.mp domain).1
        (ofDomain (place.afterRight g) tail (place.domain_right_iff g allowed _ _ |>.mp domain).2)

theorem Plan.domain : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (schedule : Schedule first second),
    Plan place schedule → TensorDomain place first second
  | _, _, _, _, _, .done _ _, .done _ => by simp [TensorDomain, OutputsAvoid, Step.Run.word]
  | _, _, _, _, place, .left f allowed tail, .left native later =>
      (place.domain_left_iff f allowed _ _).mpr ⟨native, domain (place.afterLeft f) tail later⟩
  | _, _, _, _, place, .right g allowed tail, .right native later =>
      (place.domain_right_iff g allowed _ _).mpr ⟨native, domain (place.afterRight g) tail later⟩

theorem plan_iff_domain {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (schedule : Schedule first second) :
    Nonempty (Plan place schedule) ↔ TensorDomain place first second :=
  ⟨fun ⟨plan⟩ => plan.domain place schedule, fun domain => ⟨Plan.ofDomain place schedule domain⟩⟩

theorem Plan.length_preserved : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (schedule : Schedule first second) (plan : Plan place schedule),
    (plan.realize place schedule).execution.word.length = first.word.length + second.word.length
  | _, _, _, _, _, .done _ _, .done _ => rfl
  | _, _, _, _, place, .left f _ tail, .left allowed later => by
      have unchanged := Transport.Similar.length_eq
        (Transport.Similar.moveRun (helperTransport.symm (place.left_result_iso f)) (later.realize (place.afterLeft f) tail).execution)
      have count := length_preserved (place.afterLeft f) tail later
      change (helperTransport.moveRun (helperTransport.symm (place.left_result_iso f))
        (later.realize (place.afterLeft f) tail).execution).word.length + 1 = _
      rw [← unchanged, count]
      simp only [Step.Run.word, List.length_cons]
      omega
  | _, _, _, _, place, .right g _ tail, .right allowed later => by
      have unchanged := Transport.Similar.length_eq
        (Transport.Similar.moveRun (helperTransport.symm (place.right_result_iso g)) (later.realize (place.afterRight g) tail).execution)
      have count := length_preserved (place.afterRight g) tail later
      change (helperTransport.moveRun (helperTransport.symm (place.right_result_iso g))
        (later.realize (place.afterRight g) tail).execution).word.length + 1 = _
      rw [← unchanged, count]
      simp only [Step.Run.word, List.length_cons]
      omega

end Schedule
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
