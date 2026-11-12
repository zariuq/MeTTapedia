import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperScheduleInterchange

/-!
# The schedule interpreter represents the existing selected tensor

The complete native executions are related through the actual profile's
similarity. This correspondence includes both the left run and the full
right run transported from its swapped source placement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

theorem Plan.rightOnly_similar : ∀ {left right : State S O} (place : ContextPlacement left right)
    (run : helperStep.Run right) (one : Plan place (rightOnly left run)) (two : RebasePlan S O place.swap run),
    helperTransport.Similar (one.realize place (rightOnly left run)).execution
      (helperTransport.moveRun place.swapIso (RebasePlan.realize place.swap run two).execution)
  | l, r, place, .nil _, one, two => by
      change Plan place (.done l r) at one
      cases one
      have same := ContextualRunInterpretation.Plan.unique contextualRunInterpretation two
        (ContextualRunInterpretation.Plan.nil (I := contextualRunInterpretation) (left := r) (right := l) place.swap)
      cases same
      exact ⟨helperTransport.refl place.state⟩
  | l, _, place, .cons g ag rest, one, two => by
      change Plan place (.right g ag (rightOnly l rest)) at one
      cases one with
      | right _allowed later =>
        obtain ⟨_framed, native, laterR, same⟩ := ContextualRunInterpretation.Plan.decompose contextualRunInterpretation two
        cases same
        let tailSchedule := (later.realize (place.afterRight g) (rightOnly _ rest)).execution
        let tailRebase := (RebasePlan.realize (place.swap.afterLeft g) rest laterR).execution
        let invRight := helperTransport.symm (place.right_result_iso g)
        let invLeft := helperTransport.symm (place.swap.left_result_iso g)
        let lifted := helperTransport.result_move place.swapIso (place.swap.leftFiring g) native
        have middle := rightOnly_similar (place.afterRight g) rest later laterR
        have fromSchedule := Transport.Similar.symm (Transport.Similar.moveRun invRight tailSchedule)
        have eraseRole := Transport.Similar.symm
          (Transport.Similar.moveRun (T := helperTransport) (place.afterRight g).swapIso tailRebase)
        have intoNative := Transport.Similar.trans (Transport.Similar.moveRun invLeft tailRebase)
          (Transport.Similar.moveRun lifted (helperTransport.moveRun invLeft tailRebase))
        exact ⟨helperTransport.refl place.state,
          (helperTransport.move_refl (place.rightFiring g)).trans (place.move_from_swap g).symm,
          Transport.Similar.trans fromSchedule
            (Transport.Similar.trans middle (Transport.Similar.trans eraseRole intoNative))⟩

theorem tensor_cons_similar {left right : State S O} (place : ContextPlacement left right)
    (f : Firing left) (allowed : helperStep.Admits f) (rest : helperStep.Run f.after) (other : helperStep.Run right)
    (framed : Disjoint f.selection.taken.toFinset right.present)
    (native : helperStep.Admits (s := place.state) (place.leftFiring f))
    (tail : RebasePlan S O (place.afterLeft f) rest)
    (rightPlan : RebasePlan S O (RebasePlan.realize (place.afterLeft f) rest tail).target.swap other) :
    helperTransport.Similar
      (TensorPlan.realize (⟨.cons framed native tail, rightPlan⟩ : TensorPlan place (.cons f allowed rest) other)).execution
      (.cons (place.leftFiring f) native (helperTransport.moveRun (helperTransport.symm (place.left_result_iso f))
        (TensorPlan.realize (⟨tail, rightPlan⟩ : TensorPlan (place.afterLeft f) rest other)).execution)) := by
  let one := RebasePlan.realize (place.afterLeft f) rest tail
  let two := RebasePlan.realize one.target.swap other rightPlan
  let wholeLeft := RebasePlan.realize place (.cons f allowed rest) (.cons framed native tail)
  let bridgeWhole := helperTransport.trans wholeLeft.target.swapIso (helperTransport.symm wholeLeft.resultIso)
  let bridgeTail := helperTransport.trans one.target.swapIso (helperTransport.symm one.resultIso)
  let invStep := helperTransport.symm (place.left_result_iso f)
  let tailTensor := TensorPlan.realize (⟨tail, rightPlan⟩ : TensorPlan (place.afterLeft f) rest other)
  have heads := Transport.Similar.symm (Transport.Similar.moveRun invStep one.execution)
  have ends := Transport.Similar.trans
    (Transport.Similar.symm (Transport.Similar.moveRun bridgeWhole two.execution))
    (Transport.Similar.moveRun bridgeTail two.execution)
  have compound := Transport.Similar.append heads ends
  have intoTail := Transport.Similar.moveRun invStep tailTensor.execution
  exact Transport.Similar.cons_self (Transport.Similar.trans compound intoTail)

theorem Plan.tensor_similar : ∀ {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right)
    (one : Plan place (leftFirst first second)) (two : TensorPlan place first second),
    helperTransport.Similar (one.realize place (leftFirst first second)).execution (TensorPlan.realize two).execution
  | _, _, place, .nil _, second, one, ⟨.nil _, rightPlan⟩ => by
      let raw := (RebasePlan.realize place.swap second rightPlan).execution
      let bridge := helperTransport.trans place.swapIso (helperTransport.symm (helperTransport.refl place.state))
      have fromSchedule := Plan.rightOnly_similar place second one rightPlan
      exact Transport.Similar.trans fromSchedule
        (Transport.Similar.trans (Transport.Similar.symm (Transport.Similar.moveRun (T := helperTransport) place.swapIso raw))
          (Transport.Similar.moveRun bridge raw))
  | _, _, place, .cons f allowed rest, second, one, two => by
      change Plan place (.left f allowed (leftFirst rest second)) at one
      cases one with
      | left native later =>
        cases two with
        | mk leftPlan rightPlan =>
          obtain ⟨framed, nativeR, tail, same⟩ := ContextualRunInterpretation.Plan.decompose contextualRunInterpretation leftPlan
          cases same
          let tailTensor : TensorPlan (place.afterLeft f) rest second := ⟨tail, rightPlan⟩
          let iso := helperTransport.symm (place.left_result_iso f)
          have middle := tensor_similar (place.afterLeft f) rest second later tailTensor
          have moved := Transport.Similar.trans
            (Transport.Similar.symm (Transport.Similar.moveRun iso (later.realize (place.afterLeft f) (leftFirst rest second)).execution))
            (Transport.Similar.trans middle (Transport.Similar.moveRun iso (TensorPlan.realize tailTensor).execution))
          have prefixed := Transport.Similar.cons_self (admitted := native) moved
          have selected := tensor_cons_similar place f allowed rest second framed nativeR tail rightPlan
          exact Transport.Similar.trans prefixed (Transport.Similar.symm selected)

theorem tensor_schedule_trace {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) (tensor : TensorPlan place first second)
    (schedule : Schedule first second) (plan : Plan place schedule) :
    helperTransport.TraceEquiv place.state (TensorPlan.realize tensor).execution (plan.realize place schedule).execution := by
  let canonical := Plan.ofDomain place (leftFirst first second) (plan.domain place schedule)
  have same := Plan.tensor_similar place first second canonical tensor
  exact .trans _ _ _ (.rel _ _ (.inr (Transport.Similar.symm same)))
    (all_native_orders place (leftFirst first second) schedule canonical plan)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule
