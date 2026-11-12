import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperScheduleNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperScheduleOrders

/-!
# Adjacent schedule exchanges preserve the actual native trace

The proof uses the native two-event swap, equality with the actual residual
candidates, and source-compatible transport of the complete continuation.
Transitivity constructs intermediate admitted plans from the exact domain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

theorem native_here {left right : State S O} (place : ContextPlacement left right)
    (f : Firing left) (af : helperStep.Admits f) (g : Firing right) (ag : helperStep.Admits g)
    {restL : helperStep.Run f.after} {restR : helperStep.Run g.after} (tail : Schedule restL restR)
    (one : Plan place (.left f af (.right g ag tail))) (two : Plan place (.right g ag (.left f af tail))) :
    helperTransport.TraceEquiv place.state
      (one.realize place (.left f af (.right g ag tail))).execution
      (two.realize place (.right g ag (.left f af tail))).execution := by
  cases one with
  | left nativeF next =>
      cases next with
      | right nativeG tailLR =>
          cases two with
          | right nativeG0 next =>
              cases next with
              | left nativeF0 tailRL =>
                  let invF := helperTransport.symm (place.left_result_iso f)
                  let invG := helperTransport.symm (place.right_result_iso g)
                  let invFG := helperTransport.symm ((place.afterLeft f).right_result_iso g)
                  let invGF := helperTransport.symm ((place.afterRight g).left_result_iso f)
                  let leftTail := (tailLR.realize (place.afterLeftRight f g) tail).execution
                  let rightTail := (tailRL.realize (place.afterRightLeft f g) tail).execution
                  let liftF := helperTransport.result_move invF ((place.afterLeft f).rightFiring g) nativeG
                  let liftG := helperTransport.result_move invG ((place.afterRight g).leftFiring f) nativeF0
                  have leftMoves := Transport.Similar.trans (Transport.Similar.moveRun invFG leftTail)
                    (Transport.Similar.moveRun liftF (helperTransport.moveRun invFG leftTail))
                  have rightMoves := Transport.Similar.trans (Transport.Similar.moveRun invGF rightTail)
                    (Transport.Similar.moveRun liftG (helperTransport.moveRun invGF rightTail))
                  have middle := Plan.natural (place.afterBothIso f g) tail tailLR tailRL
                  have tails := Transport.Similar.trans (Transport.Similar.symm leftMoves)
                    (Transport.Similar.trans middle rightMoves)
                  exact .rel _ _ (.inl (Transport.SwapStep.here nativeF nativeG0
                    (place.right_after_left_residual f g nativeF).symm
                    ((helperTransport.admits_move invF ((place.afterLeft f).rightFiring g)).mpr nativeG)
                    (place.left_after_right_residual f g nativeG0).symm
                    ((helperTransport.admits_move invG ((place.afterRight g).leftFiring f)).mpr nativeF0) tails))

theorem Swap.native : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    {a b : Schedule first second} (_swapped : Swap a b) (place : ContextPlacement left right)
    (one : Plan place a) (two : Plan place b),
    helperTransport.TraceEquiv place.state (one.realize place a).execution (two.realize place b).execution
  | _, _, _, _, _, _, .here f af g ag tail, place, one, two => native_here place f af g ag tail one two
  | _, _, _, _, _, _, .left f _ swapped, place, .left _ap laterP, .left _aq laterQ =>
      ((native swapped (place.afterLeft f) laterP laterQ).moveRun
        (helperTransport.symm (place.left_result_iso f))).cons
  | _, _, _, _, _, _, .right g _ swapped, place, .right _ap laterP, .right _aq laterQ =>
      ((native swapped (place.afterRight g) laterP laterQ).moveRun
        (helperTransport.symm (place.right_result_iso g))).cons

theorem Equivalent.native {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    {a b : Schedule first second} (related : Equivalent first second a b)
    (place : ContextPlacement left right) (domain : TensorDomain place first second) :
    ∀ one : Plan place a, ∀ two : Plan place b,
      helperTransport.TraceEquiv place.state (one.realize place a).execution (two.realize place b).execution := by
  induction related with
  | rel _ _ swapped => exact fun one two => swapped.native place one two
  | refl schedule =>
      intro one two
      exact .rel _ _ (.inr (Plan.natural (PlacementIso.refl place) schedule one two))
  | symm _ _ _ ih => exact fun one two => .symm _ _ (ih two one)
  | trans a middle b _ _ ihLeft ihRight =>
      intro one two
      let intermediate := Plan.ofDomain place middle domain
      exact .trans _ _ _ (ihLeft one intermediate) (ihRight intermediate two)

theorem all_native_orders {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (a b : Schedule first second) (one : Plan place a) (two : Plan place b) :
    helperTransport.TraceEquiv place.state (one.realize place a).execution (two.realize place b).execution :=
  (all_orders_equivalent a b).native place (one.domain place a) one two

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule
