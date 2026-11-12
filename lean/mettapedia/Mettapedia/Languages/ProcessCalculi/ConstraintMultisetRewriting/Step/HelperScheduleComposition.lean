import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorSchedule

/-! # Sequential composition of two-sided schedules and their actual runs -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

def append : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (_before : Schedule first second) {afterL : helperStep.Run first.last} {afterR : helperStep.Run second.last},
    Schedule afterL afterR → Schedule (first.append afterL) (second.append afterR)
  | _, _, _, _, .done _ _, _, _, after => after
  | _, _, _, _, .left f allowed tail, _, _, after => .left f allowed (append tail after)
  | _, _, _, _, .right g allowed tail, _, _, after => .right g allowed (append tail after)

theorem target_append : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (before : Schedule first second)
    {afterL : helperStep.Run first.last} {afterR : helperStep.Run second.last} (after : Schedule afterL afterR),
    HEq (target place (append before after)) (target (target place before) after)
  | _, _, _, _, _, .done _ _, _, _, _ => HEq.rfl
  | _, _, _, _, place, .left f _ tail, _, _, after => target_append (place.afterLeft f) tail after
  | _, _, _, _, place, .right g _ tail, _, _, after => target_append (place.afterRight g) tail after

def Plan.append : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (before : Schedule first second)
    {afterL : helperStep.Run first.last} {afterR : helperStep.Run second.last} (after : Schedule afterL afterR),
    Plan place before → Plan (target place before) after → Plan place (Schedule.append before after)
  | _, _, _, _, _, .done _ _, _, _, _, .done _, later => later
  | _, _, _, _, place, .left f _ tail, _, _, after, .left allowed before, later =>
      .left allowed (append (place.afterLeft f) tail after before later)
  | _, _, _, _, place, .right g _ tail, _, _, after, .right allowed before, later =>
      .right allowed (append (place.afterRight g) tail after before later)

def Plan.sequentialExecution {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (before : Schedule first second)
    {afterL : helperStep.Run first.last} {afterR : helperStep.Run second.last} (after : Schedule afterL afterR)
    (one : Plan place before) (two : Plan (target place before) after) : helperStep.Run place.state :=
  let firstResult := one.realize place before
  let secondResult := two.realize (target place before) after
  firstResult.execution.append (helperTransport.moveRun (helperTransport.symm firstResult.resultIso) secondResult.execution)

theorem Plan.append_similar : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (place : ContextPlacement left right) (before : Schedule first second)
    {afterL : helperStep.Run first.last} {afterR : helperStep.Run second.last} (after : Schedule afterL afterR)
    (one : Plan place before) (two : Plan (target place before) after),
    helperTransport.Similar ((one.append place before after two).realize place (Schedule.append before after)).execution
      (one.sequentialExecution place before after two)
  | _, _, _, _, _, .done _ _, _, _, _, .done _, two =>
      Transport.Similar.moveRun (helperTransport.symm (helperTransport.refl _)) (two.realize _ _).execution
  | _, _, _, _, place, .left f localAllowed tail, _, _, after, .left allowed before, two => by
      let one := before.realize (place.afterLeft f) tail
      let later := two.realize (target (place.afterLeft f) tail) after
      let whole := (before.append (place.afterLeft f) tail after two).realize (place.afterLeft f) (Schedule.append tail after)
      let step := helperTransport.symm (place.left_result_iso f)
      let firstResult := (Plan.left (allowed := localAllowed) allowed before).realize place (.left f localAllowed tail)
      have induction := append_similar (place.afterLeft f) tail after before two
      have suffixes := Transport.Similar.trans
        (Transport.Similar.symm (Transport.Similar.moveRun (helperTransport.symm one.resultIso) later.execution))
        (Transport.Similar.moveRun (helperTransport.symm firstResult.resultIso) later.execution)
      have composed := Transport.Similar.append (Transport.Similar.moveRun step one.execution) suffixes
      exact Transport.Similar.cons_self
        (Transport.Similar.trans (Transport.Similar.symm (Transport.Similar.moveRun step whole.execution))
          (Transport.Similar.trans induction composed))
  | _, _, _, _, place, .right g localAllowed tail, _, _, after, .right allowed before, two => by
      let one := before.realize (place.afterRight g) tail
      let later := two.realize (target (place.afterRight g) tail) after
      let whole := (before.append (place.afterRight g) tail after two).realize (place.afterRight g) (Schedule.append tail after)
      let step := helperTransport.symm (place.right_result_iso g)
      let firstResult := (Plan.right (allowed := localAllowed) allowed before).realize place (.right g localAllowed tail)
      have induction := append_similar (place.afterRight g) tail after before two
      have suffixes := Transport.Similar.trans
        (Transport.Similar.symm (Transport.Similar.moveRun (helperTransport.symm one.resultIso) later.execution))
        (Transport.Similar.moveRun (helperTransport.symm firstResult.resultIso) later.execution)
      have composed := Transport.Similar.append (Transport.Similar.moveRun step one.execution) suffixes
      exact Transport.Similar.cons_self
        (Transport.Similar.trans (Transport.Similar.symm (Transport.Similar.moveRun step whole.execution))
          (Transport.Similar.trans induction composed))

theorem target_rightOnly : ∀ {left right : State S O} (place : ContextPlacement left right) (run : helperStep.Run right),
    target place (rightOnly left run) = place.advanceRight run
  | _, _, _, .nil _ => rfl
  | _, _, place, .cons g _ rest => target_rightOnly (place.afterRight g) rest

theorem target_leftFirst : ∀ {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right),
    target place (leftFirst first second) = (place.advanceLeft first).advanceRight second
  | _, _, place, .nil _, second => target_rightOnly place second
  | _, _, place, .cons f _ rest, second => target_leftFirst (place.afterLeft f) rest second

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule
