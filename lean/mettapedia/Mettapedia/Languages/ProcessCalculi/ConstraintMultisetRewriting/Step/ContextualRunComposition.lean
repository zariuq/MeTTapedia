import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualRunNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence

/-!
# Sequential composition of contextual run interpretations

Local plans concatenate and retain their final placement. Interpreting that
concatenation is similar to composing the actual native executions with the
proved endpoint transport. Hence it agrees in the existing trace quotient.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ContextualRunInterpretation

universe uO uT uH uOcc uS uF uI uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)

def Plan.append : ∀ {left right : State} (place : I.Place left right) (run : P.Run left)
    (plan : I.Plan place run) (later : P.Run run.last),
    I.Plan (plan.realize I place run).target later → I.Plan place (run.append later)
  | _, _, _, .nil _, .nil _, _, continuation => continuation
  | _, _, place, .cons f allowed rest, .cons framed nativeAllowed tail, later, continuation =>
      .cons framed nativeAllowed (append (I.advance place f allowed) rest tail later continuation)

def Plan.sequentialExecution {left right : State} (place : I.Place left right) (run : P.Run left)
    (plan : I.Plan place run) (later : P.Run run.last)
    (continuation : I.Plan (plan.realize I place run).target later) : P.Run (I.pair place).state :=
  let one := plan.realize I place run
  let two := continuation.realize I one.target later
  one.execution.append (T.moveRun (T.symm one.resultIso) two.execution)

theorem Plan.append_target : ∀ {left right : State} (place : I.Place left right) (run : P.Run left)
    (plan : I.Plan place run) (later : P.Run run.last)
    (continuation : I.Plan (plan.realize I place run).target later),
    HEq ((plan.append I place run later continuation).realize I place (run.append later)).target
      (continuation.realize I (plan.realize I place run).target later).target
  | _, _, _, .nil _, .nil _, _, _ => HEq.rfl
  | _, _, place, .cons f allowed rest, .cons _ _ tail, later, continuation =>
      append_target (I.advance place f allowed) rest tail later continuation

theorem Plan.append_similar : ∀ {left right : State} (place : I.Place left right) (run : P.Run left)
    (plan : I.Plan place run) (later : P.Run run.last)
    (continuation : I.Plan (plan.realize I place run).target later),
    T.Similar ((plan.append I place run later continuation).realize I place (run.append later)).execution
      (plan.sequentialExecution I place run later continuation)
  | _, _, _, .nil _, .nil _, _, continuation =>
      Transport.Similar.moveRun (T.symm (T.refl _)) (continuation.realize I _ _).execution
  | _, _, place, .cons f allowed rest, .cons framed nativeAllowed tail, later, continuation => by
      let sourcePlace := I.advance place f allowed
      let one := tail.realize I sourcePlace rest
      let two := continuation.realize I one.target later
      let whole := (tail.append I sourcePlace rest later continuation).realize I sourcePlace (rest.append later)
      let step := I.resultIso place f allowed framed nativeAllowed
      let first := (Plan.cons framed nativeAllowed tail).realize I place (.cons f allowed rest)
      let moved := T.moveRun (T.symm first.resultIso) two.execution
      have induction := append_similar sourcePlace rest tail later continuation
      have suffixes : T.Similar (T.moveRun (T.symm one.resultIso) two.execution) moved :=
        Transport.Similar.trans
          (Transport.Similar.symm (Transport.Similar.moveRun (T.symm one.resultIso) two.execution))
          (Transport.Similar.moveRun (T.symm first.resultIso) two.execution)
      have composed := Transport.Similar.append (Transport.Similar.moveRun (T.symm step) one.execution) suffixes
      have tails := Transport.Similar.trans
        (Transport.Similar.symm (Transport.Similar.moveRun (T.symm step) whole.execution))
        (Transport.Similar.trans induction composed)
      exact Transport.Similar.cons_self tails

theorem Plan.append_trace {left right : State} (place : I.Place left right) (run : P.Run left)
    (plan : I.Plan place run) (later : P.Run run.last)
    (continuation : I.Plan (plan.realize I place run).target later) :
    T.TraceEquiv (I.pair place).state
      ((plan.append I place run later continuation).realize I place (run.append later)).execution
      (plan.sequentialExecution I place run later continuation) :=
  .rel _ _ (.inr (Plan.append_similar I place run plan later continuation))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ContextualRunInterpretation
