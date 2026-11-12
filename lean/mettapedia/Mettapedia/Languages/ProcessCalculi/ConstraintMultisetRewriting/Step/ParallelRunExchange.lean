import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunContinuation

/-!
# Interchange of two complete native runs

A plan supplies each event/run crossing and the endpoint isomorphism joining
the next suffix. The construction returns both actual composite executions,
their trace interchange and the separate event-count preservation laws.
The two inputs start at a common native state; contextual realization of
source-local component runs remains a separate interface obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

def RunInterchangePlan : {s : State} → P.Run s → P.Run s → Type (max uS uF uI)
  | _, _, .nil _ => PUnit
  | _, left, .cons g admitted right =>
      (crossing : T.Crossing left g admitted) ×
        (closings : crossing.Closings) ×
        (_connection : T.Iso (crossing.exchangeWith closings).residualRun.last
          (P.result (crossing.exchangeWith closings).residualFiring (crossing.exchangeWith closings).residualAdmitted)) ×
          RunInterchangePlan (crossing.exchangeWith closings).residualRun right

structure ParallelExchange {s : State} (left right : P.Run s) where
  afterLeft : P.Run left.last
  afterRight : P.Run right.last
  afterLeft_length : afterLeft.word.length = right.word.length
  afterRight_length : afterRight.word.length = left.word.length
  interchange : T.TraceEquiv s (right.append afterRight) (left.append afterLeft)

variable {T}

def RunInterchangePlan.exchange : ∀ {s : State} {left right : P.Run s},
    T.RunInterchangePlan left right → T.ParallelExchange left right
  | _, left, .nil _, _ => by
      refine ⟨.nil _, left, rfl, rfl, ?_⟩
      change T.TraceEquiv _ left (left.append (.nil _))
      rw [Step.Run.append_nil]
      exact .refl _
  | s, left, .cons g admitted right, ⟨crossing, closings, connection, tail⟩ => by
      let head := crossing.exchangeWith closings
      let later := tail.exchange
      let moved := T.moveRun connection later.afterLeft
      let lastEvent : P.Run left.last := .cons head.residualFiring head.residualAdmitted (.nil _)
      let suffix := Step.Run.castStart (left.last_append lastEvent).symm moved
      refine ⟨.cons head.residualFiring head.residualAdmitted moved, later.afterRight, ?_, ?_, ?_⟩
      · have unchanged := Similar.length_eq (Similar.moveRun connection later.afterLeft)
        change moved.word.length + 1 = right.word.length + 1
        rw [← unchanged, later.afterLeft_length]
      · exact later.afterRight_length.trans head.length_preserved
      · have continuation : T.Similar later.afterLeft suffix :=
          Similar.trans (Similar.moveRun connection later.afterLeft) (Similar.castStart _ moved)
        have continued := head.interchange.append_right continuation
        have association := Step.Run.append_castStart left lastEvent moved
        have finish : T.TraceEquiv s
            (.cons g admitted (head.residualRun.append later.afterLeft))
            (left.append (.cons head.residualFiring head.residualAdmitted moved)) :=
          Eq.mp (congrArg (fun ending => T.TraceEquiv s
            (.cons g admitted (head.residualRun.append later.afterLeft)) ending) association) continued
        exact .trans _ _ _ later.interchange.cons finish

theorem ParallelExchange.same_endpoint {s : State} {left right : P.Run s}
    (result : T.ParallelExchange left right) :
    T.Same result.afterRight.last result.afterLeft.last := by
  have same := result.interchange.same_last
  simpa only [Step.Run.last_append] using same

theorem ParallelExchange.total_length {s : State} {left right : P.Run s}
    (result : T.ParallelExchange left right) :
    (left.append result.afterLeft).word.length = left.word.length + right.word.length := by
  simp only [Step.Run.word_append, List.length_append, result.afterLeft_length]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport
