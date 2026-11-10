import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport

/-! # Existing escape publications as an admitted-event observer

Prepared publications remain payload data. The observer receives a successful
event and transports the previous public names before appending its publications
and relations. Its update agrees with the existing escaping step. This does not
assert transport laws for newly admitted events of a different profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Observation (Record)

universe uO uT uH uOcc uS uF uI uR

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO, uT, uH, uOcc, uS, uF, uI} P}

namespace Step

variable (P)

def observeRun (D : EventObserver.{uS, uF, uR}
    (EffectCore.EventObject P.effectCore P.eventAdmission)) :
    {s : State} → (run : P.Run s) → D.Data s → D.Data run.last
  | _, .nil _, data => data
  | _, .cons f admitted rest, data => observeRun D rest (D.update (P.event f admitted) data)

def observeRunEnd (D : EventObserver (EffectCore.EventObject P.effectCore P.eventAdmission))
    {s : State} (run : P.Run s) (data : D.Data s) : (t : State) × D.Data t :=
  ⟨run.last, P.observeRun D run data⟩

theorem observeRun_path (D : EventObserver (EffectCore.EventObject P.effectCore P.eventAdmission)) :
    ∀ {s : State} (run : P.Run s) (data : D.Data s),
      P.observeRun D run data = D.evaluate (run.eventPath P) data
  | _, .nil _, _ => rfl
  | _, .cons f admitted rest, data => by
      rw [Run.eventPath]
      exact (observeRun_path D rest (D.update (P.event f admitted) data)).trans
        (D.evaluate_comp (Quiver.Path.nil.cons (P.event f admitted)) (rest.eventPath P) data).symm

end Step

namespace Transport.Escape

variable (D : T.Escape)

def eventObserver : EventObserver (EffectCore.EventObject P.effectCore P.eventAdmission) where
  Data s := List (Tm (P.frame s)) × Record O
  update e past := e.target_eq ▸
    (past.1.map (X.act (P.effectCore.along e.firing e.prepared)) ++ D.publishes e.firing e.prepared,
      past.2 ++ D.records e.firing)

theorem eventObserver_agrees (x : Escaped P) (f : Firing x.state) (admitted : P.Admits f) :
    D.eventObserver.update (P.event f admitted) (x.names, x.record) =
      ((D.step.result (s := x) f admitted).names, (D.step.result (s := x) f admitted).record) := rfl

theorem eventObserver_run_agrees : ∀ {x : Escaped P} (run : D.step.Run x),
    P.observeRunEnd D.eventObserver (D.forget run) (x.names, x.record) =
      ⟨run.last.state, (run.last.names, run.last.record)⟩
  | _, .nil _ => rfl
  | x, .cons f admitted rest => by
      change P.observeRunEnd D.eventObserver (D.forget rest)
        (D.eventObserver.update (P.event f admitted) (x.names, x.record)) = _
      rw [D.eventObserver_agrees x f admitted]
      exact eventObserver_run_agrees rest

end Transport.Escape

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
