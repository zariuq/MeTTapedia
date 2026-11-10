import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventAccount
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-!
# Monoid accounts as admitted-event observers

The observer multiplies each admitted event's grade into its current record.
Its evaluation is the free-category account, in execution order. No
commutativity, enumeration of events or existence of an event is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

universe uO uT uH uOcc uS uF uM

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing) {M : Type uM} [Monoid M]
  (grade : (s : State) → Firing s → M)

def accountObserver : EventObserver (EffectCore.EventObject P.effectCore P.eventAdmission) where
  Data _ := M
  update {s} {_} event record := record * grade s event.firing

theorem accountObserver_evaluate {s t : EffectCore.EventObject P.effectCore P.eventAdmission}
    (path : Quiver.Path s t) (record : M) :
    (P.accountObserver grade).evaluate path record = record * P.pathAccount grade path := by
  induction path with
  | nil => simp [accountObserver, EventObserver.evaluate, pathAccount_nil]
  | cons path event ih =>
      let previous : M := (P.accountObserver grade).evaluate path record
      change previous * grade _ event.firing =
        record * P.pathAccount grade (path.cons event)
      rw [show previous = record * P.pathAccount grade path from ih, pathAccount_cons, mul_assoc]

theorem accountObserver_run {s : State} (run : P.Run s) (record : M) :
    (P.accountObserver grade).evaluate (run.eventPath P) record = record * run.account grade := by
  rw [accountObserver_evaluate, ← Run.account_eq_pathAccount]

theorem accountObserver_run_one {s : State} (run : P.Run s) :
    (P.accountObserver grade).evaluate (run.eventPath P) (1 : M) = run.account grade := by
  rw [accountObserver_run, one_mul]

theorem accountObserver_unique_lift (source : (P.accountObserver grade).Observed)
    (path : Quiver.PathStar source.1) :
    ∃! lifted : Quiver.PathStar source,
      (P.accountObserver grade).forget.pathStar source lifted = path :=
  EventObserver.unique_lift _ source path

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step
