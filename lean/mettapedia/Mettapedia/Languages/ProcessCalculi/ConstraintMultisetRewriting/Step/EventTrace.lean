import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TraceCategory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport

/-! # From free event paths to the existing trace quotient

The trace category receives each admitted event as its singleton run. The
extension from paths is functorial. An observation of arrows factors through
the quotient exactly when it respects the actual transport/trace relation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI uM

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO, uT, uH, uOcc, uS, uF, uI} P)

namespace Transport

local instance : Category T.StateClass := T.traceCategory

def eventGenerators : EffectCore.EventObject P.effectCore P.eventAdmission ⥤q T.StateClass where
  obj s := StateClass.mk T s
  map {s} {_t} e := Quot.mk _ {
    start := s
    run := Step.Run.cons e.firing ((P.eventAdmission_iff _ _).mp e.permitted) (.nil _)
    start_mem := rfl
    last_mem := congrArg (StateClass.mk T) e.target_eq }

def eventTraceFunctor : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ T.StateClass :=
  Paths.lift T.eventGenerators

theorem eventTraceFunctor_generators :
    Paths.of (EffectCore.EventObject P.effectCore P.eventAdmission) ⋙q
      T.eventTraceFunctor.toPrefunctor = T.eventGenerators := Paths.lift_spec _

theorem eventTraceFunctor_unique
    (F : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ T.StateClass)
    (agrees : Paths.of (EffectCore.EventObject P.effectCore P.eventAdmission) ⋙q
      F.toPrefunctor = T.eventGenerators) : F = T.eventTraceFunctor :=
  Paths.lift_unique _ _ agrees

namespace Trace

variable {M : Type uM} {x y : T.StateClass}

def observe (read : T.Arrow x y → M)
    (respects : ∀ a b, Arrow.Rel a b → read a = read b) : T.Trace x y → M :=
  Quot.lift read respects

theorem observation_exists_iff (read : T.Arrow x y → M) :
    (∃ observer : T.Trace x y → M, ∀ arrow, observer (Quot.mk _ arrow) = read arrow) ↔
      ∀ a b, Arrow.Rel a b → read a = read b := by
  constructor
  · rintro ⟨observer, agrees⟩ a b related
    rw [← agrees a, ← agrees b]
    exact congrArg observer (Quot.sound related)
  · intro respects
    exact ⟨observe T read respects, fun _ => rfl⟩

theorem observation_unique (read : T.Arrow x y → M)
    (respects : ∀ a b, Arrow.Rel a b → read a = read b)
    (observer : T.Trace x y → M)
    (agrees : ∀ arrow, observer (Quot.mk _ arrow) = read arrow) :
    observer = observe T read respects := by
  funext trace
  induction trace using Quot.inductionOn with
  | h arrow => exact agrees arrow

theorem no_observation_of_distinguished_related (read : T.Arrow x y → M)
    (a b : T.Arrow x y) (related : Arrow.Rel a b) (different : read a ≠ read b) :
    ¬ ∃ observer : T.Trace x y → M, ∀ arrow, observer (Quot.mk _ arrow) = read arrow := by
  intro factors
  exact different ((observation_exists_iff T read).mp factors a b related)

theorem length_respects (a b : T.Arrow x y) (related : Arrow.Rel a b) :
    a.run.word.length = b.run.word.length := by
  obtain ⟨middle, similar, equivalent⟩ := related
  exact (Similar.length_eq similar).trans (TraceEquiv.length_eq equivalent)

/-- Event count descends to the actual trace quotient. -/
def eventCount : T.Trace x y → Nat :=
  observe T (fun arrow => arrow.run.word.length) (length_respects T)

theorem eventCount_mk (arrow : T.Arrow x y) :
    eventCount T (Quot.mk _ arrow) = arrow.run.word.length := rfl

end Trace
end Transport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
