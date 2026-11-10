import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTrace

/-!
# Complete runs under the event-to-trace interpretation

The free-category extension agrees with the existing run representative in
the trace quotient. This identifies the whole path image, not only the
singleton generators. Every lawful quotient readout therefore commutes with
the run/path comparison, including the concrete event-count readout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI uM

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

namespace Transport

local instance : Category T.StateClass := T.traceCategory

def runArrow {s : State} (run : P.Run s) : T.Arrow (StateClass.mk T s) (StateClass.mk T run.last) :=
  ⟨s, run, rfl, rfl⟩

def runTrace {s : State} (run : P.Run s) : T.Trace (StateClass.mk T s) (StateClass.mk T run.last) :=
  Quot.mk _ (T.runArrow run)

theorem runTrace_nil (s : State) : T.runTrace (Step.Run.nil s) = 𝟙 (StateClass.mk T s) := by
  apply Quot.sound
  apply Arrow.rel_of_similar
  apply similar_nil_nil.mpr
  exact (StateClass.mk_eq_mk_iff T).mp (Quotient.out_eq (StateClass.mk T s)).symm

theorem runTrace_append {s : State} (first : P.Run s) (second : P.Run first.last) :
    Trace.comp (T.runTrace first) (T.runTrace second) =
      Quot.mk _ (⟨s, first.append second, rfl,
        congrArg (StateClass.mk T) (Step.Run.last_append first second)⟩ :
          T.Arrow (StateClass.mk T s) (StateClass.mk T second.last)) := by
  apply Quot.sound
  apply Arrow.rel_of_similar
  exact Similar.append (Similar.refl first) (Similar.symm (Similar.moveRun _ second))

theorem eventTrace_run {s : State} (run : P.Run s) :
    T.eventTraceFunctor.map (run.eventPath P) = T.runTrace run := by
  induction run with
  | nil s => exact (T.runTrace_nil s).symm
  | cons firing admitted rest ih =>
      rw [Step.Run.eventPath]
      have single : T.eventTraceFunctor.map (Quiver.Path.nil.cons (P.event firing admitted)) =
          T.runTrace (Step.Run.cons firing admitted (.nil _)) := by
        exact (Paths.lift_toPath T.eventGenerators (P.event firing admitted)).trans rfl
      change T.eventTraceFunctor.map
        ((Quiver.Path.nil.cons (P.event firing admitted)) ≫ rest.eventPath P) = _
      rw [Functor.map_comp, single, ih]
      exact T.runTrace_append (Step.Run.cons firing admitted (.nil _)) rest

theorem eventTrace_endpoint {s t : State} (run : {r : P.Run s // r.last = t}) :
    T.eventTraceFunctor.map (P.endpointPath run) =
      Quot.mk _ (⟨s, run.val, rfl, congrArg (StateClass.mk T) run.property⟩ :
        T.Arrow (StateClass.mk T s) (StateClass.mk T t)) := by
  rcases run with ⟨run, ends⟩
  cases ends
  exact T.eventTrace_run run

theorem observation_eventTrace_run {M : Type uM} {s : State} (run : P.Run s)
    (read : T.Arrow (StateClass.mk T s) (StateClass.mk T run.last) → M)
    (respects : ∀ first second, Arrow.Rel first second → read first = read second) :
    Trace.observe T read respects (T.eventTraceFunctor.map (run.eventPath P)) = read (T.runArrow run) := by
  rw [T.eventTrace_run]
  rfl

theorem eventCount_eventTrace_run {s : State} (run : P.Run s) :
    Trace.eventCount T (T.eventTraceFunctor.map (run.eventPath P)) = run.word.length := by
  rw [T.eventTrace_run]
  rfl

end Transport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
