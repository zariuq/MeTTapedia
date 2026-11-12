import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mathlib.CategoryTheory.Category.PartialFun

/-!
# The grade is a functor, and it is the only one

Runs are the free category on the admitted events. Fix the other state of a placement. One event
acts on the placements of its source: where the context is unchanged and the placed candidate is
admitted, it gives the advanced placement. This is a partial map, and by freeness it extends in
exactly one way to a functor from runs to partial maps.

* `gradeFunctor`: that functor.
* `mem_gradeFunctor_run`: on a run it is defined exactly on the grade, and its value is the
  placement the run leaves. So the grade of a composite run is not chosen: it is forced by the
  grade of one event.
* `gradeFunctor_unique`: every functor that agrees with it on single events is equal to it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T) (right : State)

/-- The action of one admitted event on the placements of its source. -/
def eventAction : {s t : State} → P.effectCore.Event P.eventAdmission s t →
    (I.Place s right →. I.Place t right)
  | _, _, ⟨f, prepared, permitted, rfl⟩ => fun place =>
      ⟨I.domain place f ∧ I.check place f,
        fun _ => I.advance place f ((P.eventAdmission_iff f prepared).mp permitted)⟩

/-- The event of an admitted firing acts by the one-step grade and the advanced placement. -/
theorem mem_eventAction {s : State} (f : Firing s) (allowed : P.Admits f)
    (place : I.Place s right) (final : I.Place (P.result f allowed) right) :
    final ∈ eventAction I right (P.event f allowed) place ↔
      (I.domain place f ∧ I.check place f) ∧ I.advance place f allowed = final := by
  show final ∈ (⟨I.domain place f ∧ I.check place f, fun _ => I.advance place f allowed⟩ :
    Part (I.Place (P.result f allowed) right)) ↔ _
  rw [Part.mem_mk_iff]
  exact ⟨fun ⟨graded, same⟩ => ⟨graded, same⟩, fun ⟨graded, same⟩ => ⟨graded, same⟩⟩

/-- The generators of the grade: a state goes to its placements, an event to its action. -/
def gradeGenerators : EffectCore.EventObject P.effectCore P.eventAdmission ⥤q PartialFun.{uP} where
  obj s := PartialFun.of (I.Place s right)
  map event := eventAction I right event

/-- **The grade functor**: the unique extension of the one-event action to runs. -/
def gradeFunctor : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ PartialFun.{uP} :=
  P.effectCore.interpret P.eventAdmission (gradeGenerators I right)

/-- The action of a run on the placements of its start. -/
def runAction {s : State} (run : P.Run s) : I.Place s right →. I.Place run.last right :=
  (gradeFunctor I right).map (run.eventPath P)

theorem runAction_nil (s : State) : runAction I right (Step.Run.nil (P := P) s) = PFun.id _ :=
  rfl

theorem runAction_cons {s : State} (f : Firing s) (allowed : P.Admits f)
    (rest : P.Run (P.result f allowed)) :
    runAction I right (.cons f allowed rest) =
      (runAction I right rest).comp (eventAction I right (P.event f allowed)) := by
  have split := (gradeFunctor I right).map_comp
    (X := (s : EffectCore.RunCategory P.effectCore P.eventAdmission))
    (Quiver.Hom.toPath (P.event f allowed)) (rest.eventPath P)
  have single : (gradeFunctor I right).map (Quiver.Hom.toPath (P.event f allowed)) =
      (gradeGenerators I right).map (P.event f allowed) :=
    Paths.lift_toPath (gradeGenerators I right) (P.event f allowed)
  rw [single] at split
  exact split

/-- **The grade functor is defined exactly on the grade, and gives the placement the run
leaves.** -/
theorem mem_gradeFunctor_run : ∀ {s : State} (run : P.Run s) (place : I.Place s right)
    (final : I.Place run.last right),
    final ∈ runAction I right run place ↔ I.Checks place run ∧ advanceRun I place run = final
  | _, .nil s, place, final => by
      rw [runAction_nil]
      show final ∈ Part.some place ↔ True ∧ place = final
      rw [Part.mem_some_iff]
      exact ⟨fun same => ⟨trivial, same.symm⟩, fun same => same.2.symm⟩
  | _, .cons f allowed rest, place, final => by
      rw [runAction_cons, PFun.comp_apply, Part.mem_bind_iff]
      constructor
      · rintro ⟨middle, reached, later⟩
        obtain ⟨graded, same⟩ := (mem_eventAction I right f allowed place middle).mp reached
        subst same
        obtain ⟨checked, ends⟩ := (mem_gradeFunctor_run rest _ final).mp later
        exact ⟨⟨graded, checked⟩, ends⟩
      · rintro ⟨⟨graded, checked⟩, ends⟩
        exact ⟨I.advance place f allowed,
          (mem_eventAction I right f allowed place _).mpr ⟨graded, rfl⟩,
          (mem_gradeFunctor_run rest _ final).mpr ⟨checked, ends⟩⟩

/-- The grade functor is defined at a placement exactly when the grade admits it. -/
theorem gradeFunctor_dom {s : State} (run : P.Run s) (place : I.Place s right) :
    (runAction I right run place).Dom ↔ I.Checks place run := by
  constructor
  · intro defined
    exact ((mem_gradeFunctor_run I right run place _).mp (Part.get_mem defined)).1
  · intro checked
    exact Part.dom_iff_mem.mpr ⟨_, (mem_gradeFunctor_run I right run place _).mpr ⟨checked, rfl⟩⟩

/-- **The grade functor is the only functor with the one-event grade.** -/
theorem gradeFunctor_unique
    (other : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ PartialFun.{uP})
    (agrees : Paths.of (EffectCore.EventObject P.effectCore P.eventAdmission) ⋙q
      other.toPrefunctor = gradeGenerators I right) :
    other = gradeFunctor I right :=
  Paths.lift_unique (gradeGenerators I right) other agrees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
