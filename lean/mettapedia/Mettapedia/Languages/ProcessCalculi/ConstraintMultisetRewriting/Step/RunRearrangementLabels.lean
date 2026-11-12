import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunEventObservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangement
import Mettapedia.CategoryTheory.LabelledFiniteGroupoid
import Mathlib.CategoryTheory.EqToHom

/-!
# Declared event observations through composed native comparisons

Local observation laws on moved, alike and residual firings give a functor
to labelled finite event sets. Forgetting labels is exactly the already
constructed event-position functor. Thus the labels follow its actual
permutation through arbitrary composition and inversion, not merely through
one elementary swap.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.EventObservation

open _root_.CategoryTheory
open RunRearrangement
open Mettapedia.CategoryTheory

universe uO uT uH uOcc uS uF uI uL

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  {Label : Type uL} (observation : T.EventObservation Label)

def labelledObject {start : State} (run : P.Run start) : LabelledFinite.Object (Option Label) where
  size := run.word.length
  label event := (observation.labels run)[event.val]?

theorem labels_present {start : State} (run : P.Run start) (event : Fin run.word.length) :
    ∃ label, (observation.labelledObject run).label event = some label := by
  have inside : event.val < (observation.labels run).length := by
    simpa only [labels, List.length_map] using event.isLt
  exact ⟨(observation.labels run)[event.val], List.getElem?_eq_getElem inside⟩

def labelledMap {start : State} {first second : Object T start}
    (witness : Generator T first second) :
    LabelledFinite.Iso (observation.labelledObject first) (observation.labelledObject second) where
  positions := Generator.events T witness
  preserves := by
    intro event
    cases witness with
    | inl similar =>
        exact congrArg (fun values : List Label => values[event.val]?)
          (observation.labels_similarity similar).symm
    | inr interchange =>
        exact observation.labels_interchange interchange event.val

def labelledGenerators (start : State) : Object T start ⥤q LabelledFinite.Object (Option Label) where
  obj run := observation.labelledObject run
  map witness := observation.labelledMap witness

def labelledFunctor (start : State) : Groupoid T start ⥤ LabelledFinite.Object (Option Label) :=
  interpret T (observation.labelledGenerators start)

theorem generators_forget (start : State) :
    observation.labelledGenerators start ⋙q LabelledFinite.forget.toPrefunctor = eventGenerators T start := by
  apply Prefunctor.ext (fun _ => rfl)
  intro first second witness
  cases witness <;> rfl

theorem functor_forget (start : State) :
    observation.labelledFunctor start ⋙ LabelledFinite.forget = eventFunctor T start := by
  apply Quiver.FreeGroupoid.lift_unique (eventGenerators T start)
  rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc]
  have generators : Quiver.FreeGroupoid.of (Object T start) ⋙q
      (observation.labelledFunctor start).toPrefunctor = observation.labelledGenerators start :=
    Quiver.FreeGroupoid.lift_spec _
  rw [generators]
  exact observation.generators_forget start

theorem positions_eq {start : State} {first second : P.Run start} (cell : Cell T first second) :
    ((observation.labelledFunctor start).map cell).positions = events T cell := by
  have same := eq_of_heq (_root_.CategoryTheory.Functor.hcongr_hom
    (observation.functor_forget start) cell)
  exact congrArg (fun arrow : CoreHom (⟨Fin first.word.length⟩ : Core (Type))
      ⟨Fin second.word.length⟩ => arrow.iso.toEquiv) same

theorem labels_cell {start : State} {first second : P.Run start} (cell : Cell T first second)
    (event : Fin first.word.length) :
    (observation.labels second)[(events T cell event).val]? = (observation.labels first)[event.val]? := by
  have preserved := ((observation.labelledFunctor start).map cell).preserves event
  change (observation.labels second)[(((observation.labelledFunctor start).map cell).positions event).val]? =
      (observation.labels first)[event.val]? at preserved
  rw [observation.positions_eq cell] at preserved
  exact preserved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.EventObservation

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.EventObservation.functor_forget
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.EventObservation.labels_cell
