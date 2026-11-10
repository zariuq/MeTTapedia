import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory

/-! # Observation after admission

An observer updates data along edges of the event quiver. The data may depend
on the current state. Decoration lifts paths; forgetting decoration recovers
the complete original path. This construction does not extend observations
to refused preparations and does not claim erasure when observations control
which edges are available.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe u v w

structure EventObserver (V : Type u) [Quiver.{v} V] where
  Data : V → Type w
  update : {s t : V} → (s ⟶ t) → Data s → Data t

namespace EventObserver

variable {V : Type u} [Quiver.{v} V] (D : EventObserver.{u, v, w} V)

def evaluate {s : V} : {t : V} → Quiver.Path s t → D.Data s → D.Data t
  | _, .nil, data => data
  | _, .cons path event, data => D.update event (evaluate path data)

theorem evaluate_comp {s t r : V} (first : Quiver.Path s t) (second : Quiver.Path t r)
    (data : D.Data s) :
    D.evaluate (first.comp second) data = D.evaluate second (D.evaluate first data) := by
  induction second with
  | nil => simp [evaluate]
  | cons path event ih => simpa only [Quiver.Path.comp_cons, evaluate] using congrArg (D.update event) ih

abbrev Observed := (s : V) × D.Data s

structure Edge (first second : D.Observed) where
  event : first.1 ⟶ second.1
  recorded : D.update event first.2 = second.2

instance observedQuiver : Quiver D.Observed where
  Hom := D.Edge

def forget : D.Observed ⥤q V where
  obj x := x.1
  map edge := edge.event

def decorate {s : V} : {t : V} → (path : Quiver.Path s t) → (data : D.Data s) →
    @Quiver.Path D.Observed _ ⟨s, data⟩ ⟨t, D.evaluate path data⟩
  | _, .nil, _ => .nil
  | _, .cons path event, data => .cons (decorate path data) ⟨event, rfl⟩

theorem forget_decorate : ∀ {s t : V} (path : Quiver.Path s t) (data : D.Data s),
    D.forget.mapPath (D.decorate path data) = path
  | _, _, .nil, _ => by simp [decorate]
  | _, _, .cons path event, data => by
      simp only [decorate, Prefunctor.mapPath_cons, forget]
      exact congrArg (fun p => Quiver.Path.cons p event) (forget_decorate path data)

/-- Every decorated path's final data is determined by its base path and initial data. -/
theorem recorded_endpoint : ∀ {first second : D.Observed} (path : Quiver.Path first second),
    D.evaluate (D.forget.mapPath path) first.2 = second.2
  | _, _, .nil => by simp [Prefunctor.mapPath, evaluate]
  | _, _, .cons path edge => by
      simp only [Prefunctor.mapPath_cons, evaluate, forget]
      exact (congrArg (D.update edge.event) (recorded_endpoint path)).trans edge.recorded

/-- A fixed base path and initial record cannot produce two distinct final records. -/
theorem endpoint_unique {s t : V} (path : Quiver.Path s t) (start : D.Data s)
    (finish : D.Data t) (lifted : @Quiver.Path D.Observed _ ⟨s, start⟩ ⟨t, finish⟩)
    (erases : D.forget.mapPath lifted = path) : finish = D.evaluate path start := by
  have h := D.recorded_endpoint lifted
  rw [erases] at h
  exact h.symm

end EventObserver

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
