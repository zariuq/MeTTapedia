import Mettapedia.GSLT.Core.OperationalColimitStageFactorization
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Compiled stages compute the colimit's reachability

If every stage of a filtered diagram corresponds operationally to a target, then
a reachability observation holds in the colimit exactly when it holds in the
target of some later stage. The targets and their compiler are parameters, and
the targets need no maps between stages.

The observation is positive: some finite run reaches an observed state. Absence,
terminality, order and multiplicity are not transported.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open _root_.CategoryTheory
open scoped _root_.CategoryTheory

universe u v

variable {J : Type u} [SmallCategory J] [IsFilteredOrEmpty J]

/-- **Stagewise correspondence lifts to the colimit**, for any target. -/
theorem run_from_stage_iff (diagram : J ⥤ OperationalTheory.{u}) (targets : J → GSLT.{v})
    (compiled : ∀ stage, OperationalCorrespondence (diagram.obj stage).theory (targets stage))
    (observe : Term diagram → Prop) (observed : ∀ stage, (targets stage).Term → Prop)
    (agree : ∀ stage {origin current}, (compiled stage).related origin current →
      (observe (inject diagram stage origin) ↔ observed stage current))
    {site : J} (start : (diagram.obj site).theory.Term)
    (load : ∀ future, (site ⟶ future) → (targets future).Term)
    (loaded : ∀ future (route : site ⟶ future),
      (compiled future).related ((diagram.map route).mapTerm start) (load future route)) :
    (∃ finish, (theory diagram).MultiStep (inject diagram site start) finish ∧ observe finish) ↔
      ∃ future, ∃ route : site ⟶ future, ∃ final,
        (targets future).MultiStep (load future route) final ∧ observed future final := by
  constructor
  · rintro ⟨finish, path, holds⟩
    obtain ⟨future, route, after, stagePath, same⟩ := (multiStep_from_stage_iff diagram start finish).mp path
    subst same
    exact ⟨future, route, ((compiled future).reachable_iff (fun term => observe (inject diagram future term))
      (observed future) (agree future) (loaded future route)).mp ⟨after, stagePath, holds⟩⟩
  · rintro ⟨future, route, result⟩
    obtain ⟨after, stagePath, holds⟩ := ((compiled future).reachable_iff
      (fun term => observe (inject diagram future term)) (observed future) (agree future)
      (loaded future route)).mpr result
    exact ⟨_, (multiStep_from_stage_iff diagram start _).mpr ⟨future, route, after, stagePath, rfl⟩, holds⟩

#print axioms run_from_stage_iff

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
