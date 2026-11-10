import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserver
import Mathlib.Combinatorics.Quiver.Covering

/-! # Unique observer lifting and change of event presentation

Forgetting an observer is bijective on outgoing edges at a fixed initial
record. Hence an entire run, not merely its final record, lifts uniquely.
Reindexing an observer along an event interpretation commutes with evaluating
every finite path. No observation is required at a refused candidate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventObserver

universe u v w u' v'

variable {V : Type u} [Quiver.{v} V] (D : EventObserver.{u, v, w} V)

theorem forget_star_injective (start : D.Observed) :
    Function.Injective (D.forget.star start) := by
  rintro ⟨⟨t, record⟩, ⟨event, recorded⟩⟩ ⟨⟨t', record'⟩, ⟨event', recorded'⟩⟩ same
  have endpoints := congrArg Sigma.fst same
  change t = t' at endpoints
  subst t'
  have events := eq_of_heq (Sigma.mk.inj same).2
  change event = event' at events
  subst event'
  have records : record = record' := recorded.symm.trans recorded'
  subst record'
  rfl

theorem forget_star_surjective (start : D.Observed) :
    Function.Surjective (D.forget.star start) := by
  rintro ⟨t, event⟩
  exact ⟨⟨⟨t, D.update event start.2⟩, ⟨event, rfl⟩⟩, rfl⟩

/-- A record at the starting state determines one complete decorated run. -/
theorem unique_lift (start : D.Observed) (path : Quiver.PathStar start.1) :
    ∃! lifted : Quiver.PathStar start, D.forget.pathStar start lifted = path := by
  have bijective : Function.Bijective (D.forget.pathStar start) :=
    ⟨Prefunctor.pathStar_injective _ D.forget_star_injective start,
     Prefunctor.pathStar_surjective _ D.forget_star_surjective start⟩
  exact bijective.existsUnique path

variable {W : Type u'} [Quiver.{v'} W]

/-- An observer on the target interprets source events through the given map. -/
def comap (interpretation : W ⥤q V) : EventObserver W where
  Data s := D.Data (interpretation.obj s)
  update event := D.update (interpretation.map event)

theorem evaluate_comap (interpretation : W ⥤q V) {s t : W}
    (path : Quiver.Path s t) (record : D.Data (interpretation.obj s)) :
    (D.comap interpretation).evaluate path record =
      D.evaluate (interpretation.mapPath path) record := by
  induction path with
  | nil => rfl
  | cons path event ih =>
      change D.update (interpretation.map event) ((D.comap interpretation).evaluate path record) = _
      rw [ih]
      rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventObserver
