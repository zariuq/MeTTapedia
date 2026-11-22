import Mettapedia.CategoryTheory.FinitePowerset
import Mettapedia.GSLT.Topos.PresheafEventAbsence
import Mettapedia.TypeTheory.PresheafEventNativeLogic

/-!
# Complete finite successor sets and proof-retaining native events

A contextual successor system maps each complete finite successor set by
direct image. This exact equation permits collisions but excludes new
successors. Its events retain a supplied occurrence identifier and an actual
selected successor. Source fibres, dependent certificates and native absence
are formed through the shared event logic. Availability reflection is derived
from the complete successor equation; a forward simulation alone is weaker.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafFiniteSuccessorEvents

open _root_.CategoryTheory
open PresheafEventCertificates
open Mettapedia.GSLT.Topos

universe u
variable {C : Type u} [Category.{u} C]
variable (P : Cᵒᵖ ⥤ Type u) (Actions : Type u)

/-- An actual labelled coalgebra with complete direct-image substitution. -/
structure System where
  successors : (world : Cᵒᵖ) → P.obj world → Actions → Finset (P.obj world)
  map_successors : ∀ {world future : Cᵒᵖ} (change : world ⟶ future)
    (source : P.obj world) (action : Actions),
    successors future (P.map change source) action =
      Mettapedia.CategoryTheory.FinitePowerset.map (P.map change)
        (successors world source action)

namespace System

variable {P Actions} (system : System P Actions)
variable {Origins : Type u}

@[ext] structure Event (Origins : Type u) (action : Actions) (world : Cᵒᵖ) where
  origin : Origins
  source : P.obj world
  target : P.obj world
  valid : target ∈ system.successors world source action

def mapEvent {Origins : Type u} {action : Actions} {world future : Cᵒᵖ}
    (change : world ⟶ future) (event : system.Event Origins action world) :
    system.Event Origins action future where
  origin := event.origin
  source := P.map change event.source
  target := P.map change event.target
  valid := by
    rw [system.map_successors]
    exact (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mpr
      ⟨event.target, event.valid, rfl⟩

def events (Origins : Type u) (action : Actions) : Cᵒᵖ ⥤ Type u where
  obj world := system.Event Origins action world
  map change := ↾(system.mapEvent change)
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Event.ext
    · rfl
    · exact Functor.map_id_apply P world event.source
    · exact Functor.map_id_apply P world event.target
  map_comp before after := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Event.ext
    · rfl
    · exact Functor.map_comp_apply P before after event.source
    · exact Functor.map_comp_apply P before after event.target

def span (Origins : Type u) (action : Actions) : EventSpan P P where
  events := system.events Origins action
  source := { app := fun _ => ↾Event.source }
  target := { app := fun _ => ↾Event.target }

abbrev SourceFibre (Origins : Type u) (action : Actions) (world : Cᵒᵖ)
    (source : P.obj world) :=
  {event : system.Event Origins action world // event.source = source}

def sourceFibreEquiv (Origins : Type u) (action : Actions) (world : Cᵒᵖ)
    (source : P.obj world) :
    system.SourceFibre Origins action world source ≃
      Origins × {target : P.obj world // target ∈ system.successors world source action} where
  toFun edge := ⟨edge.val.origin, ⟨edge.val.target, by
    simpa only [edge.property] using edge.val.valid⟩⟩
  invFun pair := ⟨⟨pair.1, source, pair.2.val, pair.2.property⟩, rfl⟩
  left_inv edge := by
    apply Subtype.ext
    apply Event.ext
    · rfl
    · exact edge.property.symm
    · rfl
  right_inv _ := rfl

def enabled (Origins : Type u) (action : Actions) : Subfunctor P :=
  PresheafEventAbsence.enabled (system.span Origins action).source ⊤

def absent (Origins : Type u) (action : Actions) : Subfunctor P :=
  PresheafEventAbsence.absent (system.span Origins action).source ⊤

/-- A supplied identifier and selected successor introduce actual availability;
this operation does not choose or manufacture an identifier. -/
theorem enabled_of_member (origin : Origins) (action : Actions) (world : Cᵒᵖ)
    (source target : P.obj world) (member : target ∈ system.successors world source action) :
    source ∈ (system.enabled Origins action).obj world :=
  ⟨⟨origin, source, target, member⟩, trivial, rfl⟩

theorem enabled_iff [Nonempty Origins] (action : Actions) (world : Cᵒᵖ)
    (source : P.obj world) :
    source ∈ (system.enabled Origins action).obj world ↔
      (system.successors world source action).Nonempty := by
  constructor
  · rintro ⟨event, _, same⟩
    change event.source = source at same
    exact ⟨event.target, by simpa only [same] using event.valid⟩
  · rintro ⟨target, member⟩
    exact ⟨⟨Classical.choice ‹Nonempty Origins›, source, target, member⟩, trivial, rfl⟩

/-- Complete future successors supply an earlier successor even when the
context map identifies distinct values. The supplied future event's
occurrence identifier is retained. -/
theorem reflects_availability (action : Actions) :
    PresheafEventAbsence.ReflectsAvailability (system.span Origins action).source ⊤ := by
  intro world future change source event _ over
  change event.source = P.map change source at over
  have member : event.target ∈ system.successors future (P.map change source) action := by
    simpa only [over] using event.valid
  rw [system.map_successors] at member
  obtain ⟨target, present, _⟩ :=
    (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mp member
  exact ⟨⟨event.origin, source, target, present⟩, trivial, rfl⟩

theorem absent_iff_empty [Nonempty Origins] (action : Actions) (world : Cᵒᵖ)
    (source : P.obj world) :
    source ∈ (system.absent Origins action).obj world ↔
      system.successors world source action = ∅ := by
  rw [absent, PresheafEventAbsence.absent_iff_present _ _
    (system.reflects_availability (Origins := Origins) action)]
  change (¬ source ∈ (system.enabled Origins action).obj world) ↔ _
  rw [system.enabled_iff]
  exact Finset.not_nonempty_iff_eq_empty

/-- Present emptiness is stable for the exact complete successor action. -/
theorem empty_substitution {world future : Cᵒᵖ} (change : world ⟶ future)
    (source : P.obj world) (action : Actions) :
    system.successors future (P.map change source) action = ∅ ↔
      system.successors world source action = ∅ := by
  rw [system.map_successors]
  exact Mettapedia.CategoryTheory.FinitePowerset.map_eq_empty_iff _ _

end System
end Mettapedia.TypeTheory.PresheafFiniteSuccessorEvents
