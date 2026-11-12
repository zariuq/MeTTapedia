import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Prepared event proposals and the fixed admission subquiver

A prepared edge retains the complete candidate and endpoint without a success
permission. The admitted subquiver is isomorphic, on its actual packets, to the
existing admitted-event quiver. Forgetting permission creates no success receipt.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore

open CategoryTheory

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

structure PreparedEvent (effect : EffectCore X O State Firing) (source target : State) where
  firing : Firing source
  prepared : effect.Prepares firing
  target_eq : effect.preparedResult firing prepared = target

def PreparedObject (_effect : EffectCore X O State Firing) := State

instance preparedQuiver (effect : EffectCore X O State Firing) : Quiver effect.PreparedObject where
  Hom source target := effect.PreparedEvent source target

variable (effect : EffectCore X O State Firing) (allow : effect.Admission)

def PreparedEvent.admit {source target : State} (event : effect.PreparedEvent source target)
    (permitted : allow event.firing event.prepared) : effect.Event allow source target :=
  ⟨event.firing, event.prepared, permitted, event.target_eq⟩

def Event.preparedEvent {source target : State} (event : effect.Event allow source target) :
    effect.PreparedEvent source target := ⟨event.firing, event.prepared, event.target_eq⟩

def admittedSubquiver : WideSubquiver effect.PreparedObject :=
  fun _ _ event => allow event.firing event.prepared

def admitGenerators : admittedSubquiver effect allow ⥤q effect.EventObject allow where
  obj state := state
  map event := PreparedEvent.admit effect allow event.val event.property

def retainGenerators : effect.EventObject allow ⥤q admittedSubquiver effect allow where
  obj state := state
  map event := ⟨Event.preparedEvent effect allow event, event.permitted⟩

theorem retain_admit {source target : admittedSubquiver effect allow} (event : source ⟶ target) :
    (retainGenerators effect allow).map ((admitGenerators effect allow).map event) = event := by
  rcases event with ⟨⟨firing, prepared, endpoint⟩, permitted⟩
  rfl

theorem admit_retain {source target : effect.EventObject allow} (event : source ⟶ target) :
    (admitGenerators effect allow).map ((retainGenerators effect allow).map event) = event := by
  cases event
  rfl

theorem event_exists_iff {source target : State} :
    Nonempty (effect.Event allow source target) ↔
      ∃ event : effect.PreparedEvent source target, allow event.firing event.prepared := by
  constructor
  · rintro ⟨event⟩
    exact ⟨Event.preparedEvent effect allow event, event.permitted⟩
  · rintro ⟨event, permitted⟩
    exact ⟨PreparedEvent.admit effect allow event permitted⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore
