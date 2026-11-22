import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectStore

/-! # Success records and admission-domain controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Step

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (P : Step X O State Firing)

def Success := (s : State) × {f : Firing s // P.Admits f}

/-- Each appended success contains the admission evidence of that event. -/
def successObserver : EventObserver (EffectCore.EventObject P.effectCore P.eventAdmission) where
  Data _ := List P.Success
  update {s} {_t} e past := past ++ [⟨s, ⟨e.firing,
    (P.eventAdmission_iff e.firing e.prepared).mp e.permitted⟩⟩]

theorem event_exists_iff {s t : State} :
    Nonempty (P.effectCore.Event P.eventAdmission s t) ↔
      ∃ (f : Firing s) (a : P.Admits f), P.result f a = t := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.firing, (P.eventAdmission_iff _ _).mp e.permitted, e.target_eq⟩
  · rintro ⟨f, a, rfl⟩
    exact ⟨P.event f a⟩

end Step

namespace EventControls

open PreparedStep.Controls

theorem prepared : guarded.step.Prepares (s := ()) () :=
  ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨(), id, Frames.models_nil _⟩⟩

/-- Top admission is a different policy, not an implementation of the guarded language. -/
def unfiltered : guarded.step.effectCore.Admission := fun _ _ => True

def unfilteredEvent : guarded.step.effectCore.Event unfiltered () () :=
  ⟨(), prepared, True.intro, rfl⟩

theorem guarded_event_absent :
    ¬ Nonempty (guarded.step.effectCore.Event guarded.step.eventAdmission () ()) := by
  rintro ⟨e⟩
  exact guarded_refused ((guarded.step.eventAdmission_iff e.firing e.prepared).mp e.permitted)

/-- The same prepared data is available without fabricating a guard-success receipt. -/
theorem distinct_admission_domains :
    Nonempty (guarded.step.effectCore.Event unfiltered () ()) ∧
    ¬ Nonempty (guarded.step.effectCore.Event guarded.step.eventAdmission () ()) :=
  ⟨⟨unfilteredEvent⟩, guarded_event_absent⟩

abbrev restricted := guarded.step.withDisequations guarded_reflects

def admittedEvent := restricted.event apart apart_admitted

def admittedPath : @Quiver.Path
    (EffectCore.EventObject restricted.effectCore restricted.eventAdmission) _
    start (restricted.result apart apart_admitted) :=
  Quiver.Path.cons Quiver.Path.nil admittedEvent

theorem receipt_after_admission :
    restricted.successObserver.evaluate admittedPath [] = [⟨start, ⟨apart, apart_admitted⟩⟩] := rfl

theorem decorated_erases :
    restricted.successObserver.forget.mapPath
      (restricted.successObserver.decorate admittedPath []) = admittedPath :=
  restricted.successObserver.forget_decorate admittedPath []

end EventControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
