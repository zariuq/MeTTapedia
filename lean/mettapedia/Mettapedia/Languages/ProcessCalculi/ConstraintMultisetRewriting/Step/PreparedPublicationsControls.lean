import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublications
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex

/-! # Inherited data, fresh success receipts and transport-domain controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace PreparedPublicationsControls

open PreparedStep.Controls

def payload : PreparedPublications guarded.step.effectCore where
  records _ := [Observation.Record.reference 0]
  names _ _ := [bit, no]

def inherited := payload.withDisequations guarded_reflects

theorem inherited_payload_available :
    inherited.names apart (EventControls.restricted.prepares apart_admitted) = [bit, no] ∧
      inherited.records apart = [Observation.Record.reference 0] := ⟨rfl, rfl⟩

/-- The transformed event publishes the inherited terms and its own success
receipt, while the base profile has no success event to inherit. -/
theorem new_receipt_without_base_receipt :
    (inherited.observer EventControls.restricted.eventAdmission).evaluate
      EventControls.admittedPath ([], []) = ([bit, no], [Observation.Record.reference 0]) ∧
    EventControls.restricted.successObserver.evaluate EventControls.admittedPath [] =
      [⟨start, ⟨apart, apart_admitted⟩⟩] ∧
    ¬ Nonempty (guarded.step.effectCore.Event guarded.step.eventAdmission () ()) :=
  ⟨rfl, EventControls.receipt_after_admission, EventControls.guarded_event_absent⟩

theorem inherited_observation_erases :
    (inherited.observer EventControls.restricted.eventAdmission).forget.mapPath
      ((inherited.observer EventControls.restricted.eventAdmission).decorate
        EventControls.admittedPath ([], [])) = EventControls.admittedPath :=
  EventObserver.forget_decorate _ _ _

end PreparedPublicationsControls

namespace PublicationTransportControls

open Presentation.Controls

/-- Two differently labelled candidates make the same real store update. -/
def program (allow : Store → Prop) : Step frame Nat Store (fun _ => Bool) :=
  (Step.ofEffect effect (fun {state} _ _ => allow state)).reindex (fun _ => ())

/-- This transport identifies the two labels because their operational effects
agree. It does not identify them in the free event category. -/
def transport (allow : Store → Prop) : Transport (program allow) where
  Iso s t := PLift (s = t)
  toStateIso i := i.down ▸ Step.StateIso.refl _
  refl _ := ⟨rfl⟩
  symm i := ⟨i.down.symm⟩
  trans i j := ⟨i.down.trans j.down⟩
  Alike _ _ := True
  alike_equivalence _ := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  selection_alike _ := rfl
  admits_alike _ := Iff.rfl
  result_alike _ _ _ := ⟨rfl⟩
  move _ f := f
  move_alike := by intros; trivial
  move_refl _ := trivial
  move_trans _ _ _ := trivial
  move_symm _ _ := trivial
  selection_move i _ := by
    rcases i with ⟨same⟩
    cases same
    exact (renameSelection_refl _).symm
  admits_move i _ := by
    rcases i with ⟨same⟩
    cases same
    rfl
  result_move i _ _ := by
    rcases i with ⟨same⟩
    cases same
    exact ⟨rfl⟩
  residual _ _ f := f
  selection_residual _ _ _ := rfl
  move_residual _ _ _ _ := trivial

def strict (state : Store) : Prop := (true, false) ∉ state

def permissive (_ : Store) : Prop := True

/-- The payload is defined everywhere, but reveals a candidate label only
where the original profile refuses execution. -/
def payload (allow : Store → Prop) : PreparedPublications (program allow).effectCore where
  records _ := []
  names {s} f _ := if (true, false) ∈ s then [f] else [false]

theorem strict_compatible : (payload strict).Compatible (transport strict) where
  records_move _ _ := rfl
  names_move i f admitted := by
    rcases i with ⟨same⟩
    cases same
    change List.Forall₂ Eq _ _
    exact List.forall₂_refl _
  records_alike _ := rfl
  names_alike {s} {_} {_} _ admitted _ := by
    obtain ⟨_, fresh⟩ := admitted
    change List.Forall₂ Eq (if _ then _ else _) (if _ then _ else _)
    simp only [if_neg fresh]
    exact List.forall₂_refl _

/-- The existing Escape construction consumes the profile-relative certificate. -/
def strictEscape : (transport strict).Escape :=
  (payload strict).toEscape (transport strict) strict_compatible
    (fun _ _ => none) (fun _ _ => .none)

theorem strict_escape_observation : strictEscape.eventObserver =
    (payload strict).observer (program strict).eventAdmission := rfl

theorem permissive_admits (f : Bool) : (program permissive).Admits (s := [(true, false)]) f :=
  ⟨Presentation.Controls.prepares [(true, false)] (), trivial⟩

/-- Total data and the base profile's transport laws do not establish the
transport law at newly admitted firings of a larger profile. -/
theorem total_payload_not_compatible : ¬ (payload permissive).Compatible (transport permissive) := by
  intro lawful
  have related := lawful.names_alike (f := true) (f' := false) True.intro
    (permissive_admits true) (permissive_admits false)
  change List.Forall₂ Eq [true] [false] at related
  cases related with
  | cons impossible _ => cases impossible

theorem same_data_different_obligation (state : Store) (f : Bool)
    (prepared : (program strict).Prepares (s := state) f) :
    (payload strict).names f prepared = (payload permissive).names f prepared := rfl

end PublicationTransportControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
