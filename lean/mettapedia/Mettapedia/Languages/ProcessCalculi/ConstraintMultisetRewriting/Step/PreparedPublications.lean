import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeEvents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesStep

/-! # Prepared publications and their profile-relative transport laws

Publication data exists on prepared candidates. Observing it after a successful
event uses that event's admission evidence. A transformer may therefore inherit
the data even when its base profile refused the candidate. Equivariance is a
separate obligation for the transport of the target profile.

The compatibility certificate below constructs the existing escape layer; it
does not infer its laws from the mere existence of publication data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Observation (Record)

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

structure PreparedPublications (E : EffectCore X O State Firing) where
  records : {s : State} → Firing s → Record O
  names : {s : State} → (f : Firing s) → (p : E.Prepares f) →
    List (Tm (E.frame (E.preparedResult f p)))

namespace PreparedPublications

variable {E : EffectCore X O State Firing} (D : PreparedPublications E)

def observer (allow : E.Admission) : EventObserver (EffectCore.EventObject E allow) where
  Data s := List (Tm (E.frame s)) × Record O
  update e past := e.target_eq ▸
    (past.1.map (X.act (E.along e.firing e.prepared)) ++ D.names e.firing e.prepared,
      past.2 ++ D.records e.firing)

/-- Starting without publications records exactly the payload of this event. -/
theorem observe_event {allow : E.Admission} {s : State} (f : Firing s)
    (prepared : E.Prepares f) (permitted : allow f prepared) :
    (D.observer allow).update ⟨f, prepared, permitted, rfl⟩ ([], []) =
      (D.names f prepared, D.records f) := rfl

variable {P : Step X O State Firing}

/-- Laws are checked on the profile whose transport will actually use them.
In particular, `names_move` and `names_alike` range over its admitted firings. -/
structure Compatible (D : PreparedPublications P.effectCore)
    (T : Transport.{uO, uT, uH, uOcc, uS, uF, uI} P) : Prop where
  records_move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s),
    D.records (T.move i f) = Record.rename (T.toStateIso i).rename (D.records f)
  names_move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s) (admitted : P.Admits f),
    List.Forall₂ (fun u v => X.E (X.act (T.toStateIso (T.result_move i f admitted)).frame.hom u) v)
      (D.names f (P.prepares admitted))
      (D.names (T.move i f) (P.prepares ((T.admits_move i f).mpr admitted)))
  records_alike : ∀ {s : State} {f f' : Firing s}, T.Alike f f' → D.records f = D.records f'
  names_alike : ∀ {s : State} {f f' : Firing s} (alike : T.Alike f f')
      (admitted : P.Admits f) (admitted' : P.Admits f'),
    List.Forall₂ (fun u v => X.E (X.act (T.toStateIso
      (T.result_alike alike admitted admitted')).frame.hom u) v)
      (D.names f (P.prepares admitted)) (D.names f' (P.prepares admitted'))

/-- Install prepared payloads in the existing escape machinery only after
establishing the target transport's publication and row laws. -/
def toEscape (D : PreparedPublications P.effectCore)
    (T : Transport P) (compatible : D.Compatible T)
    (row : (s : State) → O → Option (Tm (P.frame s)))
    (row_iso : ∀ {s t : State} (i : T.Iso s t) (o : O),
      Option.Rel (X.Carried (T.toStateIso i).frame.hom (P.knowledge t)) (row s o)
        (row t ((T.toStateIso i).rename o))) : T.Escape where
  row := row
  row_iso := row_iso
  records := D.records
  publishes := D.names
  records_move := compatible.records_move
  publishes_move := compatible.names_move
  records_alike := compatible.records_alike
  publishes_alike := compatible.names_alike

theorem toEscape_observer (D : PreparedPublications P.effectCore)
    (T : Transport P) (compatible : D.Compatible T)
    (row : (s : State) → O → Option (Tm (P.frame s)))
    (row_iso : ∀ {s t : State} (i : T.Iso s t) (o : O),
      Option.Rel (X.Carried (T.toStateIso i).frame.hom (P.knowledge t)) (row s o)
        (row t ((T.toStateIso i).rename o))) :
    (D.toEscape T compatible row row_iso).eventObserver = D.observer P.eventAdmission := rfl

/-- Telling disequations preserves the underlying prepared publications. No
proof of the base profile's admission is requested or produced. -/
def withDisequations (D : PreparedPublications P.effectCore) [P.Guarded]
    (reflects : P.Reflects) : PreparedPublications (P.withDisequations reflects).effectCore where
  records f := D.records f.base
  names f p := D.names f.base ⟨p.1, p.2.1, DisequalityFrames.solvable_base p.2.2⟩

theorem withDisequations_names (D : PreparedPublications P.effectCore) [P.Guarded]
    (reflects : P.Reflects) {s : P.DState} (f : P.DFiring s)
    (p : (P.withDisequations reflects).Prepares f) :
    (D.withDisequations reflects).names f p =
      D.names f.base ⟨p.1, p.2.1, DisequalityFrames.solvable_base p.2.2⟩ := rfl

end PreparedPublications

namespace Transport.Escape

variable {P : Step X O State Firing} {T : Transport P} (D : T.Escape)

def publications : PreparedPublications P.effectCore := ⟨D.records, D.publishes⟩

theorem publications_compatible : D.publications.Compatible T :=
  ⟨D.records_move, D.publishes_move, D.records_alike, D.publishes_alike⟩

/-- Existing escape instances recover their data and laws without changing
their observation semantics. -/
theorem publications_recover :
    D.publications.toEscape T D.publications_compatible D.row D.row_iso = D := by
  cases D
  rfl

theorem publications_observer : D.publications.observer P.eventAdmission = D.eventObserver := rfl

end Transport.Escape

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
