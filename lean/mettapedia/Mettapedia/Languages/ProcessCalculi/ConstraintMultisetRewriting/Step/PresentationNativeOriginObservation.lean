import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOriginRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-!
# Origin records commute with reference erasure

The passive key observer is pulled back along the source interpretation.
Its records therefore commute on complete runs and lift uniquely. Erasing
origin keys is a different operation: two permitted aliases of one native
event prevent this observer from descending to the base step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Interface

variable {S : Signature} {O : Type} [DecidableEq O] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {Γ : Ctx S} {sort : S.Srt}
  (catalogue : Catalogue (S := S) (O := O) (Γ := Γ) (sort := sort))
  (authorized : (s : NativeState S O Γ sort) → Nat → NativeFiring s → Prop)

def originObserver : EventObserver
    (EffectCore.EventObject (profile catalogue authorized).effectCore (profile catalogue authorized).eventAdmission) where
  Data _ := List Nat
  update event record := record ++ [event.firing.origin]

def referenceObserver : EventObserver (SourceObject catalogue authorized) :=
  (originObserver catalogue authorized).comap (forgetReferences catalogue authorized)

theorem origin_records_commute {source target : SourceObject catalogue authorized}
    (path : Quiver.Path source target) (record : List Nat) :
    (referenceObserver catalogue authorized).evaluate path record =
      (originObserver catalogue authorized).evaluate ((forgetReferences catalogue authorized).mapPath path) record :=
  EventObserver.evaluate_comap (originObserver catalogue authorized) (forgetReferences catalogue authorized) path record

theorem origin_record_unique (source : (referenceObserver catalogue authorized).Observed)
    (path : Quiver.PathStar source.1) :
    ∃! lifted : Quiver.PathStar source,
      (referenceObserver catalogue authorized).forget.pathStar source lifted = path :=
  EventObserver.unique_lift _ source path

theorem source_readback_records_origin {source target : SourceObject catalogue authorized}
    (event : SourceEvent catalogue authorized source.state target.state) :
    QuoteReference.readTree? event.reference.tree =
      some ((forgetReferences catalogue authorized).map event).firing.origin := event.reference.read

theorem origin_observer_cannot_descend {source target : NativeState S O Γ sort}
    {first second : Nat} (different : first ≠ second)
    (event : (base (S := S) (O := O) (Γ := Γ) (sort := sort)).effectCore.Event
      base.eventAdmission source target)
    (resolvedFirst : catalogue source first = some event.firing.rule)
    (resolvedSecond : catalogue source second = some event.firing.rule)
    (allowedFirst : authorized source first event.firing) (allowedSecond : authorized source second event.firing) :
    ¬ ∃ update : base.effectCore.Event base.eventAdmission source target → List Nat,
      ∀ edge : SourceEvent catalogue authorized source target,
        update (edge.erase catalogue authorized) =
          (referenceObserver catalogue authorized).update (s := ⟨source⟩) (t := ⟨target⟩) edge [] := by
  rintro ⟨update, respects⟩
  obtain ⟨left, leftErase, leftOrigin⟩ := lift_native_event catalogue authorized first event resolvedFirst allowedFirst
  obtain ⟨right, rightErase, rightOrigin⟩ := lift_native_event catalogue authorized second event resolvedSecond allowedSecond
  have sameErase : left.erase catalogue authorized = right.erase catalogue authorized := leftErase.trans rightErase.symm
  have sameRecords := (respects left).symm.trans ((congrArg update sameErase).trans (respects right))
  change [left.event.firing.origin] = [right.event.firing.origin] at sameRecords
  rw [leftOrigin, rightOrigin] at sameRecords
  exact different (List.singleton_inj.mp sameRecords)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins
