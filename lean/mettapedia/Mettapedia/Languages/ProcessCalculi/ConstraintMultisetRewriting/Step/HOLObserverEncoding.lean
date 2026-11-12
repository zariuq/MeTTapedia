import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedRunEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-! # State-indexed records on complete HOL event packets

The raw carrier is inhabited, but a valid record retains its native state
index and data. Empty data fibres remain empty. Updating a packet checks its
retained firing, source, preparation and permission before applying the native
observer. Invalid or refused packets produce the invalid sentinel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverEncoding

open HOLPreparationEncoding HOLPreparedEffectEncoding HOLPreparedRunEncoding

universe uO uT uH uOcc uS uF uR

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)
  (allow : E.Admission) (D : EventObserver.{uS, uF, uR} (EffectCore.EventObject E allow))

abbrev RawRecord := Option D.Observed

def encode {s : State} (record : D.Data s) : RawRecord E allow D := some ⟨s, record⟩

def Valid (s : State) (raw : RawRecord E allow D) : Prop :=
  ∃ record : D.Data s, raw = encode E allow D record

theorem encode_injective (s : State) : Function.Injective (encode E allow D (s := s)) := by
  intro first second same
  exact eq_of_heq (Sigma.mk.inj (Option.some.inj same)).2

theorem wrong_source {s t : State} (different : s ≠ t) (record : D.Data s) :
    ¬Valid E allow D t (encode E allow D record) := by
  rintro ⟨other, same⟩
  exact different (congrArg Sigma.fst (Option.some.inj same))

noncomputable def update (event : RawEvent E) (record : RawRecord E allow D) : RawRecord E allow D := by
  classical
  exact match event.2, record with
  | some ⟨⟨s, firing⟩, prepared⟩, some ⟨actual, data⟩ =>
      if source : actual = s then
        if event.1 = some ⟨s, firing⟩ then
          if permitted : allow firing prepared.down then
            some ⟨E.preparedResult firing prepared.down,
              D.update ⟨firing, prepared.down, permitted, rfl⟩ (source ▸ data)⟩
          else none
        else none
      else none
  | _, _ => none

theorem update_event {s t : State} (event : E.Event allow s t) (record : D.Data s) :
    update E allow D (toPacket E event).val (encode E allow D record) =
      encode E allow D (D.update event record) := by
  cases event with
  | mk firing prepared permitted target =>
      cases target
      simp [update, encode, toPacket, encodeFiring, encodeWitness, permitted]

theorem evaluate_word {s t : EffectCore.EventObject E allow} (path : Quiver.Path s t)
    (record : D.Data s) :
    (word E allow path).foldl (fun prior event => update E allow D event prior)
      (encode E allow D record) = encode E allow D (D.evaluate path record) := by
  induction path with
  | nil => simp only [word, List.foldl_nil, EventObserver.evaluate]
  | cons path event ih =>
      simp only [word, List.foldl_append, List.foldl_cons, List.foldl_nil,
        EventObserver.evaluate, ih]
      exact update_event E allow D event _

theorem valid_fibre_iff (s : State) :
    (∃ raw, Valid E allow D s raw) ↔ Nonempty (D.Data s) := by
  constructor
  · rintro ⟨_, record, _⟩
    exact ⟨record⟩
  · rintro ⟨record⟩
    exact ⟨encode E allow D record, record, rfl⟩

theorem invalid_record (s : State) : ¬Valid E allow D s none := by
  rintro ⟨record, same⟩
  cases same

theorem update_valid {s t : State} (event : RawEvent E)
    (admitted : step E allow (some s) event (some t))
    {raw : RawRecord E allow D} (valid : Valid E allow D s raw) :
    Valid E allow D t (update E allow D event raw) := by
  obtain ⟨native, rfl⟩ := (step_iff_event E allow s t event).mp admitted
  obtain ⟨record, rfl⟩ := valid
  exact ⟨D.update native record, update_event E allow D native record⟩

theorem update_invalid_record (event : RawEvent E) : update E allow D event none = none := by
  rcases event with ⟨firing, prepared⟩
  cases prepared <;> simp [update]

theorem update_missing_preparation (firing : RawFirings State Firing) (record : RawRecord E allow D) :
    update E allow D (firing, none) record = none := by
  cases record <;> rfl

theorem update_refused {s : State} (firing : Firing s) (prepared : E.Prepares firing)
    (refused : ¬allow firing prepared) (record : D.Data s) :
    update E allow D
      (encodeFiring State Firing firing, encodeWitness State Firing (Witness E) firing prepared)
      (encode E allow D record) = none := by
  simp [update, encodeFiring, encodeWitness, encode, refused]

theorem no_valid_initial_record (s : State) (empty : ¬Nonempty (D.Data s)) :
    ¬∃ raw, Valid E allow D s raw := fun valid => empty ((valid_fibre_iff E allow D s).mp valid)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverEncoding
