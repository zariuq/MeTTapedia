import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedWords
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedRunEncoding

/-!
# Complete proposed words on actual native preparation packets

The word-domain checks use the existing indexed packet decoder and the
actual admission profile. Invalid raw values remain invalid. The result
fold itself does not inspect permission. A valid domain gives an existing
native event path, retaining the complete firing/preparation word.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordPackets

open Mettapedia.Languages.HOLLight.RunModelCorrespondence
open HOLPreparationEncoding HOLPreparedEffectEncoding HOLPreparedRunEncoding

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)

def preparation (source : States State) (event : RawEvent E) : Prop :=
  HOLPreparationEncoding.prepares State Firing (Witness E) source event.1 event.2

def result (_source : States State) (event : RawEvent E) : States State :=
  HOLPreparationEncoding.result State Firing (Witness E) (next E) event.2

def permission (allow : E.Admission) (_source : States State) (event : RawEvent E) : Prop :=
  HOLPreparationEncoding.permission State Firing (Witness E) (permits E allow) event.2

theorem step_iff (allow : E.Admission) (source destination : States State) (event : RawEvent E) :
    PreparedWords.step (preparation E) (result E) (permission E allow) source event destination ↔
      HOLPreparedRunEncoding.step E allow source event destination := by
  change (_ ∧ _ ∧ destination = result E source event) ↔ (_ ∧ destination = result E source event ∧ _)
  exact ⟨fun ⟨prepared, allowed, target⟩ => ⟨prepared, target, allowed⟩,
    fun ⟨prepared, target, allowed⟩ => ⟨prepared, allowed, target⟩⟩

theorem wordRun_iff (allow : E.Admission) (events : List (RawEvent E)) (source destination : States State) :
    WordRun (HOLPreparedRunEncoding.step E allow) events source destination ↔
      PreparedWords.Domain (preparation E) (result E) (permission E allow) events source ∧
        destination = PreparedWords.target (result E) events source := by
  have same : PreparedWords.step (preparation E) (result E) (permission E allow) =
      HOLPreparedRunEncoding.step E allow := by
    funext source event destination
    exact propext (step_iff E allow source destination event)
  rw [← same]
  exact PreparedWords.wordRun_iff _ _ _ _ _ _

theorem target_valid (allow : E.Admission) (events : List (RawEvent E)) (source : State)
    (domain : PreparedWords.Domain (preparation E) (result E) (permission E allow) events (some source)) :
    ∃ destination : State, PreparedWords.target (result E) events (some source) = some destination := by
  induction events generalizing source with
  | nil => exact ⟨source, rfl⟩
  | cons event events ih =>
      obtain ⟨prepared, allowed, rest⟩ := domain
      have admitted := (step_iff E allow (some source) (result E (some source) event) event).mp
        ⟨prepared, allowed, rfl⟩
      obtain ⟨_before, middle, _initial, nextEq⟩ := step_valid_endpoints E allow admitted
      have middleEq : result E (some source) event = some middle := nextEq
      rw [middleEq] at rest
      obtain ⟨destination, finalEq⟩ := ih middle rest
      exact ⟨destination, by simpa only [PreparedWords.target, middleEq] using finalEq⟩

theorem native_path_iff (allow : E.Admission) (events : List (RawEvent E)) (source destination : State) :
    (∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ source destination,
      HOLPreparedRunEncoding.word E allow path = events) ↔
        PreparedWords.Domain (preparation E) (result E) (permission E allow) events (some source) ∧
          some destination = PreparedWords.target (result E) events (some source) :=
  (HOLPreparedRunEncoding.finite_run_iff E allow events source destination).symm.trans
    (wordRun_iff E allow events (some source) (some destination))

theorem domain_iff_native_path_exists (allow : E.Admission) (events : List (RawEvent E)) (source : State) :
    PreparedWords.Domain (preparation E) (result E) (permission E allow) events (some source) ↔
      ∃ (destination : State) (path : @Quiver.Path (EffectCore.EventObject E allow) _ source destination),
        HOLPreparedRunEncoding.word E allow path = events := by
  constructor
  · intro domain
    obtain ⟨destination, finalEq⟩ := target_valid E allow events source domain
    obtain ⟨path, same⟩ := (native_path_iff E allow events source destination).mpr ⟨domain, finalEq.symm⟩
    exact ⟨destination, path, same⟩
  · rintro ⟨destination, path, same⟩
    exact ((native_path_iff E allow events source destination).mp ⟨path, same⟩).1

theorem packet_word_length (allow : E.Admission) {source destination : EffectCore.EventObject E allow}
    (path : Quiver.Path source destination) : (HOLPreparedRunEncoding.word E allow path).length = path.length := by
  induction path with
  | nil => simp [HOLPreparedRunEncoding.word]
  | cons path event ih => simp [HOLPreparedRunEncoding.word, ih]

theorem existing_run (P : Step X O State Firing) {source : State} (run : P.Run source) :
    PreparedWords.Domain (preparation P.effectCore) (result P.effectCore) (permission P.effectCore P.eventAdmission)
      (HOLPreparedRunEncoding.word P.effectCore P.eventAdmission (run.eventPath P)) (some source) ∧
      some run.last = PreparedWords.target (result P.effectCore)
        (HOLPreparedRunEncoding.word P.effectCore P.eventAdmission (run.eventPath P)) (some source) :=
  (native_path_iff P.effectCore P.eventAdmission _ source run.last).mp ⟨run.eventPath P, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordPackets
