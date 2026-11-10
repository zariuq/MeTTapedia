import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedEffectEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mettapedia.Languages.HOLLight.RunModelCorrespondence

/-!
# Complete prepared-event words and native paths

The unindexed event word retains both firing and preparation. Its step
relation checks source and result indices and the selected admission profile.
Finite words between valid encoded endpoints correspond in both directions
to paths of the native admitted-event quiver.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedRunEncoding

open HOLPreparationEncoding HOLPreparedEffectEncoding
open Mettapedia.Languages.HOLLight.RunModelCorrespondence

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)

abbrev RawEvent := RawFirings State Firing × RawPreparation E

def step (allow : E.Admission) (source : States State) (event : RawEvent E) (target : States State) : Prop :=
  prepares State Firing (Witness E) source event.1 event.2 ∧
    target = result State Firing (Witness E) (next E) event.2 ∧
    permission State Firing (Witness E) (permits E allow) event.2

theorem step_valid_endpoints (allow : E.Admission) {source target : States State} {event : RawEvent E}
    (valid : step E allow source event target) :
    ∃ s t : State, source = some s ∧ target = some t := by
  rcases event with ⟨firing, witness⟩
  cases witness with
  | none => cases valid.1
  | some entry =>
      rcases entry with ⟨⟨s, f⟩, p⟩
      exact ⟨s, next E s f p.down, valid.1.1, valid.2.1⟩

theorem step_iff_event (allow : E.Admission) (s t : State) (event : RawEvent E) :
    step E allow (some s) event (some t) ↔
      ∃ admitted : E.Event allow s t, (toPacket E admitted).val = event := by
  constructor
  · intro valid
    let packet : EventPacket E allow s t := ⟨event, valid⟩
    exact ⟨ofPacket E packet, congrArg Subtype.val (to_ofPacket E packet)⟩
  · rintro ⟨admitted, rfl⟩
    exact (toPacket E admitted).property

def word (allow : E.Admission) :
    ∀ {s t : EffectCore.EventObject E allow}, Quiver.Path s t → List (RawEvent E)
  | _, _, .nil => []
  | _, _, .cons path event => word allow path ++ [(toPacket E event).val]

theorem word_comp (allow : E.Admission) {s t u : EffectCore.EventObject E allow}
    (first : Quiver.Path s t) (second : Quiver.Path t u) :
    word E allow (first.comp second) = word E allow first ++ word E allow second := by
  induction second with
  | nil => simp [word]
  | cons path event ih => simp only [Quiver.Path.comp_cons, word, ih, List.append_assoc]

theorem path_word_run (allow : E.Admission) {s t : EffectCore.EventObject E allow}
    (path : Quiver.Path s t) : WordRun (step E allow) (word E allow path) (some s) (some t) := by
  induction path with
  | nil => simpa only [word] using (WordRun.nil (step := step E allow) (some s))
  | @cons t u path event ih =>
      simp only [word]
      apply WordRun.append_iff.mpr
      exact ⟨some t, ih, .cons (toPacket E event).property (.nil _)⟩

theorem word_run_path (allow : E.Admission) (events : List (RawEvent E)) (s t : State)
    (run : WordRun (step E allow) events (some s) (some t)) :
    ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ s t, word E allow path = events := by
  induction events generalizing s with
  | nil =>
      have same := Option.some.inj (WordRun.nil_iff.mp run)
      subst t
      exact ⟨.nil, by simp only [word]⟩
  | cons event events ih =>
      obtain ⟨middle, first, rest⟩ := WordRun.cons_iff.mp run
      obtain ⟨_, nextState, _, target⟩ := step_valid_endpoints E allow first
      subst middle
      obtain ⟨admitted, packet⟩ := (step_iff_event E allow s nextState event).mp first
      obtain ⟨path, words⟩ := ih nextState rest
      refine ⟨(Quiver.Path.cons Quiver.Path.nil admitted).comp path, ?_⟩
      rw [word_comp, words]
      simp only [word, List.nil_append, packet, List.singleton_append]

theorem finite_run_iff (allow : E.Admission) (events : List (RawEvent E)) (s t : State) :
    WordRun (step E allow) events (some s) (some t) ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ s t, word E allow path = events := by
  constructor
  · exact word_run_path E allow events s t
  · rintro ⟨path, rfl⟩
    exact path_word_run E allow path

theorem no_event_from_invalid (allow : E.Admission) (event : RawEvent E) (target : States State) :
    ¬ step E allow none event target := by
  intro valid
  obtain ⟨s, _, impossible, _⟩ := step_valid_endpoints E allow valid
  cases impossible

theorem no_event_to_invalid (allow : E.Admission) (source : States State) (event : RawEvent E) :
    ¬ step E allow source event none := by
  intro valid
  obtain ⟨_, t, _, impossible⟩ := step_valid_endpoints E allow valid
  cases impossible

/-- A raw reflexive path at the sentinel is not an encoded native state. The
finite-run correspondence deliberately requires valid endpoints. -/
theorem invalid_reflexive (allow : E.Admission) : WordRun (step E allow) [] none none := .nil _

theorem refused_nonempty (event : RawEvent E) (events : List (RawEvent E))
    (source target : States State) :
    ¬ WordRun (step E (fun _ _ => False)) (event :: events) source target := by
  intro run
  obtain ⟨middle, valid, _⟩ := WordRun.cons_iff.mp run
  rcases event with ⟨firing, witness⟩
  cases witness with
  | none => cases valid.1
  | some entry => exact valid.2.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedRunEncoding
