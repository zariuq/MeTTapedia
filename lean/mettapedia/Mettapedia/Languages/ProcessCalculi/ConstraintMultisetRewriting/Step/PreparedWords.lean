import Mettapedia.Languages.HOLLight.RunModelCorrespondence

/-!
# Exact domains of complete proposed event words

The result fold is available independently of permission. The domain checks
preparation and permission at each computed prefix. It characterizes the
existing finite word-run relation, rather than assuming that a run succeeds.
The event carrier may contain full indexed candidate and witness packets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.PreparedWords

open Mettapedia.Languages.HOLLight.RunModelCorrespondence

universe uS uE

variable {State : Type uS} {Event : Type uE}

def target (result : State → Event → State) : List Event → State → State
  | [], state => state
  | event :: events, state => target result events (result state event)

def Domain (prepare : State → Event → Prop) (result : State → Event → State)
    (allow : State → Event → Prop) : List Event → State → Prop
  | [], _ => True
  | event :: events, state => prepare state event ∧ allow state event ∧
      Domain prepare result allow events (result state event)

def step (prepare : State → Event → Prop) (result : State → Event → State)
    (allow : State → Event → Prop) (source : State) (event : Event) (destination : State) : Prop :=
  prepare source event ∧ allow source event ∧ destination = result source event

theorem target_append (result : State → Event → State) (first second : List Event) (state : State) :
    target result (first ++ second) state = target result second (target result first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons event events ih => exact ih (result state event)

theorem domain_append (prepare : State → Event → Prop) (result : State → Event → State)
    (allow : State → Event → Prop) (first second : List Event) (state : State) :
    Domain prepare result allow (first ++ second) state ↔
      Domain prepare result allow first state ∧ Domain prepare result allow second (target result first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append, Domain, target, true_and]
  | cons event events ih => simp only [List.cons_append, Domain, target, ih, and_assoc]

theorem wordRun_iff (prepare : State → Event → Prop) (result : State → Event → State)
    (allow : State → Event → Prop) (events : List Event) (source destination : State) :
    WordRun (step prepare result allow) events source destination ↔
      Domain prepare result allow events source ∧ destination = target result events source := by
  induction events generalizing source with
  | nil =>
      rw [WordRun.nil_iff]
      exact ⟨fun same => ⟨trivial, same.symm⟩, fun both => both.2.symm⟩
  | cons event events ih =>
      rw [WordRun.cons_iff]
      constructor
      · rintro ⟨middle, ⟨prepared, permitted, rfl⟩, rest⟩
        obtain ⟨domain, final⟩ := (ih _).mp rest
        exact ⟨⟨prepared, permitted, domain⟩, final⟩
      · rintro ⟨⟨prepared, permitted, domain⟩, final⟩
        exact ⟨result source event, ⟨prepared, permitted, rfl⟩, (ih _).mpr ⟨domain, final⟩⟩

theorem domain_iff_run_exists (prepare : State → Event → Prop) (result : State → Event → State)
    (allow : State → Event → Prop) (events : List Event) (source : State) :
    Domain prepare result allow events source ↔ ∃ destination, WordRun (step prepare result allow) events source destination := by
  constructor
  · intro domain
    exact ⟨target result events source, (wordRun_iff _ _ _ _ _ _).mpr ⟨domain, rfl⟩⟩
  · rintro ⟨destination, run⟩
    exact ((wordRun_iff _ _ _ _ _ _).mp run).1

theorem result_transport {OtherState : Type*} {OtherEvent : Type*}
    (states : OtherState ≃ State) (events : OtherEvent ≃ Event)
    (result : State → Event → State) (word : List Event) (source : State) :
    target (fun state event => states.symm (result (states state) (events event)))
      (word.map events.symm) (states.symm source) = states.symm (target result word source) := by
  induction word generalizing source with
  | nil => rfl
  | cons event word ih =>
      simpa only [List.map_cons, target, Equiv.apply_symm_apply] using ih (result source event)

theorem domain_transport {OtherState : Type*} {OtherEvent : Type*}
    (states : OtherState ≃ State) (events : OtherEvent ≃ Event)
    (prepare : State → Event → Prop) (result : State → Event → State) (allow : State → Event → Prop)
    (word : List Event) (source : State) :
    Domain (fun state event => prepare (states state) (events event))
      (fun state event => states.symm (result (states state) (events event)))
      (fun state event => allow (states state) (events event)) (word.map events.symm) (states.symm source) ↔
      Domain prepare result allow word source := by
  induction word generalizing source with
  | nil => rfl
  | cons event word ih =>
      simpa only [List.map_cons, Domain, Equiv.apply_symm_apply] using
        and_congr Iff.rfl (and_congr Iff.rfl (ih (result source event)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.PreparedWords
