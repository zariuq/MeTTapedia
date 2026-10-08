import Mettapedia.GSLT.Core.ProgrammableSpace

/-!
# Admitted origins and reachable programmable spaces

Public structure constructors can describe sessions that were never launched.
`Started` restricts spaces to actual execution histories from a stored list
with no sessions. Both source admission at each retained origin and soundness
of the recorded source/policy events follow from this reachability condition.
The stored list may change; admission remains attached to its original source
occurrence rather than being silently reinterpreted at a later store.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ProgrammableSpace

universe u

/-- Admission is about the retained source occurrence and request. -/
def AdmittedSession {Atom : Type u} {language : Language Atom}
    {policy : Policy language} (session : Session language policy) : Prop :=
  language.admit session.origin.atom session.request

variable {Atom Tag : Type u} (languages : Tag → Language Atom)
  (policies : (tag : Tag) → Policy (languages tag))

def WellStarted (space : Space languages policies) : Prop :=
  ∀ work ∈ space.pending, AdmittedSession work.2

def Started (space : Space languages policies) : Prop :=
  ∃ atoms, Relation.ReflTransGen (Action languages policies) ⟨atoms, [], []⟩ space

theorem initial_started (atoms : List Atom) :
    Started languages policies ⟨atoms, [], []⟩ :=
  ⟨atoms, Relation.ReflTransGen.refl⟩

theorem action_started {before after : Space languages policies}
    (action : Action languages policies before after)
    (started : Started languages policies before) : Started languages policies after := by
  obtain ⟨atoms, execution⟩ := started
  exact ⟨atoms, execution.tail action⟩

theorem step_started {before after : Space languages policies}
    (step : Step languages policies before after)
    (started : Started languages policies before) : Started languages policies after :=
  action_started languages policies (.execute step) started

theorem start_started (space : Space languages policies) (tag : Tag)
    (scope : (languages tag).Scope) (state : (policies tag).State)
    (position : Fin space.atoms.length) (request : (languages tag).Request)
    (admitted : Admitted languages policies space tag position request)
    (started : Started languages policies space) :
    Started languages policies
      (start languages policies space tag scope state position request admitted) :=
  action_started languages policies (.launch space tag scope state position request admitted) started

theorem initial_well_started (atoms : List Atom) :
    WellStarted languages policies ⟨atoms, [], []⟩ := by
  intro work member
  cases member

theorem start_well_started (space : Space languages policies) (tag : Tag)
    (scope : (languages tag).Scope) (state : (policies tag).State)
    (position : Fin space.atoms.length) (request : (languages tag).Request)
    (admitted : Admitted languages policies space tag position request)
    (wellStarted : WellStarted languages policies space) :
    WellStarted languages policies
      (start languages policies space tag scope state position request admitted) := by
  intro work member
  change work ∈ space.pending ++ [_] at member
  rw [List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact wellStarted work old
  · exact admitted

theorem step_well_started {before after : Space languages policies}
    (step : Step languages policies before after)
    (wellStarted : WellStarted languages policies before) :
    WellStarted languages policies after := by
  cases step with
  | fire tag atoms nextAtoms front back history session receipt next nextPolicy source permitted =>
      intro work member
      change work ∈ front ++ _ :: back at member
      rw [List.mem_append, List.mem_cons] at member
      rcases member with inFront | rfl | inBack
      · exact wellStarted work (List.mem_append_left _ inFront)
      · exact wellStarted ⟨tag, session⟩
          (List.mem_append_right _ List.mem_cons_self)
      · exact wellStarted work (List.mem_append_right _ (List.mem_cons_of_mem _ inBack))

theorem action_well_started {before after : Space languages policies}
    (action : Action languages policies before after)
    (wellStarted : WellStarted languages policies before) :
    WellStarted languages policies after := by
  cases action with
  | launch tag scope state position request admitted =>
      exact start_well_started languages policies before tag scope state position request
        admitted wellStarted
  | execute step => exact step_well_started languages policies step wellStarted

theorem started_well_started (space : Space languages policies)
    (started : Started languages policies space) : WellStarted languages policies space := by
  obtain ⟨atoms, execution⟩ := started
  induction execution with
  | refl => exact initial_well_started languages policies atoms
  | tail _ action previous => exact action_well_started languages policies action previous

theorem started_sound_history (space : Space languages policies)
    (started : Started languages policies space) : SoundHistory languages policies space := by
  obtain ⟨atoms, execution⟩ := started
  induction execution with
  | refl => intro record member; cases member
  | tail _ action previous => exact action_history_sound languages policies action previous

/-- A retained session with a rejected origin cannot be a result of launching
and executing the declared source languages. -/
theorem rejected_session_not_started (space : Space languages policies) (tag : Tag)
    (session : Session (languages tag) (policies tag))
    (present : ⟨tag, session⟩ ∈ space.pending)
    (rejected : ¬ AdmittedSession session) : ¬ Started languages policies space := by
  intro started
  exact rejected (started_well_started languages policies space started ⟨tag, session⟩ present)

/-- Initial data may contain a rejected atom without evaluating it. Rejection
restricts launch of the chosen request, not storage of the atom itself. -/
theorem stored_data_is_started (atom : Atom) :
    Started languages policies ⟨[atom], [], []⟩ :=
  initial_started languages policies [atom]

namespace ReachabilityControls

/-- A structural session constructor without a source-admission proof. -/
def fabricated (tag : Tag) (atom : Atom) (scope : (languages tag).Scope)
    (state : (policies tag).State) (request : (languages tag).Request) :
    Space languages policies :=
  ⟨[atom], [⟨tag, {
    origin := ⟨[atom], 0⟩
    scope := scope
    request := request
    residual := (languages tag).initial scope request [atom]
    policyState := state }⟩], []⟩

/-- An empty, hence sound, event history does not establish an admitted launch. -/
theorem sound_history_does_not_validate_fabrication (tag : Tag) (atom : Atom)
    (scope : (languages tag).Scope) (state : (policies tag).State)
    (request : (languages tag).Request) (rejected : ¬ (languages tag).admit atom request) :
    SoundHistory languages policies (fabricated languages policies tag atom scope state request) ∧
      ¬ Started languages policies (fabricated languages policies tag atom scope state request) := by
  constructor
  · intro record member
    cases member
  · apply rejected_session_not_started languages policies _ tag
      { origin := ⟨[atom], 0⟩
        scope := scope
        request := request
        residual := (languages tag).initial scope request [atom]
        policyState := state }
    · exact List.mem_cons_self
    · exact rejected

theorem admitted_launch_is_reachable (tag : Tag) (atom : Atom)
    (scope : (languages tag).Scope) (state : (policies tag).State)
    (request : (languages tag).Request) (admitted : (languages tag).admit atom request) :
    Started languages policies (fabricated languages policies tag atom scope state request) :=
  start_started languages policies ⟨[atom], [], []⟩ tag scope state 0 request
    admitted (initial_started languages policies [atom])

end ReachabilityControls

end Mettapedia.GSLT.Core.ProgrammableSpace
