import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Logic.Relation

/-!
# Declared languages and agendas over a shared space

A stored atom is data until an explicitly selected language admits it. Source
steps, agenda policy, physical representation and observations have separate
types. A workspace may retain active sessions from several languages; stepping
one session keeps the other sessions and their scopes intact.

An event keeps both stores, both residuals, the selected source occurrence,
scope and source receipt. The generic laws establish no source execution on
their own: concrete adapters must connect `advance` to their source calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ProgrammableSpace

universe u

/-- The source semantics of a declared transaction language. -/
structure Language (Atom : Type u) where
  Scope : Type u
  Request : Type u
  Residual : Type u
  Outcome : Type u
  Receipt : Type u
  admit : Atom → Request → Prop
  initial : Scope → Request → List Atom → Residual
  advance : Scope → List Atom → Residual → Receipt → List Atom → Residual → Prop
  observes : Residual → Outcome → Prop

/-- A policy restricts source events and carries its own changing state. -/
structure Policy {Atom : Type u} (language : Language Atom) where
  State : Type u
  permits : State → language.Scope → List Atom → language.Residual →
    language.Receipt → List Atom → language.Residual → State → Prop

/-- The actual selected occurrence, including duplicate positions. -/
structure Origin (Atom : Type u) where
  snapshot : List Atom
  position : Fin snapshot.length

def Origin.atom {Atom : Type u} (origin : Origin Atom) : Atom :=
  origin.snapshot[origin.position]

structure Session {Atom : Type u} (language : Language Atom)
    (policy : Policy language) where
  origin : Origin Atom
  scope : language.Scope
  request : language.Request
  residual : language.Residual
  policyState : policy.State

structure Event {Atom : Type u} (language : Language Atom) where
  origin : Origin Atom
  scope : language.Scope
  before : List Atom
  after : List Atom
  residualBefore : language.Residual
  residualAfter : language.Residual
  receipt : language.Receipt

def Event.Valid {Atom : Type u} {language : Language Atom}
    (event : Event language) : Prop :=
  language.advance event.scope event.before event.residualBefore
    event.receipt event.after event.residualAfter

structure PolicyEvent {Atom : Type u} (language : Language Atom)
    (policy : Policy language) extends Event language where
  policyBefore : policy.State
  policyAfter : policy.State

def PolicyEvent.Valid {Atom : Type u} {language : Language Atom}
    {policy : Policy language} (event : PolicyEvent language policy) : Prop :=
  event.toEvent.Valid ∧ policy.permits event.policyBefore event.scope
    event.before event.residualBefore event.receipt event.after
    event.residualAfter event.policyAfter

variable {Atom Tag : Type u} (languages : Tag → Language Atom)
  (policies : (tag : Tag) → Policy (languages tag))

abbrev Work := (tag : Tag) × Session (languages tag) (policies tag)
abbrev Record := (tag : Tag) × PolicyEvent (languages tag) (policies tag)

structure Space where
  atoms : List Atom
  pending : List (Work languages policies)
  history : List (Record languages policies)

def Admitted (space : Space languages policies) (tag : Tag)
    (position : Fin space.atoms.length) (request : (languages tag).Request) : Prop :=
  (languages tag).admit space.atoms[position] request

/-- Admission starts an explicitly requested agenda. It neither consumes nor
evaluates atoms through any other language. -/
def start (space : Space languages policies) (tag : Tag)
    (scope : (languages tag).Scope) (state : (policies tag).State)
    (position : Fin space.atoms.length) (request : (languages tag).Request)
    (_admitted : Admitted languages policies space tag position request) :
    Space languages policies where
  atoms := space.atoms
  pending := space.pending ++ [⟨tag, {
    origin := ⟨space.atoms, position⟩
    scope := scope
    request := request
    residual := (languages tag).initial scope request space.atoms
    policyState := state }⟩]
  history := space.history

/-- A single source event, approved by the requested policy. Residual work is
replaced at its selected position and all other work keeps its exact order. -/
inductive Step : Space languages policies → Space languages policies → Prop where
  | fire (tag : Tag) (atoms nextAtoms : List Atom)
      (front back : List (Work languages policies))
      (history : List (Record languages policies))
      (session : Session (languages tag) (policies tag))
      (receipt : (languages tag).Receipt)
      (next : (languages tag).Residual) (nextPolicy : (policies tag).State)
      (source : (languages tag).advance session.scope atoms session.residual
        receipt nextAtoms next)
      (permitted : (policies tag).permits session.policyState session.scope
        atoms session.residual receipt nextAtoms next nextPolicy) :
      Step
        ⟨atoms, front ++ ⟨tag, session⟩ :: back, history⟩
        ⟨nextAtoms, front ++ ⟨tag, { session with
          residual := next
          policyState := nextPolicy }⟩ :: back,
          history ++ [⟨tag, {
            origin := session.origin
            scope := session.scope
            before := atoms
            after := nextAtoms
            residualBefore := session.residual
            residualAfter := next
            receipt := receipt
            policyBefore := session.policyState
            policyAfter := nextPolicy }⟩]⟩

def SoundHistory (space : Space languages policies) : Prop :=
  ∀ record ∈ space.history, record.2.Valid

theorem step_history_extends {before after : Space languages policies}
    (step : Step languages policies before after) :
    ∃ record : Record languages policies,
      record.2.Valid ∧ after.history = before.history ++ [record] := by
  cases step with
  | fire tag atoms nextAtoms front back history session receipt next nextPolicy source permitted =>
      exact ⟨⟨tag, {
        origin := session.origin
        scope := session.scope
        before := atoms
        after := nextAtoms
        residualBefore := session.residual
        residualAfter := next
        receipt := receipt
        policyBefore := session.policyState
        policyAfter := nextPolicy }⟩, ⟨source, permitted⟩, rfl⟩

theorem step_history_sound {before after : Space languages policies}
    (step : Step languages policies before after)
    (sound : SoundHistory languages policies before) :
    SoundHistory languages policies after := by
  obtain ⟨record, valid, appended⟩ := step_history_extends languages policies step
  intro entry member
  rw [appended, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact sound entry old
  · exact valid

theorem run_history_sound {before after : Space languages policies}
    (run : Relation.ReflTransGen (Step languages policies) before after)
    (sound : SoundHistory languages policies before) :
    SoundHistory languages policies after := by
  induction run with
  | refl => exact sound
  | tail _ step ih => exact step_history_sound languages policies step ih

def sessionKey (work : Work languages policies) :
    (tag : Tag) × (Origin Atom × (languages tag).Scope) :=
  ⟨work.1, work.2.origin, work.2.scope⟩

/-- An agenda step cannot capture, rename or discard another session. -/
theorem step_keeps_session_scopes {before after : Space languages policies}
    (step : Step languages policies before after) :
    after.pending.map (sessionKey languages policies) =
      before.pending.map (sessionKey languages policies) := by
  cases step
  simp [sessionKey]

theorem run_keeps_session_scopes {before after : Space languages policies}
    (run : Relation.ReflTransGen (Step languages policies) before after) :
    after.pending.map (sessionKey languages policies) =
      before.pending.map (sessionKey languages policies) := by
  induction run with
  | refl => rfl
  | tail _ step ih =>
      exact (step_keeps_session_scopes languages policies step).trans ih

/-- These declarations may overlap syntactically. The requested tag chooses
the interpreter; admission under another tag creates no event here. -/
theorem rejected_cannot_be_admitted (space : Space languages policies) (tag : Tag)
    (position : Fin space.atoms.length)
    (rejected : ∀ request, ¬ (languages tag).admit space.atoms[position] request) :
    ¬ ∃ request, Admitted languages policies space tag position request := by
  rintro ⟨request, admitted⟩
  exact rejected request admitted

/-- The same atoms can have simultaneously admitted requests in two declared
languages, with separate retained scopes and policy states. -/
theorem start_two_languages (space : Space languages policies)
    (first second : Tag) (firstScope : (languages first).Scope)
    (secondScope : (languages second).Scope)
    (firstPolicy : (policies first).State) (secondPolicy : (policies second).State)
    (firstPosition secondPosition : Fin space.atoms.length)
    (firstRequest : (languages first).Request) (secondRequest : (languages second).Request)
    (firstAdmitted : Admitted languages policies space first firstPosition firstRequest)
    (secondAdmitted : Admitted languages policies space second secondPosition secondRequest) :
    (start languages policies
      (start languages policies space first firstScope firstPolicy firstPosition firstRequest firstAdmitted)
      second secondScope secondPolicy secondPosition secondRequest secondAdmitted).atoms = space.atoms ∧
    (start languages policies
      (start languages policies space first firstScope firstPolicy firstPosition firstRequest firstAdmitted)
      second secondScope secondPolicy secondPosition secondRequest secondAdmitted).pending.length =
        space.pending.length + 2 := by
  constructor
  · rfl
  · simp [start]

/-- Launching a requested language is a distinct action from advancing its
source calculus. In particular, an atom generated by one agenda is not run
until it is admitted by an explicitly requested agenda. -/
inductive Action : Space languages policies → Space languages policies → Prop where
  | launch (space : Space languages policies) (tag : Tag)
      (scope : (languages tag).Scope) (state : (policies tag).State)
      (position : Fin space.atoms.length) (request : (languages tag).Request)
      (admitted : Admitted languages policies space tag position request) :
      Action space (start languages policies space tag scope state position request admitted)
  | execute {before after : Space languages policies}
      (step : Step languages policies before after) : Action before after

/-- Retained session births and source events bound an actual context stage. -/
def Space.extent (space : Space languages policies) : Nat :=
  space.pending.length + space.history.length

theorem action_extent {before after : Space languages policies}
    (action : Action languages policies before after) :
    after.extent languages policies = before.extent languages policies + 1 := by
  cases action with
  | launch => simp [Space.extent, start, Nat.add_comm, Nat.add_left_comm]
  | execute step =>
      cases step
      simp [Space.extent, Nat.add_assoc]

theorem action_history_sound {before after : Space languages policies}
    (action : Action languages policies before after)
    (sound : SoundHistory languages policies before) : SoundHistory languages policies after := by
  cases action with
  | launch => exact sound
  | execute step => exact step_history_sound languages policies step sound

theorem step_needs_session {before after : Space languages policies}
    (step : Step languages policies before after) : before.pending ≠ [] := by
  cases step
  simp

theorem unrequested_space_is_inert (atoms : List Atom) :
    ¬ ∃ after, Step languages policies ⟨atoms, [], []⟩ after := by
  rintro ⟨after, step⟩
  exact step_needs_session languages policies step rfl

theorem action_needs_atom_or_session {before after : Space languages policies}
    (action : Action languages policies before after) :
    before.atoms ≠ [] ∨ before.pending ≠ [] := by
  cases action with
  | launch tag scope state position request admitted =>
      left
      intro empty
      exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_eq position.isLt (congrArg List.length empty))
  | execute step => exact Or.inr (step_needs_session languages policies step)

end Mettapedia.GSLT.Core.ProgrammableSpace
