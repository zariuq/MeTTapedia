import Mathlib.Data.Finset.Basic

/-!
# Ownership conservation at an observation publication barrier

A finite set of accepted observations moves from a pending owner to a buffer
owner and finally to a visible owner. Emptying the first owner is insufficient
to acknowledge publication. Transfers must present a coherent snapshot: a
record held in a transfer's local variable is still buffered work.

This abstracts two implementation boundaries: a stream writer's reserved
terminal/queue handoff, and a terminal editor's pending/output-buffer handoff.
The executable correspondence obligations are different: the first observer
must share the transfer lock; the second must flush the final output buffer
even when redraw is suppressed.

Revocation records an explicit policy decision (for example an obsolete display
epoch), not an inference from absence. A failed writer cannot acknowledge.
Visibility is process-local publication, not fsync, crash durability, execution
authority, byte/order fidelity, or exactly-once output. This is an abstract
protocol contract, not a refinement proof of Python or its libraries.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.PublicationBarrier

structure State (Event : Type) where
  accepted : Finset Event
  pending : Finset Event
  buffered : Finset Event
  visible : Finset Event
  revoked : Finset Event
  healthy : Bool

variable {Event : Type} [DecidableEq Event]

def initial : State Event := ⟨∅, ∅, ∅, ∅, ∅, true⟩

def Accounted (s : State Event) : Prop :=
  ∀ e, e ∈ s.accepted ↔
    e ∈ s.pending ∨ e ∈ s.buffered ∨ e ∈ s.visible ∨ e ∈ s.revoked

inductive Step : State Event → State Event → Prop
  | accept {s} (e) (fresh : e ∉ s.accepted) :
      Step s {s with accepted := insert e s.accepted, pending := insert e s.pending}
  | buffer {s} (e) (owned : e ∈ s.pending) :
      Step s {s with pending := s.pending.erase e, buffered := insert e s.buffered}
  | publish {s} (e) (owned : e ∈ s.buffered) :
      Step s {s with buffered := s.buffered.erase e, visible := insert e s.visible}
  | revoke {s} (e) (accepted : e ∈ s.accepted) :
      Step s {s with pending := s.pending.erase e, buffered := s.buffered.erase e, revoked := insert e s.revoked}
  | fail {s} : Step s {s with healthy := false}

omit [DecidableEq Event] in
theorem initial_accounted : Accounted (initial : State Event) := by
  simp [Accounted, initial]

theorem step_accounted {s t : State Event} (h : Accounted s) (step : Step s t) :
    Accounted t := by
  cases step with
  | accept e _ =>
      intro x
      by_cases hx : x = e
      · subst x; simp
      · simpa [hx] using h x
  | buffer e owned =>
      intro x
      by_cases hx : x = e
      · subst x
        have ha := (h e).mpr (Or.inl owned)
        simp [ha]
      · simpa [hx] using h x
  | publish e owned =>
      intro x
      by_cases hx : x = e
      · subst x
        have ha := (h e).mpr (Or.inr (Or.inl owned))
        simp [ha]
      · simpa [hx] using h x
  | revoke e accepted =>
      intro x
      by_cases hx : x = e
      · subst x; simp [accepted]
      · simpa [hx] using h x
  | fail => exact h

inductive Run : State Event → Prop
  | start : Run initial
  | next {s t} : Run s → Step s t → Run t

theorem run_accounted {s : State Event} (run : Run s) : Accounted s := by
  induction run with
  | start => exact initial_accounted
  | next _ step ih => exact step_accounted ih step

def Ready (s : State Event) : Prop :=
  s.healthy = true ∧ s.pending = ∅ ∧ s.buffered = ∅

theorem ready_publishes_or_revokes {s : State Event} (h : Accounted s) (ready : Ready s) :
    s.accepted ⊆ s.visible ∪ s.revoked := by
  intro e he
  have accounted := (h e).mp he
  simpa [ready.2.1, ready.2.2] using accounted

theorem reachable_ready_is_sound {s : State Event} (run : Run s) (ready : Ready s) :
    s.accepted ⊆ s.visible ∪ s.revoked :=
  ready_publishes_or_revokes (run_accounted run) ready

omit [DecidableEq Event] in
theorem buffered_work_blocks_acknowledgement {s : State Event} {e : Event}
    (owned : e ∈ s.buffered) : ¬ Ready s := by
  intro ready
  simp [ready.2.2] at owned

omit [DecidableEq Event] in
theorem failed_writer_cannot_acknowledge {s : State Event} (failed : s.healthy = false) :
    ¬ Ready s := by
  simp [Ready, failed]

theorem buffer_state_reachable (e : Event) :
    Run (⟨{e}, ∅, {e}, ∅, ∅, true⟩ : State Event) := by
  have first : Run ({initial with accepted := {e}, pending := {e}} : State Event) :=
    Run.next Run.start (Step.accept e (by simp [initial]))
  have second := Run.next first (Step.buffer e (by simp))
  simpa [initial] using second

-- A real accept → buffer trace reaches this state. The first owner is empty
-- while a visible acknowledgement is still false.
theorem empty_pending_is_insufficient (e : Event) :
    let s : State Event := ⟨{e}, ∅, {e}, ∅, ∅, true⟩
    Run s ∧ Accounted s ∧ s.pending = ∅ ∧ e ∉ s.visible ∧ ¬ Ready s := by
  dsimp
  constructor
  · exact buffer_state_reachable e
  · constructor
    · intro x; simp
    · simp [Ready]

end Mettapedia.Protocols.Agents.PublicationBarrier
