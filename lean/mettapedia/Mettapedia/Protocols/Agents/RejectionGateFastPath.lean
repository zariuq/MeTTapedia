import Mathlib.Tactic

/-!
# The provider-rejection gate's fast path

A deterministic provider rejection (an invalid request) is retained until
observed corrective state changes. The host owns that decision: it holds the
block in the cognitive health record, or — when the record could not be
written — in its own memory only, and it releases the block once it observes
a correction. Asking the host costs a call into it on every turn, so the
native runtime keeps a fast path: it allows a request without the host only
when no block is recorded and it has not itself seen a rejection since the
host last allowed a request (its latch).

Invariants proved here, for every event trace:
* a block held only in the host's memory implies the latch is set;
* the fast path never allows a request the host would block;
* after the host allows a request, the latch is released, so the next turn
  takes the fast path again.

The counterexample is the fast path without the latch: reading only the
record, it allows a request whose block the host holds in memory because the
disk was full, so the known rejection is resent.

This is an abstract contract. It models the host's corrective-state
comparison as one `correct` event; it is not a refinement proof of
provider_rejection, of cognitive_health or of the MeTTa gate.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.RejectionGateFastPath

structure State where
  /-- The health record holds a block. -/
  recorded : Bool
  /-- The host holds a block it could not write to the record. -/
  memory : Bool
  /-- Observed corrective state changed since the block was retained. -/
  corrected : Bool
  /-- The native process saw a rejection since the host last allowed one. -/
  latched : Bool
  deriving DecidableEq

def initial : State := ⟨false, false, false, false⟩

/-- The host's authoritative answer: blocked while a block is held and no
correction has been observed. -/
def hostBlocks (s : State) : Bool := (s.recorded || s.memory) && !s.corrected

inductive Event where
  /-- A deterministic rejection; `persisted` says whether the record was written. -/
  | reject (persisted : Bool)
  | correct
  | request

inductive Outcome where
  | fast | allowed | blocked
  deriving DecidableEq

/-- Whether the fast path consults the host. -/
def consults (s : State) : Bool := s.latched || s.recorded

def decide (s : State) : Outcome :=
  if consults s then (if hostBlocks s then .blocked else .allowed) else .fast

def step (s : State) : Event → State
  | .reject persisted =>
    { s with recorded := s.recorded || persisted, memory := s.memory || !persisted,
             corrected := false, latched := true }
  | .correct => { s with corrected := true }
  | .request =>
    match decide s with
    | .allowed => ⟨false, false, false, false⟩
    | _ => s

def run (s : State) (es : List Event) : State := es.foldl step s

/-- A block held only in memory is always latched. -/
def Invariant (s : State) : Prop := s.memory = true → s.latched = true

theorem step_invariant {s : State} (h : Invariant s) (e : Event) : Invariant (step s e) := by
  rcases s with ⟨r, m, c, l⟩
  unfold Invariant at *
  cases e with
  | reject persisted => cases persisted <;> simp [step]
  | correct => simpa [step] using h
  | request =>
    cases r <;> cases m <;> cases c <;> cases l <;> simp_all [step, decide, consults, hostBlocks]

theorem run_invariant (es : List Event) : Invariant (run initial es) := by
  suffices ∀ s, Invariant s → Invariant (run s es) from this initial (by simp [Invariant, initial])
  induction es with
  | nil => intro s h; simpa [run] using h
  | cons e es ih => intro s h; exact ih (step s e) (step_invariant h e)

/-- The fast path never allows a request the host would block. -/
theorem fast_path_sound {s : State} (h : Invariant s) (fast : decide s = .fast) :
    hostBlocks s = false := by
  rcases s with ⟨r, m, c, l⟩
  unfold Invariant at h
  cases r <;> cases m <;> cases c <;> cases l <;> simp_all [decide, consults, hostBlocks]

/-- On every reachable state, a fast-path request is one the host allows. -/
theorem reachable_fast_path_sound (es : List Event) (fast : decide (run initial es) = .fast) :
    hostBlocks (run initial es) = false :=
  fast_path_sound (run_invariant es) fast

/-- After the host allows a request, the next turn takes the fast path. -/
theorem allowed_releases_the_latch {s : State} (allowed : decide s = .allowed) :
    decide (step s .request) = .fast := by
  have released : step s .request = ⟨false, false, false, false⟩ := by
    simp only [step, allowed]
  rw [released]
  rfl

/-- The rejected design: the fast path reads only the record. -/
def decideWithoutLatch (s : State) : Outcome :=
  if s.recorded then (if hostBlocks s then .blocked else .allowed) else .fast

/-- With the record unwritable, that design allows a request the host blocks. -/
theorem record_only_resends_a_rejection :
    let s := step initial (.reject false)
    decideWithoutLatch s = .fast ∧ hostBlocks s = true := by
  simp [step, initial, decideWithoutLatch, hostBlocks]

end Mettapedia.Protocols.Agents.RejectionGateFastPath
