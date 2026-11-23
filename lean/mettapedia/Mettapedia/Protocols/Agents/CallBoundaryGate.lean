import Mathlib.Tactic
import Mettapedia.Protocols.Agents.NativeCallOwner

/-!
# The gate and the binding at a provider call's boundary

Two decisions are made natively at the boundary of a provider call.

**The gate.** No call is submitted while the operator has paused cognition, a
requested recycle ends the process at this boundary, a coding check refuses
the call, and a mode runtime keeps its own gate. The host gate owns all of
that: it waits, exits or refuses. The native runtime keeps a fast path: it
passes a call without the host only when it reads, itself, the one state in
which the host gate would return at once. A coding session outlives the
agent's recycles, so the recycle request does not concern it.

**The binding.** A prepared call is bound to its owner once. The binding is
the owner's phase record: a call that has one is live, and a second binding
of a live call is refused.

Proved here:
* the fast path passes a call only when the host gate would pass it at once;
* when every fact can be read, the fast path passes exactly those calls, so
  the host is entered only to wait, exit or refuse;
* a fact that cannot be read never passes a call;
* binding a live call changes nothing, so one call still submits at most once.

Counterexamples, each a design this guards against:
* a fast path that does not read the recycle request passes a call the host
  gate would have ended the process on;
* a second binding that started the phase again lets one call submit twice.

This is an abstract contract. It is not a refinement proof of the host gate,
of the operator latch or of the MeTTa owner.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CallBoundaryGate

/-! ## The gate -/

/-- The facts of the process at the boundary. -/
structure Facts where
  /-- A coding check: every provider call is refused. -/
  check : Bool
  /-- A mode runtime, which keeps its own gate. -/
  runtime : Bool
  /-- A coding session, which outlives the agent's recycles. -/
  session : Bool
  /-- The operator latch grants cognition. -/
  running : Bool
  /-- A recycle is requested. -/
  recycle : Bool

inductive Host where
  | refuse | ownGate | exit | wait | pass
  deriving DecidableEq

/-- The host gate's authoritative answer. -/
def host (f : Facts) : Host :=
  if f.check then .refuse
  else if f.runtime then .ownGate
  else if !f.session && f.recycle then .exit
  else if !f.running then .wait
  else .pass

/-- What the native side reads of a fact: its value, or nothing. -/
inductive Read where
  | known (value : Bool) | unreadable
  deriving DecidableEq

/-- The native reading of the two stored facts. The environment's three are
always readable. -/
structure Reading where
  running : Read
  recycle : Read

/-- A reading never states a value the fact does not have. -/
def Faithful (f : Facts) (r : Reading) : Prop :=
  (∀ b, r.running = .known b → b = f.running) ∧ (∀ b, r.recycle = .known b → b = f.recycle)

/-- The fast path: clear only for the state the host passes at once. The
recycle request is read only outside a coding session. -/
def clear (f : Facts) (r : Reading) : Bool :=
  !f.check && !f.runtime && (r.running == .known true) &&
    (f.session || (r.recycle == .known false))

/-- The fast path passes a call only when the host gate would. -/
theorem clear_sound (f : Facts) (r : Reading) (h : Faithful f r) (hc : clear f r = true) :
    host f = .pass := by
  obtain ⟨hrun, hrec⟩ := h
  rcases f with ⟨check, runtime, session, running, recycle⟩
  rcases r with ⟨rr, rc⟩
  simp only [clear, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hcheck, hruntime⟩, hr⟩, hs⟩ := hc
  have hrunning : running = true := (hrun true hr).symm
  subst hcheck hruntime hrunning
  rcases hs with hs | hs
  · subst hs; simp [host]
  · have : recycle = false := (hrec false hs).symm
    subst this; simp [host]

/-- With every fact readable, the fast path passes exactly the calls the host
passes: the host is entered only to wait, exit or refuse. -/
theorem clear_complete (f : Facts) (h : host f = .pass) :
    clear f ⟨.known f.running, .known f.recycle⟩ = true := by
  rcases f with ⟨check, runtime, session, running, recycle⟩
  cases check <;> cases runtime <;> cases session <;> cases running <;> cases recycle <;>
    simp_all [host, clear]

/-- An unreadable latch never passes a call. -/
theorem unreadable_latch_is_the_hosts (f : Facts) (rc : Read) :
    clear f ⟨.unreadable, rc⟩ = false := by
  simp [clear]

/-- Outside a coding session, an unreadable recycle request never passes a call. -/
theorem unreadable_recycle_is_the_hosts (f : Facts) (rr : Read) (h : f.session = false) :
    clear f ⟨rr, .unreadable⟩ = false := by
  simp [clear, h]

/-- The rejected design: a fast path that reads the latch alone. -/
def clearLatchOnly (f : Facts) (r : Reading) : Bool :=
  !f.check && !f.runtime && (r.running == .known true)

/-- It passes a call at the boundary where the host would have ended the
process for a requested recycle. -/
theorem latch_only_misses_a_recycle :
    ∃ f r, Faithful f r ∧ clearLatchOnly f r = true ∧ host f = .exit :=
  ⟨⟨false, false, false, true, true⟩, ⟨.known true, .known true⟩, by simp [Faithful], rfl, rfl⟩

/-! ## The binding -/

open NativeCallOwner

/-- A call's phase record: absent before its binding and after its release. -/
abbrev Record (T : Type) := Option (Phase T)

inductive Step (T : Type) where
  | bind
  | event (e : Event T)

variable {T : Type}

/-- Binding creates the record of a call that has none; a live call keeps
its phase. Owner events act on a live record. -/
def step : Record T → Step T → Record T
  | none, .bind => some .ready
  | some p, .bind => some p
  | some p, .event e => some (NativeCallOwner.step p e)
  | none, .event _ => none

def submissions : Record T → List (Step T) → Nat
  | _, [] => 0
  | r, s :: ss =>
    (match r, s with
      | some p, .event e => if submits p e then 1 else 0
      | _, _ => 0) + submissions (step r s) ss

/-- A second binding of a live call changes nothing. -/
theorem rebind_changes_nothing (p : Phase T) : step (some p) .bind = some p := rfl

/-- Owner events of a live record, with its bindings dropped. -/
def events : List (Step T) → List (Event T)
  | [] => []
  | .bind :: ss => events ss
  | .event e :: ss => e :: events ss

theorem live_submissions (p : Phase T) (ss : List (Step T)) :
    submissions (some p) ss = NativeCallOwner.submissions p (events ss) := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | bind => simpa [submissions, step, events] using ih p
    | event e => simp [submissions, step, events, NativeCallOwner.submissions, ih]

/-- However often it is bound, one call submits at most once. -/
theorem at_most_one_submission (ss : List (Step T)) :
    submissions (some (.ready : Phase T)) ss ≤ 1 := by
  rw [live_submissions]
  exact NativeCallOwner.at_most_one_submission _ _

/-- The rejected design: a binding that starts the phase again. -/
def stepRebinding : Record T → Step T → Record T
  | _, .bind => some .ready
  | some p, .event e => some (NativeCallOwner.step p e)
  | none, .event _ => none

def submissionsRebinding : Record T → List (Step T) → Nat
  | _, [] => 0
  | r, s :: ss =>
    (match r, s with
      | some p, .event e => if submits p e then 1 else 0
      | _, _ => 0) + submissionsRebinding (stepRebinding r s) ss

/-- Under that design one call, bound again while live, submits twice. -/
theorem rebinding_submits_twice (a b : T) :
    submissionsRebinding (none : Record T)
      [.bind, .event .begin, .event .admitted, .event (.submit a),
       .bind, .event .begin, .event .admitted, .event (.submit b)] = 2 := by
  simp [submissionsRebinding, stepRebinding, NativeCallOwner.step, submits]

end Mettapedia.Protocols.Agents.CallBoundaryGate
