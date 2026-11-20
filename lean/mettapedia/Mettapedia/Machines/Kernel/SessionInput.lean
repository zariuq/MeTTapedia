/-!
# Private session input and its journal projection

The keyboard transport continues during authentication. Replay observes session
boundaries and ordinary public effects. An admitted input receipt is private
until the keyboard pipeline and its held inputs have settled.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.SessionInput

inductive Phase where
  | openInput | locked | draining
  deriving DecidableEq, Repr

inductive Actor where
  | shell | input | observer | other
  deriving DecidableEq, Repr

inductive Action where
  | beginLock | verified | quiet
  deriving DecidableEq, Repr

inductive Boundary where
  | lock | unlock
  deriving DecidableEq, Repr

def advance (phase : Phase) (actor : Actor) (action : Action) (quiet : Bool) :
    Phase × Option Boundary :=
  match phase, actor, action, quiet with
  | .openInput, .shell, .beginLock, _ => (.locked, some .lock)
  | .locked, .shell, .verified, _ => (.draining, none)
  | .draining, .input, .quiet, true => (.openInput, some .unlock)
  | _, _, _, _ => (phase, none)

theorem unlock_requires_drain (phase : Phase) (actor : Actor) (action : Action) (quiet : Bool)
    (emitted : (advance phase actor action quiet).2 = some .unlock) :
    phase = .draining ∧ actor = .input ∧ action = .quiet ∧ quiet = true := by
  cases phase <;> cases actor <;> cases action <;> cases quiet <;> simp_all [advance]

theorem lock_requires_shell (phase : Phase) (actor : Actor) (action : Action) (quiet : Bool)
    (emitted : (advance phase actor action quiet).2 = some .lock) :
    phase = .openInput ∧ actor = .shell ∧ action = .beginLock := by
  cases phase <;> cases actor <;> cases action <;> cases quiet <;> simp_all [advance]

inductive Traffic where
  | ps2 (payload : Nat)
  | usbKeyboard (privateReceipt : Bool) (payload : Nat)
  | desktopInput (payload : Nat)
  | screen (locked : Bool) (payload : Nat)
  | credential (payload : Nat)
  | other (payload : Nat)
  | boundary (value : Boundary)
  deriving DecidableEq, Repr

def retain (phase : Phase) (event : Traffic) : Bool :=
  match event with
  | .credential _ => false
  | .usbKeyboard privateReceipt _ => !privateReceipt && decide (phase = .openInput)
  | .screen locked _ => !locked && decide (phase = .openInput)
  | .ps2 _ | .desktopInput _ => decide (phase = .openInput)
  | .other _ | .boundary _ => true

def project (phase : Phase) (events : List Traffic) : List Traffic :=
  events.filter (retain phase)

inductive PrivateTraffic : Traffic → Prop where
  | ps2 (payload : Nat) : PrivateTraffic (.ps2 payload)
  | usbKeyboard (marked : Bool) (payload : Nat) : PrivateTraffic (.usbKeyboard marked payload)
  | desktopInput (payload : Nat) : PrivateTraffic (.desktopInput payload)
  | screen (locked : Bool) (payload : Nat) : PrivateTraffic (.screen locked payload)
  | credential (payload : Nat) : PrivateTraffic (.credential payload)

theorem private_traffic_discarded {phase : Phase} (privatePhase : phase ≠ .openInput)
    {event : Traffic} (privateEvent : PrivateTraffic event) : retain phase event = false := by
  cases privateEvent <;> simp [retain, privatePhase]

/-- Even the number of inputs and attempts within an interval is erased by
the input projection. Public events interleaved with those inputs remain. -/
theorem erase_private_interval {phase : Phase} (privatePhase : phase ≠ .openInput)
    (events : List Traffic) (allPrivate : ∀ event ∈ events, PrivateTraffic event) :
    project phase events = [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have discard := private_traffic_discarded privatePhase (allPrivate event (by simp))
    have discardRest : ∀ event ∈ rest, PrivateTraffic event := by
      intro next member
      exact allPrivate next (by simp [member])
    simp [project, discard, show rest.filter (retain phase) = [] from ih discardRest]

theorem insert_private_traffic {phase : Phase} (privatePhase : phase ≠ .openInput)
    (before middle after : List Traffic) (allPrivate : ∀ event ∈ middle, PrivateTraffic event) :
    project phase (before ++ middle ++ after) = project phase (before ++ after) := by
  have erased := erase_private_interval privatePhase middle allPrivate
  simp only [project] at erased ⊢
  simp [List.filter_append, erased]

theorem late_private_receipt_discarded (phase : Phase) (payload : Nat) :
    retain phase (.usbKeyboard true payload) = false := by
  simp [retain]

example : project .draining [.usbKeyboard false 42, .other 9, .screen true 7, .boundary .unlock] =
    [.other 9, .boundary .unlock] := by decide

example : project .openInput [.ps2 28, .credential 7] = [.ps2 28] := by decide

end Mettapedia.Machines.Kernel.SessionInput
