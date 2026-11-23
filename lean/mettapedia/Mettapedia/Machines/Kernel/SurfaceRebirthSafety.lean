/-
  SurfaceRebirthSafety.lean — Abstract generational resource custody,
  authenticated incarnation notices, settled retirement, and zero-collision rebirth.

  Separates user-initiated close guards from owner-exit retirement, models retirement
  settlement explicitly (never conflating notice delivery with backend deactivation),
  and proves:
  1. New-incarnation registration always succeeds after confirmed retirement + rebirth.
  2. Delayed notices for a stale prior incarnation leave the active new registration untouched.
  3. Unsettled retirement blocks registration rather than silently aliasing a live handle.
  4. User-initiated close guards remain preserved for dead or already-closing slots.
-/
namespace Mettapedia.Machines.Kernel.SurfaceRebirthSafety

/-- Lifecycle phase of a slot-hosted presented resource. -/
inductive ResourcePhase where
  | none
  | active
  | closing
  | retired
  deriving DecidableEq, Repr

/-- Explicit settlement status of a backend retirement/deactivation obligation. -/
inductive Settlement where
  | settled
  | unsettled
  deriving DecidableEq, Repr

/-- Reusable custody slot parameterized over an arbitrary generation/incarnation type `Inc`. -/
structure SlotState (Inc : Type) where
  incarnation   : Option Inc
  ownerAlive    : Bool
  closePending  : Bool
  phase         : ResourcePhase
  backendActive : Bool
  deriving DecidableEq, Repr

/-- User-initiated close policy: allowed iff a live, non-closing owner holds an active resource. -/
def userCloseAllowed {Inc : Type} (s : SlotState Inc) : Bool :=
  s.incarnation.isSome && s.ownerAlive && !s.closePending && (s.phase == .active)

/-- Authenticated owner-exit notice for `noticeInc`, with explicit backend retirement settlement.
    Notices whose incarnation does not match the slot's current incarnation are ignored. -/
def onAuthenticatedExit {Inc : Type} [DecidableEq Inc]
    (s : SlotState Inc) (noticeInc : Inc) (retireOutcome : Settlement) : SlotState Inc :=
  if s.incarnation = some noticeInc then
    match s.phase, retireOutcome with
    | .active, .settled =>
        { s with ownerAlive := false, closePending := false, phase := .retired, backendActive := false }
    | .closing, .settled =>
        { s with ownerAlive := false, closePending := false, phase := .retired, backendActive := false }
    | _, _ =>
        { s with ownerAlive := false }
  else
    s

/-- Authenticated generation rebirth onto a fresh incarnation `nextInc`.
    Replaces custody only when `nextInc` differs from the current incarnation;
    sweeps lifecycle state to `.none` iff prior retirement settled (or no active resource remained). -/
def onRebirth {Inc : Type} [DecidableEq Inc]
    (s : SlotState Inc) (nextInc : Inc) (retireOutcome : Settlement) : SlotState Inc :=
  if s.incarnation = some nextInc then s
  else
    let clean :=
      match s.phase, retireOutcome with
      | .none, _       => true
      | .retired, _    => true
      | _, .settled    => true
      | _, .unsettled  => false
    { incarnation   := some nextInc,
      ownerAlive    := true,
      closePending  := false,
      phase         := if clean then .none else s.phase,
      backendActive := if clean then false else s.backendActive }

/-- Outcome of registering a fresh presented resource for `caller`. -/
inductive RegisterResult (Inc : Type) where
  | accept (s : SlotState Inc)
  | rejectAlreadyRegistered
  | rejectWrongIncarnation
  deriving DecidableEq, Repr

/-- Resource registration: requires matching live incarnation and zero residual presentation state. -/
def register {Inc : Type} [DecidableEq Inc] (s : SlotState Inc) (caller : Inc) :
    RegisterResult Inc :=
  if s.incarnation ≠ some caller || !s.ownerAlive then
    .rejectWrongIncarnation
  else if s.phase ≠ .none || s.backendActive then
    .rejectAlreadyRegistered
  else
    .accept { s with phase := .active, backendActive := true }

/-- Settled exit always retires an active resource and clears backend activity. -/
theorem settled_exit_retires_active {Inc : Type} [DecidableEq Inc]
    (s : SlotState Inc) (inc : Inc)
    (hinc : s.incarnation = some inc) (hact : s.phase = .active) :
    let s' := onAuthenticatedExit s inc .settled
    s'.ownerAlive = false ∧ s'.phase = .retired ∧ s'.backendActive = false := by
  simp [onAuthenticatedExit, hinc, hact]

/-- After settled retirement + rebirth onto a distinct incarnation, registration ALWAYS succeeds. -/
theorem register_after_settled_rebirth {Inc : Type} [DecidableEq Inc]
    (s : SlotState Inc) (nextInc : Inc)
    (hne : s.incarnation ≠ some nextInc) :
    ∃ s'', register (onRebirth s nextInc .settled) nextInc = .accept s'' ∧
           s''.incarnation = some nextInc ∧
           s''.phase = .active ∧
           s''.backendActive = true := by
  cases hph : s.phase <;> simp [onRebirth, hne, hph, register]

/-- Full round-trip: settled exit of `oldInc`, followed by rebirth to `newInc ≠ oldInc`,
    followed by registration by `newInc` always succeeds with zero stale residue. -/
theorem settled_exit_rebirth_register {Inc : Type} [DecidableEq Inc]
    (s : SlotState Inc) (oldInc newInc : Inc)
    (hcur : s.incarnation = some oldInc) (hne : oldInc ≠ newInc) :
    ∃ s'', register (onRebirth (onAuthenticatedExit s oldInc .settled) newInc .settled) newInc = .accept s'' ∧
           s''.incarnation = some newInc ∧
           s''.backendActive = true := by
  have hne' : (onAuthenticatedExit s oldInc .settled).incarnation ≠ some newInc := by
    cases hph : s.phase <;> simp [onAuthenticatedExit, hcur, hph, hne]
  rcases register_after_settled_rebirth (onAuthenticatedExit s oldInc .settled) newInc hne' with
    ⟨s'', hreg, hinc, _, hba⟩
  exact ⟨s'', hreg, hinc, hba⟩

/-- Delayed stale-incarnation notice safety: once a slot has been reborn and registered under
    `newInc`, a late exit notice for `oldInc ≠ newInc` leaves the new registration untouched. -/
theorem stale_incarnation_notice_ignored {Inc : Type} [DecidableEq Inc]
    (s : SlotState Inc) (oldInc newInc : Inc) (outcome : Settlement)
    (hcur : s.incarnation = some newInc) (hne : oldInc ≠ newInc) :
    onAuthenticatedExit s oldInc outcome = s := by
  have hne' : s.incarnation ≠ some oldInc := by
    rw [hcur]
    intro h
    exact hne (Option.some.inj h).symm
  simp [onAuthenticatedExit, hne']

/-- Unsettled retirement refuses collision rather than silently aliasing a live backend handle. -/
theorem unsettled_retirement_refuses_collision {Inc : Type} [DecidableEq Inc]
    (s : SlotState Inc) (nextInc : Inc)
    (hne : s.incarnation ≠ some nextInc) (hact : s.phase = .active) :
    register (onRebirth s nextInc .unsettled) nextInc = .rejectAlreadyRegistered := by
  simp [onRebirth, hne, hact, register]

/-- User-initiated close guard is strictly preserved for dead or already-closing slots. -/
theorem user_close_guard_preserved {Inc : Type} (s : SlotState Inc)
    (hguard : s.ownerAlive = false ∨ s.closePending = true) :
    userCloseAllowed s = false := by
  cases hguard with
  | inl hd => simp [userCloseAllowed, hd]
  | inr hc => simp [userCloseAllowed, hc]

end Mettapedia.Machines.Kernel.SurfaceRebirthSafety
