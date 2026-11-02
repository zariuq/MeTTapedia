import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

/-!
# Deferred native cancellation under reentrant scopes

The reference tracks an explicit stack of client scopes and three lifecycle
phases. The implementation tracks a scope count and two separate flags. A
close request prevents fresh execution immediately; cancellation waits for the
last client scope, or enters its own administrative scope from quiescence.
The cancellation latch is set before the callback boundary.

The trace records invocation of native cancellation, rather than completion of
every foreign finalizer. Retained observations are immutable supplied values.
Reference counts, retained-memory validity, TLS/context restoration, locking,
atomic publication, counter overflow and termination of cleanup callbacks are
native obligations. Invalid unmatched leaves are outside the C API contract;
the executable model reports them rather than modeling unsigned underflow.
This is a scheduler refinement, not verification of a C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DeferredClose

universe u v
variable {Value : Type u}

inductive Scope where
  | execution
  | metadata
  deriving DecidableEq, Repr

inductive Action where
  | enterExecution
  | enterMetadata
  | leave
  | close (lockAvailable : Bool)
  | observe (index : Nat)
  | callbackEffect (label : Nat)
  deriving DecidableEq, Repr

inductive Event (Value : Type u) where
  | entered (scope : Scope)
  | left
  | requestedClose
  | administrativeEnter
  | administrativeLeave
  | cancelNative
  | rejectedExecution
  | observed (value : Option Value)
  | callbackEffect (label : Nat)
  | unmatchedLeave
  deriving DecidableEq, Repr

structure Transition (State : Type v) (Value : Type u) where
  next : State
  events : List (Event Value)

namespace Reference

inductive Phase where
  | live
  | requested
  | claimed
  deriving DecidableEq, Repr

def Phase.closed : Phase → Bool
  | .live => false
  | _ => true

def Phase.isClaimed : Phase → Bool
  | .claimed => true
  | _ => false

def Phase.request : Phase → Phase
  | .live => .requested
  | phase => phase

structure State (Value : Type u) where
  scopes : List Scope
  phase : Phase
  retained : List Value
  deriving DecidableEq, Repr

/-- The source specification cancels precisely when pending close becomes
quiescent. It does not inspect native counters or implementation flags. -/
def releaseScope (state : State Value) : Transition (State Value) Value :=
  match state.scopes with
  | [] => ⟨state, [.unmatchedLeave]⟩
  | _ :: rest =>
      match rest, state.phase with
      | [], .requested => ⟨{state with scopes := [], phase := .claimed}, [.left, .cancelNative]⟩
      | _, _ => ⟨{state with scopes := rest}, [.left]⟩

def requestClose (state : State Value) (lockAvailable : Bool) : Transition (State Value) Value :=
  let marked := {state with phase := state.phase.request}
  match state.scopes with
  | [] =>
      if lockAvailable then
        ⟨{marked with phase := .claimed},
          [.requestedClose, .administrativeEnter] ++
            (if state.phase.isClaimed then [] else [.cancelNative]) ++ [.administrativeLeave]⟩
      else ⟨marked, [.requestedClose]⟩
  | _ :: _ => ⟨marked, [.requestedClose]⟩

def step (state : State Value) : Action → Transition (State Value) Value
  | .enterExecution =>
      match state.phase with
      | .live => ⟨{state with scopes := .execution :: state.scopes}, [.entered .execution]⟩
      | _ => ⟨state, [.rejectedExecution]⟩
  | .enterMetadata => ⟨{state with scopes := .metadata :: state.scopes}, [.entered .metadata]⟩
  | .leave => releaseScope state
  | .close lockAvailable => requestClose state lockAvailable
  | .observe index => ⟨state, [.observed state.retained[index]?]⟩
  | .callbackEffect label => ⟨state, [.callbackEffect label]⟩

end Reference

namespace Native

structure State (Value : Type u) where
  activeEntries : Nat
  closed : Bool
  nativeWorkClosed : Bool
  retained : List Value
  deriving DecidableEq, Repr

def scopeEnter (state : State Value) : State Value :=
  {state with activeEntries := state.activeEntries + 1}

/-- This mutation precedes the foreign cancellation callback. There is no
second callback when reentrant code encounters an already claimed latch. -/
def claimNative (state : State Value) : Transition (State Value) Value :=
  if state.nativeWorkClosed then ⟨state, []⟩
  else ⟨{state with nativeWorkClosed := true}, [.cancelNative]⟩

def settle (state : State Value) : Transition (State Value) Value :=
  if state.activeEntries == 0 && state.closed then claimNative state
  else ⟨state, []⟩

def scopeLeave (state : State Value) (event : Event Value := .left) :
    Transition (State Value) Value :=
  if state.activeEntries == 0 then ⟨state, [.unmatchedLeave]⟩
  else
    let departed := {state with activeEntries := state.activeEntries - 1}
    let result := settle departed
    ⟨result.next, event :: result.events⟩

/-- The administrative entry is permitted only after observing zero client
scopes under the engine lock. It is not a fresh execution admission. -/
def requestClose (state : State Value) (lockAvailable : Bool) : Transition (State Value) Value :=
  let marked := {state with closed := true}
  if lockAvailable && state.activeEntries == 0 then
    let entered := scopeEnter marked
    let claimed := claimNative entered
    let departed := scopeLeave claimed.next .administrativeLeave
    ⟨departed.next,
      [.requestedClose, .administrativeEnter] ++ claimed.events ++ departed.events⟩
  else ⟨marked, [.requestedClose]⟩

def step (state : State Value) : Action → Transition (State Value) Value
  | .enterExecution =>
      if state.closed then ⟨state, [.rejectedExecution]⟩
      else ⟨scopeEnter state, [.entered .execution]⟩
  | .enterMetadata => ⟨scopeEnter state, [.entered .metadata]⟩
  | .leave => scopeLeave state
  | .close lockAvailable => requestClose state lockAvailable
  | .observe index => ⟨state, [.observed state.retained[index]?]⟩
  | .callbackEffect label => ⟨state, [.callbackEffect label]⟩

end Native

/-- The source stack and lifecycle phase independently determine the native
count and flags. Retained observations remain a separate exact component. -/
def Related (reference : Reference.State Value) (native : Native.State Value) : Prop :=
  native.activeEntries = reference.scopes.length ∧
    native.closed = reference.phase.closed ∧
    native.nativeWorkClosed = reference.phase.isClaimed ∧
    native.retained = reference.retained

theorem step_refines (reference : Reference.State Value) (native : Native.State Value)
    (related : Related reference native) (action : Action) :
    Related (Reference.step reference action).next (Native.step native action).next ∧
      (Reference.step reference action).events = (Native.step native action).events := by
  rcases reference with ⟨scopes, phase, retained⟩
  rcases native with ⟨active, closed, claimed, values⟩
  change active = scopes.length ∧ closed = phase.closed ∧
    claimed = phase.isClaimed ∧ values = retained at related
  obtain ⟨rfl, rfl, rfl, rfl⟩ := related
  cases action with
  | enterExecution =>
      cases phase <;> simp [Reference.step, Native.step, Related, Reference.Phase.closed,
        Reference.Phase.isClaimed, Native.scopeEnter]
  | enterMetadata =>
      simp [Reference.step, Native.step, Related, Native.scopeEnter]
  | leave =>
      cases scopes with
      | nil => simp [Reference.step, Reference.releaseScope, Native.step, Native.scopeLeave, Related]
      | cons first rest =>
          cases rest <;> cases phase <;>
            simp [Reference.step, Reference.releaseScope, Native.step, Native.scopeLeave,
              Native.settle, Native.claimNative, Related, Reference.Phase.closed, Reference.Phase.isClaimed]
  | close available =>
      cases scopes <;> cases phase <;> cases available <;>
        simp [Reference.step, Reference.requestClose, Reference.Phase.request,
          Reference.Phase.closed, Reference.Phase.isClaimed, Native.step, Native.requestClose,
          Native.scopeEnter, Native.claimNative, Native.scopeLeave, Native.settle, Related]
  | observe index => simp [Reference.step, Native.step, Related]
  | callbackEffect label => simp [Reference.step, Native.step, Related]

def run {State : Type v} (step : State → Action → Transition State Value) :
    State → List Action → Transition State Value
  | state, [] => ⟨state, []⟩
  | state, action :: rest =>
      let first := step state action
      let later := run step first.next rest
      ⟨later.next, first.events ++ later.events⟩

theorem run_append {State : Type v} (step : State → Action → Transition State Value)
    (state : State) (first second : List Action) :
    run step state (first ++ second) =
      let firstRun := run step state first
      let suffix := run step firstRun.next second
      ⟨suffix.next, firstRun.events ++ suffix.events⟩ := by
  induction first generalizing state with
  | nil => simp [run]
  | cons action rest ih => simp [run, ih, List.append_assoc]

/-- Every finite nested-close trace preserves exact observations and event
order, not only the final closed flag or a cancellation counter. -/
theorem run_refines (reference : Reference.State Value) (native : Native.State Value)
    (related : Related reference native) (actions : List Action) :
    Related (run Reference.step reference actions).next (run Native.step native actions).next ∧
      (run Reference.step reference actions).events = (run Native.step native actions).events := by
  induction actions generalizing reference native with
  | nil => exact ⟨related, rfl⟩
  | cons action rest ih =>
      obtain ⟨next, events⟩ := step_refines reference native related action
      obtain ⟨final, later⟩ := ih _ _ next
      exact ⟨final, by simp only [run, events, later]⟩

def cancellationCount (events : List (Event Value)) : Nat :=
  events.countP fun event => match event with | .cancelNative => true | _ => false

def executionCount (events : List (Event Value)) : Nat :=
  events.countP fun event => match event with | .entered .execution => true | _ => false

def claimedCredit (state : Native.State Value) : Nat := if state.nativeWorkClosed then 1 else 0

theorem cancellationCount_append (first second : List (Event Value)) :
    cancellationCount (first ++ second) = cancellationCount first + cancellationCount second := by
  simp [cancellationCount]

theorem executionCount_append (first second : List (Event Value)) :
    executionCount (first ++ second) = executionCount first + executionCount second := by
  simp [executionCount]

/-- Each cancellation event consumes the one previously unclaimed native
lifetime. Repeated close attempts cannot manufacture another lifetime. -/
theorem native_step_laws (state : Native.State Value) (action : Action) :
    (Native.step state action).next.retained = state.retained ∧
      (state.closed = true → (Native.step state action).next.closed = true) ∧
      claimedCredit state + cancellationCount (Native.step state action).events =
        claimedCredit (Native.step state action).next := by
  rcases state with ⟨active, closed, claimed, retained⟩
  cases action with
  | enterExecution =>
      cases closed <;> simp [Native.step, Native.scopeEnter, claimedCredit, cancellationCount]
  | enterMetadata => simp [Native.step, Native.scopeEnter, claimedCredit, cancellationCount]; rfl
  | leave =>
      cases active with
      | zero => simp [Native.step, Native.scopeLeave, claimedCredit, cancellationCount]
      | succ active =>
          cases active <;> cases closed <;> cases claimed <;>
            simp [Native.step, Native.scopeLeave, Native.settle, Native.claimNative,
              claimedCredit, cancellationCount]
  | close available =>
      cases active <;> cases available <;> cases claimed <;>
        simp [Native.step, Native.requestClose, Native.scopeEnter, Native.claimNative,
          Native.scopeLeave, Native.settle, claimedCredit, cancellationCount]
  | observe index => simp [Native.step, claimedCredit, cancellationCount]; rfl
  | callbackEffect label => simp [Native.step, claimedCredit, cancellationCount]; rfl

theorem native_run_laws (state : Native.State Value) (actions : List Action) :
    (run Native.step state actions).next.retained = state.retained ∧
      (state.closed = true → (run Native.step state actions).next.closed = true) ∧
      claimedCredit state + cancellationCount (run Native.step state actions).events =
        claimedCredit (run Native.step state actions).next := by
  induction actions generalizing state with
  | nil => simp [run, cancellationCount]
  | cons action rest ih =>
      obtain ⟨retained, closed, credit⟩ := native_step_laws state action
      obtain ⟨laterRetained, laterClosed, laterCredit⟩ := ih (Native.step state action).next
      refine ⟨laterRetained.trans retained, fun wasClosed => laterClosed (closed wasClosed), ?_⟩
      simp only [run, cancellationCount_append]
      omega

theorem cancellation_at_most_once (state : Native.State Value) (actions : List Action) :
    cancellationCount (run Native.step state actions).events ≤ 1 := by
  have balance := (native_run_laws state actions).2.2
  have bound : claimedCredit (run Native.step state actions).next ≤ 1 := by
    unfold claimedCredit
    split <;> omega
  omega

theorem claimed_before_callback (state : Native.State Value) :
    (Native.claimNative state).next.nativeWorkClosed = true := by
  cases flag : state.nativeWorkClosed <;> simp [Native.claimNative, flag]

theorem claim_is_idempotent (state : Native.State Value) :
    Native.claimNative (Native.claimNative state).next =
      ⟨(Native.claimNative state).next, []⟩ := by
  cases flag : state.nativeWorkClosed <;> simp [Native.claimNative, flag]

theorem claimed_trace_never_recancels (state : Native.State Value) (actions : List Action)
    (claimed : state.nativeWorkClosed = true) :
    cancellationCount (run Native.step state actions).events = 0 := by
  have balance := (native_run_laws state actions).2.2
  have before : claimedCredit state = 1 := by simp [claimedCredit, claimed]
  have bound : claimedCredit (run Native.step state actions).next ≤ 1 := by
    unfold claimedCredit
    split <;> omega
  omega

theorem close_during_active_scope (state : Native.State Value) (available : Bool)
    (active : 0 < state.activeEntries) :
    Native.requestClose state available = ⟨{state with closed := true}, [.requestedClose]⟩ := by
  have nonzero : state.activeEntries ≠ 0 := by omega
  simp [Native.requestClose, nonzero]

theorem unavailable_lock_keeps_close_pending (state : Native.State Value) :
    Native.requestClose state false = ⟨{state with closed := true}, [.requestedClose]⟩ := by
  simp [Native.requestClose]

theorem last_leave_performs_pending_cancellation (state : Native.State Value)
    (last : state.activeEntries = 1) (closed : state.closed = true)
    (unclaimed : state.nativeWorkClosed = false) :
    Native.scopeLeave state =
      ⟨{state with activeEntries := 0, nativeWorkClosed := true}, [.left, .cancelNative]⟩ := by
  simp [Native.scopeLeave, last, Native.settle, closed, Native.claimNative, unclaimed]

theorem nested_leave_keeps_native_work (state : Native.State Value) (depth : Nat)
    (nested : state.activeEntries = depth + 2) :
    Native.scopeLeave state = ⟨{state with activeEntries := depth + 1}, [.left]⟩ := by
  simp [Native.scopeLeave, nested, Native.settle]

theorem closed_execution_is_rejected (state : Native.State Value) (closed : state.closed = true) :
    Native.step state .enterExecution = ⟨state, [.rejectedExecution]⟩ := by
  simp [Native.step, closed]

theorem retained_observation_after_close (state : Native.State Value) (index : Nat) :
    Native.step {state with closed := true} (.observe index) =
      ⟨{state with closed := true}, [.observed state.retained[index]?]⟩ := rfl

theorem closed_step_enters_no_execution (state : Native.State Value) (action : Action)
    (closed : state.closed = true) : executionCount (Native.step state action).events = 0 := by
  rcases state with ⟨active, flag, claimed, retained⟩
  change flag = true at closed
  subst flag
  cases action with
  | enterExecution => simp [Native.step, executionCount]
  | enterMetadata => simp [Native.step, executionCount]
  | leave =>
      cases active with
      | zero => simp [Native.step, Native.scopeLeave, executionCount]
      | succ active =>
          cases active <;> cases claimed <;>
            simp [Native.step, Native.scopeLeave, Native.settle, Native.claimNative, executionCount]
  | close available =>
      cases active <;> cases available <;> cases claimed <;>
        simp [Native.step, Native.requestClose, Native.scopeEnter, Native.claimNative,
          Native.scopeLeave, Native.settle, executionCount]
  | observe index => simp [Native.step, executionCount]
  | callbackEffect label => simp [Native.step, executionCount]

theorem closed_trace_enters_no_execution (state : Native.State Value) (actions : List Action)
    (closed : state.closed = true) : executionCount (run Native.step state actions).events = 0 := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      have nextClosed := (native_step_laws state action).2.1 closed
      simpa only [run, executionCount_append, closed_step_enters_no_execution state action closed,
        Nat.zero_add] using ih (Native.step state action).next nextClosed

/-! Cleanup callbacks can reenter metadata, request another close, attempt
fresh execution and emit actual callback effects. Their scopes are balanced
by construction. No callback can manufacture a new native lifetime. -/
inductive Callback where
  | done
  | close (lockAvailable : Bool)
  | execute
  | observe (index : Nat)
  | effect (label : Nat)
  | metadata (body : Callback)
  | sequence (first second : Callback)
  deriving DecidableEq, Repr

def Callback.actions : Callback → List Action
  | .done => []
  | .close available => [.close available]
  | .execute => [.enterExecution]
  | .observe index => [.observe index]
  | .effect label => [.callbackEffect label]
  | .metadata body => .enterMetadata :: (body.actions ++ [.leave])
  | .sequence first second => first.actions ++ second.actions

theorem metadata_leave_preserves_claimed (state : Native.State Value)
    (claimed : state.nativeWorkClosed = true) :
    Native.scopeLeave (Native.scopeEnter state) = ⟨state, [.left]⟩ := by
  rcases state with ⟨active, closed, flag, retained⟩
  change flag = true at claimed
  subst flag
  cases active <;> cases closed <;>
    simp [Native.scopeLeave, Native.scopeEnter, Native.settle, Native.claimNative]

/-- Reentrant metadata is permitted after close; its balanced scopes leave
the caller's administrative entry, lifetime latch and retained data intact. -/
theorem callbacks_return_to_owner (state : Native.State Value) (callback : Callback)
    (closed : state.closed = true) (claimed : state.nativeWorkClosed = true) :
    (run Native.step state callback.actions).next = state := by
  induction callback generalizing state with
  | done => rfl
  | close available =>
      rcases state with ⟨active, flag, latch, retained⟩
      change flag = true at closed
      change latch = true at claimed
      subst flag
      subst latch
      cases active <;> cases available <;>
        simp [Callback.actions, run, Native.step, Native.requestClose, Native.scopeEnter,
          Native.claimNative, Native.scopeLeave, Native.settle]
  | execute => simp [Callback.actions, run, closed_execution_is_rejected state closed]
  | observe index => rfl
  | effect label => rfl
  | metadata body ih =>
      change (run Native.step (Native.scopeEnter state) (body.actions ++ [.leave])).next = state
      rw [run_append]
      have returned := ih (Native.scopeEnter state) closed claimed
      simp only [returned, run, Native.step, metadata_leave_preserves_claimed state claimed]
  | sequence first second ihFirst ihSecond =>
      rw [Callback.actions, run_append]
      simpa only [ihFirst state closed claimed] using ihSecond state closed claimed

theorem callback_effects_never_repeat_cancellation (state : Native.State Value) (callback : Callback)
    (claimed : state.nativeWorkClosed = true) :
    cancellationCount (run Native.step state callback.actions).events = 0 :=
  claimed_trace_never_recancels state callback.actions claimed

theorem callbacks_cannot_restart_execution (state : Native.State Value) (callback : Callback)
    (closed : state.closed = true) :
    executionCount (run Native.step state callback.actions).events = 0 :=
  closed_trace_enters_no_execution state callback.actions closed

namespace Native

/-- The callback runs between latch acquisition and administrative leave,
with the real administrative scope still included in activeEntries. -/
def closeWithCallbacks (state : State Value) (available : Bool) (callback : Callback) :
    Transition (State Value) Value :=
  let marked := {state with closed := true}
  if available && state.activeEntries == 0 then
    let entered := scopeEnter marked
    let claimed := claimNative entered
    let called := if entered.nativeWorkClosed then ⟨claimed.next, []⟩
        else run step claimed.next callback.actions
    let departed := scopeLeave called.next .administrativeLeave
    ⟨departed.next,
      [.requestedClose, .administrativeEnter] ++ claimed.events ++ called.events ++ departed.events⟩
  else ⟨marked, [.requestedClose]⟩

end Native

theorem administrative_callback_boundary (state : Native.State Value)
    (quiescent : state.activeEntries = 0) :
    let entered := Native.scopeEnter {state with closed := true}
    let boundary := (Native.claimNative entered).next
    boundary.activeEntries = 1 ∧ boundary.closed = true ∧ boundary.nativeWorkClosed = true ∧
      boundary.retained = state.retained := by
  rcases state with ⟨active, closed, latch, retained⟩
  change active = 0 at quiescent
  subst active
  cases latch <;> simp [Native.scopeEnter, Native.claimNative]

/-- The cancellation invocation precedes every callback event. The caller's
administrative scope is released only after all nested metadata scopes return. -/
theorem quiescent_close_with_callbacks (state : Native.State Value) (callback : Callback)
    (quiescent : state.activeEntries = 0) :
    let boundary := (Native.claimNative (Native.scopeEnter {state with closed := true})).next
    let called := run Native.step boundary callback.actions
    Native.closeWithCallbacks state true callback =
      ⟨{state with activeEntries := 0, closed := true, nativeWorkClosed := true},
        [.requestedClose, .administrativeEnter] ++
          (if state.nativeWorkClosed then [] else [.cancelNative]) ++
          (if state.nativeWorkClosed then [] else called.events) ++ [.administrativeLeave]⟩ := by
  rcases state with ⟨active, closed, latch, retained⟩
  change active = 0 at quiescent
  subst active
  have returned := callbacks_return_to_owner
    (⟨1, true, true, retained⟩ : Native.State Value) callback rfl rfl
  cases latch <;>
    simp [Native.closeWithCallbacks, Native.scopeEnter, Native.claimNative,
      returned, Native.scopeLeave, Native.settle]

theorem quiescent_close_cancels_once_with_callbacks (state : Native.State Value) (callback : Callback)
    (quiescent : state.activeEntries = 0) (unclaimed : state.nativeWorkClosed = false) :
    cancellationCount (Native.closeWithCallbacks state true callback).events = 1 := by
  rcases state with ⟨active, closed, latch, retained⟩
  change active = 0 at quiescent
  change latch = false at unclaimed
  subst active
  subst latch
  rw [quiescent_close_with_callbacks _ callback rfl]
  have noMore := callback_effects_never_repeat_cancellation
    (⟨1, true, true, retained⟩ : Native.State Value) callback rfl
  simp only [Bool.false_eq_true, ↓reduceIte, cancellationCount_append]
  change 0 + 1 + cancellationCount
    (run Native.step (⟨1, true, true, retained⟩ : Native.State Value) callback.actions).events + 0 = 1
  omega

namespace Native

/-- The outer client's last leave invokes cleanup before restoring its
saved context. No extra administrative scope is needed on this route. -/
def leaveWithCallbacks (state : State Value) (callback : Callback) : Transition (State Value) Value :=
  if state.activeEntries == 0 then ⟨state, [.unmatchedLeave]⟩
  else
    let departed := {state with activeEntries := state.activeEntries - 1}
    if departed.activeEntries == 0 && departed.closed then
      let claimed := claimNative departed
      let called := if departed.nativeWorkClosed then ⟨claimed.next, []⟩
          else run step claimed.next callback.actions
      ⟨called.next, [.left] ++ claimed.events ++ called.events⟩
    else ⟨departed, [.left]⟩

end Native

theorem last_leave_with_callbacks (state : Native.State Value) (callback : Callback)
    (last : state.activeEntries = 1) (closed : state.closed = true)
    (unclaimed : state.nativeWorkClosed = false) :
    Native.leaveWithCallbacks state callback =
      ⟨{state with activeEntries := 0, nativeWorkClosed := true},
        [.left, .cancelNative] ++
          (run Native.step {state with activeEntries := 0, nativeWorkClosed := true}
            callback.actions).events⟩ := by
  rcases state with ⟨active, flag, latch, retained⟩
  change active = 1 at last
  change flag = true at closed
  change latch = false at unclaimed
  subst active
  subst flag
  subst latch
  have returned := callbacks_return_to_owner
    (⟨0, true, true, retained⟩ : Native.State Value) callback rfl rfl
  simp [Native.leaveWithCallbacks, Native.claimNative, returned]

theorem claimed_close_skips_callbacks (state : Native.State Value) (callback : Callback)
    (claimed : state.nativeWorkClosed = true) :
    Native.closeWithCallbacks state true callback = Native.requestClose state true := by
  rcases state with ⟨active, closed, latch, retained⟩
  change latch = true at claimed
  subst latch
  cases active <;> simp [Native.closeWithCallbacks, Native.requestClose, Native.scopeEnter,
    Native.claimNative, Native.scopeLeave, Native.settle]

namespace Controls

def initial : Native.State Nat := ⟨0, false, false, [7, 7, 9]⟩

theorem active_close_keeps_resources_until_last_leave :
    let beforeLeave := run Native.step initial [.enterExecution, .close true, .observe 0]
    beforeLeave.next.activeEntries = 1 ∧ beforeLeave.next.closed = true ∧
      beforeLeave.next.nativeWorkClosed = false ∧
      beforeLeave.events = [.entered .execution, .requestedClose, .observed (some 7)] ∧
      (Native.step beforeLeave.next .leave).events = [.left, .cancelNative] := by decide

theorem nested_and_repeated_close_do_not_cancel_an_inner_scope :
    let before := run Native.step initial
      [.enterExecution, .enterMetadata, .close true, .close true, .leave]
    before.next.activeEntries = 1 ∧ before.next.nativeWorkClosed = false ∧
      cancellationCount before.events = 0 ∧
      (Native.step before.next .leave).events = [.left, .cancelNative] := by decide

theorem closed_engine_rejects_execution_and_retains_results :
    let result := run Native.step initial [.close true, .enterExecution, .observe 0, .observe 1]
    result.next.retained = [7, 7, 9] ∧ cancellationCount result.events = 1 ∧
      result.events = [.requestedClose, .administrativeEnter, .cancelNative, .administrativeLeave,
        .rejectedExecution, .observed (some 7), .observed (some 7)] := by decide

theorem unavailable_close_is_serviced_by_a_later_metadata_leave :
    let pending := (Native.step initial (.close false)).next
    pending.closed = true ∧ pending.nativeWorkClosed = false ∧
      (run Native.step pending [.enterMetadata, .leave]).events =
        [.entered .metadata, .left, .cancelNative] := by decide

def reentrant : Callback :=
  .metadata (.sequence (.close true)
    (.sequence (.metadata (.sequence (.effect 11) (.observe 0)))
      (.sequence .execute (.observe 1))))

theorem administrative_cleanup_allows_nested_metadata_without_reentry :
    let result := Native.closeWithCallbacks initial true reentrant
    result.next = ⟨0, true, true, [7, 7, 9]⟩ ∧
      result.events = [.requestedClose, .administrativeEnter, .cancelNative,
        .entered .metadata, .requestedClose, .entered .metadata, .callbackEffect 11,
        .observed (some 7), .left, .rejectedExecution, .observed (some 7),
        .left, .administrativeLeave] := by decide

theorem deferred_cleanup_also_claims_before_reentrant_callbacks :
    let pending : Native.State Nat := ⟨1, true, false, [7]⟩
    let result := Native.leaveWithCallbacks pending reentrant
    result.next = ⟨0, true, true, [7]⟩ ∧ cancellationCount result.events = 1 ∧
      executionCount result.events = 0 := by decide

/-- Cancelling at the request instead of the quiescent boundary violates
the live scope's resource lifetime, even if the final closed flag agrees. -/
theorem premature_cancellation_is_detected :
    let active : Native.State Nat := ⟨1, false, false, [7]⟩
    cancellationCount (Native.requestClose active true).events = 0 ∧
      cancellationCount (Native.claimNative {active with closed := true}).events = 1 := by decide

/-- Decrementing without the pending-close join loses required cleanup. -/
theorem omitting_last_leave_cleanup_is_detected :
    let pending : Native.State Nat := ⟨1, true, false, [7]⟩
    let faulty := {pending with activeEntries := pending.activeEntries - 1}
    (Native.scopeLeave pending).next.nativeWorkClosed = true ∧ faulty.nativeWorkClosed = false := by decide

def lateLatch (state : Native.State Nat) : Transition (Native.State Nat) Nat :=
  let nested := Native.step {state with closed := true} (.close true)
  ⟨{nested.next with nativeWorkClosed := true}, .cancelNative :: nested.events⟩

def earlyLatch (state : Native.State Nat) : Transition (Native.State Nat) Nat :=
  let claimed := Native.claimNative {state with closed := true}
  let nested := Native.step claimed.next (.close true)
  ⟨nested.next, claimed.events ++ nested.events⟩

/-- The callback can close again before a late latch is written. The event
trace distinguishes two real cleanup invocations from one final true flag. -/
theorem latch_after_callback_repeats_cancellation :
    (lateLatch initial).next.nativeWorkClosed = true ∧
      (earlyLatch initial).next.nativeWorkClosed = true ∧
      cancellationCount (lateLatch initial).events = 2 ∧
      cancellationCount (earlyLatch initial).events = 1 := by decide

theorem clearing_retained_values_on_close_loses_an_observation :
    let closed := (Native.requestClose initial true).next
    (Native.step closed (.observe 0)).events = [.observed (some 7)] ∧
      (Native.step {closed with retained := ([] : List Nat)} (.observe 0)).events = [.observed none] := by decide

theorem ignoring_closed_admission_reopens_execution :
    let closed := (Native.requestClose initial true).next
    (Native.step closed .enterExecution).events = [.rejectedExecution] ∧
      (Native.scopeEnter closed).activeEntries = 1 := by decide

theorem repeated_cleanup_does_not_rerun_callback_effects :
    let first := (Native.closeWithCallbacks initial true (.effect 11)).next
    (Native.closeWithCallbacks first true (.effect 22)).events =
      [.requestedClose, .administrativeEnter, .administrativeLeave] := by decide

end Controls

end Mettapedia.Machines.DeferredClose
