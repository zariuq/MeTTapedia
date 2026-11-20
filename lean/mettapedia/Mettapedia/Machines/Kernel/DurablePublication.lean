import Mettapedia.Machines.Kernel.InvocationContext

/-!
# Admission and durability of file publication

The caller can submit a move after the stream and its writes have settled.
A matching reply ends transport custody. An indeterminate durability result
leaves the caller fenced until recovery inspects the volume.
-/

namespace Mettapedia.Machines.Kernel.DurablePublication

open InvocationContext

structure Readiness where
  received : Nat
  written : Nat
  verified : Nat
  requiresReadback : Bool
  checksumMatches : Bool
  streamClosed : Bool

def Readiness.permits (r : Readiness) : Bool :=
  r.streamClosed && (r.received == r.written) &&
    (!r.requiresReadback || ((r.verified == r.written) && r.checksumMatches))

inductive Phase where
  | staged
  | waiting (run request : Nat)
  | saved (run : Nat)
  | refused
  | uncertain (run request : Nat)
  deriving DecidableEq

inductive Commit where
  | durable | refused | indeterminate

structure Receipt where
  run : Nat
  request : Nat
  commit : Commit

def submit (state : State) (phase : Phase) (context : Context)
    (ready : Readiness) (transportAccepted : Bool) : State × Phase :=
  match phase with
  | .staged =>
    if ready.permits then
      let (next, outcome) := invoke state context transportAccepted
      match outcome with
      | .blocked request | .polling request => (next, .waiting context.authorityRun request)
      | .refused => (next, .refused)
    else (state, .staged)
  | _ => (state, phase)

def receive (state : State) (phase : Phase) (reply : Receipt) : State × Phase :=
  match phase with
  | .waiting run request =>
    if reply.run == run && reply.request == request && state.currentRun == run &&
        decide (request ∈ state.pending) then
      let next := settle state request
      match reply.commit with
      | .durable => (next, .saved run)
      | .refused => (next, .refused)
      | .indeterminate => (next, .uncertain run request)
    else (state, phase)
  | _ => (state, phase)

theorem incomplete_stream_preserves (state : State) (context : Context)
    (ready : Readiness) (accepted : Bool) (openStream : ready.streamClosed = false) :
    submit state .staged context ready accepted = (state, .staged) := by
  simp [submit, Readiness.permits, openStream]

theorem readback_mismatch_preserves (state : State) (context : Context) (ready : Readiness)
    (accepted : Bool) (required : ready.requiresReadback = true)
    (mismatch : ready.checksumMatches = false) :
    submit state .staged context ready accepted = (state, .staged) := by
  simp [submit, Readiness.permits, required, mismatch]

theorem submit_stale_refuses (state : State) (context : Context) (ready : Readiness)
    (accepted : Bool) (complete : ready.permits = true)
    (stale : context.authorityRun ≠ state.currentRun) :
    submit state .staged context ready accepted = (state, .refused) := by
  simp [submit, complete, stale_run_refused state context stale accepted]

theorem submit_same_publication (state : State) (context : Context) (ready : Readiness)
    (accepted : Bool) (execution : ExecutionClass) :
    submit state .staged { context with task := { context.task with execution := execution } }
        ready accepted = submit state .staged context ready accepted := by
  simp only [submit, invoke]
  rw [authenticated_execution_irrelevant]
  by_cases prepared : ready.permits = true <;>
    by_cases allowed : (authenticated state context && accepted) = true <;>
      cases execution <;> cases context.task.execution <;>
        simp [prepared, allowed, continuation]

theorem stale_receipt_preserves (state : State) (run request : Nat) (reply : Receipt)
    (stale : reply.run ≠ run) :
    receive state (.waiting run request) reply = (state, .waiting run request) := by
  simp [receive, stale]

theorem wrong_request_preserves (state : State) (run request : Nat) (reply : Receipt)
    (wrong : reply.request ≠ request) :
    receive state (.waiting run request) reply = (state, .waiting run request) := by
  simp [receive, wrong]

theorem retired_run_preserves (state : State) (run request : Nat) (reply : Receipt)
    (retired : state.currentRun ≠ run) :
    receive state (.waiting run request) reply = (state, .waiting run request) := by
  simp [receive, retired]

theorem indeterminate_settles_only_transport (state : State) (run request : Nat)
    (current : state.currentRun = run) (outstanding : request ∈ state.pending) :
    receive state (.waiting run request) ⟨run, request, .indeterminate⟩ =
      (settle state request, .uncertain run request) := by
  simp [receive, current, outstanding]

inductive Action where
  | offer (context : Context) (ready : Readiness) (transportAccepted : Bool)
  | reply (evidence : Receipt)

def step (s : State × Phase) : Action → State × Phase
  | .offer context ready accepted => submit s.1 s.2 context ready accepted
  | .reply receipt => receive s.1 s.2 receipt

theorem uncertainty_preserved (state : State) (run request : Nat) (actions : List Action) :
    actions.foldl step (state, .uncertain run request) = (state, .uncertain run request) := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action <;> simpa only [List.foldl_cons, step, submit, receive] using ih

/-! A filesystem receipt is evaluated after the source identity and the
transfer's readiness have been checked. An indeterminate commit permits both
namespace observations on recovery. It supplies no second attempt. -/

structure FileNames where
  staging : Option Nat
  destination : Option Nat
  deriving DecidableEq

structure Replacement where
  expected : Nat
  readiness : Readiness
  receipt : Commit

def FileNames.replace (names : FileNames) (offer : Replacement) : List FileNames :=
  if offer.readiness.permits && names.staging == some offer.expected then
    let moved := ⟨none, some offer.expected⟩
    match offer.receipt with
    | .refused => [names]
    | .durable => [moved]
    | .indeterminate => [names, moved]
  else [names]

def replaceAll (names : FileNames) (offers : List Replacement) : List FileNames :=
  offers.foldl (fun reachable offer => reachable.flatMap (·.replace offer)) [names]

theorem invalid_replacement_preserves (names : FileNames) (offer : Replacement)
    (invalid : offer.readiness.permits = false ∨ names.staging ≠ some offer.expected) :
    names.replace offer = [names] := by
  rcases invalid with unready | stale <;> simp [FileNames.replace, *]

theorem invalid_replacements_preserve (names : FileNames) (offers : List Replacement)
    (invalid : ∀ offer ∈ offers, offer.readiness.permits = false ∨
      names.staging ≠ some offer.expected) :
    replaceAll names offers = [names] := by
  induction offers with
  | nil => rfl
  | cons offer rest ih =>
    have first := invalid_replacement_preserves names offer (invalid offer (by simp))
    simpa [replaceAll, first] using ih (fun e present => invalid e (by simp [present]))

theorem durable_replacement_publishes (names : FileNames) (ready : Readiness) (expected : Nat)
    (eligible : ready.permits = true) (same : names.staging = some expected) :
    names.replace ⟨expected, ready, .durable⟩ = [⟨none, some expected⟩] := by
  simp [FileNames.replace, eligible, same]

theorem indeterminate_replacement_recovers_old_or_new
    (names : FileNames) (ready : Readiness) (expected : Nat)
    (eligible : ready.permits = true) (same : names.staging = some expected) :
    names.replace ⟨expected, ready, .indeterminate⟩ = [names, ⟨none, some expected⟩] := by
  simp [FileNames.replace, eligible, same]

private def start : State := ⟨4, 8, []⟩
private def worker : Context := ⟨4, ⟨12, 4, .worker⟩⟩
private def complete : Readiness := ⟨700, 700, 700, true, true, true⟩

example : (submit start .staged worker complete true).2 = .waiting 4 9 := by decide

example : (submit start .staged worker { complete with verified := 699 } true).2 = .staged :=
  by decide

example :
    (receive (submit start .staged worker complete true).1 (.waiting 4 9) ⟨4, 9, .durable⟩).2 =
      .saved 4 := by decide

example : replaceAll ⟨some 29, some 17⟩ [
      ⟨28, complete, .durable⟩, ⟨29, { complete with streamClosed := false }, .durable⟩] =
    [⟨some 29, some 17⟩] := by decide

example : (FileNames.mk (some 29) (some 17)).replace ⟨29, complete, .durable⟩ =
    [⟨none, some 29⟩] := by decide

#print axioms submit_same_publication
#print axioms indeterminate_settles_only_transport
#print axioms uncertainty_preserved
#print axioms invalid_replacements_preserve
#print axioms durable_replacement_publishes
#print axioms indeterminate_replacement_recovers_old_or_new

end Mettapedia.Machines.Kernel.DurablePublication
