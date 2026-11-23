import Mettapedia.Languages.Prolog.SWI.Publish

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Constraint guards before destructive retraction

A protocol abstraction of SWI-Prolog commit `6b14930` on `cf6960c`.
`decompile`/`decompileHead` establish structural unification. Pending wakeups
must then accept before the outer operation calls `retractClauseDefinition`.
A wakeup may have its own persistent database effects; those are distinguished
from the outer operation's erase requests. `foreignWakeup` observes one query
result and cuts its remaining alternatives.

Candidate selection and constraint solving are inputs. The scanner describes
erase requests, not the return value of `retractClauseDefinition`: event vetoes,
reentrant removal of the current candidate, and the first-call generation
refresh belong to the surrounding C loop. No fixed-generation enumeration or
whole-database rollback is assumed here.
-/

namespace Mettapedia.Languages.Prolog.SWI.Retract

inductive Verdict (E : Type) where
  | accepted
  | rejected
  | raised (error : E)
  deriving DecidableEq

inductive Edit (K : Type) where
  | insert (key : K)
  | erase (key : K)
  deriving DecidableEq

/-- An observation of the first query result. Effects include the search up to
    that observation; the alternatives are continuations discarded by cut. -/
structure Wake (K E : Type) where
  verdict : Verdict E
  effects : List (Edit K) := []
  alternatives : List (List (Edit K) × Verdict E) := []

structure Candidate (K E : Type) where
  key : K
  /-- Ordinary structural success; decompilation exceptions are outside this abstraction. -/
  unifies : Bool
  /-- None means ALERT_WAKEUP is clear. Other alert bits do not enter the guard. -/
  wake : Option (Wake K E) := none
  otherAlerts : Nat := 0

inductive Event (K E : Type) where
  | callback (edit : Edit K)
  | checked (key : K) (verdict : Verdict E)
  /-- An erase requested by this retract operation, not by a wakeup. -/
  | erase (key : K)
  deriving DecidableEq

variable {K E : Type}

/-- The result of clause_constraints_run after propagating a caught exception.
    A true query return cannot authorize erasure with an exception pending. -/
def guardResult (returned : Bool) (pending : Option E) : Verdict E :=
  match pending with
  | some e => .raised e
  | none => if returned then .accepted else .rejected

theorem guard_result_pending_exception (returned : Bool) (e : E) :
    guardResult returned (some e) = .raised e := rfl

theorem guard_result_accepted_iff (returned : Bool) (pending : Option E) :
    guardResult returned pending = .accepted ↔ returned = true ∧ pending = none := by
  cases pending <;> cases returned <;> simp [guardResult]

def decision (c : Candidate K E) : Verdict E :=
  if c.unifies then
    match c.wake with
    | none => .accepted
    | some w => w.verdict
  else .rejected

def callbacks (w : Wake K E) : List (Event K E) := w.effects.map Event.callback

def checkedTrace (k : K) : Verdict E → List (Event K E)
  | .accepted => [.checked k .accepted, .erase k]
  | .rejected => [.checked k .rejected]
  | .raised e => [.checked k (.raised e)]

/-- `before = false` retains the old erase-before-wakeup ordering on a pending
    candidate. One such candidate witnesses the bug for either predicate. -/
def candidateTrace (before : Bool) (c : Candidate K E) : List (Event K E) :=
  if c.unifies then
    match c.wake with
    | none => checkedTrace c.key .accepted
    | some w =>
      if before then callbacks w ++ checkedTrace c.key w.verdict
      else .erase c.key :: (callbacks w ++ [.checked c.key w.verdict])
  else []

def Event.isErase : Event K E → Bool
  | .erase _ => true
  | _ => false

/-- Each direct erase is immediately preceded by its successful guard.
    Callback edits are separate events and cannot certify an outer erase. -/
inductive Guarded : List (Event K E) → Prop where
  | nil : Guarded []
  | other {e : Event K E} {es : List (Event K E)} :
      e.isErase = false → Guarded es → Guarded (e :: es)
  | commit (k : K) {es : List (Event K E)} :
      Guarded es → Guarded (.checked k .accepted :: .erase k :: es)

theorem Guarded.append {xs ys : List (Event K E)} (hx : Guarded xs) (hy : Guarded ys) :
    Guarded (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | other he _ ih => exact .other he ih
  | commit k _ ih => exact .commit k ih

theorem Guarded.no_initial_erase {k : K} {es : List (Event K E)} :
    ¬ Guarded (.erase k :: es) := by
  intro h
  cases h with
  | other he _ => cases he

theorem callbacks_guarded (w : Wake K E) : Guarded (callbacks w) := by
  unfold callbacks
  induction w.effects with
  | nil => exact .nil
  | cons e es ih => exact .other rfl ih

theorem checked_trace_guarded (k : K) (v : Verdict E) : Guarded (checkedTrace k v) := by
  cases v with
  | accepted => exact .commit k .nil
  | rejected => exact .other rfl .nil
  | raised e => exact .other rfl .nil

theorem fixed_candidate_guarded (c : Candidate K E) : Guarded (candidateTrace true c) := by
  unfold candidateTrace
  split
  · cases c.wake with
    | none => exact checked_trace_guarded _ _
    | some w => exact (callbacks_guarded w).append (checked_trace_guarded _ _)
  · exact .nil

theorem structural_failure_short_circuits (before : Bool) (c : Candidate K E)
    (h : c.unifies = false) : candidateTrace before c = [] ∧ decision c = .rejected := by
  simp [candidateTrace, decision, h]

theorem no_wakeup_fast_path (before : Bool) (c : Candidate K E)
    (hu : c.unifies = true) (hw : c.wake = none) :
    candidateTrace before c = [.checked c.key .accepted, .erase c.key] := by
  simp [candidateTrace, checkedTrace, hu, hw]

theorem unrelated_alerts_ignored (before : Bool) (c : Candidate K E) (bits : Nat) :
    candidateTrace before { c with otherAlerts := bits } = candidateTrace before c ∧
    decision { c with otherAlerts := bits } = decision c := ⟨rfl, rfl⟩

theorem foreign_wakeup_cuts_alternatives (before : Bool) (k : K) (w : Wake K E)
    (later : List (List (Edit K) × Verdict E)) :
    candidateTrace before { key := k, unifies := true, wake := some { w with alternatives := later } } =
      candidateTrace before { key := k, unifies := true, wake := some w } := rfl

/-- These modes stop at the first authorized erase request, or visit all
    candidates. They do not model C callback vetoes or retract's redo context. -/
inductive Mode where
  | firstAuthorized | allCandidates
  deriving DecidableEq

inductive Outcome (K E : Type) where
  | exhausted
  | authorized (key : K)
  | exception (error : E)
  deriving DecidableEq

structure Result (K E : Type) where
  trace : List (Event K E)
  outcome : Outcome K E

def Result.prepend (es : List (Event K E)) (r : Result K E) : Result K E :=
  { trace := es ++ r.trace, outcome := r.outcome }

def Result.then (r next : Result K E) : Result K E :=
  match r.outcome with
  | .exhausted => next.prepend r.trace
  | _ => r

def scan (before : Bool) (mode : Mode) : List (Candidate K E) → Result K E
  | [] => ⟨[], .exhausted⟩
  | c :: cs =>
    let es := candidateTrace before c
    match decision c with
    | .raised e => ⟨es, .exception e⟩
    | .accepted =>
      match mode with
      | .firstAuthorized => ⟨es, .authorized c.key⟩
      | .allCandidates => (scan before mode cs).prepend es
    | .rejected => (scan before mode cs).prepend es

theorem fixed_scan_guarded (mode : Mode) (cs : List (Candidate K E)) :
    Guarded (scan true mode cs).trace := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    cases hd : decision c with
    | raised e => simpa [scan, hd] using fixed_candidate_guarded c
    | rejected => simpa [scan, hd, Result.prepend] using (fixed_candidate_guarded c).append ih
    | accepted =>
      cases mode with
      | firstAuthorized => simpa [scan, hd] using fixed_candidate_guarded c
      | allCandidates => simpa [scan, hd, Result.prepend] using (fixed_candidate_guarded c).append ih

theorem Result.prepend_then (es : List (Event K E)) (r next : Result K E) :
    (r.prepend es).then next = (r.then next).prepend es := by
  cases r with
  | mk tr out => cases out <;> simp [Result.prepend, Result.then, List.append_assoc]

theorem scan_append (before : Bool) (mode : Mode) (xs ys : List (Candidate K E)) :
    scan before mode (xs ++ ys) = (scan before mode xs).then (scan before mode ys) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    cases hd : decision c with
    | raised e => simp [scan, hd, Result.then]
    | rejected => simp [scan, hd, ih, Result.prepend_then]
    | accepted =>
      cases mode with
      | firstAuthorized => simp [scan, hd, Result.then]
      | allCandidates => simp [scan, hd, ih, Result.prepend_then]

/-- A throwing prefix ends the traversal. Its previous requests and wakeup
    effects remain; no suffix candidate is evaluated. -/
theorem exception_stops_scan (before : Bool) (mode : Mode) (xs ys : List (Candidate K E))
    (e : E) (h : (scan before mode xs).outcome = .exception e) :
    scan before mode (xs ++ ys) = scan before mode xs := by
  rw [scan_append]
  simp [Result.then, h]

def requests : List (Event K E) → List K
  | [] => []
  | .erase k :: es => k :: requests es
  | _ :: es => requests es

theorem requests_append (xs ys : List (Event K E)) :
    requests (xs ++ ys) = requests xs ++ requests ys := by
  induction xs with
  | nil => rfl
  | cons e es ih => cases e <;> simp [requests, ih]

theorem callbacks_no_requests (w : Wake K E) : requests (callbacks w) = [] := by
  unfold callbacks
  induction w.effects with
  | nil => rfl
  | cons e es ih => exact ih

def acceptedRequest (c : Candidate K E) : List K :=
  match decision c with
  | .accepted => [c.key]
  | _ => []

theorem fixed_candidate_requests (c : Candidate K E) :
    requests (candidateTrace true c) = acceptedRequest c := by
  unfold candidateTrace acceptedRequest decision
  split
  · cases c.wake with
    | none => rfl
    | some w =>
      change requests (callbacks w ++ checkedTrace c.key w.verdict) =
        (match w.verdict with | .accepted => [c.key] | _ => [])
      rw [requests_append, callbacks_no_requests]
      cases w.verdict <;> rfl
  · rfl

/-- The accepted candidates before the first exception. -/
def acceptedPrefix : List (Candidate K E) → List K
  | [] => []
  | c :: cs =>
    match decision c with
    | .accepted => c.key :: acceptedPrefix cs
    | .rejected => acceptedPrefix cs
    | .raised _ => []

theorem fixed_all_requests (cs : List (Candidate K E)) :
    requests (scan true .allCandidates cs).trace = acceptedPrefix cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases hd : decision c <;>
      simp [scan, hd, Result.prepend, requests_append, fixed_candidate_requests,
        acceptedRequest, acceptedPrefix, ih]

/-- Database replay separates the outer requests from the effects of hooks. -/
def applyEdit [DecidableEq K] (db : K → Bool) : Edit K → K → Bool
  | .insert k => fun q => if q = k then true else db q
  | .erase k => fun q => if q = k then false else db q

def replay [DecidableEq K] (db : K → Bool) : List (Event K E) → K → Bool
  | [] => db
  | .callback e :: es => replay (applyEdit db e) es
  | .erase k :: es => replay (applyEdit db (.erase k)) es
  | .checked _ _ :: es => replay db es

theorem replay_append [DecidableEq K] (db : K → Bool) (xs ys : List (Event K E)) :
    replay db (xs ++ ys) = replay (replay db xs) ys := by
  induction xs generalizing db with
  | nil => rfl
  | cons e es ih => cases e <;> simp [replay, ih]

/-- An exception does not roll back effects already in the completed prefix. -/
theorem exception_preserves_prefix [DecidableEq K] (before : Bool) (mode : Mode)
    (db : K → Bool) (xs ys : List (Candidate K E)) (e : E)
    (h : (scan before mode xs).outcome = .exception e) :
    replay db (scan before mode (xs ++ ys)).trace = replay db (scan before mode xs).trace := by
  rw [exception_stops_scan before mode xs ys e h]

/-- allVars checks plain, pairwise distinct variable cells. Attributed cells
    are a separate case even if a term classifier calls them variables. -/
inductive Arg where
  | plain (cell : Nat)
  | attributed (cell : Nat)
  | value
  deriving DecidableEq

def Arg.isPlain : Arg → Bool
  | .plain _ => true
  | _ => false

def allVars (args : List Arg) : Bool := args.all Arg.isPlain && decide args.Nodup

theorem allVars_plain (args : List Arg) (h : allVars args = true) :
    ∀ a ∈ args, ∃ cell, a = .plain cell := by
  have hp : args.all Arg.isPlain = true ∧ decide args.Nodup = true := by
    simpa [allVars] using h
  intro a ha
  have hh := List.all_eq_true.mp hp.1 a ha
  cases a with
  | plain n => exact ⟨n, rfl⟩
  | attributed n => cases hh
  | value => cases hh

theorem allVars_nonsharing (args : List Arg) (h : allVars args = true) : args.Nodup := by
  have hp : args.all Arg.isPlain = true ∧ decide args.Nodup = true := by
    simpa [allVars] using h
  exact of_decide_eq_true hp.2

theorem attributed_argument_slow (args : List Arg) (n : Nat) (h : Arg.attributed n ∈ args) :
    allVars args = false := by
  cases hv : allVars args with
  | false => rfl
  | true =>
    obtain ⟨cell, he⟩ := allVars_plain args hv (.attributed n) h
    cases he

/-- The existing publication invariant protects any visible continuation
    clause during arbitrary modeled writer/GC interleavings, including GC
    entered by a wakeup, as long as the access generation remains active. -/
theorem predicate_access_visible_live {R : Type} [DecidableEq R] [DecidableEq K]
    {s0 s : Publish.St R K} (hi : Publish.Init s0) (hr : Publish.Reach Publish.fixed s0 s)
    (r : R) (ha : (s.rd r).pc.active = true) (k : K)
    (hv : s.visAt k (s.rd r).gen) : s.freed k = false := by
  have hf := ((Publish.reach_inv (Publish.init_inv hi) hr).rd r).act_free ha k
  cases hk : s.freed k with
  | false => rfl
  | true => exact False.elim (hf hk hv)

end Mettapedia.Languages.Prolog.SWI.Retract

namespace Mettapedia.Languages.Prolog.SWI.Retract
variable {K E : Type}

theorem rejected_candidate_no_request (c : Candidate K E) (h : decision c = .rejected) :
    requests (candidateTrace true c) = [] := by
  rw [fixed_candidate_requests]
  simp [acceptedRequest, h]

theorem throwing_candidate_no_request (c : Candidate K E) (e : E) (h : decision c = .raised e) :
    requests (candidateTrace true c) = [] := by
  rw [fixed_candidate_requests]
  simp [acceptedRequest, h]

/-- A throwing candidate contributes no outer erase, and the next candidate
    is never evaluated, even if its wakeup would have effects. -/
theorem throwing_candidate_stops (mode : Mode) (c : Candidate K E)
    (cs : List (Candidate K E)) (e : E) (h : decision c = .raised e) :
    scan true mode (c :: cs) = ⟨candidateTrace true c, .exception e⟩ := by
  simp [scan, h]

/-! Concrete witnesses use clause identities 0, 1, 2 for p(a), p(b), p(c). -/
namespace Examples

def constrained (k : Nat) (verdict : Verdict Nat) (effects : List (Edit Nat) := []) : Candidate Nat Nat :=
  { key := k, unifies := true, wake := some { verdict := verdict, effects := effects } }

def accept (k : Nat) : Candidate Nat Nat := constrained k .accepted
def reject (k : Nat) : Candidate Nat Nat := constrained k .rejected
def throws (k error : Nat) : Candidate Nat Nat := constrained k (.raised error)
def present : Nat → Bool := fun _ => true

/-- Without the patch, a single rejected candidate has already been erased.
    This one-candidate schedule applies to retract and retractall. -/
theorem stock_rejection_unsafe (mode : Mode) :
    ¬ Guarded (scan false mode [reject 0]).trace ∧
    (scan false mode [reject 0]).outcome = .exhausted ∧
    replay present (scan false mode [reject 0]).trace 0 = false := by
  constructor
  · exact Guarded.no_initial_erase
  · exact ⟨rfl, by cases mode <;> decide⟩

/-- A thrown wakeup also comes too late in the old ordering. -/
theorem stock_exception_unsafe (mode : Mode) :
    ¬ Guarded (scan false mode [throws 0 17]).trace ∧
    (scan false mode [throws 0 17]).outcome = .exception 17 ∧
    replay present (scan false mode [throws 0 17]).trace 0 = false := by
  constructor
  · exact Guarded.no_initial_erase
  · exact ⟨rfl, by cases mode <;> decide⟩

theorem fixed_rejection_preserves_candidate (mode : Mode) :
    requests (scan true mode [reject 0]).trace = [] ∧
    replay present (scan true mode [reject 0]).trace 0 = true := by
  exact ⟨rfl, by cases mode <;> decide⟩

/-- Earlier authorized deletions remain after an exception; the throwing and
    subsequent clauses remain. This is a prefix commit, not a transaction. -/
theorem exception_keeps_prior_deletions :
    let r := scan true .allCandidates [accept 0, throws 1 17, accept 2]
    r.outcome = .exception 17 ∧ requests r.trace = [0] ∧
    replay present r.trace 0 = false ∧ replay present r.trace 1 = true ∧
    replay present r.trace 2 = true := by decide

/-- A failed wakeup can itself delete another clause. The outer operation
    issues no erase request, so a global rollback theorem would be false. -/
theorem failed_wakeup_can_modify_database (mode : Mode) :
    let r := scan true mode [constrained 0 .rejected [.erase 1]]
    Guarded r.trace ∧ requests r.trace = [] ∧ replay present r.trace 0 = true ∧
    replay present r.trace 1 = false := by
  refine ⟨fixed_scan_guarded mode _, rfl, ?_, ?_⟩ <;> cases mode <;> decide

/-- freeze(X, X == b): reject p(a), authorize p(b), preserve p(c). The fixed
    trace preserves p(a), unlike the old retract retry ordering. -/
theorem first_authorized_skips_rejections :
    let cs := [reject 0, accept 1, reject 2]
    let fixed := scan true .firstAuthorized cs
    let stock := scan false .firstAuthorized cs
    fixed.outcome = .authorized 1 ∧ requests fixed.trace = [1] ∧
    replay present fixed.trace 0 = true ∧ replay present fixed.trace 1 = false ∧
    replay present fixed.trace 2 = true ∧ requests stock.trace = [0, 1] := by decide

/-- The all-candidates traversal has the same guarded filtering behavior. -/
theorem all_authorized_filters_rejections :
    let r := scan true .allCandidates [reject 0, accept 1, reject 2]
    r.outcome = .exhausted ∧ requests r.trace = [1] ∧
    replay present r.trace 0 = true ∧ replay present r.trace 1 = false ∧
    replay present r.trace 2 = true := by decide

theorem no_accepted_candidate_no_deletions (mode : Mode) :
    let r := scan true mode [reject 0, reject 1, reject 2]
    r.outcome = .exhausted ∧ requests r.trace = [] ∧
    replay present r.trace 0 = true ∧ replay present r.trace 1 = true ∧
    replay present r.trace 2 = true := by
  exact ⟨rfl, rfl, by cases mode <;> decide, by cases mode <;> decide, by cases mode <;> decide⟩

/-- A partially failed structural unification does not run its scheduled hook. -/
theorem failed_structure_never_runs_hook (mode : Mode) :
    let c : Candidate Nat Nat := { constrained 0 .accepted [.erase 1] with unifies := false }
    (scan true mode [c]).trace = [] ∧
    replay present (scan true mode [c]).trace 1 = true := by
  exact ⟨rfl, by cases mode <;> decide⟩

theorem plain_nonsharing_fast_path : allVars [.plain 0, .plain 1] = true := by decide

theorem shared_variable_slow_path : allVars [.plain 0, .plain 0] = false := by decide

theorem attributed_variable_slow_path : allVars [.attributed 0] = false := by decide

end Examples
end Mettapedia.Languages.Prolog.SWI.Retract

namespace Mettapedia.Languages.Prolog.SWI.Retract
variable {K E : Type}

def Verdict.isAccepted : Verdict E → Bool
  | .accepted => true
  | _ => false

def Verdict.noException : Verdict E → Bool
  | .raised _ => false
  | _ => true

/-- An independent list specification: stop at the first throw, then filter
    the remaining prefix by successful constraint acceptance. -/
theorem accepted_prefix_filter (cs : List (Candidate K E)) :
    acceptedPrefix cs =
      ((cs.takeWhile fun c => (decision c).noException).filter fun c =>
        (decision c).isAccepted).map Candidate.key := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases hd : decision c <;>
      simp [acceptedPrefix, hd, Verdict.noException, Verdict.isAccepted, ih]

theorem fixed_all_filter (cs : List (Candidate K E)) :
    requests (scan true .allCandidates cs).trace =
      ((cs.takeWhile fun c => (decision c).noException).filter fun c =>
        (decision c).isAccepted).map Candidate.key := by
  rw [fixed_all_requests, accepted_prefix_filter]

theorem fixed_first_requests (cs : List (Candidate K E)) :
    requests (scan true .firstAuthorized cs).trace = (acceptedPrefix cs).take 1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases hd : decision c <;>
      simp [scan, hd, Result.prepend, requests_append, fixed_candidate_requests,
        acceptedRequest, acceptedPrefix, ih]

end Mettapedia.Languages.Prolog.SWI.Retract
