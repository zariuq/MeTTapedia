import Mathlib.Tactic

/-!
# A failed provider call's facts, classified natively

A provider call that fails is reported and paced by its native owner. What
its observers saw is kept with the call until its release, as one cause: an
admission denial with its retry-after, a transport failure the engine
classified, an answer the engine refused to keep, a refused preparation, a
completion without its local receipt, or another error class. A later
observation replaces an earlier one; a fallback (the ledger's accounting
failure) is noted only when there is none.

The facts the pacer receives are a function of the cause, the HTTP status
(0 for none) and the owner's retry-after (negative for none):
* a deterministic rejection (400–499 except 408, 409, 425, 429) is named by
  its status;
* a timeout, a rate limit (429) and a server error (5xx) are transient;
* the owner's retry-after wins; else a denial's own, never below 0; else
  none.
A compaction is maintenance: its caller learns only whether a later try can
pass, and the retry-after.

Invariants proved here:
* a deterministic rejection is named by its status, and is not transient
  unless the engine saw a timeout;
* the owner's retry-after is the one paced; a denial's retry is never below
  0; without either, no retry-after is invented;
* an observed cause survives any number of fallbacks, and the last observed
  cause is the one reported;
* a call bound again starts without a cause: a released call's cause never
  answers for the next;
* a compaction is retried exactly after a rate limit, a server error, or a
  denial with a positive retry-after.

Counterexample:
* a fallback that replaces an observed cause loses a denial's retry-after:
  the provider asked for 30 s and the pacer answers with none.

This is an abstract contract, not a refinement proof of
`src/call_failure_cetta.metta` or `src/llm_accounting_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CallFailureFacts

/-- What a failed call's observers saw. -/
inductive Cause
  | none
  | denied (retry : Int)
  | transport (timeout : Bool)
  | refusedAnswer
  | preparation
  | conflict
  | error
  deriving DecidableEq

/-- A failure's name: its error class, or a deterministic rejection's status. -/
inductive Code
  | classOf (cause : Cause)
  | rejected (status : Nat)
  deriving DecidableEq

structure Facts where
  code : Code
  transient : Bool
  retry : Int
  deriving DecidableEq

def rejectedStatus (status : Nat) : Bool :=
  decide (400 ≤ status ∧ status < 500 ∧ status ≠ 408 ∧ status ≠ 409 ∧ status ≠ 425 ∧ status ≠ 429)

def ownRetry : Cause → Int
  | .denied r => max r 0
  | _ => -1

def timeout : Cause → Bool
  | .transport t => t
  | _ => false

/-- The facts the pacer receives. -/
def facts (cause : Cause) (status : Nat) (owner : Int) : Facts where
  code := if rejectedStatus status then .rejected status else .classOf cause
  transient := timeout cause || decide (status = 429) || decide (500 ≤ status)
  retry := if 0 ≤ owner then owner else ownRetry cause

theorem rejection_named_by_status (cause : Cause) (status : Nat) (owner : Int)
    (h : rejectedStatus status = true) : (facts cause status owner).code = .rejected status := by
  simp [facts, h]

theorem rejection_not_transient (cause : Cause) (status : Nat) (owner : Int)
    (h : rejectedStatus status = true) (ht : timeout cause = false) :
    (facts cause status owner).transient = false := by
  simp only [rejectedStatus, decide_eq_true_eq] at h
  obtain ⟨_, hlt, _, _, _, h429⟩ := h
  simp [facts, ht, h429]
  omega

theorem owner_retry_paced (cause : Cause) (status : Nat) (owner : Int) (h : 0 ≤ owner) :
    (facts cause status owner).retry = owner := by
  simp [facts, h]

theorem denial_retry_never_negative (r : Int) (status : Nat) (owner : Int) :
    0 ≤ (facts (.denied r) status owner).retry := by
  by_cases h : 0 ≤ owner
  · simp [facts, h]
  · simp [facts, h, ownRetry]

theorem no_invented_retry (cause : Cause) (status : Nat) (owner : Int)
    (h : owner < 0) (hc : ∀ r, cause ≠ .denied r) : (facts cause status owner).retry = -1 := by
  have hn : ¬ 0 ≤ owner := by omega
  cases cause <;> simp_all [facts, ownRetry]

/-! ## The cause kept with a call -/

/-- What an observer notes: an observation, or the accounting fallback. -/
inductive Note
  | observed (cause : Cause)
  | fallback (cause : Cause)

def note (kept : Cause) : Note → Cause
  | .observed c => c
  | .fallback c => if kept = .none then c else kept

def keep (kept : Cause) (notes : List Note) : Cause := notes.foldl note kept

theorem fallback_never_replaces (c : Cause) (hc : c ≠ .none) (fallbacks : List Cause) :
    keep c (fallbacks.map Note.fallback) = c := by
  induction fallbacks with
  | nil => rfl
  | cons f rest ih => simpa [keep, note, hc] using ih

/-- The reported cause is the last observation, whatever fallbacks follow it. -/
theorem last_observation_reported (kept c : Cause) (hc : c ≠ .none) (fallbacks : List Cause) :
    keep kept (Note.observed c :: fallbacks.map Note.fallback) = c := by
  simpa [keep, note] using fallback_never_replaces c hc fallbacks

/-- Calls keep their causes by correlation; binding and release forget one. -/
def Store := String → Cause

def bind (store : Store) (id : String) : Store := fun other => if other = id then .none else store other
def release (store : Store) (id : String) : Store := bind store id

theorem bound_call_starts_without_cause (store : Store) (id : String) : bind store id id = .none := by
  simp [bind]

theorem release_forgets (store : Store) (id : String) : release store id id = .none := by
  simp [release, bind]

theorem other_calls_untouched (store : Store) (id other : String) (h : other ≠ id) :
    bind store id other = store other := by
  simp [bind, h]

/-! ## A compaction's caller -/

def compactionRetryable (cause : Cause) (status : Nat) (owner : Int) : Bool :=
  decide (status = 429) || decide (500 ≤ status) ||
    (match cause with | .denied _ => decide (0 < (facts cause status owner).retry) | _ => false)

theorem compaction_retryable_iff (cause : Cause) (status : Nat) (owner : Int) :
    compactionRetryable cause status owner = true ↔
      status = 429 ∨ 500 ≤ status ∨ (∃ r, cause = .denied r ∧ 0 < (facts cause status owner).retry) := by
  cases cause <;> simp [compactionRetryable, or_assoc]

theorem compaction_rejection_not_retried (status : Nat) (owner : Int)
    (h : rejectedStatus status = true) (cause : Cause) (hc : ∀ r, cause ≠ .denied r) :
    compactionRetryable cause status owner = false := by
  simp only [rejectedStatus, decide_eq_true_eq] at h
  obtain ⟨_, hlt, _, _, _, h429⟩ := h
  cases cause <;> simp_all [compactionRetryable]

/-! ## Counterexample: a fallback that replaces -/

def noteReplacing (_kept : Cause) : Note → Cause
  | .observed c => c
  | .fallback c => c

/-- With replacing fallbacks, a denial asking for 30 s, followed by the
accounting fallback, is paced with no retry-after. -/
theorem replacing_fallback_loses_retry :
    (facts ((([Note.observed (.denied 30), Note.fallback .error]).foldl noteReplacing .none)) 0 (-1)).retry = -1 ∧
    (facts (keep .none [Note.observed (.denied 30), Note.fallback .error]) 0 (-1)).retry = 30 := by
  decide

end Mettapedia.Protocols.Agents.CallFailureFacts
