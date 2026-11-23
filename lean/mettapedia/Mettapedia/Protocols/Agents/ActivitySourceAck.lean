import Mathlib.Tactic

/-!
# Settling an acknowledged activity batch at its source

An acknowledged batch names runtime occurrences and channel handover inputs.
Settling it at the source checks the whole batch first: one invalid id, or
one runtime occurrence the ledger has not committed, settles nothing. Then
each handover input is marked done, and the batch is marked processed in
the ledger. Either step may fail; the answer is then 0 and the next boundary
retries.

Invariants proved here:
* a batch with an invalid id, or with an uncommitted runtime occurrence,
  leaves the source as it was;
* settling is idempotent: a batch settled once settles again with nothing
  left to change;
* a failed attempt followed by a successful retry leaves the source as one
  successful settlement does.

The counterexample is settling while validating: an implementation that
marks each handover input done as it reads the batch has already changed the
source when a later id turns out invalid.

This is an abstract contract, not a refinement proof of
`src/activity_source_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ActivitySourceAck

/-- An id of a batch, as validation classifies it. -/
inductive Id
  | runtime (n : ℕ)
  | update (n : ℕ)
  | invalid
  deriving DecidableEq

/-- The source: handover inputs marked done, inputs processed in the ledger,
and the runtime occurrences the ledger has committed. -/
structure Source where
  done : Finset ℕ
  processed : Finset ℕ
  committed : Finset ℕ

def updates : List Id → List ℕ
  | [] => []
  | .update n :: rest => n :: updates rest
  | _ :: rest => updates rest

def runtimes : List Id → List ℕ
  | [] => []
  | .runtime n :: rest => n :: runtimes rest
  | _ :: rest => runtimes rest

def Valid (batch : List Id) : Prop := Id.invalid ∉ batch

/-- One attempt. `renameOk` and `markOk` say whether the folder and the ledger
accept their writes this time. The whole batch is checked before any write. -/
def settle (s : Source) (batch : List Id) (renameOk markOk : Bool) : ℕ × Source :=
  if Id.invalid ∈ batch then (0, s)
  else if ¬ (∀ n ∈ runtimes batch, n ∈ s.committed) then (0, s)
  else if ¬ renameOk then (0, s)
  else
    let marked := { s with done := s.done ∪ (updates batch).toFinset }
    if ¬ markOk then (0, marked)
    else (1, { marked with processed := marked.processed ∪ (updates batch).toFinset })

theorem invalid_settles_nothing (s : Source) (batch : List Id) (r m : Bool)
    (h : ¬ Valid batch) : settle s batch r m = (0, s) := by
  unfold Valid at h; push Not at h
  simp [settle, h]

theorem uncommitted_settles_nothing (s : Source) (batch : List Id) (r m : Bool) (n : ℕ)
    (hn : n ∈ runtimes batch) (hc : n ∉ s.committed) : settle s batch r m = (0, s) := by
  have h2 : ¬ (∀ k ∈ runtimes batch, k ∈ s.committed) := fun h => hc (h n hn)
  by_cases h1 : Id.invalid ∈ batch
  · simp [settle, h1]
  · simp [settle, h1, h2]

theorem settled_again (s : Source) (batch : List Id)
    (h : (settle s batch true true).1 = 1) :
    settle (settle s batch true true).2 batch true true = (1, (settle s batch true true).2) := by
  unfold settle at h ⊢
  split_ifs at h ⊢ with h1 h2
  all_goals simp_all [Finset.union_assoc]

theorem retry_converges (s : Source) (batch : List Id) (r m : Bool)
    (h : (settle s batch true true).1 = 1) :
    (settle (settle s batch r m).2 batch true true).2 = (settle s batch true true).2 := by
  have h1 : Id.invalid ∉ batch := by intro hi; simp [settle, hi] at h
  have h2 : ∀ n ∈ runtimes batch, n ∈ s.committed := by
    by_contra hc; simp [settle, h1, hc] at h
  have h3 : ¬ ∃ n ∈ runtimes batch, n ∉ s.committed := fun ⟨n, hn, hc⟩ => hc (h2 n hn)
  cases r <;> cases m <;> simp [settle, h1, h3, Finset.union_assoc]

/-! ## Counterexample: settling while validating -/

/-- Marks each handover input done as it reads it, and stops at an invalid id. -/
def eagerSettle (s : Source) : List Id → ℕ × Source
  | [] => (1, s)
  | .invalid :: _ => (0, s)
  | .update n :: rest => eagerSettle { s with done := insert n s.done } rest
  | .runtime _ :: rest => eagerSettle s rest

theorem eager_changes_source_on_invalid :
    let s : Source := ⟨∅, ∅, ∅⟩
    (eagerSettle s [.update 7, .invalid]).1 = 0 ∧ 7 ∈ (eagerSettle s [.update 7, .invalid]).2.done ∧
      (settle s [.update 7, .invalid] true true).2.done = ∅ := by
  decide

end Mettapedia.Protocols.Agents.ActivitySourceAck
