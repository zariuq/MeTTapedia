import Mathlib.Tactic

/-!
# Attachment downloads: the ledger's open dispatches are exactly the unfinished

The Telegram client logs a message that carries a file as
`attachment_dispatched` before its download begins, and as `attachment_ready`
once it finished (saved or failed, with its announcement). The download runs
without a thread or a blocked turn, so a restart can interrupt it; at start
the client downloads again every attachment the ledger dispatched and did not
finish. Records are keyed by chat and message.

Invariants proved here, for any ledger:
* a key is recovered exactly when its last record is a dispatch: nothing
  dispatched and unfinished is skipped, nothing finished is fetched again;
* a dispatch after a ready (the same message dispatched again) is recovered.

Counterexample: recovering every key ever dispatched fetches a finished
download again.

This is an abstract contract, not a refinement proof of
`channels/telegram_files.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.AttachmentRecovery

/-- A ledger record about a key. -/
inductive Rec
  | dispatched (k : ℕ)
  | ready (k : ℕ)
  deriving DecidableEq

def Rec.key : Rec → ℕ
  | .dispatched k => k
  | .ready k => k

/-- The fold the client makes: a dispatch opens its key, a ready closes it. -/
def step (open_ : Finset ℕ) : Rec → Finset ℕ
  | .dispatched k => insert k open_
  | .ready k => open_.erase k

def openKeys (rs : List Rec) : Finset ℕ := rs.foldl step ∅

/-- The last record about `k`, if any. -/
def lastAbout (k : ℕ) : List Rec → Option Rec
  | [] => none
  | r :: rest =>
    match lastAbout k rest with
    | some x => some x
    | none => if r.key = k then some r else none

theorem foldl_step_mem (k : ℕ) (rs : List Rec) (s : Finset ℕ) :
    k ∈ rs.foldl step s ↔
      (lastAbout k rs = some (.dispatched k) ∨ (lastAbout k rs = none ∧ k ∈ s)) := by
  induction rs generalizing s with
  | nil => simp [lastAbout]
  | cons r rest ih =>
    rw [List.foldl_cons, ih]
    cases h : lastAbout k rest with
    | some x => simp [lastAbout, h]
    | none =>
      cases r with
      | dispatched j =>
        by_cases hj : j = k
        · subst hj; simp [lastAbout, h, step, Rec.key]
        · simp [lastAbout, h, step, Rec.key, hj, Ne.symm hj]
      | ready j =>
        by_cases hj : j = k
        · subst hj; simp [lastAbout, h, step, Rec.key]
        · simp [lastAbout, h, step, Rec.key, hj, Ne.symm hj]

/-- **Exactly the unfinished**: a key is recovered iff its last record is a dispatch. -/
theorem recovered_iff (k : ℕ) (rs : List Rec) :
    k ∈ openKeys rs ↔ lastAbout k rs = some (.dispatched k) := by
  rw [openKeys, foldl_step_mem]
  simp

theorem lastAbout_concat (k : ℕ) (pre : List Rec) (r : Rec) :
    lastAbout k (pre ++ [r]) = if r.key = k then some r else lastAbout k pre := by
  induction pre with
  | nil => simp [lastAbout]
  | cons p pre ih =>
    simp only [List.cons_append, lastAbout, ih]
    by_cases hr : r.key = k <;> simp [hr]

/-- A finished download is not fetched again. -/
theorem finished_not_recovered (k : ℕ) (pre : List Rec) :
    k ∉ openKeys (pre ++ [.ready k]) := by
  rw [recovered_iff, lastAbout_concat]
  simp [Rec.key]

/-- A message dispatched again after it finished is recovered. -/
theorem redispatched_recovered (k : ℕ) (pre : List Rec) :
    k ∈ openKeys (pre ++ [.dispatched k]) := by
  rw [recovered_iff, lastAbout_concat]
  simp [Rec.key]

/-- Recovering every key ever dispatched fetches a finished download again. -/
theorem ever_dispatched_refetches :
    ∃ rs : List Rec, 7 ∈ (rs.filterMap fun r => match r with | .dispatched k => some k | _ => none) ∧
      7 ∉ openKeys rs :=
  ⟨[.dispatched 7, .ready 7], by simp, by simp [openKeys, step]⟩

end Mettapedia.Protocols.Agents.AttachmentRecovery
