import Mettapedia.Protocols.Agents.CapturedInputScope
import Mathlib.Data.List.TakeDrop

/-!
# Recoverable append checkpoints for managed loops

The durable intent contains bytes and a captured delivery frame. Recovery
observes the actual suffix, rejects an unrelated suffix or stale writer, and
appends only the unobserved part. Settlement follows a completed byte
observation. This is an abstract protocol contract, not a C refinement proof.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ResumableModeCheckpoint

open Mettapedia.Protocols.Mail
open Mettapedia.Protocols.Agents.InputSettlement
open Mettapedia.Protocols.Agents.CapturedInputScope

structure Intent (α : Type) where
  base : List α
  delta : List α
  frame : Frame

def progress {α : Type} (i : Intent α) (observed : List α) : Nat :=
  observed.length - i.base.length

abbrev ValidPrefix {α : Type} (i : Intent α) (observed : List α) : Prop :=
  i.base.length ≤ observed.length ∧
  progress i observed ≤ i.delta.length ∧
  observed = i.base ++ i.delta.take (progress i observed)

/-- All three checks use the observed bytes and lengths, not a completion tag. -/
def resume {α : Type} [DecidableEq α] (active writer : Nat)
    (i : Intent α) (observed : List α) : Option (List α) :=
  if active = writer ∧ ValidPrefix i observed then
    some (observed ++ i.delta.drop (progress i observed))
  else none

theorem valid_prefix_completes {α : Type} (i : Intent α) (observed : List α)
    (h : ValidPrefix i observed) :
    observed ++ i.delta.drop (progress i observed) = i.base ++ i.delta := by
  calc
    observed ++ i.delta.drop (progress i observed) =
        (i.base ++ i.delta.take (progress i observed)) ++ i.delta.drop (progress i observed) :=
      congrArg (fun xs => xs ++ i.delta.drop (progress i observed)) h.2.2
    _ = i.base ++ i.delta := by rw [List.append_assoc, List.take_append_drop]

theorem resume_exact {α : Type} [DecidableEq α] (owner : Nat)
    (i : Intent α) (observed : List α) (h : ValidPrefix i observed) :
    resume owner owner i observed = some (i.base ++ i.delta) := by
  unfold resume
  rw [if_pos ⟨rfl, h⟩]
  exact congrArg some (valid_prefix_completes i observed h)

theorem prefix_is_valid {α : Type} (i : Intent α) (n : Nat)
    (hn : n ≤ i.delta.length) :
    ValidPrefix i (i.base ++ i.delta.take n) := by
  have hp : progress i (i.base ++ i.delta.take n) = n := by
    simp [progress, List.length_take, Nat.min_eq_left hn]
  refine ⟨by simp, ?_, ?_⟩
  · simpa [hp] using hn
  · rw [hp]

/-- A crash at any byte boundary resumes the same intent without duplicate bytes. -/
theorem crash_at_any_prefix {α : Type} [DecidableEq α] (owner : Nat)
    (i : Intent α) (n : Nat) (hn : n ≤ i.delta.length) :
    resume owner owner i (i.base ++ i.delta.take n) = some (i.base ++ i.delta) :=
  resume_exact owner i _ (prefix_is_valid i n hn)

theorem completed_replay_is_noop {α : Type} [DecidableEq α] (owner : Nat)
    (i : Intent α) :
    resume owner owner i (i.base ++ i.delta) = some (i.base ++ i.delta) := by
  simpa using crash_at_any_prefix owner i i.delta.length (by rfl)

theorem stale_writer_refused {α : Type} [DecidableEq α] (active writer : Nat)
    (i : Intent α) (observed : List α) (h : active ≠ writer) :
    resume active writer i observed = none := by
  simp [resume, h]

theorem foreign_suffix_refused {α : Type} [DecidableEq α] (owner : Nat)
    (i : Intent α) (observed : List α) (h : ¬ValidPrefix i observed) :
    resume owner owner i observed = none := by
  simp [resume, h]

/-- A checkpoint may settle its frame only after the append has been observed. -/
def settle {α : Type} [DecidableEq α] (active writer : Nat)
    (i : Intent α) (observed : List α) (mailbox : Mailbox) : Option Mailbox :=
  if active = writer ∧ observed = i.base ++ i.delta then
    some (checkpoint i.frame mailbox)
  else none

theorem partial_append_cannot_settle {α : Type} [DecidableEq α]
    (owner : Nat) (i : Intent α) (observed : List α) (mailbox : Mailbox)
    (unfinished : observed ≠ i.base ++ i.delta) :
    settle owner owner i observed mailbox = none := by
  simp [settle, unfinished]

theorem late_delivery_survives {α : Type} [DecidableEq α] (owner : Nat)
    (base delta : List α) (p : Presenter) {before : Mailbox}
    (valid : before.Valid) {m : Message} (fresh : m.id ∉ before.ids) :
    ∃ after, settle owner owner ⟨base, delta, capture p before⟩
        (base ++ delta) (before.deliver m) = some after ∧ m ∈ after.unread := by
  refine ⟨checkpoint (capture p before) (before.deliver m), ?_, ?_⟩
  · simp [settle]
  · exact (fresh_arrival_survives p valid fresh).1

/-- A torn multibyte UTF-8 sequence is recovered as bytes, without replacement. -/
example : resume 7 7 (⟨[65], [226, 130, 172], ⟨[]⟩⟩ : Intent Nat)
    [65, 226, 130] = some [65, 226, 130, 172] := by decide

/-- Blindly appending the full delta after a crash duplicates an already written prefix. -/
example : ([65, 226, 130] ++ [226, 130, 172] : List Nat) ≠
    [65, 226, 130, 172] := by decide

/-- Correct length cannot authorize an unrelated suffix. -/
example : resume 7 7 (⟨[65], [226, 130, 172], ⟨[]⟩⟩ : Intent Nat)
    [65, 9, 9] = none := by decide

end Mettapedia.Protocols.Agents.ResumableModeCheckpoint
