/-!
# Re-pinning a coding session at resume

`(work-resume "id" "current")` moves a stopped session to the current runtime:
1. freeze the current runtime as a bundle;
2. check that the bundle's own start-up reader accepts a copy of the session's checkpoint;
3. replace `runtime.json` by one rename, keeping the previous record;
4. append the change to `runs.jsonl`.

The execution records are never touched.

* **Effect identity.** A re-pin leaves the execution records as they were, so an uncertain
  execution stays uncertain, and the identities a run may still dispatch are exactly those it
  could dispatch before (`repin_keeps_executions`, `repin_keeps_dispatchable`). An execution is
  created by exclusive create, so a recorded identity is never dispatched again
  (`recorded_not_dispatchable`).
* **One-record publication.** At any crash point the pin a resume reads is the old record or the
  new one, and it is the new one only after its check passed (`crash_reads_old_or_checked`). A
  failed check changes no record (`failed_check_changes_nothing`). A crash before the rename
  leaves at most an unreferenced bundle.
* **Rollback.** The record kept beside the new pin is the pin it replaced
  (`repin_keeps_previous`).
* **Re-pinning to the pin itself** changes nothing (`repin_same_is_noop`).

* **The recheck.** The check runs outside the session lock and reads one checkpoint revision.
  The publication, under the lock, rechecks that revision, so a published pin was checked
  against the checkpoint it now pairs with (`rechecked_pairs_current`). Without the recheck, a
  checkpoint that changed during the check is paired with an unchecked bundle
  (`unrechecked_pairs_stale`). Inbox lines appended meanwhile are kept
  (`rechecked_keeps_inbox`). The pin and the checkpoint revision are one manifest. Independent
  renames of several files would not be a joint publication.
* **The manifest is rechecked too.** Another resume can change the manifest during the check
  without changing a checkpoint file. Rechecking only the checkpoint then overwrites that
  reservation (`checkpoint_only_overwrites_reservation`). With the manifest rechecked, a
  publication replaces exactly the manifest it observed (`fully_rechecked_replaces_observed`).

Scope: the check is modelled as a given Boolean verdict on a (checkpoint, bundle) pair. Whether
the live reader is right about a checkpoint is the job of the native tests, not of this model.
The rename is atomic, as POSIX `rename` within one directory is.
-/

namespace PettaClaw.CodingSessionRepin

inductive ExecStatus where
  | dispatching
  | running
  | exited (code : Int)
  deriving DecidableEq, Repr

structure Record where
  bundle : Nat
  previous : Option Nat
  /-- The manifest's run token; another resume replaces it with a fresh one. -/
  run : Nat := 0
  deriving DecidableEq, Repr

structure Session where
  pin : Record
  runs : List (Nat × Nat)
  executions : List (Nat × ExecStatus)
  /-- The requester's input lines, appended at any time. -/
  inbox : List Nat
  /-- The revision (digest) of the files the start-up reader reads. -/
  checkpoint : Nat
  deriving DecidableEq, Repr

/-- An execution's result is uncertain when its record never reached an exit. -/
def uncertain : ExecStatus → Bool
  | .exited _ => false
  | _ => true

/-- Exclusive create: an identity may be dispatched only if no record holds it. -/
def dispatchable (s : Session) (i : Nat) : Bool := !(s.executions.any (·.1 == i))

/-- The steps of a re-pin, as far as a crash may interrupt them. -/
inductive Reached where
  | frozen
  | checked
  | renamed
  | logged
  deriving DecidableEq, Repr

/-- The re-pin to `bundle`, with the check's verdict on (checkpoint, bundle). -/
def repin (check : Nat → Nat → Bool) (s : Session) (bundle : Nat) : Session :=
  if bundle = s.pin.bundle then s
  else if check s.checkpoint bundle then
    { s with pin := { bundle := bundle, previous := some s.pin.bundle },
             runs := (s.pin.bundle, bundle) :: s.runs }
  else s

/-! ## The check runs outside the lock

The check takes up to minutes, and the turn-start reaper takes the same lock, so the lock is not
held across it. The check reads checkpoint revision `seen`. The publication runs under the lock
and rechecks the revision. -/

def repinRechecked (check : Nat → Nat → Bool) (seen : Nat) (s : Session) (bundle : Nat) :
    Session :=
  if bundle = s.pin.bundle then s
  else if check seen bundle = true ∧ s.checkpoint = seen then
    { s with pin := { bundle := bundle, previous := some s.pin.bundle },
             runs := (s.pin.bundle, bundle) :: s.runs }
  else s

/-- Without the recheck: publish on the check's verdict alone. -/
def repinUnrechecked (check : Nat → Nat → Bool) (seen : Nat) (s : Session) (bundle : Nat) :
    Session :=
  if bundle = s.pin.bundle then s
  else if check seen bundle = true then
    { s with pin := { bundle := bundle, previous := some s.pin.bundle },
             runs := (s.pin.bundle, bundle) :: s.runs }
  else s

/-- A pin published with the recheck was checked against the checkpoint it now pairs with. -/
theorem rechecked_pairs_current (check) (seen : Nat) (s : Session) (b : Nat)
    (h : (repinRechecked check seen s b).pin ≠ s.pin) : check s.checkpoint b = true := by
  unfold repinRechecked at h
  by_cases hb : b = s.pin.bundle
  · simp [hb] at h
  · by_cases hc : check seen b = true ∧ s.checkpoint = seen
    · rw [hc.2]; exact hc.1
    · simp [hb, hc] at h

/-- Without it, a checkpoint that changed during the check is paired with a bundle that was never
checked against it. -/
def changedDuringCheck : Session :=
  { pin := { bundle := 1, previous := none }, runs := [], executions := [], inbox := [],
    checkpoint := 8 }

theorem unrechecked_pairs_stale :
    (repinUnrechecked (fun c _ => c == 7) 7 changedDuringCheck 2).pin.bundle = 2 ∧
      (fun c (_ : Nat) => c == 7) changedDuringCheck.checkpoint 2 = false := by decide

/-- Input appended to the inbox while the check ran is kept. -/
theorem rechecked_keeps_inbox (check) (seen : Nat) (s : Session) (b : Nat) :
    (repinRechecked check seen s b).inbox = s.inbox ∧
      (repinRechecked check seen s b).executions = s.executions := by
  unfold repinRechecked
  by_cases hb : b = s.pin.bundle
  · simp [hb]
  · by_cases hc : check seen b = true ∧ s.checkpoint = seen
    · simp [hb, hc]
    · simp [hb, hc]

/-! ## The manifest is rechecked too

Another resume, a reservation or a consumed token, can change the manifest during the check,
without changing any checkpoint file. The publication rechecks the manifest it observed. -/

def repinFullyRechecked (check : Nat → Nat → Bool) (seen : Nat) (seenPin : Record) (s : Session)
    (bundle : Nat) : Session :=
  if bundle = s.pin.bundle then s
  else if check seen bundle = true ∧ s.checkpoint = seen ∧ s.pin = seenPin then
    { s with pin := { bundle := bundle, previous := some s.pin.bundle },
             runs := (s.pin.bundle, bundle) :: s.runs }
  else s

/-- A publication replaces exactly the manifest that was observed: a reservation made during the
check is never overwritten. -/
theorem fully_rechecked_replaces_observed (check) (seen : Nat) (seenPin : Record) (s : Session)
    (b : Nat) (h : (repinFullyRechecked check seen seenPin s b).pin ≠ s.pin) :
    s.pin = seenPin ∧ check s.checkpoint b = true := by
  unfold repinFullyRechecked at h
  by_cases hb : b = s.pin.bundle
  · simp [hb] at h
  · by_cases hc : check seen b = true ∧ s.checkpoint = seen ∧ s.pin = seenPin
    · exact ⟨hc.2.2, hc.2.1 ▸ hc.1⟩
    · simp [hb, hc] at h

/-- Checking the checkpoint alone overwrites a reservation made during the check. -/
def reservedDuringCheck : Session :=
  { pin := { bundle := 1, previous := none, run := 2 }, runs := [], executions := [], inbox := [],
    checkpoint := 7 }

theorem checkpoint_only_overwrites_reservation :
    (repinRechecked (fun _ _ => true) 7 reservedDuringCheck 3).pin.run = 0 ∧
      reservedDuringCheck.pin.run = 2 ∧
      repinFullyRechecked (fun _ _ => true) 7 { bundle := 1, previous := none, run := 1 }
        reservedDuringCheck 3 = reservedDuringCheck := by decide

/-- The session files after a crash at a given point of the re-pin. -/
def crashAt (check : Nat → Nat → Bool) (s : Session) (bundle : Nat) : Reached → Session
  | .frozen => s
  | .checked => s
  | .renamed =>
    if bundle ≠ s.pin.bundle ∧ check s.checkpoint bundle = true then
      { s with pin := { bundle := bundle, previous := some s.pin.bundle } }
    else s
  | .logged => repin check s bundle

theorem repin_keeps_executions (check) (s : Session) (b : Nat) :
    (repin check s b).executions = s.executions := by
  unfold repin; split
  · rfl
  · split <;> rfl

theorem repin_keeps_dispatchable (check) (s : Session) (b i : Nat) :
    dispatchable (repin check s b) i = dispatchable s i := by
  unfold dispatchable; rw [repin_keeps_executions]

theorem repin_keeps_uncertain (check) (s : Session) (b : Nat) :
    (repin check s b).executions.filter (fun e => uncertain e.2) =
      s.executions.filter (fun e => uncertain e.2) := by
  rw [repin_keeps_executions]

theorem recorded_not_dispatchable (s : Session) (i : Nat) (st : ExecStatus)
    (h : (i, st) ∈ s.executions) : dispatchable s i = false := by
  unfold dispatchable
  simp only [Bool.not_eq_false', List.any_eq_true, beq_iff_eq]
  exact ⟨(i, st), h, rfl⟩

theorem failed_check_changes_nothing (check) (s : Session) (b : Nat)
    (h : check s.checkpoint b = false) : repin check s b = s := by
  unfold repin; split
  · rfl
  · simp [h]

theorem repin_same_is_noop (check) (s : Session) : repin check s s.pin.bundle = s := by
  unfold repin; simp

theorem repin_keeps_previous (check) (s : Session) (b : Nat) (hne : b ≠ s.pin.bundle)
    (h : check s.checkpoint b = true) :
    (repin check s b).pin = { bundle := b, previous := some s.pin.bundle } := by
  unfold repin; simp [hne, h]

/-- Whatever step a crash interrupts, the pin a resume reads afterwards is the old record or the
new one, and the new one only after its check passed. -/
theorem crash_reads_old_or_checked (check) (s : Session) (b : Nat) (r : Reached) :
    (crashAt check s b r).pin = s.pin ∨
      ((crashAt check s b r).pin.bundle = b ∧ check s.checkpoint b = true) := by
  cases r with
  | frozen => exact Or.inl rfl
  | checked => exact Or.inl rfl
  | renamed =>
    simp only [crashAt]
    by_cases h : b ≠ s.pin.bundle ∧ check s.checkpoint b = true
    · rw [if_pos h]; exact Or.inr ⟨rfl, h.2⟩
    · rw [if_neg h]; exact Or.inl rfl
  | logged =>
    simp only [crashAt, repin]
    by_cases hb : b = s.pin.bundle
    · rw [if_pos hb]; exact Or.inl rfl
    · rw [if_neg hb]
      by_cases hc : check s.checkpoint b = true
      · rw [if_pos hc]; exact Or.inr ⟨rfl, hc⟩
      · rw [if_neg hc]; exact Or.inl rfl

/-- No crash point loses an execution record. -/
theorem crash_keeps_executions (check) (s : Session) (b : Nat) (r : Reached) :
    (crashAt check s b r).executions = s.executions := by
  cases r with
  | frozen => rfl
  | checked => rfl
  | renamed =>
    simp only [crashAt]
    by_cases h : b ≠ s.pin.bundle ∧ check s.checkpoint b = true
    · rw [if_pos h]
    · rw [if_neg h]
  | logged => exact repin_keeps_executions check s b

end PettaClaw.CodingSessionRepin

#print axioms PettaClaw.CodingSessionRepin.repin_keeps_executions
#print axioms PettaClaw.CodingSessionRepin.repin_keeps_dispatchable
#print axioms PettaClaw.CodingSessionRepin.repin_keeps_uncertain
#print axioms PettaClaw.CodingSessionRepin.recorded_not_dispatchable
#print axioms PettaClaw.CodingSessionRepin.failed_check_changes_nothing
#print axioms PettaClaw.CodingSessionRepin.repin_same_is_noop
#print axioms PettaClaw.CodingSessionRepin.repin_keeps_previous
#print axioms PettaClaw.CodingSessionRepin.crash_reads_old_or_checked
#print axioms PettaClaw.CodingSessionRepin.crash_keeps_executions
#print axioms PettaClaw.CodingSessionRepin.rechecked_pairs_current
#print axioms PettaClaw.CodingSessionRepin.unrechecked_pairs_stale
#print axioms PettaClaw.CodingSessionRepin.rechecked_keeps_inbox
#print axioms PettaClaw.CodingSessionRepin.fully_rechecked_replaces_observed
#print axioms PettaClaw.CodingSessionRepin.checkpoint_only_overwrites_reservation
