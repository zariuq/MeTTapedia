import Mettapedia.Machines.Kernel.EpochWriterLease
import Mathlib.Tactic

/-!
# Files Service Restart Settlement During Accepted Drive I/O

Models the joint settlement contract between `kernel_service_restart` for `sexfiles`
(`home`), `kernel_region_writer` (`sexdrive` as `peer`), and the kernel epoch-journal
batch during an in-flight I/O or epoch flush:

1. **Accepted-I/O Barrier**: `sexfiles` cannot be restarted while `sexdrive` holds the
   shared bounce-buffer writer lease (`current = peer`) or while an offered read job is
   still pending at `sexdrive`.
2. **Completion & Discharge**: Even after `sexfiles` exits, `sexdrive`'s `.claim` /
   `.release` transitions remain permitted and discharge `job = 0` back to `home`,
   unblocking restart cleanly.
3. **Orphan Offer Quiescence**: If `sexfiles` died after `.offer` without delivering
   any request to `sexdrive`, kernel quiescence `.cancel` discharges `job = 0` while
   preserving coherence, monotonicity of `revision`, and all unrelated writers.
4. **Epoch-Flush Resume Monotonicity**: Resuming the epoch journal inside the same boot
   session after `sexfiles` restart (`flushedThrough > 0`) preserves strict prefix
   monotonicity without resetting `nextEvent` to `1` or duplicating flushed records.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.FilesRestartSettlement

open EpochWriterLease

/-- Kernel preflight gate for restarting `sexfiles` (`home`).
Restart is allowed only when the shared bounce-region lease is coherent, currently
owned by `home`, and either idle (`job = 0`) or orphaned with no pending Drive I/O. -/
def FilesRestartPermitted (w : World) (driveHasPendingRequest : Bool) : Prop :=
  Coherent w ∧
  w.lease.current = w.lease.home ∧
  (w.lease.job = 0 ∨ driveHasPendingRequest = false)

/-- Kernel quiescence step applied only after `FilesRestartPermitted` holds:
if `home` left an unaccepted orphaned offer (`job ≠ 0`, `driveHasPendingRequest = false`),
cancel it cleanly; if `job = 0`, leave the world unchanged. -/
def quiesceOrphanOffer (w : World) : World :=
  if w.lease.job = 0 then w
  else transfer w ⟨w.lease.region, w.lease.home, .cancel, w.lease.revision, w.lease.job⟩

/-- Theorem 1: While Drive (`peer`) holds the shared region writer lease during
accepted I/O, Files restart is strictly forbidden. -/
theorem restart_blocked_while_peer_holds_writer
    {w : World} {pending : Bool}
    (hPeer : w.lease.current = w.lease.peer) :
    ¬ FilesRestartPermitted w pending := by
  intro ⟨hCoh, hHome, _⟩
  have hDist := hCoh.1.2.2.2.1
  exact hDist (hHome.symm.trans hPeer)

/-- Theorem 2: While an offered job is pending at Drive, Files restart is blocked even
before Drive claims the writer lease. -/
theorem restart_blocked_while_offer_pending_at_drive
    {w : World} (hJob : w.lease.job ≠ 0) :
    ¬ FilesRestartPermitted w true := by
  intro ⟨_, _, hDisj⟩
  rcases hDisj with hZero | hFalse
  · exact hJob hZero
  · cases hFalse

/-- Theorem 3: Once Drive completes accepted I/O and releases the writer lease back to
Files, the resulting world is coherent, idle (`job = 0`), and permits Files restart. -/
theorem peer_release_unblocks_files_restart
    {w : World} {cmd : Command} {pending : Bool}
    (hPerm : Permitted w cmd)
    (hRel : cmd.action = .release) :
    FilesRestartPermitted (transfer w cmd) pending := by
  refine ⟨transfer_preserves_coherent hPerm, ?_, Or.inl ?_⟩
  · simp [transfer, nextCurrent, hRel]
  · simp [transfer, nextJob, hRel]

/-- Theorem 4: Accepted two-step Drive read (`claim` then `release`) after Files offered
a job and exited keeps Files restart blocked while Drive holds the writer, then
discharges the job and unblocks Files restart while preserving coherence. -/
theorem accepted_offer_claim_then_release_unblocks_restart
    {w : World} {claimCmd releaseCmd : Command} {pending : Bool}
    (hClaimPerm : Permitted w claimCmd)
    (hClaimAct : claimCmd.action = .claim)
    (hRelPerm : Permitted (transfer w claimCmd) releaseCmd)
    (hRelAct : releaseCmd.action = .release) :
    Coherent (transfer w claimCmd) ∧
    ¬ FilesRestartPermitted (transfer w claimCmd) pending ∧
    FilesRestartPermitted (transfer (transfer w claimCmd) releaseCmd) pending ∧
    (transfer (transfer w claimCmd) releaseCmd).lease.revision = w.lease.revision + 2 := by
  refine ⟨transfer_preserves_coherent hClaimPerm, ?_, ?_, ?_⟩
  · apply restart_blocked_while_peer_holds_writer
    simp [transfer, nextCurrent, hClaimAct]
  · exact peer_release_unblocks_files_restart hRelPerm hRelAct
  · simp [transfer]

/-- Theorem 5: Quiescing an idle or orphaned-offer world always produces a coherent,
idle (`current = home ∧ job = 0`) world with non-decreasing revision and untouched
unrelated writers. -/
theorem quiesce_orphan_preserves_coherent_and_idles
    {w : World} {pending : Bool}
    (hRestart : FilesRestartPermitted w pending)
    (hRevBound : w.lease.revision < machineMaximum) :
    let w' := quiesceOrphanOffer w
    Coherent w' ∧
    w'.lease.current = w'.lease.home ∧
    w'.lease.job = 0 ∧
    w.lease.revision ≤ w'.lease.revision ∧
    (∀ frame, w'.outsideWriter frame = w.outsideWriter frame) := by
  rcases hRestart with ⟨hCoh, hHome, _⟩
  by_cases hJob : w.lease.job = 0
  · dsimp only
    rw [quiesceOrphanOffer, if_pos hJob]
    exact ⟨hCoh, hHome, hJob, le_rfl, fun _ => rfl⟩
  · dsimp only
    rw [quiesceOrphanOffer, if_neg hJob]
    have hCancelPerm :
        Permitted w ⟨w.lease.region, w.lease.home, .cancel, w.lease.revision, w.lease.job⟩ := by
      refine ⟨hCoh, rfl, hJob, rfl, hRevBound, ?_⟩
      simp [ActionPermitted, hHome]
    refine ⟨transfer_preserves_coherent hCancelPerm, ?_, ?_, ?_, ?_⟩
    · simp [transfer, nextCurrent, hHome]
    · simp [transfer, nextJob]
    · simp [transfer]
    · intro frame; rfl

/-- Epoch journal resume state across an in-boot `sexfiles` restart. -/
structure EpochResumeState where
  flushedThrough : Nat
  producer : Nat
  diskNextEvent : Nat
  deriving DecidableEq, Repr

/-- Valid epoch-batch state when `sexfiles` restarts in the same boot session:
`producer > flushedThrough`, and replayed disk journal `diskNextEvent` is at least
`flushedThrough + 1` and at most `producer`. -/
def EpochResumeState.Valid (s : EpochResumeState) : Prop :=
  s.flushedThrough < s.producer ∧
  s.flushedThrough + 1 ≤ s.diskNextEvent ∧
  s.diskNextEvent ≤ s.producer

/-- Same-boot resume chooses `diskNextEvent` directly when `flushedThrough > 0`
(skipping `begin_session`, which would rewind `next_event` to `1`). -/
def resumedNextEvent (s : EpochResumeState) : Nat :=
  if s.flushedThrough = 0 then 1 else s.diskNextEvent

/-- Settling the replayed prefix advances `flushedThrough` to `nextEvent - 1`. -/
def settlePrefix (s : EpochResumeState) : EpochResumeState :=
  { s with flushedThrough := resumedNextEvent s - 1 }

/-- Theorem 6: Resuming an in-boot epoch journal never rewinds `flushedThrough`,
keeps `flushedThrough < producer`, and preserves `flushedThrough + 1 ≤ diskNextEvent`. -/
theorem epoch_resume_monotone_and_valid
    {s : EpochResumeState} (hValid : s.Valid) :
    let s' := settlePrefix s
    s.flushedThrough ≤ s'.flushedThrough ∧ s'.Valid := by
  rcases hValid with ⟨hProd, hGe, hLe⟩
  by_cases hZero : s.flushedThrough = 0
  · simp only [settlePrefix, resumedNextEvent, if_pos hZero, EpochResumeState.Valid]
    refine ⟨by omega, ?_, ?_, hLe⟩ <;> omega
  · simp only [settlePrefix, resumedNextEvent, if_neg hZero, EpochResumeState.Valid]
    refine ⟨by omega, ?_, ?_, hLe⟩ <;> omega

/-- Theorem 7: Counterexample showing why calling `begin_session` (which resets
`nextEvent := 1`) after an in-boot restart with `flushedThrough > 0` violates the
journal invariant `flushedThrough + 1 ≤ nextEvent`. -/
theorem begin_session_on_in_boot_restart_violates_invariant
    {s : EpochResumeState} (hNonzero : 0 < s.flushedThrough) :
    ¬ (s.flushedThrough + 1 ≤ 1) := by
  omega

#print axioms restart_blocked_while_peer_holds_writer
#print axioms restart_blocked_while_offer_pending_at_drive
#print axioms peer_release_unblocks_files_restart
#print axioms accepted_offer_claim_then_release_unblocks_restart
#print axioms quiesce_orphan_preserves_coherent_and_idles
#print axioms epoch_resume_monotone_and_valid
#print axioms begin_session_on_in_boot_restart_violates_invariant

end Mettapedia.Machines.Kernel.FilesRestartSettlement
