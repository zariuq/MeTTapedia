import Mettapedia.Machines.Kernel.EpochLedger
import Mathlib.Tactic

/-!
# Epoch-bound exclusive writer leases

A finite region keeps the same pages while its unique writer moves between two
authorized holders. Leaving the home holder creates a persistent logical-job
obligation; returning requires the same job and discharges it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochWriterLease

open EpochLedger

structure Lease where
  region : Nat
  home : Nat
  peer : Nat
  current : Nat
  revision : Nat
  job : Nat
  frames : List Nat
  deriving DecidableEq, Repr

structure World where
  lease : Lease
  regionWriters : List (Nat × Nat)
  outsideWriter : Nat → Nat
  terminal : List Nat

inductive Action where
  | offer
  | claim
  | release
  | cancel
  | recover
  deriving DecidableEq, Repr

structure Command where
  region : Nat
  source : Nat
  action : Action
  expectedRevision : Nat
  job : Nat
  deriving DecidableEq, Repr

def machineMaximum : Nat := 2 ^ 64 - 1

def Lease.Valid (lease : Lease) : Prop :=
  lease.region ≠ 0 ∧ lease.home ≠ 0 ∧ lease.peer ≠ 0 ∧
  lease.home ≠ lease.peer ∧ lease.revision ≠ 0 ∧
  lease.frames ≠ [] ∧ lease.frames.Nodup ∧
  (lease.current = lease.home ∨
   lease.current = lease.peer ∧ lease.job ≠ 0)

def Coherent (world : World) : Prop :=
  world.lease.Valid ∧
  world.regionWriters = world.lease.frames.map (fun frame => (frame, world.lease.current))

def ActionPermitted (world : World) (command : Command) : Prop :=
  match command.action with
  | .offer => command.source = world.lease.home ∧
      world.lease.current = world.lease.home ∧ world.lease.job = 0
  | .claim => command.source = world.lease.peer ∧
      world.lease.current = world.lease.home ∧ world.lease.job = command.job
  | .release => command.source = world.lease.peer ∧
      world.lease.current = world.lease.peer ∧ world.lease.job = command.job
  | .cancel => command.source = world.lease.home ∧
      world.lease.current = world.lease.home ∧ world.lease.job = command.job
  | .recover => command.source = world.lease.home ∧
      world.lease.current = world.lease.peer ∧ world.lease.job = command.job ∧
      world.terminal.contains world.lease.peer = true

instance actionPermittedDecidable (world : World) (command : Command) :
    Decidable (ActionPermitted world command) := by
  cases action : command.action <;> simp [ActionPermitted, action] <;> infer_instance

def Permitted (world : World) (command : Command) : Prop :=
  Coherent world ∧ command.region = world.lease.region ∧ command.job ≠ 0 ∧
  command.expectedRevision = world.lease.revision ∧
  world.lease.revision < machineMaximum ∧ ActionPermitted world command

instance permittedDecidable (world : World) (command : Command) :
    Decidable (Permitted world command) := by
  unfold Permitted Coherent Lease.Valid
  infer_instance

def nextCurrent (lease : Lease) (command : Command) : Nat := match command.action with
  | .claim => lease.peer
  | .release | .recover => lease.home
  | .offer | .cancel => lease.current

def nextJob (lease : Lease) (command : Command) : Nat := match command.action with
  | .offer => command.job
  | .claim => lease.job
  | .release | .cancel | .recover => 0

def transfer (world : World) (command : Command) : World :=
  let nextLease := { world.lease with
    current := nextCurrent world.lease command
    revision := world.lease.revision + 1
    job := nextJob world.lease command }
  { lease := nextLease
    regionWriters := world.lease.frames.map
      (fun frame => (frame, nextCurrent world.lease command))
    outsideWriter := world.outsideWriter
    terminal := world.terminal }

def step (world : World) (command : Command) : World := transfer world command

def checkedTransfer (maximum capacity : Nat) (ledger : Ledger World Command)
    (command : Command) : Option (Ledger World Command) :=
  if Permitted ledger.current command then commit maximum capacity step ledger command else none

theorem transferred_writers_exact (world : World) (command : Command) :
    (transfer world command).regionWriters =
      world.lease.frames.map (fun frame => (frame, nextCurrent world.lease command)) := by
  rfl

theorem transfer_preserves_unrelated_writer {world : World} {command : Command}
    (frame : Nat) :
    (transfer world command).outsideWriter frame = world.outsideWriter frame := by
  rfl

theorem transfer_preserves_frames (world : World) (command : Command) :
    (transfer world command).lease.frames = world.lease.frames := by
  rfl

theorem transfer_preserves_lease_valid {world : World} {command : Command}
    (permitted : Permitted world command) : (transfer world command).lease.Valid := by
  rcases permitted with ⟨⟨valid, writers⟩, region, job, revision, _, permittedAction⟩
  rcases valid with ⟨region_nonzero, home_nonzero, peer_nonzero, distinct,
    revision_nonzero, frames_nonempty, frames_nodup, current⟩
  refine ⟨region_nonzero, home_nonzero, peer_nonzero, distinct, ?_, frames_nonempty,
    frames_nodup, ?_⟩
  · simp [transfer]
  · cases action : command.action <;> simp only [ActionPermitted, action] at permittedAction
    · left
      rcases permittedAction with ⟨source, at_home, idle⟩
      simpa [transfer, nextCurrent, action]
    · right
      rcases permittedAction with ⟨source, at_home, same_job⟩
      have old_job : world.lease.job ≠ 0 := by simpa [same_job] using job
      exact ⟨by simp [transfer, nextCurrent, action], by simpa [transfer, nextJob, action] using old_job⟩
    · left
      rcases permittedAction with ⟨source, at_peer, same_job⟩
      simp [transfer, nextCurrent, action]
    · left
      rcases permittedAction with ⟨source, at_home, same_job⟩
      simpa [transfer, nextCurrent, action] using at_home
    · left
      rcases permittedAction with ⟨source, at_peer, same_job, terminal⟩
      simp [transfer, nextCurrent, action]

theorem transfer_preserves_coherent {world : World} {command : Command}
    (permitted : Permitted world command) : Coherent (transfer world command) :=
  ⟨transfer_preserves_lease_valid permitted, rfl⟩

theorem transfer_preserves_frame_inventory {world : World} {command : Command}
    (coherent : Coherent world) :
    (transfer world command).regionWriters.map Prod.fst = world.regionWriters.map Prod.fst := by
  rw [coherent.2]
  simp [transfer]

theorem checkedTransfer_permitted {maximum capacity : Nat}
    {ledger next : Ledger World Command} {command : Command}
    (accepted : checkedTransfer maximum capacity ledger command = some next) :
    Permitted ledger.current command := by
  unfold checkedTransfer at accepted
  split at accepted
  · assumption
  · cases accepted

theorem checkedTransfer_preserves_valid {maximum capacity : Nat}
    {ledger next : Ledger World Command} {command : Command}
    (valid : Valid step ledger)
    (accepted : checkedTransfer maximum capacity ledger command = some next) :
    Valid step next := by
  unfold checkedTransfer at accepted
  split at accepted
  · exact commit_preserves_valid step valid accepted
  · cases accepted

namespace Controls

def homeLease : Lease := ⟨6, 11, 2, 11, 1, 0, [40, 41]⟩
def homeWorld : World := ⟨homeLease, [(40, 11), (41, 11)], fun _ => 7, []⟩
def offer : Command := ⟨6, 11, .offer, 1, 99⟩
def offeredWorld : World := transfer homeWorld offer
def claim : Command := ⟨6, 2, .claim, 2, 99⟩
def peerWorld : World := transfer offeredWorld claim
def release : Command := ⟨6, 2, .release, 3, 99⟩
def recover : Command := ⟨6, 11, .recover, 3, 99⟩
def deadPeerWorld : World := { peerWorld with terminal := [2] }

theorem home_coherent : Coherent homeWorld := by
  constructor
  · simp [homeWorld, homeLease, Lease.Valid]
  · decide
theorem offer_permitted : Permitted homeWorld offer := by decide
theorem offered_coherent : Coherent offeredWorld := transfer_preserves_coherent offer_permitted
theorem offer_keeps_home_writer :
    offeredWorld.lease.current = 11 ∧ offeredWorld.lease.job = 99 := by decide
theorem claim_permitted : Permitted offeredWorld claim := by decide
theorem peer_coherent : Coherent peerWorld := transfer_preserves_coherent claim_permitted
theorem obligation_is_live : peerWorld.lease.current = 2 ∧ peerWorld.lease.job = 99 := by decide
theorem both_frames_move : peerWorld.regionWriters = [(40, 2), (41, 2)] := by decide
theorem unrelated_frame_survives : peerWorld.outsideWriter 55 = 7 := by decide
theorem release_permitted : Permitted peerWorld release := by decide
theorem return_discharges :
    (transfer peerWorld release).lease.current = 11 ∧
    (transfer peerWorld release).lease.job = 0 := by decide
theorem live_recovery_refused : ¬ Permitted peerWorld recover := by
  intro permitted
  have action := permitted.2.2.2.2.2
  norm_num [ActionPermitted, recover, peerWorld, offeredWorld, homeWorld, homeLease,
    offer, claim, transfer, nextCurrent, nextJob] at action
theorem dead_peer_coherent : Coherent deadPeerWorld := by
  simpa [Coherent, deadPeerWorld] using peer_coherent
theorem recover_permitted : Permitted deadPeerWorld recover := by
  refine ⟨dead_peer_coherent, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [ActionPermitted, recover, deadPeerWorld, peerWorld, offeredWorld,
      homeWorld, homeLease, offer, claim, transfer, nextCurrent, nextJob, machineMaximum]
theorem recovery_discharges :
    (transfer deadPeerWorld recover).lease.current = 11 ∧
    (transfer deadPeerWorld recover).lease.job = 0 := by decide

def stale : Command := { offer with expectedRevision := 0 }
def wrongJob : Command := { release with job := 100 }

theorem stale_refused : ¬ Permitted homeWorld stale := by decide
theorem wrong_job_refused : ¬ Permitted peerWorld wrongJob := by decide

def maxedLease : Lease := { homeLease with revision := machineMaximum }
def maxedWorld : World := { homeWorld with lease := maxedLease }
def maxedOffer : Command := { offer with expectedRevision := machineMaximum }

theorem revision_exhaustion_refused : ¬ Permitted maxedWorld maxedOffer := by
  simp [Permitted, maxedWorld, maxedLease, machineMaximum]

def start : Ledger World Command := ⟨homeWorld, homeWorld, 0, [], [], true⟩

theorem start_valid : Valid step start := by simp [Valid, start, replay, traceFrom]
theorem checked_offer_exists :
    ∃ next, checkedTransfer 8 8 start offer = some next := by
  unfold checkedTransfer
  change ∃ next, (if Permitted homeWorld offer then commit 8 8 step start offer else none) = some next
  rw [if_pos offer_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  exact ⟨_, rfl⟩
theorem exhausted_refused : checkedTransfer 8 0 start offer = none := by decide

end Controls

#print axioms transfer_preserves_coherent
#print axioms transferred_writers_exact
#print axioms transfer_preserves_lease_valid
#print axioms transfer_preserves_frame_inventory
#print axioms transfer_preserves_unrelated_writer
#print axioms checkedTransfer_preserves_valid
#print axioms Controls.obligation_is_live
#print axioms Controls.return_discharges
#print axioms Controls.live_recovery_refused
#print axioms Controls.recovery_discharges
#print axioms Controls.stale_refused
#print axioms Controls.wrong_job_refused
#print axioms Controls.revision_exhaustion_refused
#print axioms Controls.exhausted_refused

end Mettapedia.Machines.Kernel.EpochWriterLease
