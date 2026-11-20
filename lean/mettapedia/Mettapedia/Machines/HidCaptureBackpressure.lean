import Mettapedia.Machines.NetworkJournalGate

/-!
# Finite input queues across a durability pause

A producer can overrun a finite hardware queue before a paused consumer runs.
Draining every retained event afterward cannot recover the dropped prefix.
Conversely, interleaving one pull after each offer loses nothing at any positive
capacity. This explains why an admission-paced test can pass while a burst fails.

The model counts one finite queue. DMA rings, private outboxes, event payloads,
device timing and the native observer require separate bindings. In particular,
it does not assert that permission to run alone supplies enough capture service.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HidCaptureBackpressure

@[ext] structure Queue where
  queued : Nat := 0
  offered : Nat := 0
  captured : Nat := 0
  dropped : Nat := 0
  deriving Repr, DecidableEq

def empty : Queue := {}

def offer (capacity : Nat) (s : Queue) : Queue :=
  if s.queued < capacity then
    { s with queued := s.queued + 1, offered := s.offered + 1 }
  else { s with offered := s.offered + 1, dropped := s.dropped + 1 }

def pull (s : Queue) : Queue :=
  if s.queued = 0 then s
  else { s with queued := s.queued - 1, captured := s.captured + 1 }

def conserved (s : Queue) : Prop := s.offered = s.queued + s.captured + s.dropped

theorem offer_conserves (capacity : Nat) (s : Queue) (h : conserved s) :
    conserved (offer capacity s) := by
  unfold offer conserved at *
  split_ifs <;> (try dsimp) <;> omega

theorem pull_conserves (s : Queue) (h : conserved s) : conserved (pull s) := by
  unfold pull conserved at *
  split_ifs <;> (try dsimp) <;> omega

def burst (capacity : Nat) : Nat -> Queue
  | 0 => empty
  | n + 1 => offer capacity (burst capacity n)

theorem burst_eq (capacity n : Nat) :
    burst capacity n =
      { queued := min n capacity
        offered := n
        captured := 0
        dropped := n - capacity } := by
  induction n with
  | zero => simp [burst, empty]
  | succ n ih =>
    rw [burst, ih]
    unfold offer
    split_ifs <;> ext <;> (try dsimp at *) <;> omega

theorem burst_lossless_iff (capacity n : Nat) :
    (burst capacity n).dropped = 0 <-> n <= capacity := by
  rw [burst_eq]
  dsimp
  omega

def drain (s : Queue) : Nat -> Queue
  | 0 => s
  | n + 1 => pull (drain s n)

theorem drain_eq (s : Queue) (n : Nat) :
    drain s n =
      { s with
        queued := s.queued - n
        captured := s.captured + min s.queued n } := by
  induction n with
  | zero => simp [drain]
  | succ n ih =>
    rw [drain, ih]
    unfold pull
    split_ifs <;> ext <;> (try dsimp at *) <;> omega

theorem drain_cannot_restore_drops (s : Queue) (n : Nat) :
    (drain s n).dropped = s.dropped := by rw [drain_eq]

theorem overflow_then_complete_drain (capacity : Nat) :
    drain (burst capacity (capacity + 1)) capacity =
      { queued := 0, offered := capacity + 1, captured := capacity, dropped := 1 } := by
  rw [drain_eq, burst_eq]
  ext <;> (try dsimp) <;> omega

def paced (capacity : Nat) : Nat -> Queue
  | 0 => empty
  | n + 1 => pull (offer capacity (paced capacity n))

theorem paced_eq (capacity n : Nat) (positive : 0 < capacity) :
    paced capacity n = { queued := 0, offered := n, captured := n, dropped := 0 } := by
  induction n with
  | zero => rfl
  | succ n ih => simp [paced, ih, offer, pull, positive]

def servicePull (threshold : Nat) (batch : NetworkJournalGate.Batch) (s : Queue) : Queue :=
  if NetworkJournalGate.clientEligible threshold batch then pull s else s

def attemptedBurst (threshold : Nat) (batch : NetworkJournalGate.Batch)
    (capacity : Nat) : Nat -> Queue
  | 0 => empty
  | n + 1 => servicePull threshold batch (offer capacity (attemptedBurst threshold batch capacity n))

theorem active_attempts_cannot_capture (threshold capacity n : Nat)
    (batch : NetworkJournalGate.Batch) (active : batch.active = true) :
    attemptedBurst threshold batch capacity n = burst capacity n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [attemptedBurst, servicePull, NetworkJournalGate.active_excludes (s := batch) active threshold,
      burst, ih]

theorem active_pause_overflows (threshold capacity : Nat)
    (batch : NetworkJournalGate.Batch) (active : batch.active = true) :
    drain (attemptedBurst threshold batch capacity (capacity + 1)) capacity =
      { queued := 0, offered := capacity + 1, captured := capacity, dropped := 1 } := by
  rw [active_attempts_cannot_capture threshold capacity (capacity + 1) batch active]
  exact overflow_then_complete_drain capacity

example : (burst 16 17).dropped = 1 := by decide
example : (paced 16 17).dropped = 0 := by decide

end Mettapedia.Machines.HidCaptureBackpressure
