import Mettapedia.Machines.NetworkBackpressureTrace

/-!+# Concrete batch counters at the service-model boundary

Producer names the next event. Flushed names a completed durable prefix.
An explicit flush excludes clients even below the batch threshold, so the
earlier debt-only model is an overapproximation during that phase.

These arithmetic refinements and finite observation checks do not prove the C
observer, block device, FIFO implementation, eventual fairness, or hardware.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NetworkJournalGate

open NetworkBackpressure NetworkBackpressure.Trace

structure Batch where
  producer : Nat
  flushed : Nat
  epoch : Nat
  active : Bool
  deriving Repr, DecidableEq

def Valid (s : Batch) : Prop := s.producer = s.epoch + 1 ∧ s.flushed ≤ s.epoch

instance (s : Batch) : Decidable (Valid s) := by unfold Valid; infer_instance

def debt (s : Batch) := s.producer - 1 - s.flushed

def clientEligible (threshold : Nat) (s : Batch) : Bool :=
  !s.active && decide (debt s < threshold)

def project (s : Batch) (receiver : State) : State :=
  { receiver with backlog := s.epoch - s.flushed, committed := s.flushed }

theorem debt_eq {s : Batch} (valid : Valid s) : debt s = s.epoch - s.flushed := by
  simp [debt, valid.1]

theorem inactive_exact {s : Batch} (valid : Valid s) (inactive : s.active = false)
    (threshold : Nat) (receiver : State) :
    clientEligible threshold s = true ↔ Eligible threshold (project s receiver) .network := by
  simp [clientEligible, inactive, debt_eq valid, Eligible, project]

theorem eligible_refines {s : Batch} (valid : Valid s) (threshold : Nat) (receiver : State)
    (allowed : clientEligible threshold s = true) :
    Eligible threshold (project s receiver) .network := by
  simp only [clientEligible, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at allowed
  simpa [Eligible, project, ← debt_eq valid] using allowed.2

theorem active_excludes {s : Batch} (active : s.active = true) (threshold : Nat) :
    clientEligible threshold s = false := by simp [clientEligible, active]

/-- Suppressed internal work leaves the producer and logical epoch unchanged. -/
def record (internal : Bool) (s : Batch) : Batch :=
  if internal then s else { s with producer := s.producer + 1, epoch := s.epoch + 1 }

theorem internal_does_not_append (s : Batch) : record true s = s := rfl

theorem append_refines {s : Batch} (valid : Valid s) (receiver : State) :
    project (record false s) receiver = apply .append (project s receiver) := by
  have bounded := valid.2
  cases s
  cases receiver
  simp_all [project, record, apply, Valid]
  omega

theorem durable_prefix_replay {s : Batch} (receiver : State) {count : Nat}
    (bounded : count ≤ s.epoch - s.flushed) (threshold : Nat) :
    replay threshold (project s receiver) (List.replicate count Action.commit) =
      some (project { s with flushed := s.flushed + count } receiver) := by
  induction count generalizing s with
  | zero => simp [replay, project]
  | succ n ih =>
      have positive : s.flushed < s.epoch := by omega
      have admitted : Admitted threshold (project s receiver) .commit := by
        constructor
        · dsimp [Prepared, project]; omega
        · trivial
      have same : apply .commit (project s receiver) =
          project { s with flushed := s.flushed + 1 } receiver := by
        cases receiver
        simp [apply, project]
        omega
      simp only [List.replicate_succ, replay, if_pos admitted, same]
      have rest : n ≤ s.epoch - (s.flushed + 1) := by omega
      simpa [project, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (s := { s with flushed := s.flushed + 1 }) rest

inductive Event | initial | append | flushBegin | flushEnd | retry | flushed | select
  deriving Repr, DecidableEq

structure Observation where
  batch : Batch
  event : Event
  selected : Nat
  network : Bool
  browser : Bool
  drive : Bool
  files : Bool
  writes : Nat
  syncs : Nat
  deriving Repr, DecidableEq

def consistent (threshold : Nat) (o : Observation) : Bool :=
  decide (Valid o.batch) &&
  (o.network == clientEligible threshold o.batch) &&
  (o.browser == clientEligible threshold o.batch) && o.drive && o.files

def follows (threshold : Nat) (before after : Observation) : Bool :=
  let b := before.batch
  let a := after.batch
  decide (before.writes ≤ after.writes ∧ before.syncs ≤ after.syncs) &&
  match after.event with
  | .initial => false
  | .append => clientEligible threshold b && !a.active &&
      decide (a.epoch = b.epoch + 1 ∧ a.producer = b.producer + 1 ∧ a.flushed = b.flushed)
  | .flushBegin => !b.active && a.active &&
      decide (a.epoch = b.epoch ∧ a.producer = b.producer ∧ a.flushed = b.flushed)
  | .flushEnd => b.active && !a.active &&
      decide (a.epoch = b.epoch ∧ a.producer = b.producer ∧ b.flushed ≤ a.flushed ∧
        a.flushed ≤ b.flushed + 8 ∧ (b.flushed < a.flushed → before.syncs < after.syncs))
  | .retry | .flushed => a == b
  | .select => (a == b) &&
      (if after.selected == 1 then after.network else
       if after.selected == 3 then after.browser else
       after.selected == 0 || after.selected == 2 || after.selected == 11)

def check (threshold : Nat) : List Observation → Bool
  | [] => false
  | first :: rest => consistent threshold first && loop first rest
where
  loop (previous : Observation) : List Observation → Bool
  | [] => true
  | next :: rest => consistent threshold next && follows threshold previous next && loop next rest

example : clientEligible 64 ⟨65, 0, 64, false⟩ = false := by decide
example : clientEligible 64 ⟨65, 8, 64, false⟩ = true := by decide
example : clientEligible 64 ⟨65, 8, 64, true⟩ = false := by decide

#print axioms inactive_exact
#print axioms eligible_refines
#print axioms append_refines
#print axioms durable_prefix_replay

end Mettapedia.Machines.NetworkJournalGate
