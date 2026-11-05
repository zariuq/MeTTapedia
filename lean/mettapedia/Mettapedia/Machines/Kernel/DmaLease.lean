import Mathlib.Tactic

/-!
# Bounded DMA lease and controller-generation lifecycle

Reusable DMA storage is available again after either an exact submitted tag and
completion phase are observed, or a quarantined lease is retired across an
observed controller-quiescence boundary.  Retirement binds the buffer to the
next controller generation; it still cannot be prepared until rebuilt queues
publish that generation as active.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.DmaLease

structure Buffer where
  virtualAddress : Nat
  physicalAddress : Nat
  length : Nat
  deriving DecidableEq, Repr

inductive Phase where
  | available
  | prepared (tag : Nat)
  | inFlight (tag : Nat)
  | quarantined
  deriving DecidableEq, Repr

structure Lease where
  buffer : Buffer
  phase : Phase
  deriving DecidableEq, Repr

inductive Action where
  | prepare (tag : Nat)
  | submit (tag : Nat)
  | abort (tag : Nat)
  | complete (expected observed : Nat) (expectedPhase observedPhase : Bool)
  | uncertain (tag : Nat) (submitted : Bool)
  deriving DecidableEq, Repr

inductive Status where
  | ok
  | busy
  | invalid
  deriving DecidableEq, Repr

def step (lease : Lease) (action : Action) : Lease × Status := match action, lease.phase with
  | .prepare tag, .available =>
      if tag = 0 then (lease, .invalid) else ({ lease with phase := .prepared tag }, .ok)
  | .prepare _, _ => (lease, .busy)
  | .submit tag, .prepared held =>
      if tag = held then ({ lease with phase := .inFlight tag }, .ok) else (lease, .invalid)
  | .submit _, _ => (lease, .invalid)
  | .abort tag, .prepared held =>
      if tag = held then ({ lease with phase := .available }, .ok) else (lease, .invalid)
  | .abort _, _ => (lease, .invalid)
  | .complete expected observed expectedPhase observedPhase, .inFlight held =>
      if expected = held ∧ observed = held ∧ expectedPhase = observedPhase then
        ({ lease with phase := .available }, .ok)
      else ({ lease with phase := .quarantined }, .invalid)
  | .complete _ _ _ _, _ => ({ lease with phase := .quarantined }, .invalid)
  | .uncertain tag false, .prepared held =>
      if tag = held then ({ lease with phase := .available }, .ok)
      else ({ lease with phase := .quarantined }, .invalid)
  | .uncertain tag true, .inFlight held =>
      ({ lease with phase := .quarantined }, if tag = held then .ok else .invalid)
  | .uncertain _ _, _ => ({ lease with phase := .quarantined }, .invalid)

theorem step_preserves_buffer (lease : Lease) (action : Action) :
    (step lease action).1.buffer = lease.buffer := by
  rcases lease with ⟨buffer, phase⟩
  cases action <;> cases phase <;> simp [step] <;> split <;> simp_all
  all_goals split <;> simp_all

theorem quarantine_absorbing (lease : Lease) (action : Action)
    (quarantined : lease.phase = .quarantined) :
    (step lease action).1.phase = .quarantined := by
  rcases lease with ⟨buffer, phase⟩
  simp at quarantined
  subst phase
  cases action <;> simp [step]

theorem exact_completion_reuses {lease next : Lease} {expected observed : Nat}
    {expectedPhase observedPhase : Bool}
    (inFlight : lease.phase = .inFlight expected)
    (transition : step lease (.complete expected observed expectedPhase observedPhase) =
      (next, .ok)) :
    observed = expected ∧ observedPhase = expectedPhase ∧ next.phase = .available := by
  rcases lease with ⟨buffer, phase⟩
  simp at inFlight
  subst phase
  simp [step] at transition
  split at transition
  · have leaseEq : ({ buffer := buffer, phase := Phase.available } : Lease) = next :=
      congrArg Prod.fst transition
    cases leaseEq
    simp_all
  · cases transition

theorem mismatched_completion_quarantines (lease : Lease) (held observed : Nat)
    (expectedPhase observedPhase : Bool) (inFlight : lease.phase = .inFlight held)
    (mismatch : observed ≠ held ∨ observedPhase ≠ expectedPhase) :
    (step lease (.complete held observed expectedPhase observedPhase)).1.phase = .quarantined := by
  rcases lease with ⟨buffer, phase⟩
  simp at inFlight
  subst phase
  simp [step]
  split
  · simp_all
  · rfl

theorem submitted_uncertainty_quarantines (lease : Lease) (tag : Nat)
    (inFlight : lease.phase = .inFlight tag) :
    (step lease (.uncertain tag true)).1.phase = .quarantined := by
  rcases lease with ⟨buffer, phase⟩
  simp at inFlight
  subst phase
  simp [step]

theorem prepared_abort_reuses {lease next : Lease} {tag : Nat}
    (prepared : lease.phase = .prepared tag)
    (transition : step lease (.abort tag) = (next, .ok)) :
    next.phase = .available := by
  rcases lease with ⟨buffer, phase⟩
  simp at prepared
  subst phase
  have phaseEq := congrArg (fun result => result.1.phase) transition
  simpa [step] using phaseEq.symm

inductive DevicePhase where
  | active
  | resetting
  | quiescent
  deriving DecidableEq, Repr

structure DeviceEpoch where
  identity : Nat
  generation : Nat
  limit : Nat
  phase : DevicePhase
  deriving DecidableEq, Repr

structure BoundLease where
  lease : Lease
  device : Nat
  generation : Nat
  deriving DecidableEq, Repr

def beginReset (device : DeviceEpoch) : DeviceEpoch × Status :=
  if device.phase = .active ∧ device.identity ≠ 0 ∧ device.generation ≠ 0 ∧
      device.generation < device.limit then
    ({ device with phase := .resetting }, .ok)
  else (device, .invalid)

def observeQuiescent (device : DeviceEpoch) (ccEnabled cstsReady : Bool) :
    DeviceEpoch × Status :=
  if device.phase = .resetting ∧ ccEnabled = false ∧ cstsReady = false then
    ({ device with phase := .quiescent }, .ok)
  else (device, .invalid)

def retireQuarantined (bound : BoundLease) (device : DeviceEpoch) :
    BoundLease × Status :=
  if device.phase = .quiescent ∧ device.generation < device.limit ∧
      bound.lease.phase = .quarantined ∧ bound.device = device.identity ∧
      bound.generation = device.generation then
    ({ bound with
        lease := { bound.lease with phase := .available }
        generation := device.generation + 1 }, .ok)
  else (bound, .invalid)

def rebindAvailable (bound : BoundLease) (device : DeviceEpoch) :
    BoundLease × Status :=
  if device.phase = .quiescent ∧ device.generation < device.limit ∧
      bound.lease.phase = .available ∧ bound.device = device.identity ∧
      bound.generation = device.generation then
    ({ bound with generation := device.generation + 1 }, .ok)
  else (bound, .invalid)

def resume (device : DeviceEpoch) (queuesReady : Bool) : DeviceEpoch × Status :=
  if device.phase = .quiescent ∧ queuesReady = true ∧ device.identity ≠ 0 ∧
      device.generation ≠ 0 ∧ device.generation < device.limit then
    ({ device with generation := device.generation + 1, phase := .active }, .ok)
  else (device, .invalid)

def prepareBound (bound : BoundLease) (device : DeviceEpoch) (tag : Nat) :
    BoundLease × Status :=
  if device.phase = .active ∧ bound.device = device.identity ∧
      bound.generation = device.generation then
    let result := step bound.lease (.prepare tag)
    ({ bound with lease := result.1 }, result.2)
  else (bound, .invalid)

theorem retirement_preserves_buffer (bound : BoundLease) (device : DeviceEpoch) :
    (retireQuarantined bound device).1.lease.buffer = bound.lease.buffer := by
  simp only [retireQuarantined]
  split <;> rfl

theorem retirement_ok_iff (bound : BoundLease) (device : DeviceEpoch) :
    (retireQuarantined bound device).2 = .ok ↔
      device.phase = .quiescent ∧ device.generation < device.limit ∧
      bound.lease.phase = .quarantined ∧ bound.device = device.identity ∧
      bound.generation = device.generation := by
  unfold retireQuarantined
  split <;> simp_all

theorem retirement_binds_next_generation (bound next : BoundLease) (device : DeviceEpoch)
    (transition : retireQuarantined bound device = (next, .ok)) :
    next.lease.phase = .available ∧ next.generation = device.generation + 1 := by
  simp only [retireQuarantined] at transition
  split at transition
  · cases transition
    simp
  · cases transition

theorem prepare_refused_while_quiescent (bound : BoundLease) (device : DeviceEpoch)
    (quiescent : device.phase = .quiescent) (tag : Nat) :
    (prepareBound bound device tag).2 = .invalid := by
  simp [prepareBound, quiescent]

theorem resume_advances_generation {device next : DeviceEpoch}
    (transition : resume device true = (next, .ok)) :
    device.phase = .quiescent ∧ next.phase = .active ∧
      next.generation = device.generation + 1 := by
  simp only [resume] at transition
  split at transition
  · rename_i permitted
    cases transition
    simp_all
  · cases transition

theorem failed_quiescence_observation_preserves_device (device : DeviceEpoch)
    (ccEnabled cstsReady : Bool)
    (observedUnsafe : ccEnabled = true ∨ cstsReady = true) :
    observeQuiescent device ccEnabled cstsReady = (device, .invalid) := by
  simp only [observeQuiescent]
  split
  · simp_all
  · rfl

namespace ResetControls

def buffer : Buffer := ⟨0x500000, 0x200000, 4096⟩
def active : DeviceEpoch := ⟨9, 1, 4, .active⟩
def bound : BoundLease := ⟨⟨buffer, .quarantined⟩, 9, 1⟩
def resetting : DeviceEpoch := (beginReset active).1
def quiescent : DeviceEpoch := (observeQuiescent resetting false false).1
def retired : BoundLease := (retireQuarantined bound quiescent).1
def resumed : DeviceEpoch := (resume quiescent true).1

theorem reset_begins : resetting.phase = .resetting := by decide
theorem enabled_controller_not_quiescent :
    (observeQuiescent resetting true false).2 = .invalid := by decide
theorem exact_quiescence_observed : quiescent.phase = .quiescent := by decide
theorem old_lease_retired :
    retired.lease.phase = .available ∧ retired.generation = 2 := by decide
theorem retired_lease_cannot_prepare_early :
    (prepareBound retired quiescent 18).2 = .invalid := by decide
theorem rebuilt_generation_resumes :
    resumed.phase = .active ∧ resumed.generation = 2 := by decide
theorem retired_lease_prepares_after_resume :
    (prepareBound retired resumed 18).2 = .ok ∧
      (prepareBound retired resumed 18).1.lease.phase = .prepared 18 := by decide
theorem stale_identity_refused :
    (retireQuarantined { bound with device := 10 } quiescent).2 = .invalid := by decide
theorem exhausted_generation_refuses_reset :
    (beginReset { active with generation := 4 }).2 = .invalid := by decide

end ResetControls

namespace Controls

def buffer : Buffer := ⟨0x400000, 0x100000, 4096⟩
def available : Lease := ⟨buffer, .available⟩
def prepared : Lease := (step available (.prepare 17)).1
def submitted : Lease := (step prepared (.submit 17)).1
def complete : Lease := (step submitted (.complete 17 17 true true)).1
def wrongTag : Lease := (step submitted (.complete 17 18 true true)).1
def timeout : Lease := (step submitted (.uncertain 17 true)).1

theorem prepared_exact : prepared.phase = .prepared 17 := by decide
theorem submitted_exact : submitted.phase = .inFlight 17 := by decide
theorem completion_reuses : complete.phase = .available := by decide
theorem wrong_tag_quarantines : wrongTag.phase = .quarantined := by decide
theorem timeout_quarantines : timeout.phase = .quarantined := by decide
theorem quarantined_cannot_prepare :
    (step timeout (.prepare 18)).1.phase = .quarantined ∧
    (step timeout (.prepare 18)).2 = .busy := by decide
theorem pre_submit_abort_reuses :
    (step prepared (.uncertain 17 false)).1.phase = .available := by decide
theorem wrong_pre_submit_abort_quarantines :
    (step prepared (.uncertain 18 false)).1.phase = .quarantined := by decide

end Controls

#print axioms step_preserves_buffer
#print axioms quarantine_absorbing
#print axioms exact_completion_reuses
#print axioms mismatched_completion_quarantines
#print axioms submitted_uncertainty_quarantines
#print axioms prepared_abort_reuses
#print axioms retirement_preserves_buffer
#print axioms retirement_ok_iff
#print axioms retirement_binds_next_generation
#print axioms prepare_refused_while_quiescent
#print axioms resume_advances_generation
#print axioms failed_quiescence_observation_preserves_device
#print axioms Controls.quarantined_cannot_prepare

end Mettapedia.Machines.Kernel.DmaLease
