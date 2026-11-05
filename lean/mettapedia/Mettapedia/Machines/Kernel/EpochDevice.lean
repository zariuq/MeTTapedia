import Mettapedia.Machines.Kernel.EpochLedger
import Mettapedia.Languages.C11.IntegerOperators
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Recorded synchronous device commands

An authorized PCI command records identity, before/expected/observed register
values and whether a write was attempted. A failed readback remains an event:
the observed value, not a fictional rollback, becomes the replay state.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochDevice

open EpochLedger
open Mettapedia.Languages.C11.IntegerOperators

def commandWidth : Nat := 16

def commandBound : Nat := 2 ^ commandWidth

structure Command where
  subject : Nat
  slot : Nat
  device : Nat
  identity : Nat
  expectedIdentity : Nat
  allowed : Nat
  setBits : Nat
  clearBits : Nat
  before : Nat
  expected : Nat
  after : Nat
  attempted : Bool
  success : Bool
  deriving DecidableEq, Repr

structure World where
  registers : Nat → Nat

def identityValid (command : Command) : Bool :=
  command.identity == command.expectedIdentity

def nextValue (command : Command) : Nat :=
  (command.before ||| command.setBits) &&& wordComplement commandWidth command.clearBits

def Permitted (world : World) (command : Command) : Prop :=
  command.subject ≠ 0 ∧ command.slot ≠ 0 ∧ command.device ≠ 0 ∧
  command.expectedIdentity ≠ 0 ∧ command.allowed ≠ 0 ∧
  command.allowed < commandBound ∧ command.setBits < commandBound ∧
  command.clearBits < commandBound ∧ command.before < commandBound ∧
  command.expected < commandBound ∧ command.after < commandBound ∧
  (command.setBits ||| command.clearBits) &&&
      wordComplement commandWidth command.allowed = 0 ∧
  command.setBits &&& command.clearBits = 0 ∧
  if identityValid command then
    world.registers command.device = command.before ∧
    command.expected = nextValue command ∧
    command.attempted = decide (command.expected ≠ command.before) ∧
    command.success = decide (command.after = command.expected)
  else
    command.attempted = false ∧ command.success = false

instance permittedDecidable (world : World) (command : Command) :
    Decidable (Permitted world command) := by
  unfold Permitted
  infer_instance

def applyCommand (world : World) (command : Command) : World :=
  if identityValid command then
    { registers := Function.update world.registers command.device command.after }
  else world

def step (world : World) (command : Command) : World := applyCommand world command

def checkedCommand (maximum capacity : Nat)
    (ledger : Ledger World Command) (command : Command) : Option (Ledger World Command) :=
  if Permitted ledger.current command then commit maximum capacity step ledger command else none

theorem applyCommand_preserves_other (world : World) (command : Command) {device : Nat}
    (different : device ≠ command.device) :
    (applyCommand world command).registers device = world.registers device := by
  unfold applyCommand
  split
  · simp [different]
  · rfl

theorem checkedCommand_permitted {maximum capacity : Nat}
    {ledger next : Ledger World Command} {command : Command}
    (accepted : checkedCommand maximum capacity ledger command = some next) :
    Permitted ledger.current command := by
  unfold checkedCommand at accepted
  split at accepted
  · assumption
  · cases accepted

theorem checkedCommand_preserves_valid {maximum capacity : Nat}
    {ledger next : Ledger World Command} {command : Command}
    (valid : Valid step ledger)
    (accepted : checkedCommand maximum capacity ledger command = some next) :
    Valid step next := by
  unfold checkedCommand at accepted
  split at accepted
  · exact commit_preserves_valid step valid accepted
  · cases accepted

theorem checkedCommand_current {maximum capacity : Nat}
    {ledger next : Ledger World Command} {command : Command}
    (accepted : checkedCommand maximum capacity ledger command = some next) :
    next.current = applyCommand ledger.current command := by
  unfold checkedCommand at accepted
  split at accepted
  · unfold commit at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      rfl
    · cases accepted
  · cases accepted

theorem checkedCommand_preserves_other_device {maximum capacity : Nat}
    {ledger next : Ledger World Command} {command : Command} {device : Nat}
    (different : device ≠ command.device)
    (accepted : checkedCommand maximum capacity ledger command = some next) :
    next.current.registers device = ledger.current.registers device := by
  rw [checkedCommand_current accepted]
  exact applyCommand_preserves_other _ _ different

namespace Controls

def initial : World :=
  ⟨fun device => if device = 0x300 then 1 else if device = 0x400 then 9 else 0⟩

def success : Command :=
  ⟨13, 19, 0x300, 0x100e8086, 0x100e8086, 6, 4, 0, 1, 5, 5, true, true⟩

def readbackFailure : Command :=
  ⟨13, 19, 0x300, 0x100e8086, 0x100e8086, 6, 4, 0, 1, 5, 4, true, false⟩

def identityFailure : Command :=
  ⟨13, 19, 0x300, 0xdeadbeef, 0x100e8086, 6, 4, 0, 0, 0, 0, false, false⟩

def start : Ledger World Command := ⟨initial, initial, 0, [], [], true⟩

def succeeded : Ledger World Command :=
  ⟨initial, applyCommand initial success, 1, [success],
    [⟨1, success, initial, applyCommand initial success⟩], true⟩

def failedReadback : Ledger World Command :=
  ⟨initial, applyCommand initial readbackFailure, 1, [readbackFailure],
    [⟨1, readbackFailure, initial, applyCommand initial readbackFailure⟩], true⟩

def failedIdentity : Ledger World Command :=
  ⟨initial, applyCommand initial identityFailure, 1, [identityFailure],
    [⟨1, identityFailure, initial, applyCommand initial identityFailure⟩], true⟩

theorem start_valid : Valid step start := by simp [Valid, start, replay, traceFrom]

theorem success_permitted : Permitted initial success := by decide
theorem readback_failure_permitted : Permitted initial readbackFailure := by decide
theorem identity_failure_permitted : Permitted initial identityFailure := by decide

theorem success_is_checked : checkedCommand 10 8 start success = some succeeded := by
  unfold checkedCommand
  change (if Permitted initial success then commit 10 8 step start success else none) = some succeeded
  rw [if_pos success_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem readback_failure_is_recorded :
    checkedCommand 10 8 start readbackFailure = some failedReadback := by
  unfold checkedCommand
  change (if Permitted initial readbackFailure then
    commit 10 8 step start readbackFailure else none) = some failedReadback
  rw [if_pos readback_failure_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem identity_failure_is_recorded :
    checkedCommand 10 8 start identityFailure = some failedIdentity := by
  unfold checkedCommand
  change (if Permitted initial identityFailure then
    commit 10 8 step start identityFailure else none) = some failedIdentity
  rw [if_pos identity_failure_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem success_publishes_expected : succeeded.current.registers 0x300 = 5 := by decide

theorem failed_readback_publishes_observation :
    failedReadback.current.registers 0x300 = 4 ∧ failedReadback.events.length = 1 := by decide

theorem identity_failure_has_no_device_effect :
    failedIdentity.current.registers 0x300 = 1 ∧ failedIdentity.events.length = 1 := by decide

theorem unrelated_device_survives : succeeded.current.registers 0x400 = 9 := by
  have preserved := checkedCommand_preserves_other_device (ledger := start) (next := succeeded)
    (command := success) (device := 0x400) (by decide) success_is_checked
  exact preserved.trans (by rfl)

theorem exhausted_is_refused : checkedCommand 10 0 start success = none := by decide

end Controls

#print axioms applyCommand_preserves_other
#print axioms checkedCommand_preserves_valid
#print axioms checkedCommand_preserves_other_device
#print axioms Controls.success_is_checked
#print axioms Controls.readback_failure_is_recorded
#print axioms Controls.identity_failure_is_recorded
#print axioms Controls.failed_readback_publishes_observation
#print axioms Controls.identity_failure_has_no_device_effect
#print axioms Controls.unrelated_device_survives
#print axioms Controls.exhausted_is_refused

end Mettapedia.Machines.Kernel.EpochDevice
