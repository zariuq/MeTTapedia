import Mettapedia.Machines.Kernel.EpochMemory
import Mathlib.Tactic

/-!
# Keyed application handover

A terminal application handover transfers a finite, nonempty set of physical
frames from one subject/key to another, revokes the source's ambient runtime
state, and records the whole change as one bounded epoch. Unrelated frames are
preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochHandover

open EpochLedger EpochMemory

structure Transfer where
  before : Binding
  after : Binding
  deriving DecidableEq, Repr

structure Event where
  source : Nat
  destination : Nat
  task : Nat
  pool : Nat
  sourceKey : Nat
  destinationKey : Nat
  transfers : List Transfer
  deriving DecidableEq, Repr

structure World where
  memory : Memory
  sourceCapabilities : Nat
  sourceMessages : Nat
  retired : Bool

def TransferValid (world : World) (event : Event) (transfer : Transfer) : Prop :=
  transfer.before.frame = transfer.after.frame ∧
  transfer.before.subject = event.source ∧
  transfer.after.subject = event.destination ∧
  transfer.before.key = event.sourceKey ∧
  transfer.after.key = event.destinationKey ∧
  world.memory.live transfer.before.frame = some transfer.before

def Permitted (world : World) (event : Event) : Prop :=
  world.retired = false ∧ world.sourceCapabilities ≠ 0 ∧
  event.source ≠ 0 ∧ event.destination ≠ 0 ∧ event.source ≠ event.destination ∧
  event.task ≠ 0 ∧ event.pool ≠ 0 ∧
  event.sourceKey ≠ 0 ∧ event.destinationKey ≠ 0 ∧
  event.sourceKey ≠ event.destinationKey ∧ event.transfers ≠ [] ∧
  event.transfers.Pairwise (fun left right => left.before.frame ≠ right.before.frame) ∧
  event.transfers.Forall (TransferValid world event)

instance permittedDecidable (world : World) (event : Event) :
    Decidable (Permitted world event) := by
  unfold Permitted TransferValid
  infer_instance

def transferOne (memory : Memory) (transfer : Transfer) : Memory :=
  { live := Function.update memory.live transfer.before.frame (some transfer.after)
    retired := Function.update memory.retired transfer.before.frame (some transfer.before) }

def transferAll : Memory → List Transfer → Memory
  | memory, [] => memory
  | memory, transfer :: rest => transferAll (transferOne memory transfer) rest

def applyHandover (world : World) (event : Event) : World :=
  { memory := transferAll world.memory event.transfers
    sourceCapabilities := 0
    sourceMessages := 0
    retired := true }

def step (world : World) (event : Event) : World := applyHandover world event

def checkedHandover (maximum capacity : Nat)
    (ledger : Ledger World Event) (event : Event) : Option (Ledger World Event) :=
  if Permitted ledger.current event then commit maximum capacity step ledger event else none

theorem transferOne_preserves_other (memory : Memory) (transfer : Transfer) {frame : Nat}
    (different : frame ≠ transfer.before.frame) :
    (transferOne memory transfer).live frame = memory.live frame ∧
      (transferOne memory transfer).retired frame = memory.retired frame := by
  simp [transferOne, different]

theorem transferAll_preserves_other (memory : Memory) (transfers : List Transfer) {frame : Nat}
    (different : ∀ transfer ∈ transfers, frame ≠ transfer.before.frame) :
    (transferAll memory transfers).live frame = memory.live frame ∧
      (transferAll memory transfers).retired frame = memory.retired frame := by
  induction transfers generalizing memory with
  | nil => simp [transferAll]
  | cons transfer rest ih =>
      have headDifferent : frame ≠ transfer.before.frame := different transfer (by simp)
      have tailDifferent : ∀ item ∈ rest, frame ≠ item.before.frame := by
        intro item member
        exact different item (by simp [member])
      rw [show transferAll memory (transfer :: rest) =
        transferAll (transferOne memory transfer) rest by rfl]
      rw [(ih (transferOne memory transfer) tailDifferent).1,
        (ih (transferOne memory transfer) tailDifferent).2]
      exact transferOne_preserves_other memory transfer headDifferent

theorem checkedHandover_permitted {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (accepted : checkedHandover maximum capacity ledger event = some next) :
    Permitted ledger.current event := by
  unfold checkedHandover at accepted
  split at accepted
  · assumption
  · cases accepted

theorem checkedHandover_preserves_valid {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (valid : Valid step ledger)
    (accepted : checkedHandover maximum capacity ledger event = some next) :
    Valid step next := by
  unfold checkedHandover at accepted
  split at accepted
  · exact commit_preserves_valid step valid accepted
  · cases accepted

theorem checkedHandover_current {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (accepted : checkedHandover maximum capacity ledger event = some next) :
    next.current = applyHandover ledger.current event := by
  unfold checkedHandover at accepted
  split at accepted
  · unfold commit at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      rfl
    · cases accepted
  · cases accepted

theorem checkedHandover_revokes_source {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (accepted : checkedHandover maximum capacity ledger event = some next) :
    next.current.sourceCapabilities = 0 ∧ next.current.sourceMessages = 0 ∧
      next.current.retired = true := by
  rw [checkedHandover_current accepted]
  simp [applyHandover]

theorem checkedHandover_preserves_other_frame {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event} {frame : Nat}
    (different : ∀ transfer ∈ event.transfers, frame ≠ transfer.before.frame)
    (accepted : checkedHandover maximum capacity ledger event = some next) :
    next.current.memory.live frame = ledger.current.memory.live frame ∧
      next.current.memory.retired frame = ledger.current.memory.retired frame := by
  rw [checkedHandover_current accepted]
  exact transferAll_preserves_other _ _ different

namespace Controls

def oldA : Binding := ⟨2, 9, 100, 0x49000000, 5, 9⟩
def newA : Binding := ⟨2, 14, 100, 0x79000000, 7, 14⟩
def oldB : Binding := ⟨5, 9, 101, 0x49001000, 5, 9⟩
def newB : Binding := ⟨5, 14, 101, 0x79001000, 7, 14⟩
def observer : Binding := ⟨7, 3, 200, 0x43000000, 5, 3⟩

def initialMemory : Memory :=
  { live := fun frame =>
      if frame = oldA.frame then some oldA
      else if frame = oldB.frame then some oldB
      else if frame = observer.frame then some observer
      else none
    retired := fun _ => none }

def initial : World := ⟨initialMemory, 12, 3, false⟩

def handover : Event :=
  ⟨9, 14, 77, 0x79000000, 9, 14,
    [⟨oldA, newA⟩, ⟨oldB, newB⟩]⟩

def start : Ledger World Event := ⟨initial, initial, 0, [], [], true⟩

def finished : Ledger World Event :=
  ⟨initial, applyHandover initial handover, 1, [handover],
    [⟨1, handover, initial, applyHandover initial handover⟩], true⟩

theorem initial_valid : Valid step start := by
  simp [Valid, start, replay, traceFrom]

theorem handover_permitted : Permitted initial handover := by decide

theorem finished_is_checked : checkedHandover 10 8 start handover = some finished := by
  unfold checkedHandover
  change (if Permitted initial handover then commit 10 8 step start handover else none) = some finished
  rw [if_pos handover_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem finished_valid : Valid step finished :=
  checkedHandover_preserves_valid initial_valid finished_is_checked

theorem frames_change_key_together :
    finished.current.memory.live oldA.frame = some newA ∧
      finished.current.memory.live oldB.frame = some newB ∧
      finished.current.memory.retired oldA.frame = some oldA ∧
      finished.current.memory.retired oldB.frame = some oldB := by
  decide

theorem source_authority_is_gone :
    finished.current.sourceCapabilities = 0 ∧
      finished.current.sourceMessages = 0 ∧ finished.current.retired = true := by
  exact checkedHandover_revokes_source finished_is_checked

theorem observer_survives :
    finished.current.memory.live observer.frame = some observer ∧
      finished.current.memory.retired observer.frame = none := by
  have preserved := checkedHandover_preserves_other_frame
    (ledger := start) (next := finished) (event := handover)
    (frame := observer.frame) (by decide) finished_is_checked
  have liveBefore : start.current.memory.live observer.frame = some observer := by rfl
  have retiredBefore : start.current.memory.retired observer.frame = none := by rfl
  exact ⟨preserved.1.trans liveBefore, preserved.2.trans retiredBefore⟩

def sameKey : Event := { handover with destinationKey := 9 }

theorem same_key_refused : checkedHandover 10 8 start sameKey = none := by decide

end Controls

#print axioms transferAll_preserves_other
#print axioms checkedHandover_preserves_valid
#print axioms checkedHandover_revokes_source
#print axioms checkedHandover_preserves_other_frame
#print axioms Controls.finished_is_checked
#print axioms Controls.finished_valid
#print axioms Controls.frames_change_key_together
#print axioms Controls.source_authority_is_gone
#print axioms Controls.observer_survives
#print axioms Controls.same_key_refused

end Mettapedia.Machines.Kernel.EpochHandover
