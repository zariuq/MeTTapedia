import Mettapedia.Machines.Kernel.EpochHandover
import Mathlib.Tactic

/-!
# Keyed successor activation

Activation publishes a finite set of previously absent successor bindings,
marks exactly one dormant incarnation active, and admits its task once. The
predecessor must already be retired under the same nonzero key.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochActivation

open EpochLedger EpochMemory

structure Event where
  predecessor : Nat
  successor : Nat
  task : Nat
  surface : Nat
  key : Nat
  bindings : List Binding
  deriving DecidableEq, Repr

structure World where
  memory : Memory
  predecessorRetired : Bool
  predecessorKey : Nat
  dormant : Bool
  activated : Bool
  runQueue : List Nat

def Permitted (world : World) (event : Event) : Prop :=
  world.predecessorRetired = true ∧ world.dormant = true ∧ world.activated = false ∧
  event.predecessor ≠ 0 ∧ event.successor ≠ 0 ∧ event.predecessor ≠ event.successor ∧
  event.task ≠ 0 ∧ event.surface ≠ 0 ∧ event.key ≠ 0 ∧
  event.key = world.predecessorKey ∧ event.task ∉ world.runQueue ∧ event.bindings ≠ [] ∧
  event.bindings.Pairwise (fun left right => left.frame ≠ right.frame) ∧
  event.bindings.Forall (fun binding =>
    binding.subject = event.successor ∧ binding.key = event.key ∧
      world.memory.live binding.frame = none)

instance permittedDecidable (world : World) (event : Event) :
    Decidable (Permitted world event) := by
  unfold Permitted
  infer_instance

def installAll : Memory → List Binding → Memory
  | memory, [] => memory
  | memory, binding :: rest => installAll (install memory binding) rest

def activate (world : World) (event : Event) : World :=
  { memory := installAll world.memory event.bindings
    predecessorRetired := world.predecessorRetired
    predecessorKey := world.predecessorKey
    dormant := false
    activated := true
    runQueue := world.runQueue ++ [event.task] }

def step (world : World) (event : Event) : World := activate world event

def checkedActivation (maximum capacity : Nat)
    (ledger : Ledger World Event) (event : Event) : Option (Ledger World Event) :=
  if Permitted ledger.current event then commit maximum capacity step ledger event else none

theorem installAll_preserves_other (memory : Memory) (bindings : List Binding) {frame : Nat}
    (different : ∀ binding ∈ bindings, frame ≠ binding.frame) :
    (installAll memory bindings).live frame = memory.live frame ∧
      (installAll memory bindings).retired frame = memory.retired frame := by
  induction bindings generalizing memory with
  | nil => simp [installAll]
  | cons binding rest ih =>
      have headDifferent : frame ≠ binding.frame := different binding (by simp)
      have tailDifferent : ∀ item ∈ rest, frame ≠ item.frame := by
        intro item member
        exact different item (by simp [member])
      rw [show installAll memory (binding :: rest) = installAll (install memory binding) rest by rfl]
      rw [(ih (install memory binding) tailDifferent).1,
        (ih (install memory binding) tailDifferent).2]
      exact install_preserves_other memory binding headDifferent

theorem checkedActivation_permitted {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (accepted : checkedActivation maximum capacity ledger event = some next) :
    Permitted ledger.current event := by
  unfold checkedActivation at accepted
  split at accepted
  · assumption
  · cases accepted

theorem checkedActivation_preserves_valid {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (valid : Valid step ledger)
    (accepted : checkedActivation maximum capacity ledger event = some next) :
    Valid step next := by
  unfold checkedActivation at accepted
  split at accepted
  · exact commit_preserves_valid step valid accepted
  · cases accepted

theorem checkedActivation_current {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (accepted : checkedActivation maximum capacity ledger event = some next) :
    next.current = activate ledger.current event := by
  unfold checkedActivation at accepted
  split at accepted
  · unfold commit at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      rfl
    · cases accepted
  · cases accepted

theorem checkedActivation_admits_once {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event}
    (accepted : checkedActivation maximum capacity ledger event = some next) :
    next.current.dormant = false ∧ next.current.activated = true ∧
      next.current.runQueue = ledger.current.runQueue ++ [event.task] := by
  rw [checkedActivation_current accepted]
  simp [activate]

theorem checkedActivation_preserves_other_frame {maximum capacity : Nat}
    {ledger next : Ledger World Event} {event : Event} {frame : Nat}
    (different : ∀ binding ∈ event.bindings, frame ≠ binding.frame)
    (accepted : checkedActivation maximum capacity ledger event = some next) :
    next.current.memory.live frame = ledger.current.memory.live frame ∧
      next.current.memory.retired frame = ledger.current.memory.retired frame := by
  rw [checkedActivation_current accepted]
  exact installAll_preserves_other _ _ different

namespace Controls

def first : Binding := ⟨2, 16, 300, 0x50000000, 5, 9⟩
def second : Binding := ⟨5, 16, 301, 0x50001000, 7, 9⟩
def observer : Binding := ⟨7, 3, 400, 0x43000000, 5, 3⟩

def initialMemory : Memory :=
  { live := fun frame => if frame = observer.frame then some observer else none
    retired := fun _ => none }

def initial : World := ⟨initialMemory, true, 9, true, false, [3, 14]⟩
def event : Event := ⟨9, 16, 2000, 301, 9, [first, second]⟩

def start : Ledger World Event := ⟨initial, initial, 0, [], [], true⟩
def finished : Ledger World Event :=
  ⟨initial, activate initial event, 1, [event],
    [⟨1, event, initial, activate initial event⟩], true⟩

theorem initial_valid : Valid step start := by
  simp [Valid, start, replay, traceFrom]

theorem event_permitted : Permitted initial event := by decide

theorem finished_is_checked : checkedActivation 10 8 start event = some finished := by
  unfold checkedActivation
  change (if Permitted initial event then commit 10 8 step start event else none) = some finished
  rw [if_pos event_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem finished_valid : Valid step finished :=
  checkedActivation_preserves_valid initial_valid finished_is_checked

theorem both_frames_become_live :
    finished.current.memory.live first.frame = some first ∧
      finished.current.memory.live second.frame = some second := by
  decide

theorem task_admitted_exactly_once :
    finished.current.dormant = false ∧ finished.current.activated = true ∧
      finished.current.runQueue = [3, 14, 2000] := by
  exact checkedActivation_admits_once finished_is_checked

theorem observer_survives :
    finished.current.memory.live observer.frame = some observer ∧
      finished.current.memory.retired observer.frame = none := by
  have preserved := checkedActivation_preserves_other_frame
    (ledger := start) (next := finished) (event := event)
    (frame := observer.frame) (by decide) finished_is_checked
  have liveBefore : start.current.memory.live observer.frame = some observer := by rfl
  have retiredBefore : start.current.memory.retired observer.frame = none := by rfl
  exact ⟨preserved.1.trans liveBefore, preserved.2.trans retiredBefore⟩

def wrongKey : Event := { event with key := 10 }

theorem wrong_key_refused : checkedActivation 10 8 start wrongKey = none := by decide

def livePredecessor : World := { initial with predecessorRetired := false }
def liveStart : Ledger World Event := ⟨livePredecessor, livePredecessor, 0, [], [], true⟩

theorem live_predecessor_refused : checkedActivation 10 8 liveStart event = none := by decide

end Controls

#print axioms installAll_preserves_other
#print axioms checkedActivation_preserves_valid
#print axioms checkedActivation_admits_once
#print axioms checkedActivation_preserves_other_frame
#print axioms Controls.finished_is_checked
#print axioms Controls.finished_valid
#print axioms Controls.both_frames_become_live
#print axioms Controls.task_admitted_exactly_once
#print axioms Controls.observer_survives
#print axioms Controls.wrong_key_refused
#print axioms Controls.live_predecessor_refused

end Mettapedia.Machines.Kernel.EpochActivation
