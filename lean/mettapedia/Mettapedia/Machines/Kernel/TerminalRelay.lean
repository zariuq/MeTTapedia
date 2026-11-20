import Mettapedia.Machines.Kernel.InvocationContext

/-!
# Terminal relay custody

An attached job has a fixed starter and child incarnation. Detachment moves
its presentation and keeps the newest bounded output. A terminal with the
held grant may adopt the presentation. Forced retirement still consults the
exact starter and child. The byte-ring representation and held kernel queries
are separate runtime obligations.
-/

namespace Mettapedia.Machines.Kernel.TerminalRelay

structure Run where
  target : Nat
  task : Nat
  deriving DecidableEq

structure Slot where
  run : Run
  number : Nat
  deriving DecidableEq

inductive Presentation where
  | attached (slot : Slot)
  | detached (name : Nat)
  deriving DecidableEq

structure Relay where
  starter : Run
  child : Run
  presentation : Presentation
  output : List UInt8
  deriving DecidableEq

def newest (capacity : Nat) (bytes : List UInt8) : List UInt8 :=
  bytes.drop (bytes.length - capacity)

theorem newest_bounded (capacity : Nat) (bytes : List UInt8) :
    (newest capacity bytes).length ≤ capacity := by
  simp only [newest, List.length_drop]
  omega

inductive Action where
  | detach (presenter : Slot) (name : Nat) (screen : List UInt8)
  | adopt (presenter : Slot) (name : Nat) (holdsGrant : Bool)
  | write (bytes : List UInt8)

def step (capacity : Nat) (s : Relay) : Action → Relay
  | .detach presenter name screen =>
    if s.presentation = .attached presenter ∧ name ≠ 0 then
      { s with presentation := .detached name, output := newest capacity (screen ++ s.output) }
    else s
  | .adopt presenter name holdsGrant =>
    if holdsGrant = true ∧ s.presentation = .detached name then
      { s with presentation := .attached presenter }
    else s
  | .write bytes =>
    match s.presentation with
    | .attached _ => { s with output := s.output ++ bytes.take (capacity - s.output.length) }
    | .detached _ => { s with output := newest capacity (s.output ++ bytes) }

def custody (s : Relay) : Run × Run := (s.starter, s.child)

def mayForceStop (s : Relay) (caller currentChild : Run) : Bool :=
  decide (caller = s.starter ∧ currentChild = s.child)

theorem stale_presenter_cannot_detach (capacity : Nat) (s : Relay) (slot : Slot)
    (name : Nat) (screen : List UInt8) (wrong : s.presentation ≠ .attached slot) :
    step capacity s (.detach slot name screen) = s := by
  simp [step, wrong]

theorem ungranted_cannot_adopt (capacity : Nat) (s : Relay) (newSlot : Slot) (name : Nat) :
    step capacity s (.adopt newSlot name false) = s := by
  simp [step]

theorem adoption_preserves_output (capacity : Nat) (s : Relay) (newSlot : Slot) (name : Nat) :
    (step capacity s (.adopt newSlot name true)).output = s.output := by
  simp only [step]
  split <;> rfl

theorem step_preserves_custody (capacity : Nat) (s : Relay) (action : Action) :
    custody (step capacity s action) = custody s := by
  cases action <;> simp only [step] <;> split <;> rfl

theorem trace_preserves_custody (capacity : Nat) (s : Relay) (actions : List Action) :
    custody (actions.foldl (step capacity) s) = custody s := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih =>
    simp only [List.foldl_cons]
    rw [ih, step_preserves_custody]

theorem trace_preserves_stop (capacity : Nat) (s : Relay) (actions : List Action)
    (caller currentChild : Run) :
    mayForceStop (actions.foldl (step capacity) s) caller currentChild =
      mayForceStop s caller currentChild := by
  have fixed := trace_preserves_custody capacity s actions
  have starter := congrArg Prod.fst fixed
  have child := congrArg Prod.snd fixed
  simp only [custody] at starter child
  simp only [mayForceStop, starter, child]

theorem step_output_bounded (capacity : Nat) (s : Relay) (action : Action)
    (bounded : s.output.length ≤ capacity) : (step capacity s action).output.length ≤ capacity := by
  cases action with
  | detach =>
    simp only [step]
    split
    · exact newest_bounded _ _
    · exact bounded
  | adopt =>
    simp only [step]
    split <;> exact bounded
  | write bytes =>
    simp only [step]
    split
    · simp only [List.length_append, List.length_take]
      have kept := Nat.min_le_left (capacity - s.output.length) bytes.length
      omega
    · exact newest_bounded _ _

private def first : Slot := ⟨⟨41, 70⟩, 2⟩
private def replacement : Slot := ⟨⟨41, 71⟩, 2⟩
private def child : Run := ⟨42, 90⟩
private def running : Relay := ⟨first.run, child, .attached first, [1, 2]⟩

example : step 4 running (.detach replacement 1 [3]) = running := by decide

example : (List.foldl (step 4) running
    [.detach first 1 [3], .write [4, 5], .adopt replacement 1 true]).output = [1, 2, 4, 5] := by decide

example : mayForceStop (step 4 (step 4 running (.detach first 1 []))
    (.adopt replacement 1 true)) replacement.run child = false := by decide

#print axioms trace_preserves_custody
#print axioms trace_preserves_stop
#print axioms step_output_bounded

end Mettapedia.Machines.Kernel.TerminalRelay
