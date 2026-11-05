import Mathlib.Tactic

/-!
# Partitioned frame identities

Each BOOT range owns one fixed interval of frame indexes.  Independent ranges
therefore retain the same physical identities when their allocation order is
exchanged.  The runtime additionally checks bounded local indexes and vacancy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.PartitionedFrameAllocation

structure FrameId where
  range : Nat
  offset : Nat
  deriving DecidableEq, Repr

def physicalIndex (quota : Nat) (frame : FrameId) : Nat :=
  (frame.range - 1) * quota + frame.offset

def Valid (quota : Nat) (frame : FrameId) : Bool :=
  decide (frame.range > 0 ∧ quota > 0 ∧ frame.offset < quota)

theorem different_ranges_distinct {left right : FrameId}
    (different : left.range ≠ right.range) : left ≠ right := by
  intro same
  exact different (congrArg FrameId.range same)

abbrev State := FrameId → Option Nat

def permitted (state : State) (quota : Nat) (frame : FrameId) : Bool :=
  Valid quota frame && decide (state frame = none)

def install (state : State) (quota : Nat) (frame : FrameId) (token : Nat) : Option State :=
  if permitted state quota frame then
    some (Function.update state frame (some token))
  else none

theorem install_exact {state next : State} {quota token : Nat} {frame : FrameId}
    (accepted : install state quota frame token = some next) :
    next frame = some token := by
  unfold install at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst next
    simp
  · cases accepted

theorem install_preserves_other {state next : State} {quota token : Nat}
    {frame other : FrameId} (different : other ≠ frame)
    (accepted : install state quota frame token = some next) :
    next other = state other := by
  unfold install at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst next
    simp [different]
  · cases accepted

theorem independent_installs_commute (state : State)
    {left right : FrameId} {leftToken rightToken : Nat}
    (differentRanges : left.range ≠ right.range) :
    Function.update (Function.update state left (some leftToken)) right (some rightToken) =
      Function.update (Function.update state right (some rightToken)) left (some leftToken) := by
  have different : left ≠ right := different_ranges_distinct differentRanges
  have different' : right ≠ left := Ne.symm different
  funext frame
  by_cases atLeft : frame = left <;> by_cases atRight : frame = right <;>
    simp [atLeft, atRight, different, different']

namespace Controls

def empty : State := fun _ => none
def leftFrame : FrameId := ⟨1, 0⟩
def rightFrame : FrameId := ⟨2, 0⟩
def leftThenRight : State :=
  Function.update (Function.update empty leftFrame (some 11)) rightFrame (some 22)
def rightThenLeft : State :=
  Function.update (Function.update empty rightFrame (some 22)) leftFrame (some 11)

theorem exact_physical_indexes :
    physicalIndex 4 leftFrame = 0 ∧ physicalIndex 4 rightFrame = 4 := by decide
theorem orders_equal : leftThenRight = rightThenLeft := by
  exact independent_installs_commute empty (left := leftFrame) (right := rightFrame)
    (leftToken := 11) (rightToken := 22) (by decide)
theorem ranges_distinct : leftFrame ≠ rightFrame := by decide

end Controls

#print axioms different_ranges_distinct
#print axioms install_exact
#print axioms install_preserves_other
#print axioms independent_installs_commute

end Mettapedia.Machines.Kernel.PartitionedFrameAllocation
