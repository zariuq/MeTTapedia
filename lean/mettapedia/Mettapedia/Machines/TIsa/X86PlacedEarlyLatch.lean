import Mettapedia.Machines.TIsa.P1EarlyLoopContinuation
import Mettapedia.Machines.TIsa.X86PlacedJcc
import Mettapedia.Machines.TIsa.X86BranchGate
import Mettapedia.Machines.TIsa.X86RegisterIncrement

/-! # Early-loop latches in a placed image

An early latch tests its Boolean continuation, increments the unsigned
index when enabled, and compares the incremented index to the bound.
The certificate checks both branch destinations and all five instructions.
Only the layout and assigned logical registers vary between images.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 350000

namespace Mettapedia.Machines.TIsa.X86PlacedEarlyLatch

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode handlers)
open P1EarlyLoopContinuation (LoopRegisters)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev physical (register : P1Source.Reg) : Fin 16 :=
  placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
    (Registers.logicalSlot register)

abbrev Represents :=
  RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)

structure Layout where
  registers : LoopRegisters
  start : Nat
  top : Nat
  stop : Nat

def Layout.endAt (layout : Layout) : Nat := layout.start + 22
def Layout.stopDelta (layout : Layout) : BitVec 32 :=
  .ofInt 32 ((layout.stop : Int) - (layout.start + 9))
def Layout.topDelta (layout : Layout) : BitVec 32 :=
  .ofInt 32 ((layout.top : Int) - (layout.start + 22))

def Layout.target (layout : Layout) (index bound : Word) (enabled : Bool) : Nat :=
  if enabled then
    if index.toNat + 1 < bound.toNat then layout.top else layout.endAt
  else layout.stop

def Layout.Checked (layout : Layout) (image : NativeImage.View) : Prop :=
  layout.endAt ≤ image.size ∧ layout.stop ≤ image.size ∧ layout.top ≤ image.size ∧
  (layout.registers.index ≠ layout.registers.bound ∧ layout.registers.condition ≠ layout.registers.index ∧
    layout.registers.condition ≠ layout.registers.bound) ∧
  (layout.stop : Int) = layout.start + 9 + layout.stopDelta.toInt ∧
  (layout.top : Int) = layout.start + 22 + layout.topDelta.toInt ∧
  Code image layout.start (X86BranchGate.code (physical layout.registers.condition) layout.stopDelta) ∧
  Code image (layout.start + 9) (X86RegisterIncrement.code (physical layout.registers.index)) ∧
  Code image (layout.start + 13)
    (registerCode 0x39 (physical layout.registers.bound) (physical layout.registers.index)) ∧
  Code image (layout.start + 16) (X86NativeJcc.code (.ordinary .below) layout.topDelta)

instance (layout : Layout) (image : NativeImage.View) : Decidable (layout.Checked image) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev writes (layout : Layout) : Finset Register := X86RegisterIncrement.writes (physical layout.registers.index)

private theorem outside_flags : ∀ register : P1Source.Reg,
    key (physical register) ∉ ({.rflags, .rip} : Finset Register) := by decide

private theorem outside_index : ∀ register index : P1Source.Reg, register ≠ index →
    key (physical register) ∉ X86RegisterIncrement.writes (physical index) := by decide

private theorem test (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {layout : Layout} (point : At image state base layout.start) (checked : layout.Checked image)
    (enabled : Bool) (known : lookup state (physical layout.registers.condition) = some (booleanWord enabled)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      RegisterFrame X86BranchGate.writes state after ∧
      Nonempty (At image after base (if enabled then layout.start + 9 else layout.stop)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨extent, stopInside, _, _, relative, _, code, _⟩ := checked
  have inside : layout.start + 9 ≤ image.size := by
    unfold Layout.endAt at extent
    omega
  let input : X86BranchGate.Inputs state (physical layout.registers.condition) :=
    { toBasis := point.basis (by omega)
      value := booleanWord enabled
      flags := point.flags
      valueKnown := known
      flagsKnown := point.knownFlags
      quiet := point.quiet
      upper := by
        change (address base.toInt layout.start).toInt + 9 < (2^47 : Int)
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      displacement := layout.stopDelta
      target := address base.toInt layout.stop
      jump := by
        change (address base.toInt layout.stop).toInt =
          (address base.toInt layout.start).toInt + 9 + layout.stopDelta.toInt
        rw [point.location _ stopInside, point.location _ (by omega)]
        omega
      loaded := point.bytes _ (by omega) _ code }
  obtain ⟨after, flags, ran, frame, _, flagRead, rip⟩ :=
    X86BranchGate.executes (handlers other extra) extra vector state (physical layout.registers.condition) input
  have installed : X86BranchGate.handlers (handlers other extra) extra = handlers other extra := rfl
  rw [installed] at ran
  change after.regs.get? .rip = some ((if booleanWord enabled = (0#64) then address base.toInt layout.stop
    else address (address base.toInt layout.start).toInt 9).signExtend 64) at rip
  rw [point.relative_address layout.start 9 (by omega)] at rip
  have location : after.regs.get? .rip =
      some ((address base.toInt (if enabled then layout.start + 9 else layout.stop)).signExtend 64) := by
    cases enabled with
    | false => exact rip
    | true =>
      change after.regs.get? .rip = some ((if (1#64) = (0#64) then address base.toInt layout.stop
        else address base.toInt (layout.start + 9)).signExtend 64) at rip
      rwa [if_neg (by decide : (1#64) ≠ (0#64))] at rip
  exact ⟨after, ran, frame, ⟨point.advance frame X86BranchGate.writes_data location flags flagRead⟩⟩

private theorem advance_index (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {layout : Layout} (point : At image state base (layout.start + 9)) (checked : layout.Checked image)
    (index : Word) (known : lookup state (physical layout.registers.index) = some index) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes layout) state after ∧ lookup after (physical layout.registers.index) = some (index + 1) ∧
      Nonempty (At image after base (layout.start + 13)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent : layout.start + 13 ≤ image.size := by
    have := checked.1
    unfold Layout.endAt at this
    omega
  let input : X86RegisterIncrement.Inputs state (physical layout.registers.index) :=
    { toBasis := point.basis (by omega)
      value := index
      flags := point.flags
      valueKnown := known
      flagsKnown := point.knownFlags
      quiet := point.quiet
      upper := by
        change (address base.toInt (layout.start + 9)).toInt + 4 < (2^47 : Int)
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      loaded := point.bytes _ (by omega) _ checked.2.2.2.2.2.2.2.1 }
  obtain ⟨after, flags, ran, frame, updated, flagRead, rip⟩ :=
    X86RegisterIncrement.executes (handlers other extra) vector state _ input
  have installed : X86FrameIncrement.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [installed] at ran
  change after.regs.get? .rip = some ((address (address base.toInt (layout.start + 9)).toInt 4).signExtend 64) at rip
  rw [point.relative_address (layout.start + 9) 4 (by omega)] at rip
  exact ⟨after, ran, frame, updated, ⟨point.advance frame (X86RegisterIncrement.writes_data _) rip flags flagRead⟩⟩

private theorem backedge (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {layout : Layout} (point : At image state base (layout.start + 13)) (checked : layout.Checked image)
    (index bound : Word) (indexRead : lookup state (physical layout.registers.index) = some index)
    (boundRead : lookup state (physical layout.registers.bound) = some bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      RegisterFrame {.rflags, .rip} state after ∧
      Nonempty (At image after base (if index.toNat < bound.toNat then layout.top else layout.endAt)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨extent, _, topInside, _, _, relative, _, _, code, branch⟩ := checked
  have inside : layout.start + 16 ≤ image.size := by
    unfold Layout.endAt at extent
    omega
  let cmp := X86PlacedScalar.window point inside 0x39 _ _ code
  obtain ⟨output, compared, _, _, arithmetic⟩ := X86Comparison.fetched_compare64_defined
    (handlers other extra) vector state _ _ cmp index bound point.flags
      boundRead indexRead point.knownFlags point.quiet
  have arithmeticInstalled : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [arithmeticInstalled] at compared
  let flags := X86Flags.mergeFlags point.flags output
  let middle := X86Move.putPointer (X86Flags.putFlags state flags) (address base.toInt (layout.start + 16))
  have frame : RegisterFrame {.rflags, .rip} state middle := (flags_frame _ _).trans (pointer_frame _ _)
  have known : middle.regs.get? .rflags = some flags := by
    rw [(pointer_frame _ _).registers .rflags (by decide)]
    simp [X86Flags.putFlags]
  let atBranch : At image middle base (layout.start + 16) :=
    point.advance frame (by decide) (X86FuelPrefix.pointer_rip _ _) flags known
  have selects : X86NativeJcc.selects (.ordinary .below) flags = decide (index.toNat < bound.toNat) := by
    simpa only [X86PreparedCompare.positive, Comparison.evaluate, BitVec.lt_def] using
      (X86PreparedCompare.condition_values (X86PreparedCompare.subtraction_flags _ _ _ _ _ arithmetic) .lessUnsigned).1
  obtain ⟨after, jumped, last, reached⟩ := X86PlacedJcc.executes other extra vector
    atBranch (target := layout.top) (by exact extent) topInside (.ordinary .below) layout.topDelta (by omega) branch
  have footprint := (frame.trans last).mono (by decide : ({.rflags, .rip} : Finset Register) ∪ {.rip} ⊆ {.rflags, .rip})
  have ran := @X86FuelPrefix.fetches_then (handlers other extra) vector 1 1 state middle after
    (X86FuelPrefix.fetches_one _ _ compared) jumped
  change Nonempty (At image after base (if X86NativeJcc.selects (.ordinary .below) flags then layout.top
    else layout.start + 22)) at reached
  exact ⟨after, ran, footprint, by simpa only [selects, decide_eq_true_eq, Layout.endAt] using reached⟩

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {layout : Layout} (point : At image state base layout.start) (checked : layout.Checked image)
    (index bound : Word) (enabled : Bool)
    (indexRead : lookup state (physical layout.registers.index) = some index)
    (boundRead : lookup state (physical layout.registers.bound) = some bound)
    (guardRead : lookup state (physical layout.registers.condition) = some (booleanWord enabled))
    (inside : index.toNat < bound.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if enabled then 5 else 2)).run state = .ok () after ∧
      RegisterFrame (writes layout) state after ∧
      lookup after (physical layout.registers.index) = some (if enabled then index + 1 else index) ∧
      Nonempty (At image after base (layout.target index bound enabled)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨guarded, tested, frame, ⟨next⟩⟩ := test other extra vector point checked enabled guardRead
  have coversFlags : X86BranchGate.writes ⊆ writes layout := by simp [X86BranchGate.writes, X86RegisterIncrement.writes]
  have keepsIndex := (frame.lookup _ (outside_flags layout.registers.index)).trans indexRead
  cases enabled with
  | false => exact ⟨guarded, tested, frame.mono coversFlags, keepsIndex, ⟨next⟩⟩
  | true =>
    obtain ⟨incremented, incrementRun, incFrame, advanced, ⟨cmp⟩⟩ :=
      advance_index other extra vector next checked index keepsIndex
    have keepsBound := (incFrame.lookup _ (outside_index _ _ (Ne.symm checked.2.2.2.1.1))).trans
      ((frame.lookup _ (outside_flags layout.registers.bound)).trans boundRead)
    obtain ⟨after, continued, readOnly, reached⟩ :=
      backedge other extra vector cmp checked (index + 1) bound advanced keepsBound
    have ran := @X86FuelPrefix.fetches_then (handlers other extra) vector 2 3 state guarded after tested
      (@X86FuelPrefix.fetches_then (handlers other extra) vector 1 2 guarded incremented after incrementRun continued)
    have footprint := (frame.trans (incFrame.trans readOnly)).mono
      (Finset.union_subset coversFlags (Finset.union_subset (Finset.Subset.refl _) coversFlags))
    have indexNow := (readOnly.lookup _ (outside_flags layout.registers.index)).trans advanced
    refine ⟨after, ran, footprint, indexNow, ?_⟩
    simpa only [P1EarlyLoopContinuation.index_successor index bound inside, Layout.target, if_true] using reached

theorem refines (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {layout : Layout} (point : At image state base layout.start) (checked : layout.Checked image)
    (model : P1WordExecution.State) (live : Finset P1Source.Reg)
    (indexed : layout.registers.index ∈ live) (bounded : layout.registers.bound ∈ live)
    (guarded : layout.registers.condition ∈ live) (readback : Represents live model.registers state)
    (enabled : Bool) (condition : model.registers layout.registers.condition = booleanWord enabled)
    (inside : (model.registers layout.registers.index).toNat < (model.registers layout.registers.bound).toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if enabled then 5 else 2)).run state = .ok () after ∧
      RegisterFrame (writes layout) state after ∧
      Nonempty (At image after base
        (layout.target (model.registers layout.registers.index) (model.registers layout.registers.bound) enabled)) ∧
      Represents live (P1EarlyLoopContinuation.increments layout.registers model enabled).registers after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, ran, frame, index, reached⟩ :=
    executes other extra vector point checked _ _ enabled
      (readback _ indexed) (readback _ bounded) ((readback _ guarded).trans (congrArg some condition)) inside
  refine ⟨after, ran, frame, reached, ?_⟩
  intro register member
  by_cases same : register = layout.registers.index
  · subst register
    cases enabled <;> simpa [P1EarlyLoopContinuation.increments, P1WordExecution.State.write] using index
  · have kept := frame.lookup _ (outside_index register layout.registers.index same)
    cases enabled <;> simpa [P1EarlyLoopContinuation.increments, P1WordExecution.State.write, same] using
      kept.trans (readback register member)

end Mettapedia.Machines.TIsa.X86PlacedEarlyLatch
