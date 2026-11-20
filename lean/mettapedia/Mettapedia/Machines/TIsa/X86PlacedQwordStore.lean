import Mettapedia.Machines.TIsa.X86PlacedMemory
import Mettapedia.Machines.TIsa.X86BoundedStore

/-! # Placed qword stores through an explicit bounds check -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedQwordStore

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (CodeApart Cell Reads footprint)
open X86BoundedStore (Instruction Inputs Fits layout bytes count)
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86PlacedScalar.handlers (X86Bounds.baseHandlers other) extra

def Checked (image : NativeImage.View) (offset : Nat) (code : Instruction) : Prop :=
  offset + (bytes code).length + 3 ≤ image.size ∧ offset + code.reject ≤ image.size ∧
  (X86Bounds.branchDelta (layout code) 23).toInt = (code.reject : Int) - 23 ∧
  (X86Bounds.branchDelta (layout code) (X86Bounds.compareAt (layout code))).toInt =
    (code.reject : Int) - X86Bounds.compareAt (layout code) ∧
  (X86Bounds.branchDelta (layout code) (X86Bounds.exitAt (layout code))).toInt =
    (code.reject : Int) - X86Bounds.exitAt (layout code) ∧
  Code image offset (bytes code)

instance (image : NativeImage.View) (offset : Nat) (code : Instruction) :
    Decidable (Checked image offset code) := inferInstanceAs (Decidable (_ ∧ _))

def input {image : NativeImage.View} {native : State} {base : BitVec 48} {offset : Nat}
    {code : Instruction} (point : At image native base offset) (checked : Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) :
    Inputs code native (point.basis (by have := checked.1; omega)) :=
  { toFacts := facts
    geometry :=
      { extent := image.size - offset
        upper := by
          change (address base.toInt offset).toInt + (image.size - offset : Nat) < (2^47 : Int)
          have extent := checked.1
          rw [point.location _ (by omega)]
          have := point.upper
          omega
        codeWithin := by
          have extent := checked.1
          have length := X86BoundedStore.bytes_length code
          omega
        rejectWithin := by
          change code.reject ≤ image.size - offset
          have extent := checked.2.1
          omega
        overflowDelta := checked.2.2.1
        shortDelta := checked.2.2.2.1
        rangeDelta := checked.2.2.2.2.1 }
    tailWithin := by
      change X86Bounds.exitAt (layout code) + 10 ≤ image.size - offset
      have extent := checked.1
      have length := X86BoundedStore.bytes_length code
      omega
    loaded := point.bytes _ (by have := checked.1; omega) _ checked.2.2.2.2.2 }

theorem writes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : State} {base : BitVec 48} {offset : Nat} {code : Instruction}
    (point : At image native base offset) (checked : Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) (wide : code.wide = true)
    (inside : Fits (input point checked facts)) (value : Word)
    (cell : Cell facts.pointer (X86BoundedStore.displacement code))
    (known : lookup native (X86BoundedStore.physical code.source) = some value)
    (apart : CodeApart image base (footprint cell.address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (count code)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (footprint cell.address) native after ∧
      Reads after cell.address value ∧ Nonempty (At image after base (offset + (bytes code).length)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let data : X86BoundedStore.Writable (input point checked facts) :=
    ⟨value, known, cell.address, by simpa [wide, X86DataStore.byteCount] using cell.upper,
      cell.effective, Or.inr (by simpa only [wide, X86DataStore.byteCount, if_true] using cell.aligned)⟩
  obtain ⟨after, flags, ran, frame, stored, rip, knownFlags, _, _, _⟩ :=
    X86BoundedStore.succeeds (X86PlacedScalar.baseHandlers other) extra vector code native _
      (input point checked facts) inside data
  have linked : X86BoundedStore.handlers (X86PlacedScalar.baseHandlers other) extra =
      handlers other extra := rfl
  rw [linked] at ran
  change after.regs.get? .rip =
    some ((address (address base.toInt offset).toInt (bytes code).length).signExtend 64) at rip
  rw [point.relative_address offset _ (by have := checked.1; omega)] at rip
  have frame : X86StateFrame.Frame X86Bounds.writes (footprint cell.address) native after := by
    simpa only [X86DataStore.writes, wide, X86DataStore.byteCount, if_true, data] using frame
  have stored : Reads after cell.address value := by
    intro index inside
    have payload (wide : Bool) (known : wide = true) :
        (X86DataStore.payload wide value).extractLsb' (8 * index) 8 = value.extractLsb' (8 * index) 8 := by
      subst wide
      rfl
    have byte := stored index (by rw [wide]; exact inside)
    change after.mem.get? (X86WriteWords.physicalAddress cell.address index) =
      some ((X86DataStore.payload code.wide value).extractLsb' (8 * index) 8) at byte
    rwa [payload code.wide wide] at byte
  exact ⟨after, ran, frame, stored, ⟨X86PlacedMemory.advance point frame X86Bounds.writes_data apart rip flags knownFlags⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedQwordStore
