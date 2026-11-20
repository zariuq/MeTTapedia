import Mettapedia.Machines.TIsa.X86PlacedScalar
import Mettapedia.Machines.TIsa.X86BoundedLoad
import Mettapedia.Machines.TIsa.P1WordExecution

/-! # Qword loads at a placed program point

The capability's mathematical range and the fetched bounds checks agree
on admission. A successful load observes the related word. A range
refusal reaches the image's checked failure edge without reading data.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedQwordLoad

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86BoundedLoad (Instruction Inputs Fits Readable layout displacement bytes count)
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
          have length := X86BoundedLoad.bytes_length code
          omega
        rejectWithin := by
          change code.reject ≤ image.size - offset
          have := checked.2.1
          omega
        overflowDelta := checked.2.2.1
        shortDelta := checked.2.2.2.1
        rangeDelta := checked.2.2.2.2.1 }
    tailWithin := by
      change X86Bounds.exitAt (layout code) + 10 ≤ image.size - offset
      have extent := checked.1
      have length := X86BoundedLoad.bytes_length code
      omega
    loaded := point.bytes _ (by have := checked.1; omega) _ checked.2.2.2.2.2 }

def source (code : Instruction) : P1Source.Instr :=
  .load .u64 .word64 code.region code.destination code.base (displacement code)

structure CapabilityView {code : Instruction} {native : State}
    (facts : X86Bounds.Facts (layout code) native) (model : P1WordExecution.State) : Prop where
  pointer : facts.pointer = model.registers code.base
  base : facts.base = (model.regions code.region).base
  length : facts.length = (model.regions code.region).length
  active : (model.regions code.region).mode ≠ .absent
  range : facts.base.toNat + facts.length.toNat < 2^64
  lower : facts.base.toNat ≤ facts.pointer.toNat
  upper : facts.pointer.toNat ≤ facts.base.toNat + facts.length.toNat

theorem access {code : Instruction} {native : State}
    (facts : X86Bounds.Facts (layout code) native) (model : P1WordExecution.State)
    (view : CapabilityView facts model) :
    let location := facts.pointer.toNat + code.offset.val
    P1WordExecution.wordAddress (model.regions code.region) (model.registers code.base) (displacement code) =
      if (facts.pointer - facts.base).toNat + code.offset.val + 8 ≤ facts.length.toNat ∧ location % 8 = 0
      then some location else none := by
  dsimp only
  have sourceBounds := X86BoundsArithmetic.source_guard facts.base facts.length facts.pointer
    code.offset (8 : Fin 128) view.range view.lower view.upper
  unfold P1WordExecution.wordAddress
  rw [← view.pointer, ← view.base, ← view.length]
  by_cases fits : (facts.pointer - facts.base).toNat + code.offset.val + 8 ≤ facts.length.toNat
  · rw [show Memory.access? facts.base facts.length facts.pointer (displacement code).toInt 8 =
      some (facts.pointer.toNat + code.offset.val) from sourceBounds.mp fits]
    simp only [fits, true_and]
    rfl
  · have absent : Memory.access? facts.base facts.length facts.pointer (displacement code).toInt 8 = none := by
      cases fetched : Memory.access? facts.base facts.length facts.pointer (displacement code).toInt 8 with
      | none => rfl
      | some location =>
        have observed := (P1Memory.access?_iff_inside facts.base facts.length facts.pointer
          (displacement code) 8 location view.range view.lower view.upper).mp fetched
        have exactLocation := observed.2.2
        have natural := X86BoundsArithmetic.offset_toInt code.offset
        change (displacement code).toInt = _ at natural
        rw [natural] at exactLocation
        have same : location = facts.pointer.toNat + code.offset.val := by omega
        exact (fits (sourceBounds.mpr (same ▸ fetched))).elim
    rw [absent]
    simp only [fits, false_and, if_false]
    rfl

theorem source_reads {code : Instruction} {native : State}
    (facts : X86Bounds.Facts (layout code) native) (model : P1WordExecution.State)
    (view : CapabilityView facts model)
    (inside : (facts.pointer - facts.base).toNat + code.offset.val + 8 ≤ facts.length.toNat)
    (aligned : (facts.pointer.toNat + code.offset.val) % 8 = 0)
    (value : Word) (present : model.memory (facts.pointer.toNat + code.offset.val) = some value) :
    P1WordExecution.execute model (.instruction (source code)) = .continuing (model.write code.destination value) := by
  have location := (access facts model view).trans (if_pos ⟨inside, aligned⟩)
  simp only [source, P1WordExecution.execute.eq_2, P1WordExecution.instruction, if_neg view.active,
    location, Option.bind_some, present]
  rfl

theorem source_refuses {code : Instruction} {native : State}
    (facts : X86Bounds.Facts (layout code) native) (model : P1WordExecution.State)
    (view : CapabilityView facts model)
    (outside : ¬ (facts.pointer - facts.base).toNat + code.offset.val + 8 ≤ facts.length.toNat) :
    P1WordExecution.execute model (.instruction (source code)) = P1WordExecution.fail .invalidInput model := by
  have location := (access facts model view).trans (if_neg (fun yes => outside yes.1))
  simp only [source, P1WordExecution.execute.eq_2, P1WordExecution.instruction, if_neg view.active,
    location, Option.bind_none]

theorem reads (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {native : State}
    {base : BitVec 48} {offset : Nat} {code : Instruction}
    (point : At image native base offset) (checked : Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) (wide : code.wide = true)
    (inside : Fits (input point checked facts)) (data : Readable (input point checked facts)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (count code)).run native = .ok () after ∧
      RegisterFrame (X86BoundedLoad.writes code) native after ∧
      lookup after (X86BoundedLoad.physical code.destination) = some data.word ∧
      Nonempty (At image after base (offset + (bytes code).length)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, flags, ran, framed, loaded, rip, flagRead, _, _, _⟩ :=
    X86BoundedLoad.succeeds (X86PlacedScalar.baseHandlers other) extra vector code native
      _ (input point checked facts) inside data
  have linked : X86BoundedLoad.handlers (X86PlacedScalar.baseHandlers other) extra =
      handlers other extra := rfl
  rw [linked] at ran
  change after.regs.get? .rip = some
    ((address (address base.toInt offset).toInt (bytes code).length).signExtend 64) at rip
  rw [point.relative_address offset _ (by have := checked.1; omega)] at rip
  exact ⟨after, ran, framed, by simpa [wide, X86DataLoad.value] using loaded,
    ⟨point.advance framed (X86BoundedLoad.writes_data code) rip flags flagRead⟩⟩

theorem refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {native : State}
    {base : BitVec 48} {offset : Nat} {code : Instruction}
    (point : At image native base offset) (checked : Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) (outside : ¬ Fits (input point checked facts)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86Bounds.boundsSteps (layout code) facts.base facts.pointer facts.length)).run native =
      .ok () after ∧ RegisterFrame X86Bounds.writes native after ∧
      Nonempty (At image after base (offset + code.reject)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, ran, frame, rip, controls, _⟩ :=
    X86BoundedLoad.rejects (X86PlacedScalar.baseHandlers other) extra vector code native
      _ (input point checked facts) outside
  have linked : X86BoundedLoad.handlers (X86PlacedScalar.baseHandlers other) extra =
      handlers other extra := rfl
  rw [linked] at ran
  change after.regs.get? .rip = some
    ((address (address base.toInt offset).toInt code.reject).signExtend 64) at rip
  rw [point.relative_address offset _ (by have := checked.1; omega)] at rip
  obtain ⟨flags, nextFlags⟩ := X86ControlFlags.flags_present controls point.flags point.knownFlags
  exact ⟨after, ran, frame, ⟨point.advance frame X86Bounds.writes_data rip flags nextFlags⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedQwordLoad
