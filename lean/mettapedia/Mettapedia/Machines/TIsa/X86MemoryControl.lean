import Mettapedia.Machines.TIsa.ContinuationProjection
import Mettapedia.Machines.TIsa.X86BoundedLoadSource
import Mettapedia.Machines.TIsa.X86BoundedStoreSource
import Mettapedia.Machines.TIsa.X86MemoryFailure

/-!
# Control and data refinement of emitted bounded memory instructions

The source control cell advances by the length of the selected template.
The native execution uses that template's bytes at its placed address.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryControl

open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView
open Cells Control CellEffects

local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Location := Control.Location Key
abbrev ControlledWorld := Multiset (Cell Location)

structure Entry (view : View) (values : Key → Word) (native : State)
    (region : Fin 9) (baseRegister : Fin 12) (layout : X86Bounds.Layout) where
  origin : X86LegacyFetch.Basis native
  base : Int
  offset : Nat
  placed : origin.address.toInt = base + offset
  profile : X86Readiness.Profile
  flags : BitVec 32
  known : ∀ key ∈ view.keys, readback view.modes native key = some (values key)
  frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size
  frameAligned : (values (.register 0)).toNat % 8 = 0
  holds : profile.Holds native
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  geometry : X86Bounds.Context layout origin.address
  tailWithin : X86Bounds.exitAt layout + 10 ≤ geometry.extent
  rangeFits : (values (.capabilityBase region.val)).toNat +
    (values (.capabilityLength region.val)).toNat < 2 ^ 64
  pointerLower : (values (.capabilityBase region.val)).toNat ≤ (values (.register baseRegister)).toNat
  pointerUpper : (values (.register baseRegister)).toNat ≤
    (values (.capabilityBase region.val)).toNat + (values (.capabilityLength region.val)).toNat

private theorem next_address {base origin : Int} {offset size : Nat}
    (placed : origin = base + (offset : Int)) :
    X86Execution.address origin size = X86Execution.address base (offset + size) := by
  rw [placed]
  simp only [X86Execution.address, Int.natCast_add, Int.add_assoc]

def loadEdge (activation offset : Nat) (instruction : X86BoundedLoad.Instruction)
    (dataAddress : Nat) : Edge Key :=
  ⟨activation, BitVec.ofNat 64 offset,
    BitVec.ofNat 64 (offset + (X86BoundedLoad.bytes instruction).length),
    X86BoundedLoadSource.recipe instruction dataAddress⟩

def storeEdge (activation offset : Nat) (instruction : X86BoundedStore.Instruction)
    (dataAddress : Nat) : Edge Key :=
  ⟨activation, BitVec.ofNat 64 offset,
    BitVec.ofNat 64 (offset + (X86BoundedStore.bytes instruction).length),
    X86BoundedStoreSource.recipe instruction dataAddress⟩

theorem load_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (activation : Nat) (sourceOp : P1Source.Instr)
    (instruction : X86BoundedLoad.Instruction)
    (lowered : X86BoundedLoadSource.lower? sourceOp instruction.reject = some instruction)
    (view : View) (before : Location → Word) (native : State)
    (entry : Entry view (dataValues before) native instruction.region instruction.base
      (X86BoundedLoad.layout instruction))
    (loaded : codeLoaded native entry.origin.address.toInt (X86BoundedLoad.bytes instruction))
    (dataAddress : Nat) (following : ControlledWorld)
    (safe : entry.profile.enabled = false ∨ X86CanonicalSpan.narrow (BitVec.ofNat 64 dataAddress) &&&
      BitVec.ofNat 48 (X86DataLoad.byteCount instruction.wide - 1) = (0#48))
    (source : (profile [(loadEdge activation entry.offset instruction dataAddress).recipe]).theory.rewrites
      (encode (scopedKeys activation view.keys) before) following) :
    letI : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BoundedLoadSource.p1 instruction = sourceOp ∧
    before (.inl activation) = BitVec.ofNat 64 entry.offset ∧
    ∃ afterValues : Location → Word,
      following = encode (scopedKeys activation view.keys) afterValues ∧
      afterValues (.inl activation) =
        BitVec.ofNat 64 (entry.offset + (X86BoundedLoad.bytes instruction).length) ∧
      ∃ after nextFlags, (X86FuelPrefix.fetches (X86BoundedLoad.count instruction)).run native = .ok () after ∧
        RegisterFrame (X86BoundedLoad.writes instruction) native after ∧
        represents view (encode view.keys (dataValues afterValues)) after ∧
        after.regs.get? .rip = some ((X86Execution.address entry.base
          (entry.offset + (X86BoundedLoad.bytes instruction).length)).signExtend 64) ∧
        after.regs.get? .rflags = some nextFlags ∧
        after.regs.get? .log_register_writes = some false ∧
        X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
        ∀ count ≤ X86BoundedLoad.count instruction, ∀ observed,
          (X86FuelPrefix.fetches count).run native = .ok () observed →
            RegisterFrame (X86BoundedLoad.writes instruction) native observed := by
  let : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨afterValues, point, next, endpoint, dataStep⟩ :=
    (loadEdge activation entry.offset instruction dataAddress).project_firing view.keys before following source
  obtain ⟨after, flags, run, frame, observed, rip, flagsRead, quiet, control, holds, prefixes⟩ :=
    X86BoundedLoadSource.from_source other extra vector instruction view (dataValues before) native
      entry.origin entry.profile entry.flags entry.known entry.frameArea entry.frameAligned entry.holds
      entry.flagsKnown entry.quiet entry.geometry entry.tailWithin loaded entry.rangeFits entry.pointerLower
      entry.pointerUpper dataAddress (encode view.keys (dataValues afterValues)) safe dataStep
  rw [next_address entry.placed] at rip
  exact ⟨X86BoundedLoadSource.lower?_source lowered, point, afterValues, endpoint, next,
    after, flags, run, frame, observed, rip, flagsRead, quiet, control, holds, prefixes⟩

theorem store_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (activation : Nat) (sourceOp : P1Source.Instr)
    (instruction : X86BoundedStore.Instruction)
    (lowered : X86BoundedStoreSource.lower? sourceOp instruction.reject = some instruction)
    (view : View) (before : Location → Word) (native : State)
    (entry : Entry view (dataValues before) native instruction.region instruction.base
      (X86BoundedStore.layout instruction))
    (loaded : codeLoaded native entry.origin.address.toInt (X86BoundedStore.bytes instruction))
    (dataAddress : Nat) (following : ControlledWorld)
    (safe : entry.profile.enabled = false ∨ X86MemoryStore.target dataAddress &&&
      BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48))
    (source : (profile [(storeEdge activation entry.offset instruction dataAddress).recipe]).theory.rewrites
      (encode (scopedKeys activation view.keys) before) following)
    (descriptors : X86MemoryStore.DescriptorsApart view native
      (X86DataStore.writes instruction.wide (X86MemoryStore.target dataAddress))) :
    letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BoundedStoreSource.p1 instruction = sourceOp ∧
    before (.inl activation) = BitVec.ofNat 64 entry.offset ∧
    ∃ afterValues : Location → Word,
      following = encode (scopedKeys activation view.keys) afterValues ∧
      afterValues (.inl activation) =
        BitVec.ofNat 64 (entry.offset + (X86BoundedStore.bytes instruction).length) ∧
      ∃ after nextFlags, (X86FuelPrefix.fetches (X86BoundedStore.count instruction)).run native = .ok () after ∧
        X86StateFrame.Frame X86Bounds.writes
          (X86DataStore.writes instruction.wide (X86MemoryStore.target dataAddress)) native after ∧
        represents view (encode view.keys (dataValues afterValues)) after ∧
        (∀ index < X86DataStore.byteCount instruction.wide,
          after.mem.get? (X86WriteWords.physicalAddress (X86MemoryStore.target dataAddress) index) =
            some ((dataValues before (.register instruction.source)).extractLsb' (8 * index) 8)) ∧
        after.regs.get? .rip = some ((X86Execution.address entry.base
          (entry.offset + (X86BoundedStore.bytes instruction).length)).signExtend 64) ∧
        after.regs.get? .rflags = some nextFlags ∧
        after.regs.get? .log_register_writes = some false ∧
        X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
        ∀ count ≤ X86BoundedStore.count instruction, ∀ observed,
          (X86FuelPrefix.fetches count).run native = .ok () observed →
            X86StateFrame.Frame X86Bounds.writes
              (X86DataStore.writes instruction.wide (X86MemoryStore.target dataAddress)) native observed := by
  let : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨afterValues, point, next, endpoint, dataStep⟩ :=
    (storeEdge activation entry.offset instruction dataAddress).project_firing view.keys before following source
  obtain ⟨after, flags, run, frame, observed, stored, rip, flagsRead, quiet, control, holds, prefixes⟩ :=
    X86BoundedStoreSource.from_source other extra vector instruction view (dataValues before) native
      entry.origin entry.profile entry.flags entry.known entry.frameArea entry.frameAligned entry.holds
      entry.flagsKnown entry.quiet entry.geometry entry.tailWithin loaded entry.rangeFits entry.pointerLower
      entry.pointerUpper dataAddress (encode view.keys (dataValues afterValues)) safe dataStep descriptors
  rw [next_address entry.placed] at rip
  exact ⟨X86BoundedStoreSource.lower?_source lowered, point, afterValues, endpoint, next,
    after, flags, run, frame, observed, stored, rip, flagsRead, quiet, control, holds, prefixes⟩

def failureEdge (activation offset : Nat) (write : Bool) (width : P1Source.Width)
    (layout : X86Bounds.Layout) (pointer : Fin 12) : Edge Key :=
  ⟨activation, BitVec.ofNat 64 offset, BitVec.ofNat 64 (offset + layout.reject),
    X86MemoryFailure.recipe write width layout pointer⟩

theorem failure_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (activation offset : Nat) (base : Int) (write : Bool)
    (width : P1Source.Width) (layout : X86Bounds.Layout) (pointer : Fin 12)
    (sized : width.bytes = layout.count.val) (keys : Finset Key) (modes : Fin 9 → Word)
    (before : Location → Word) (native : State)
    (entry : X86MemoryFailure.Entry layout pointer keys modes (dataValues before) native)
    (placed : entry.origin.address.toInt = base + offset) (following : ControlledWorld)
    (source : (profile [(failureEdge activation offset write width layout pointer).recipe]).theory.rewrites
      (encode (scopedKeys activation keys) before) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    before (.inl activation) = BitVec.ofNat 64 offset ∧
    ∃ afterValues : Location → Word,
      following = encode (scopedKeys activation keys) afterValues ∧
      afterValues (.inl activation) = BitVec.ofNat 64 (offset + layout.reject) ∧
      encode keys (dataValues afterValues) = encode keys (dataValues before) ∧
      ∃ after nextFlags,
        (X86FuelPrefix.fetches (X86MemoryFailure.count layout pointer (dataValues before))).run native = .ok () after ∧
        RegisterFrame X86Bounds.writes native after ∧
        (∀ key, readback modes after key = readback modes native key) ∧
        after.regs.get? .rip = some ((address base (offset + layout.reject)).signExtend 64) ∧
        after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
        X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
        ∀ count ≤ X86MemoryFailure.count layout pointer (dataValues before), ∀ observed,
          (X86FuelPrefix.fetches count).run native = .ok () observed → RegisterFrame X86Bounds.writes native observed := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨afterValues, point, next, endpoint, dataStep⟩ :=
    (failureEdge activation offset write width layout pointer).project_firing keys before following source
  obtain ⟨unchanged, after, nextFlags, run, frame, readbacks, rip, flagsRead, quiet, control, holds, prefixes⟩ :=
    X86MemoryFailure.source_executes other extra vector write width layout pointer sized keys modes
      (dataValues before) native entry (encode keys (dataValues afterValues)) dataStep
  rw [X86Bounds.position, next_address placed] at rip
  exact ⟨point, afterValues, endpoint, next, unchanged, after, nextFlags, run, frame, readbacks, rip,
    flagsRead, quiet, control, holds, prefixes⟩

namespace Controls

theorem word_operations_resume_at_72 :
    ((X86BoundedLoadSource.lower? (.load .u64 .word64 0 6 1 (8#32)) 512).map
      (fun instruction => (loadEdge 0 16 instruction 128).next) = some (72#64)) ∧
    ((X86BoundedStoreSource.lower? (.store .word64 0 1 (8#32) 6) 512).map
      (fun instruction => (storeEdge 0 16 instruction 128).next) = some (72#64)) := by
  decide

theorem wrong_load_offset_refused (i : X86BoundedLoad.Instruction)
    (keys : Finset Key) (before : Location → Word) (following : ControlledWorld)
    (point : before (.inl 0) = (16#64)) :
    ¬ (profile [(loadEdge 0 17 i 128).recipe]).theory.rewrites
      (encode (scopedKeys 0 keys) before) following := by
  intro fired
  obtain ⟨_, current, _, _, _⟩ := (loadEdge 0 17 i 128).project_firing keys before following fired
  change before (.inl 0) = (17#64) at current
  rw [point] at current
  exact (by decide : (16#64) ≠ (17#64)) current

end Controls

#print axioms load_executes
#print axioms store_executes
#print axioms failure_executes
#print axioms Controls.word_operations_resume_at_72
#print axioms Controls.wrong_load_offset_refused

end Mettapedia.Machines.TIsa.X86MemoryControl
