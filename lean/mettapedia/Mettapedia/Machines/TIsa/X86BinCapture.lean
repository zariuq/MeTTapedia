import Mettapedia.Machines.TIsa.JsonImport
import Mettapedia.Machines.TIsa.X86Arithmetic
import Mettapedia.Tools.KernelReflexivity

/-!
# Captured U64 ADD/SUB output from the actual C emitter

The probe calls emit_instr for both operations and every logical
destination/source/source tuple. The complete pre-patching instruction
buffer is retained, including its fuel prefix and recorded spans. Kernel
checks establish the register map, all 3456 input tuples, span partition,
scratch mask and exact nine-byte BIN data body.

The middle instruction's loaded bytes instantiate the original Sail
fetch/dispatch/arithmetic theorem. Mutating its opcode invalidates the
check. X86BinBlock composes the surrounding copies and arithmetic. Fuel-prefix
execution, buffer-state correctness of the C compiler and full ABI/program
refinement remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace Mettapedia.Machines.TIsa.X86BinCapture

open X86RegisterRefinement X86RegisterEncoding X86Arithmetic

noncomputable def captured : List Nat × List NativeImage.TemplateSample :=
  tisa_template_capture% "Mettapedia/Machines/TIsa/Models/NativeX86/BinHelper.json"


def physical (register : Fin 12) : Fin 16 :=
  placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
    (Registers.logicalSlot register)

def scratch : Fin 16 :=
  placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
    (Registers.scratchSlot 0)

def decodeOperation (operation : Nat) : DefinedOperation := if operation = 0 then .add else .sub

def expected (operation : DefinedOperation) (destination left right : Fin 12) : List Nat :=
  [(rex true (physical left) scratch).toNat, 137, (modRM (physical left) scratch).toNat,
    (rex true (physical right) scratch).toNat, (opcode operation).toNat,
    (modRM (physical right) scratch).toNat,
    (rex true scratch (physical destination)).toNat, 137,
    (modRM scratch (physical destination)).toNat]

def sampleCheck (sample : NativeImage.TemplateSample) : Bool :=
  match sample.inputs with
  | [operation, destination, left, right] =>
    if valid : operation < 2 ∧ destination < 12 ∧ left < 12 ∧ right < 12 then
      sample.bytes.all (fun byte => decide (byte < 256)) &&
        (NativeImage.spanEnd? 0 sample.spans == some sample.bytes.length) &&
        (sample.spans.map NativeImage.Span.kind == ["FUEL_STEP", "BIN"]) &&
        (sample.scratchMask == 3) &&
        (sample.body "BIN" == some (expected (decodeOperation operation)
          ⟨destination, valid.2.1⟩ ⟨left, valid.2.2.1⟩ ⟨right, valid.2.2.2⟩))
    else false
  | _ => false

def inventory : List (List Nat) :=
  (List.range 2).flatMap fun operation =>
    (List.range 12).flatMap fun destination =>
      (List.range 12).flatMap fun left =>
        (List.range 12).map fun right => [operation, destination, left, right]

theorem register_map_exact : captured.1 = (Registers.canonical .x86_64).registers := by
  kernel_reflexivity

theorem row_count : captured.2.length = 3456 := by kernel_reflexivity


theorem row_inventory : captured.2.map NativeImage.TemplateSample.inputs = inventory := by
  kernel_reflexivity


theorem every_sample_checked : captured.2.all sampleCheck = true := by kernel_reflexivity


theorem sample_present (operation : Fin 2) (destination left right : Fin 12) :
    ∃ sample ∈ captured.2, sample.inputs = [operation.val, destination.val, left.val, right.val] := by
  apply List.mem_map.mp
  rw [row_inventory]
  simp only [inventory, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨operation.val, operation.isLt, destination.val, destination.isLt,
    left.val, left.isLt, right.val, right.isLt, rfl⟩

theorem checked_body (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val]) :
    sample.body "BIN" = some (expected (decodeOperation operation.val) destination left right) := by
  have checked := List.all_eq_true.mp every_sample_checked sample member
  rw [sampleCheck, inputs] at checked
  have valid : operation.val < 2 ∧ destination.val < 12 ∧ left.val < 12 ∧ right.val < 12 :=
    ⟨operation.isLt, destination.isLt, left.isLt, right.isLt⟩
  simp only [dif_pos valid,
    Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.2

theorem every_output_exact (operation : Fin 2) (destination left right : Fin 12) :
    ∃ sample ∈ captured.2,
      sample.inputs = [operation.val, destination.val, left.val, right.val] ∧
      sample.body "BIN" = some (expected (decodeOperation operation.val) destination left right) := by
  obtain ⟨sample, member, inputs⟩ := sample_present operation destination left right
  exact ⟨sample, member, inputs, checked_body operation destination left right sample member inputs⟩

theorem captured_middle_fields (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (address opcodeAddress modrmAddress : BitVec 48)
    (present : X86LegacyFetch.loaded state address opcodeAddress modrmAddress ((body.drop 3).take 3)) :
    state.mem.get? (address.signExtend 52).toNat = some (rex true (physical right) scratch) ∧
      state.mem.get? (opcodeAddress.signExtend 52).toNat = some (opcode (decodeOperation operation.val)) ∧
      state.mem.get? (modrmAddress.signExtend 52).toNat = some (modRM (physical right) scratch) := by
  have same := Option.some.inj (output.symm.trans (checked_body operation destination left right sample member inputs))
  subst body
  simpa only [expected, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
    X86LegacyFetch.loaded, BitVec.ofNat_toNat, BitVec.setWidth_eq] using present

def windowOfCapturedMiddle (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (basis : X86LegacyFetch.Basis state)
    (present : X86LegacyFetch.loaded state basis.address basis.opcodeAddress basis.modrmAddress
      ((body.drop 3).take 3)) :
    X86LegacyFetch.Window state (opcode (decodeOperation operation.val)) true (physical right) scratch :=
  let fields := captured_middle_fields operation destination left right sample member inputs body output state
    basis.address basis.opcodeAddress basis.modrmAddress present
  { toBasis := basis
    prefixByte := fields.1
    opcodeByte := fields.2.1
    modrmByte := fields.2.2 }

local instance : X86Registers.MemoryPrimitives := X86Memory.ordinary

theorem captured_middle_executes (other : X86Registers.OtherOpcodeHandlers)
    (vector : X86Registers.VectorOpcodeHandlers)
    (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (basis : X86LegacyFetch.Basis state)
    (present : X86LegacyFetch.loaded state basis.address basis.opcodeAddress basis.modrmAddress
      ((body.drop 3).take 3))
    (leftValue rightValue : Word) (flags : BitVec 32)
    (leftKnown : lookup state scratch = some leftValue)
    (rightKnown : lookup state (physical right) = some rightValue)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : X86Registers.OtherOpcodeHandlers := linkedHandlers other
    letI : X86Registers.VectorOpcodeHandlers := vector
    ∃ resultFlags, (X86Registers.Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (put state scratch (result (decodeOperation operation.val) leftValue rightValue))
          (X86Flags.mergeFlags flags resultFlags)) basis.next) :=
  fetched_register64 other vector (decodeOperation operation.val) state (physical right) scratch
    (windowOfCapturedMiddle operation destination left right sample member inputs body output state basis present)
    leftValue rightValue flags rightKnown leftKnown flagsKnown quiet

noncomputable def firstSample : NativeImage.TemplateSample :=
  captured.2[0]'(by rw [row_count]; decide)

def mutateOpcode (sample : NativeImage.TemplateSample) : NativeImage.TemplateSample :=
  match sample.spans.find? (fun span => span.kind == "BIN") with
  | none => sample
  | some span => { sample with bytes := sample.bytes.set (span.offset + 4) 0x29 }

theorem first_sample_checked : sampleCheck firstSample = true := by kernel_reflexivity
theorem altered_opcode_refused : sampleCheck (mutateOpcode firstSample) = false := by kernel_reflexivity

end Mettapedia.Machines.TIsa.X86BinCapture

#print axioms Mettapedia.Machines.TIsa.X86BinCapture.every_output_exact
#print axioms Mettapedia.Machines.TIsa.X86BinCapture.altered_opcode_refused
#print axioms Mettapedia.Machines.TIsa.X86BinCapture.captured_middle_executes
