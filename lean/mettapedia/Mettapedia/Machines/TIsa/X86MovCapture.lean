import Mettapedia.Machines.TIsa.JsonImport
import Mettapedia.Machines.TIsa.X86ResourceCopy
import Mettapedia.Tools.KernelReflexivity

/-!
# Captured bytes from the actual C MOV helper

The capture calls emit_mov_r64_r64 for all fourteen register/scratch slots.
Kernel checks establish the exact register map, complete pair inventory,
three-byte outputs and self-copy elision. The byte fields are those consumed
by the pinned Sail fetch theorem. A changed REX byte is refused.

The qualification command regenerates the capture from the current source.
These finite output checks do not assert C compilation correctness for
arbitrary buffer states or certify a complete emitted program.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace Mettapedia.Machines.TIsa.X86MovCapture

open X86RegisterRefinement X86RegisterEncoding

local instance : X86Registers.MemoryPrimitives := X86Memory.ordinary

noncomputable def captured : List Nat × List (Nat × Nat × List Nat) :=
  tisa_mov_capture% "Mettapedia/Machines/TIsa/Models/NativeX86/MovHelper.json"

def physical (slot : Fin 14) : Fin 16 :=
  placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) slot

def expected (destination source : Fin 14) : List Nat :=
  if destination = source then [] else
    [(rex true (physical source) (physical destination)).toNat,
      137, (modRM (physical source) (physical destination)).toNat]

noncomputable def lookup (destination source : Fin 14) : Option (List Nat) :=
  (captured.2.find? fun row => row.1 == destination.val && row.2.1 == source.val).map fun row => row.2.2

theorem register_map_exact : captured.1 = (Registers.canonical .x86_64).registers := by
  kernel_reflexivity

theorem row_count : captured.2.length = 196 := by kernel_reflexivity

theorem row_inventory : captured.2.map (fun row => (row.1, row.2.1)) =
    (List.range 14).flatMap (fun destination => (List.range 14).map (destination, ·)) := by
  kernel_reflexivity

theorem every_output_exact : ∀ destination source : Fin 14,
    lookup destination source = some (expected destination source) := by
  decide

theorem self_copy_elided (register : Fin 14) : lookup register register = some [] := by
  simpa [expected] using every_output_exact register register

theorem distinct_copy_has_three_bytes (destination source : Fin 14) (different : destination ≠ source) :
    lookup destination source = some
      [(rex true (physical source) (physical destination)).toNat, 137,
        (modRM (physical source) (physical destination)).toNat] := by
  simpa only [expected, if_neg different] using every_output_exact destination source

theorem captured_code_fields (destination source : Fin 14) (different : destination ≠ source)
    (state : State) (address opcodeAddress modrmAddress : BitVec 48) (bytes : List Nat)
    (emitted : lookup destination source = some bytes)
    (present : X86LegacyFetch.loaded state address opcodeAddress modrmAddress bytes) :
    state.mem.get? (address.signExtend 52).toNat =
        some (rex true (physical source) (physical destination)) ∧
      state.mem.get? (opcodeAddress.signExtend 52).toNat = some (0x89#8) ∧
      state.mem.get? (modrmAddress.signExtend 52).toNat =
        some (modRM (physical source) (physical destination)) := by
  have same := (Option.some.inj
    ((distinct_copy_has_three_bytes destination source different).symm.trans emitted)).symm
  subst bytes
  simpa only [X86LegacyFetch.loaded, BitVec.ofNat_toNat, BitVec.setWidth_eq] using present

def rowCheck (row : Nat × Nat × List Nat) : Bool :=
  if valid : row.1 < 14 ∧ row.2.1 < 14 then
    row.2.2 == expected ⟨row.1, valid.1⟩ ⟨row.2.1, valid.2⟩
  else false

theorem captured_rows_checked : captured.2.all rowCheck = true := by kernel_reflexivity

theorem altered_prefix_rejected : rowCheck (5, 4, [76, 137, 193]) = false := by decide

def windowOfCaptured (destination source : Fin 14) (different : destination ≠ source)
    (state : State) (basis : X86LegacyFetch.Basis state) (bytes : List Nat)
    (emitted : lookup destination source = some bytes)
    (present : X86LegacyFetch.loaded state basis.address basis.opcodeAddress basis.modrmAddress bytes) :
    X86ResourceCopy.Window state (physical source) (physical destination) :=
  let fields := captured_code_fields destination source different state basis.address
    basis.opcodeAddress basis.modrmAddress bytes emitted present
  { toBasis := basis
    prefixByte := fields.1
    opcodeByte := fields.2.1
    modrmByte := fields.2.2 }

theorem captured_copy_refines [X86Registers.OtherOpcodeHandlers] [X86Registers.VectorOpcodeHandlers]
    (keys : Finset (Fin 12)) (values : Fin 12 → Word) (state : State)
    (basis : X86LegacyFetch.Basis state) (source destination : Fin 12)
    (different : destination ≠ source) (bytes : List Nat)
    (emitted : lookup (Registers.logicalSlot destination) (Registers.logicalSlot source) = some bytes)
    (present : X86LegacyFetch.loaded state basis.address basis.opcodeAddress basis.modrmAddress bytes)
    (sourcePresent : source ∈ keys) (destinationPresent : destination ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values state)
    (quiet : state.regs.get? .log_register_writes = some false) :
    ∃ invocation : Cells.Invocation (X86ResourceCopy.copyAction source destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination (values source)) ∧
      ∃ after,
        (X86Registers.Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
        RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
          keys (Function.update values destination (values source)) after := by
  have slotsDifferent : Registers.logicalSlot destination ≠ Registers.logicalSlot source := by
    intro same
    exact different (Registers.logicalSlot_injective same)
  let window := windowOfCaptured _ _ slotsDifferent state basis bytes emitted present
  exact X86ResourceCopy.fetched_copy_refines (Registers.canonical .x86_64)
    (Registers.canonical_admitted .x86_64) keys values state source destination window
    sourcePresent destinationPresent represented quiet


end Mettapedia.Machines.TIsa.X86MovCapture
