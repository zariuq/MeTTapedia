import Mettapedia.Machines.TIsa.NativeFuelRefinement
import Mettapedia.Machines.TIsa.X86FueledBin

/-!
# Accepted native images execute the fueled U64 arithmetic template

The image/fuel checks derive the patched prefix; bodyCheck independently
reads the following nine actual bytes for the declared operation and operands.
Those bytes and raw image placement supply the complete instruction contract.
Bounds are derived from successful image reads, and the counter-write exclusion
covers the complete image required by the caller.

This theorem is generic over accepted images and aliasing operands. It assumes
no execution result or compiler correctness. Installing executable memory,
source admission, the failure handler and complete program/ABI composition
remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeFueledBin
open NativeImage X86RegisterRefinement X86Arithmetic
open X86BinCapture (expected)

def bodyCheckOn (view : View) (offset : Nat) (operation : DefinedOperation) (destination left right : Fin 12) : Bool :=
  readRange? view (offset + 40) 9 ==
    some ((expected operation destination left right).map (BitVec.ofNat 8))

def bodyCheck (image : Image) (span : Span) (operation : DefinedOperation) (destination left right : Fin 12) : Bool :=
  bodyCheckOn image.view span.offset operation destination left right

theorem body_bytes (image : Image) (span : Span) (operation : DefinedOperation) (destination left right : Fin 12)
    (checked : bodyCheck image span operation destination left right = true) :
    readRange? image.view (span.offset + 40) 9 =
      some ((expected operation destination left right).map (BitVec.ofNat 8)) := beq_iff_eq.mp checked

theorem body_bound (image : Image) (span : Span) (operation : DefinedOperation) (destination left right : Fin 12)
    (checked : bodyCheck image span operation destination left right = true) : span.offset + 49 ≤ image.size := by
  let last : Nat := (expected operation destination left right)[8]'(by change 8 < 9; decide)
  have lastPresent : (expected operation destination left right)[8]? = some last :=
    List.getElem?_eq_getElem (by change 8 < 9; decide)
  have atLast : ((expected operation destination left right).map (BitVec.ofNat 8))[8]? =
      some (BitVec.ofNat 8 last) := by
    simp only [List.getElem?_map, lastPresent, Option.map_some]
  have read := X86CodePlacement.read_range_byte image.view (span.offset + 40) 9 _
    (body_bytes image span operation destination left right checked) 8 (BitVec.ofNat 8 last) (by decide) atLast
  have bound := NativeFuelRefinement.read_bound image (span.offset + 40 + 8) _ read
  omega

def inputsOfImage (image : Image) (layout : image.layoutCheck = true)
    (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (body : bodyCheck image span operation destination left right = true)
    (state : State) (origin : X86LegacyFetch.Basis state) (frame : X86FuelPrefix.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset)
    (placed : X86CodePlacement.Placed state base image.view)
    (outside : ∀ index byte, image.view.read index = some byte →
      ((X86Execution.address base index).signExtend 52).toNat ∉
        X86WriteWords.written frame.usedAddress (List.range 8)) :
    X86FueledBin.Inputs state operation destination left right where
  toInputs := NativeFuelRefinement.inputsOfImage image layout fuel span present kind patch found
    state origin frame base lower upper location placed
  wholeUpper := by
    have within := body_bound image span operation destination left right body
    change origin.address.toInt + 49 < (2 ^ 47 : Int)
    rw [location]
    omega
  bodyLoaded := by
    have read := body_bytes image span operation destination left right body
    have loaded := X86CodePlacement.range_code state base image.view (span.offset + 40)
      (expected operation destination left right) placed read
    have whereBody : origin.address.toInt + 40 = base + (span.offset + 40 : Nat) := by
      rw [location]
      simp only [Int.natCast_add]
      omega
    change X86Execution.codeLoaded state (origin.address.toInt + 40) _
    rw [whereBody]
    exact loaded
  bodyOutside := by
    intro index byte presentByte
    have within : index < 9 := (List.getElem?_eq_some_iff.mp presentByte).choose
    have read := X86CodePlacement.read_range_byte image.view (span.offset + 40) 9 _
      (body_bytes image span operation destination left right body) index (BitVec.ofNat 8 byte) within
      (by simp only [List.getElem?_map, presentByte, Option.map_some])
    have protectedBytes := outside (span.offset + 40 + index) _ read
    have address : X86Execution.address base (span.offset + 40 + index) =
        X86Execution.address (origin.address.toInt + 40) index := by
      rw [location]
      simp only [X86Execution.address, Int.natCast_add, Int.add_assoc]
      congr 1
    change ((X86Execution.address (origin.address.toInt + 40) index).signExtend 52).toNat ∉
      X86WriteWords.written frame.usedAddress (List.range 8)
    simpa only [address] using protectedBytes

local instance : _root_.X86Registers.MemoryPrimitives := X86Memory.ordinary

theorem executes_checked (other : _root_.X86Registers.OtherOpcodeHandlers)
    (extra : _root_.X86Registers.OtherTwoByteHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (image : Image) (layout : image.layoutCheck = true) (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (body : bodyCheck image span operation destination left right = true)
    (state : State) (origin : X86LegacyFetch.Basis state) (frame : X86FuelPrefix.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset) (placed : X86CodePlacement.Placed state base image.view)
    (outside : ∀ index byte, image.view.read index = some byte →
      ((X86Execution.address base index).signExtend 52).toNat ∉ X86WriteWords.written frame.usedAddress (List.range 8))
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) keys values state) :
    let input := inputsOfImage image layout fuel span present kind patch found operation destination left right
      body state origin frame base lower upper location placed outside
    letI : _root_.X86Registers.OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : _root_.X86Registers.VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86FueledBin.instructionCount input)).run state = .ok () after ∧
      X86FueledBin.Result state input keys values after :=
  X86FueledBin.executes other extra vector operation destination left right state
    (inputsOfImage image layout fuel span present kind patch found operation destination left right
      body state origin frame base lower upper location placed outside)
    keys values leftPresent rightPresent represented

theorem observed_run_refines (other : _root_.X86Registers.OtherOpcodeHandlers)
    (extra : _root_.X86Registers.OtherTwoByteHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (image : Image) (layout : image.layoutCheck = true) (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (body : bodyCheck image span operation destination left right = true)
    (state : State) (origin : X86LegacyFetch.Basis state) (frame : X86FuelPrefix.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset) (placed : X86CodePlacement.Placed state base image.view)
    (outside : ∀ index byte, image.view.read index = some byte →
      ((X86Execution.address base index).signExtend 52).toNat ∉ X86WriteWords.written frame.usedAddress (List.range 8))
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) keys values state)
    (after : State) :
    let input := inputsOfImage image layout fuel span present kind patch found operation destination left right
      body state origin frame base lower upper location placed outside
    letI : _root_.X86Registers.OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : _root_.X86Registers.VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches (X86FueledBin.instructionCount input)).run state = .ok () after →
      X86FueledBin.Result state input keys values after :=
  X86FueledBin.any_run_refines other extra vector operation destination left right state
    (inputsOfImage image layout fuel span present kind patch found operation destination left right
      body state origin frame base lower upper location placed outside)
    keys values leftPresent rightPresent represented after

namespace Controls

private def view : View := View.ofArray (((X86FuelPrefix.expected (0x1e0#32) ++ expected .add 4 4 5).map
  (BitVec.ofNat 8)).toArray)

theorem actual_add_body_checked : bodyCheckOn view 0 .add 4 4 5 = true := by kernel_reflexivity

private def mutated : View := ⟨view.size, fun index => if index = 44 then some (0x29#8) else view.read index⟩

theorem changed_opcode_refused : bodyCheckOn mutated 0 .add 4 4 5 = false := by kernel_reflexivity

theorem changed_opcode_is_sub : bodyCheckOn mutated 0 .sub 4 4 5 = true := by kernel_reflexivity

end Controls
end Mettapedia.Machines.TIsa.NativeFueledBin

#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.inputsOfImage
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.executes_checked
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.observed_run_refines
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.Controls.actual_add_body_checked
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.Controls.changed_opcode_refused
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.Controls.changed_opcode_is_sub
