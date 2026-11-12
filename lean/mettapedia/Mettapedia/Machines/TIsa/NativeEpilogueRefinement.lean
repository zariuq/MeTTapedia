import Mettapedia.Machines.TIsa.X86Epilogue
import Mettapedia.Machines.TIsa.ImportedImages

/-!
# Checked native images supply the public epilogue contract

The existing layout checker validates the exact ten-byte epilogue. Its extent,
raw image placement, architectural context and saved-stack facts construct the
full fetched epilogue inputs. The execution theorem restores the saved values
and returns without assuming an execution result. An altered POP byte is refused.

Saved-stack provenance from the prologue, complete source/control/ABI
composition and physical memory installation remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeEpilogueRefinement
open NativeImage X86RegisterRefinement

theorem bytes_exact (image : Image) (checked : image.layoutCheck = true) :
    readRange? image.view image.epilogueOffset 10 = some (X86Epilogue.expected.map (BitVec.ofNat 8)) := by
  have exactBytes : readRange? image.view image.epilogueOffset 10 = some NativeImage.epilogue := by
    simp only [Image.layoutCheck, Image.layoutCheckOn, Bool.and_eq_true, beq_iff_eq] at checked
    tauto
  exact exactBytes

theorem extent (image : Image) (checked : image.layoutCheck = true) : image.epilogueOffset + 10 = image.size := by
  simp only [Image.layoutCheck, Image.layoutCheckOn, Bool.and_eq_true, beq_iff_eq] at checked
  tauto

def inputsOfImage (image : Image) (checked : image.layoutCheck = true)
    (state : State) (context : X86PlainFetch.Facts state) (frame : X86Epilogue.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base image.view)
    (rip : state.regs.get? .rip = some ((X86Execution.address base image.epilogueOffset).signExtend 64)) :
    X86Epilogue.Inputs state where
  toFrameFacts := frame
  context := context
  code := X86Execution.address base image.epilogueOffset
  codeUpper := by
    rw [X86Execution.address_toInt base lower upper image.epilogueOffset (by have := extent image checked; omega)]
    have length := extent image checked
    omega
  loaded := by
    rw [X86Execution.address_toInt base lower upper image.epilogueOffset (by have := extent image checked; omega)]
    exact X86CodePlacement.range_code state base image.view image.epilogueOffset X86Epilogue.expected placed (bytes_exact image checked)
  rip := rip

local instance : _root_.X86Registers.MemoryPrimitives := X86Memory.ordinary

theorem executes_checked (other : _root_.X86Registers.OtherOpcodeHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (image : Image) (checked : image.layoutCheck = true)
    (state : State) (context : X86PlainFetch.Facts state) (frame : X86Epilogue.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base image.view)
    (rip : state.regs.get? .rip = some ((X86Execution.address base image.epilogueOffset).signExtend 64)) :
    let input := inputsOfImage image checked state context frame base lower upper placed rip
    letI : _root_.X86Registers.OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : _root_.X86Registers.VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧ X86Epilogue.Result state input after :=
  let input := inputsOfImage image checked state context frame base lower upper placed rip
  ⟨_, X86Epilogue.executes other vector state input, X86Epilogue.finished_result state input⟩

namespace Controls
private noncomputable def image : Image := ImportedImages.images[0]'(by rw [ImportedImages.image_count]; decide)
private noncomputable def changed : View := ⟨image.size, fun index =>
  if index = image.epilogueOffset + 7 then some (0x5d#8) else image.view.read index⟩

theorem actual_image_checked : image.layoutCheck = true := by kernel_reflexivity
theorem changed_pop_refused : image.layoutCheckOn changed = false := by kernel_reflexivity

end Controls
end Mettapedia.Machines.TIsa.NativeEpilogueRefinement

#print axioms Mettapedia.Machines.TIsa.NativeEpilogueRefinement.bytes_exact
#print axioms Mettapedia.Machines.TIsa.NativeEpilogueRefinement.inputsOfImage
#print axioms Mettapedia.Machines.TIsa.NativeEpilogueRefinement.executes_checked
#print axioms Mettapedia.Machines.TIsa.NativeEpilogueRefinement.Controls.changed_pop_refused
