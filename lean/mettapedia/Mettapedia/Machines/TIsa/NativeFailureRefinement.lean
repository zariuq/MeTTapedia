import Mettapedia.Machines.TIsa.NativeFailureProfile
import Mettapedia.Machines.TIsa.NativeFuelRefinement

/-!
# Checked native handler images supply complete execution inputs

The adapter derives code bounds, the signed E9 target and loaded instructions
from raw handler/profile checks, image layout and placement. Frame facts and
write exclusion for the caller's complete image remain explicit premises.
The resulting theorem executes the four original fetched instructions and
establishes the complete handler result without an execution hypothesis.

This joins image contents to handler semantics. The source admission/driver,
public epilogue, ABI and whole-program compiler theorem remain separate.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeFailureRefinement
open NativeImage X86RegisterRefinement

theorem selected_member (image : Image) (span : Span) (patch : Patch)
    (found : NativeFailureProfile.exitPatch? image span = some patch) : patch ∈ image.branches :=
  List.mem_of_find?_eq_some found

theorem checked_data (image : Image) (span : Span) (value : BitVec 32)
    (checked : NativeFailureProfile.spanCheck image span value = true)
    (patch : Patch) (found : NativeFailureProfile.exitPatch? image span = some patch) :
    patch.fieldOffset = span.offset + 24 ∧ patch.target = image.epilogueOffset ∧
      readRange? image.view span.offset 28 =
        some ((X86FailureHandler.expected value (BitVec.ofInt 32 patch.relative)).map (BitVec.ofNat 8)) := by
  obtain ⟨actual, selected, _, _, _, field, _, target, bytes⟩ := NativeFailureProfile.bytes_of image span value checked
  have same := Option.some.inj (selected.symm.trans found)
  subst actual
  exact ⟨field, target, bytes⟩

theorem span_bound (image : Image) (span : Span) (value : BitVec 32)
    (checked : NativeFailureProfile.spanCheck image span value = true)
    (patch : Patch) (found : NativeFailureProfile.exitPatch? image span = some patch) : span.offset + 28 ≤ image.size := by
  have bytes := (checked_data image span value checked patch found).2.2
  let last : Nat := (X86FailureHandler.expected value (BitVec.ofInt 32 patch.relative))[27]'(by change 27 < 28; decide)
  have lastPresent : (X86FailureHandler.expected value (BitVec.ofInt 32 patch.relative))[27]? = some last :=
    List.getElem?_eq_getElem (by change 27 < 28; decide)
  have atLast : ((X86FailureHandler.expected value (BitVec.ofInt 32 patch.relative)).map (BitVec.ofNat 8))[27]? =
      some (BitVec.ofNat 8 last) := by
    simp only [List.getElem?_map, lastPresent, Option.map_some]
  have read := X86CodePlacement.read_range_byte image.view span.offset 28 _ bytes 27 (BitVec.ofNat 8 last) (by decide) atLast
  have bound := NativeFuelRefinement.read_bound image (span.offset + 27) (BitVec.ofNat 8 last) read
  omega

theorem relative_target (image : Image) (layout : image.layoutCheck = true)
    (span : Span) (value : BitVec 32) (checked : NativeFailureProfile.spanCheck image span value = true)
    (patch : Patch) (found : NativeFailureProfile.exitPatch? image span = some patch) :
    (image.epilogueOffset : Int) = (span.offset : Int) + 28 + (BitVec.ofInt 32 patch.relative).toInt := by
  obtain ⟨field, destination, _⟩ := checked_data image span value checked patch found
  obtain ⟨bytes, _, relative, target, _⟩ := NativeFuelRefinement.patch_data image layout patch
    (selected_member image span patch found)
  have signed : (BitVec.ofInt 32 patch.relative).toInt = patch.relative := by
    apply BitVec.toInt_ofInt_eq_self (by decide)
    · rw [← relative]; exact BitVec.le_toInt _
    · rw [← relative]; exact BitVec.toInt_lt
  rw [signed]
  simp only [RelativeBranch.decodedTarget, relative, field, destination, Int.natCast_add] at target
  omega

def inputsOfImage (image : Image) (layout : image.layoutCheck = true)
    (span : Span) (value : BitVec 32) (checked : NativeFailureProfile.spanCheck image span value = true)
    (patch : Patch) (found : NativeFailureProfile.exitPatch? image span = some patch)
    (state : State) (origin : X86LegacyFetch.Basis state) (facts : X86FailureHandler.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset) (placed : X86CodePlacement.Placed state base image.view)
    (outside : ∀ index byte, image.view.read index = some byte →
      ((X86Execution.address base index).signExtend 52).toNat ∉
        X86WriteWords.written facts.statusAddress (List.range 8) ∪ X86WriteWords.written facts.resultAddress (List.range 8)) :
    X86FailureHandler.Inputs state value where
  toBasis := origin
  toFrameFacts := facts
  displacement := BitVec.ofInt 32 patch.relative
  epilogue := X86Execution.address base image.epilogueOffset
  upper := by
    have within := span_bound image span value checked patch found
    rw [location]
    omega
  jump := by
    have targetBound : image.epilogueOffset ≤ image.size := by
      have target := NativeFuelRefinement.target_bound image layout patch (selected_member image span patch found)
      rw [(checked_data image span value checked patch found).2.1] at target
      exact target
    rw [X86Execution.address_toInt base lower upper image.epilogueOffset targetBound, location]
    have target := relative_target image layout span value checked patch found
    omega
  loaded := by
    apply X86CodePlacement.code_of_read_range state base image.view span.offset origin.address
      (X86FailureHandler.expected value (BitVec.ofInt 32 patch.relative)) location placed
    exact (checked_data image span value checked patch found).2.2
  codeOutside := by
    intro index byte present
    have within : index < 28 := (List.getElem?_eq_some_iff.mp present).choose
    have read := X86CodePlacement.read_range_byte image.view span.offset 28 _
      (checked_data image span value checked patch found).2.2 index (BitVec.ofNat 8 byte) within
      (by simp only [List.getElem?_map, present, Option.map_some])
    have safe := outside (span.offset + index) _ read
    have address : X86Execution.address base (span.offset + index) = X86Execution.address origin.address.toInt index := by
      rw [location]
      simp only [X86Execution.address, Int.natCast_add, Int.add_assoc]
    simpa only [address] using safe

local instance : _root_.X86Registers.MemoryPrimitives := X86Memory.ordinary

theorem executes_checked (other : _root_.X86Registers.OtherOpcodeHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (image : Image) (layout : image.layoutCheck = true)
    (span : Span) (value : BitVec 32) (checked : NativeFailureProfile.spanCheck image span value = true)
    (patch : Patch) (found : NativeFailureProfile.exitPatch? image span = some patch)
    (state : State) (origin : X86LegacyFetch.Basis state) (facts : X86FailureHandler.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset) (placed : X86CodePlacement.Placed state base image.view)
    (outside : ∀ index byte, image.view.read index = some byte →
      ((X86Execution.address base index).signExtend 52).toNat ∉
        X86WriteWords.written facts.statusAddress (List.range 8) ∪ X86WriteWords.written facts.resultAddress (List.range 8)) :
    let input := inputsOfImage image layout span value checked patch found state origin facts base lower upper location placed outside
    letI : _root_.X86Registers.OtherOpcodeHandlers := X86FailureHandler.linkedHandlers other
    letI : _root_.X86Registers.VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧ X86FailureHandler.Result state input after :=
  let input := inputsOfImage image layout span value checked patch found state origin facts base lower upper location placed outside
  ⟨_, X86FailureHandler.executes other vector state value input, X86FailureHandler.finished_result state value input⟩

end Mettapedia.Machines.TIsa.NativeFailureRefinement

#print axioms Mettapedia.Machines.TIsa.NativeFailureRefinement.span_bound
#print axioms Mettapedia.Machines.TIsa.NativeFailureRefinement.relative_target
#print axioms Mettapedia.Machines.TIsa.NativeFailureRefinement.inputsOfImage
#print axioms Mettapedia.Machines.TIsa.NativeFailureRefinement.executes_checked
