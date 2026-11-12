import Mettapedia.Machines.TIsa.X86CodePlacement
import Mettapedia.Machines.TIsa.NativeFuelProfile
import Mettapedia.Machines.TIsa.NativeBranchProfile

/-!
# Checked native fuel images refine the original fetched prefix

The accepted image and fuel-span checks supply every byte, branch field,
signed displacement bound and target equation. Raw image placement in the
actual Sail memory map then derives codeLoaded; the caller supplies only
architectural and frame facts. The generic theorem applies to any image
accepted by those executable checks, with current imported images as instances.

No fetched execution or compiler correctness is a premise. Installing the
code in executable memory, failure-handler semantics, source admission, full
program composition and the ABI remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeFuelRefinement
open NativeImage X86RegisterRefinement

theorem selected_member (image : Image) (span : Span) (patch : Patch)
    (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    patch ∈ image.branches := List.mem_of_find?_eq_some found

theorem selected_location (image : Image) (span : Span) (patch : Patch)
    (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    patch.opcodeOffset = span.offset + 26 := by
  have selected : (patch.opcodeOffset == span.offset + 26) = true :=
    List.find?_some (p := fun candidate : Patch => candidate.opcodeOffset == span.offset + 26) found
  exact beq_iff_eq.mp selected

theorem bytes_exact (image : Image) (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    readRange? image.view span.offset 40 =
      some ((X86FuelPrefix.expected (BitVec.ofInt 32 patch.relative)).map (BitVec.ofNat 8)) := by
  have checked := NativeFuelProfile.full_span_checked_of image fuel span present kind
  simp only [NativeFuelProfile.fullSpanCheck, found, Bool.and_eq_true, beq_iff_eq] at checked
  tauto

theorem read_bound (image : Image) (index : Nat) (byte : Byte)
    (read : image.view.read index = some byte) : index < image.size := by
  by_contra outside
  simp only [Image.view, if_neg outside] at read
  cases read

theorem span_bound (image : Image) (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    span.offset + 40 ≤ image.size := by
  have last := X86CodePlacement.read_range_byte image.view span.offset 40 _
    (bytes_exact image fuel span present kind patch found) 39 (1#8) (by decide) rfl
  have bound := read_bound image (span.offset + 39) (1#8) last
  omega

theorem patch_data (image : Image) (layout : image.layoutCheck = true) (patch : Patch)
    (present : patch ∈ image.branches) :
    ∃ bytes, readFour? image.view patch.fieldOffset = some bytes ∧
      (RelativeBranch.decode32 bytes).toInt = patch.relative ∧
      RelativeBranch.decodedTarget patch.fieldOffset bytes = (patch.target : Int) ∧
      patch.target ≤ image.epilogueOffset := by
  have checked := image.checked_branch layout patch present
  cases read : readFour? image.view patch.fieldOffset with
  | none => simp only [Patch.check, read, Bool.false_eq_true] at checked
  | some bytes =>
    refine ⟨bytes, rfl, ?_, ?_, ?_⟩
    all_goals
      simp only [Patch.check, read, Bool.and_eq_true, decide_eq_true_eq] at checked
      tauto

theorem target_bound (image : Image) (layout : image.layoutCheck = true) (patch : Patch)
    (present : patch ∈ image.branches) : patch.target ≤ image.size := by
  obtain ⟨_, _, _, _, target⟩ := patch_data image layout patch present
  have checked := layout
  have extent : image.epilogueOffset + 10 = image.view.size := by
    simp only [Image.layoutCheck, Image.layoutCheckOn, Bool.and_eq_true, beq_iff_eq] at checked
    tauto
  change image.epilogueOffset + 10 = image.size at extent
  omega

theorem relative_target (image : Image) (layout : image.layoutCheck = true)
    (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    (patch.target : Int) = (span.offset : Int) + 32 + (BitVec.ofInt 32 patch.relative).toInt := by
  have belongs := selected_member image span patch found
  have located := selected_location image span patch found
  have conditional := (NativeFuelProfile.exhaustion_patch_fields_of image fuel span present kind patch found).1
  have prefixChecked := NativeBranchProfile.checked_prefix patch image.view image.bodyOffset image.epilogueOffset
    (image.checked_branch layout patch belongs)
  have field : patch.fieldOffset = patch.opcodeOffset + 2 := by
    simp only [Patch.prefixCheck, conditional, ite_true, Bool.and_eq_true, beq_iff_eq] at prefixChecked
    tauto
  obtain ⟨bytes, _, relative, target, _⟩ := patch_data image layout patch belongs
  have signed : (BitVec.ofInt 32 patch.relative).toInt = patch.relative := by
    apply BitVec.toInt_ofInt_eq_self (by decide)
    · rw [← relative]
      exact BitVec.le_toInt _
    · rw [← relative]
      exact BitVec.toInt_lt
  rw [signed]
  simp only [RelativeBranch.decodedTarget, relative, field, located, Int.natCast_add] at target
  omega

def inputsOfImage (image : Image) (layout : image.layoutCheck = true)
    (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch)
    (state : State) (origin : X86LegacyFetch.Basis state) (frame : X86FuelPrefix.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset)
    (placed : X86CodePlacement.Placed state base image.view) : X86FuelPrefix.Inputs state where
  toBasis := origin
  toFrameFacts := frame
  displacement := BitVec.ofInt 32 patch.relative
  exhausted := X86Execution.address base patch.target
  upper := by
    have within := span_bound image fuel span present kind patch found
    rw [location]
    omega
  jump := by
    rw [X86Execution.address_toInt base lower upper patch.target (target_bound image layout patch
      (selected_member image span patch found)), location]
    have target := relative_target image layout fuel span present kind patch found
    omega
  loaded := by
    apply X86CodePlacement.code_of_read_range state base image.view span.offset origin.address
      (X86FuelPrefix.expected (BitVec.ofInt 32 patch.relative)) location placed
    simpa only [X86FuelPrefix.expected_length] using bytes_exact image fuel span present kind patch found

local instance : _root_.X86Registers.MemoryPrimitives := X86Memory.ordinary

theorem executes_checked (other : _root_.X86Registers.OtherOpcodeHandlers)
    (extra : _root_.X86Registers.OtherTwoByteHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (image : Image) (layout : image.layoutCheck = true) (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch)
    (state : State) (origin : X86LegacyFetch.Basis state) (frame : X86FuelPrefix.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset)
    (placed : X86CodePlacement.Placed state base image.view) :
    let input := inputsOfImage image layout fuel span present kind patch found state origin frame
      base lower upper location placed
    letI : _root_.X86Registers.OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : _root_.X86Registers.VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86FuelPrefix.instructionCount input)).run state = .ok () after ∧
      X86FuelPrefix.Result state input after :=
  X86FuelPrefix.executes other extra vector state
    (inputsOfImage image layout fuel span present kind patch found state origin frame base lower upper location placed)

theorem observed_run_refines (other : _root_.X86Registers.OtherOpcodeHandlers)
    (extra : _root_.X86Registers.OtherTwoByteHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (image : Image) (layout : image.layoutCheck = true) (fuel : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch)
    (state : State) (origin : X86LegacyFetch.Basis state) (frame : X86FuelPrefix.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset)
    (placed : X86CodePlacement.Placed state base image.view) (after : State) :
    let input := inputsOfImage image layout fuel span present kind patch found state origin frame
      base lower upper location placed
    letI : _root_.X86Registers.OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : _root_.X86Registers.VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches (X86FuelPrefix.instructionCount input)).run state = .ok () after →
      X86FuelPrefix.Result state input after :=
  X86FuelPrefix.any_run_refines other extra vector state
    (inputsOfImage image layout fuel span present kind patch found state origin frame base lower upper location placed) after

theorem imported_span_executes (other : _root_.X86Registers.OtherOpcodeHandlers)
    (extra : _root_.X86Registers.OtherTwoByteHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (state : State) (origin : X86LegacyFetch.Basis state) (frame : X86FuelPrefix.FrameFacts state)
    (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + image.size < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + span.offset)
    (placed : X86CodePlacement.Placed state base image.view) :
    ∃ patch, ∃ found : NativeFuelProfile.exhaustionPatch? image span = some patch,
      let input := inputsOfImage image (List.all_eq_true.mp ImportedImages.all_layouts_checked image member)
        (List.all_eq_true.mp NativeFuelProfile.all_full_spans_checked image member)
        span present kind patch found state origin frame base lower upper location placed
      letI : _root_.X86Registers.OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
      letI : _root_.X86Registers.VectorOpcodeHandlers := vector
      ∃ after, (X86FuelPrefix.fetches (X86FuelPrefix.instructionCount input)).run state = .ok () after ∧
        X86FuelPrefix.Result state input after := by
  obtain ⟨patch, found, _⟩ := NativeFuelProfile.full_span_bytes image member span present kind
  exact ⟨patch, found, executes_checked other extra vector image
    (List.all_eq_true.mp ImportedImages.all_layouts_checked image member)
    (List.all_eq_true.mp NativeFuelProfile.all_full_spans_checked image member)
    span present kind patch found state origin frame base lower upper location placed⟩

end Mettapedia.Machines.TIsa.NativeFuelRefinement

#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.relative_target
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.inputsOfImage
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.executes_checked
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.observed_run_refines
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.imported_span_executes
