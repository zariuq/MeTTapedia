import Mettapedia.Machines.TIsa.ImportedImages
import Mettapedia.Machines.TIsa.X86BranchCondition

/-!
# Conditional-branch coverage of the imported native images

Every conditional branch in the current fifteen images belongs to the
proved flag-condition family. Unconditional E9 branches are classified
separately. This coverage result joins actual image certificates; full
execution refinement and source control-flow composition remain separate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeBranchProfile

open NativeImage X86BranchCondition

def condition? (byte : Byte) : Option Condition :=
  if byte == (0x82#8) then some .below
  else if byte == (0x83#8) then some .aboveEqual
  else if byte == (0x84#8) then some .zero
  else if byte == (0x85#8) then some .nonzero
  else if byte == (0x87#8) then some .above
  else none

theorem condition_opcode (condition : Condition) : condition? (opcode condition) = some condition := by
  cases condition <;> rfl

theorem condition_sound (byte : Byte) (condition : Condition)
    (decoded : condition? byte = some condition) : opcode condition = byte := by
  cases condition <;> revert byte <;> decide

def supported (patch : Patch) : Bool :=
  if patch.conditional then (condition? patch.opcode).isSome else patch.opcode == (0xe9#8)

def imageSupported (image : Image) : Bool := image.branches.all supported

theorem every_imported_image_supported : ImportedImages.images.all imageSupported = true := by
  kernel_reflexivity

theorem conditional_coverage (image : Image) (member : image ∈ ImportedImages.images)
    (patch : Patch) (present : patch ∈ image.branches) (conditional : patch.conditional = true) :
    ∃ condition, patch.opcode = opcode condition := by
  have checked := List.all_eq_true.mp every_imported_image_supported image member
  have branch := List.all_eq_true.mp checked patch present
  have found : (condition? patch.opcode).isSome = true := by
    simpa only [supported, conditional, ite_true] using branch
  cases decoded : condition? patch.opcode with
  | none => simp only [decoded, Option.isSome_none, Bool.false_eq_true] at found
  | some condition => exact ⟨condition, (condition_sound patch.opcode condition decoded).symm⟩

theorem checked_prefix (patch : Patch) (image : View) (bodyOffset epilogueOffset : Nat)
    (checked : patch.check image bodyOffset epilogueOffset = true) : patch.prefixCheck image = true := by
  cases read : readFour? image patch.fieldOffset with
  | none => simp [Patch.check, read] at checked
  | some bytes =>
    simp only [Patch.check, read, Bool.and_eq_true, decide_eq_true_eq] at checked
    tauto

theorem conditional_bytes (image : Image) (member : image ∈ ImportedImages.images)
    (patch : Patch) (present : patch ∈ image.branches) (conditional : patch.conditional = true) :
    ∃ condition, image.view.read patch.opcodeOffset = some (0x0f#8) ∧
      image.view.read (patch.opcodeOffset + 1) = some (opcode condition) ∧
      patch.fieldOffset = patch.opcodeOffset + 2 := by
  obtain ⟨condition, same⟩ := conditional_coverage image member patch present conditional
  have imageChecked := List.all_eq_true.mp ImportedImages.all_layouts_checked image member
  have branchChecked := image.checked_branch imageChecked patch present
  have prefixChecked := checked_prefix patch image.view image.bodyOffset image.epilogueOffset branchChecked
  simp only [Patch.prefixCheck, conditional, ite_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at prefixChecked
  rw [same] at prefixChecked
  refine ⟨condition, ?_, ?_, ?_⟩ <;> tauto

theorem unconditional_count :
    ((ImportedImages.images.flatMap Image.branches).filter (fun patch => !patch.conditional)).length = 185 := by
  kernel_reflexivity

theorem unconditional_bytes (image : Image) (member : image ∈ ImportedImages.images)
    (patch : Patch) (present : patch ∈ image.branches) (unconditional : patch.conditional = false) :
    image.view.read patch.opcodeOffset = some (0xe9#8) ∧ patch.fieldOffset = patch.opcodeOffset + 1 := by
  have imageChecked := List.all_eq_true.mp ImportedImages.all_layouts_checked image member
  have branchChecked := image.checked_branch imageChecked patch present
  have prefixChecked := checked_prefix patch image.view image.bodyOffset image.epilogueOffset branchChecked
  simp only [Patch.prefixCheck, unconditional, Bool.false_eq_true, ite_false,
    Bool.and_eq_true, beq_iff_eq] at prefixChecked
  tauto

namespace Controls

example : condition? (0x87#8) = some .above := rfl
example : condition? (0x86#8) = none := rfl

end Controls
end Mettapedia.Machines.TIsa.NativeBranchProfile

#print axioms Mettapedia.Machines.TIsa.NativeBranchProfile.every_imported_image_supported
#print axioms Mettapedia.Machines.TIsa.NativeBranchProfile.conditional_bytes
