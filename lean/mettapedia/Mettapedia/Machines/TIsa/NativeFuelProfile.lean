import Mettapedia.Machines.TIsa.ImportedImages
import Mettapedia.Machines.TIsa.X86FuelPrefix

/-!
# Fuel-prefix byte and branch coverage of the imported native images

Each FUEL_STEP span has the fixed budget-load, TEST, zero-budget branch,
used-load and CMP bytes, followed by a patched exhaustion branch and the
original eight-byte memory increment. The checks read the actual imported
byte images and join both branch roles to their exported patches. The
exhaustion displacement decodes to the recorded exhaustion-handler span.

Every current image has a fuel span. Mutation controls change the increment,
counter field and exhaustion target. Complete prefix execution, image-to-state
placement, compiler-buffer behavior and ABI composition are separate proofs.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeFuelProfile
open NativeImage

def headBytes : List Byte :=
  [0x4c, 0x8b, 0xb7, 0xa0, 0, 0, 0, 0x4d, 0x85, 0xf6, 0x0f, 0x84, 16, 0, 0, 0,
    0x4c, 0x8b, 0xbf, 0xa8, 0, 0, 0, 0x4d, 0x39, 0xf7, 0x0f, 0x83]

def incrementBytes : List Byte := [0x48, 0x83, 0x87, 0xa8, 0, 0, 0, 1]

def exhaustedOffset? (image : Image) : Option Nat :=
  (image.spans.find? (fun span => span.kind == "EXHAUSTED_HANDLER")).map Span.offset

def spanCheckOn (image : Image) (view : View) (span : Span) : Bool :=
  span.length == 40 &&
    readRange? view span.offset 28 == some headBytes &&
    readRange? view (span.offset + 32) 8 == some incrementBytes &&
    image.branches.any (fun patch => patch.opcodeOffset == span.offset + 10 && patch.conditional &&
      patch.opcode == (0x84#8) && patch.target == span.offset + 32) &&
    image.branches.any (fun patch => patch.opcodeOffset == span.offset + 26 && patch.conditional &&
      patch.opcode == (0x83#8) && exhaustedOffset? image == some patch.target)

def spanCheck (image : Image) (span : Span) : Bool := spanCheckOn image image.view span

def imageCheck (image : Image) : Bool :=
  image.spans.all (fun span => if span.kind == "FUEL_STEP" then spanCheck image span else true)

theorem all_checked : ImportedImages.images.all imageCheck = true := by kernel_reflexivity

theorem every_image_has_fuel : ImportedImages.images.all (fun image =>
    image.spans.any (fun span => span.kind == "FUEL_STEP")) = true := by kernel_reflexivity

theorem checked_span (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    spanCheck image span = true := by
  have allSpans := List.all_eq_true.mp all_checked image member
  have one := List.all_eq_true.mp allSpans span present
  simpa only [kind, beq_self_eq_true, ite_true] using one

theorem increment_bytes (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    readRange? image.view (span.offset + 32) 8 = some incrementBytes := by
  have checked := checked_span image member span present kind
  simp only [spanCheck, spanCheckOn, Bool.and_eq_true, beq_iff_eq] at checked
  tauto

theorem no_cap_branch (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    ∃ patch ∈ image.branches, patch.opcodeOffset = span.offset + 10 ∧
      patch.conditional = true ∧ patch.opcode = (0x84#8) ∧ patch.target = span.offset + 32 := by
  have checked := checked_span image member span present kind
  have selected : image.branches.any (fun patch => patch.opcodeOffset == span.offset + 10 &&
      patch.conditional && patch.opcode == (0x84#8) && patch.target == span.offset + 32) = true := by
    simp only [spanCheck, spanCheckOn, Bool.and_eq_true] at checked
    tauto
  obtain ⟨patch, within, fields⟩ := List.any_eq_true.mp selected
  simp only [Bool.and_eq_true, beq_iff_eq] at fields
  exact ⟨patch, within, by tauto⟩

theorem exhausted_branch (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    ∃ patch ∈ image.branches, patch.opcodeOffset = span.offset + 26 ∧
      patch.conditional = true ∧ patch.opcode = (0x83#8) ∧ exhaustedOffset? image = some patch.target := by
  have checked := checked_span image member span present kind
  have selected : image.branches.any (fun patch => patch.opcodeOffset == span.offset + 26 &&
      patch.conditional && patch.opcode == (0x83#8) && exhaustedOffset? image == some patch.target) = true := by
    simp only [spanCheck, spanCheckOn, Bool.and_eq_true] at checked
    tauto
  obtain ⟨patch, within, fields⟩ := List.any_eq_true.mp selected
  simp only [Bool.and_eq_true, beq_iff_eq] at fields
  exact ⟨patch, within, by tauto⟩

theorem exhausted_target_decoded (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    ∃ patch ∈ image.branches, patch.opcodeOffset = span.offset + 26 ∧
      exhaustedOffset? image = some patch.target ∧
      ∃ bytes, readFour? image.view patch.fieldOffset = some bytes ∧
        RelativeBranch.decodedTarget patch.fieldOffset bytes = (patch.target : Int) := by
  obtain ⟨patch, within, located, _, _, target⟩ := exhausted_branch image member span present kind
  exact ⟨patch, within, located, target, ImportedImages.all_branch_targets_exact image member patch within⟩

def exhaustionPatch? (image : Image) (span : Span) : Option Patch :=
  image.branches.find? (fun patch => patch.opcodeOffset == span.offset + 26)

def fullSpanCheck (image : Image) (span : Span) : Bool :=
  match exhaustionPatch? image span with
  | none => false
  | some patch => patch.conditional && patch.opcode == (0x83#8) &&
      exhaustedOffset? image == some patch.target &&
      readRange? image.view span.offset 40 ==
        some ((X86FuelPrefix.expected (BitVec.ofInt 32 patch.relative)).map (BitVec.ofNat 8))

def fullImageCheck (image : Image) : Bool :=
  image.spans.all (fun span => if span.kind == "FUEL_STEP" then fullSpanCheck image span else true)

theorem all_full_spans_checked : ImportedImages.images.all fullImageCheck = true := by kernel_reflexivity

theorem full_span_checked_of (image : Image) (checked : fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    fullSpanCheck image span = true := by
  have one := List.all_eq_true.mp checked span present
  simpa only [kind, beq_self_eq_true, ite_true] using one

theorem full_span_checked (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    fullSpanCheck image span = true := by
  exact full_span_checked_of image (List.all_eq_true.mp all_full_spans_checked image member) span present kind

theorem full_span_bytes (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP") :
    ∃ patch, exhaustionPatch? image span = some patch ∧
      readRange? image.view span.offset 40 =
        some ((X86FuelPrefix.expected (BitVec.ofInt 32 patch.relative)).map (BitVec.ofNat 8)) := by
  have checked := full_span_checked image member span present kind
  cases found : exhaustionPatch? image span with
  | none => simp only [fullSpanCheck, found, Bool.false_eq_true] at checked
  | some patch =>
    refine ⟨patch, rfl, ?_⟩
    simp only [fullSpanCheck, found, Bool.and_eq_true, beq_iff_eq] at checked
    tauto

theorem exhaustion_patch_fields_of (image : Image) (checked : fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : exhaustionPatch? image span = some patch) :
    patch.conditional = true ∧ patch.opcode = (0x83#8) ∧ exhaustedOffset? image = some patch.target := by
  have one := full_span_checked_of image checked span present kind
  simp only [fullSpanCheck, found, Bool.and_eq_true, beq_iff_eq] at one
  tauto

theorem exhaustion_patch_fields (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : exhaustionPatch? image span = some patch) :
    patch.conditional = true ∧ patch.opcode = (0x83#8) ∧ exhaustedOffset? image = some patch.target :=
  exhaustion_patch_fields_of image (List.all_eq_true.mp all_full_spans_checked image member)
    span present kind patch found

namespace Controls

private noncomputable def image : Image :=
  ImportedImages.images[0]'(by rw [ImportedImages.image_count]; decide)

private noncomputable def fuel : Span :=
  (image.spans.find? (fun span => span.kind == "FUEL_STEP")).getD ⟨0, 0, "missing"⟩

theorem actual_span_checked : spanCheck image fuel = true := by kernel_reflexivity

private noncomputable def changedByte (offset : Nat) (byte : Byte) : View :=
  ⟨image.size, fun index => if index = fuel.offset + offset then some byte else image.view.read index⟩

theorem changed_immediate_refused : spanCheckOn image (changedByte 39 (0#8)) fuel = false := by
  kernel_reflexivity

theorem changed_counter_field_refused : spanCheckOn image (changedByte 35 (0xa0#8)) fuel = false := by
  kernel_reflexivity

private noncomputable def wrongTarget : Image :=
  { image with branches := image.branches.map fun patch =>
    if patch.opcodeOffset = fuel.offset + 26 then { patch with target := patch.target + 1 } else patch }

theorem changed_exhaustion_target_refused : spanCheck wrongTarget fuel = false := by kernel_reflexivity

end Controls
end Mettapedia.Machines.TIsa.NativeFuelProfile

#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.all_checked
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.increment_bytes
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.exhausted_target_decoded
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.Controls.changed_immediate_refused
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.Controls.changed_counter_field_refused
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.Controls.changed_exhaustion_target_refused
