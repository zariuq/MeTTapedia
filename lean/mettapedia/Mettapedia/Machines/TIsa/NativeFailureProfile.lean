import Mettapedia.Machines.TIsa.ImportedImages
import Mettapedia.Machines.TIsa.X86FailureHandler

/-!
# Actual emitted failure-handler bytes and exit branches

All current invalid-input, exhausted and unsupported spans are checked against
the complete twenty-eight-byte handler contract, including the actual patched
jump to the public epilogue. Each current image has an exhaustion span.
The checks inspect raw bytes independently of the span label and patch value.
Status-byte and wrong-outcome mutation controls reject altered contracts.

These are image/profile facts. Raw placement, caller memory separation,
handler execution and the public epilogue are separate proof obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeFailureProfile
open NativeImage

def outcome? (span : Span) : Option (BitVec 32) :=
  if span.kind == "INVALID_INPUT_HANDLER" then some (3#32)
  else if span.kind == "EXHAUSTED_HANDLER" then some (4#32)
  else if span.kind == "UNSUPPORTED_HANDLER" then some (2#32)
  else none

def exitPatch? (image : Image) (span : Span) : Option Patch :=
  image.branches.find? (fun patch => patch.opcodeOffset == span.offset + 23)

def spanCheckOn (image : Image) (view : View) (span : Span) (value : BitVec 32) : Bool :=
  match exitPatch? image span with
  | none => false
  | some patch => span.length == 28 && !patch.conditional && patch.opcode == (0xe9#8) &&
      patch.fieldOffset == span.offset + 24 && patch.nextIp == span.offset + 28 &&
      patch.target == image.epilogueOffset &&
      readRange? view span.offset 28 ==
        some ((X86FailureHandler.expected value (BitVec.ofInt 32 patch.relative)).map (BitVec.ofNat 8))

def spanCheck (image : Image) (span : Span) (value : BitVec 32) : Bool := spanCheckOn image image.view span value

def imageCheck (image : Image) : Bool :=
  image.spans.all (fun span => match outcome? span with
    | none => true
    | some value => spanCheck image span value)

theorem all_checked : ImportedImages.images.all imageCheck = true := by kernel_reflexivity

theorem every_image_has_exhaustion : ImportedImages.images.all (fun image =>
    image.spans.any (fun span => span.kind == "EXHAUSTED_HANDLER")) = true := by kernel_reflexivity

theorem checked_span (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (value : BitVec 32) (kind : outcome? span = some value) :
    spanCheck image span value = true := by
  have spans := List.all_eq_true.mp all_checked image member
  have checked := List.all_eq_true.mp spans span present
  simpa only [kind] using checked

theorem bytes_of (image : Image) (span : Span) (value : BitVec 32)
    (checked : spanCheck image span value = true) :
    ∃ patch, exitPatch? image span = some patch ∧ span.length = 28 ∧
      patch.conditional = false ∧ patch.opcode = (0xe9#8) ∧
      patch.fieldOffset = span.offset + 24 ∧ patch.nextIp = span.offset + 28 ∧
      patch.target = image.epilogueOffset ∧
      readRange? image.view span.offset 28 =
        some ((X86FailureHandler.expected value (BitVec.ofInt 32 patch.relative)).map (BitVec.ofNat 8)) := by
  cases found : exitPatch? image span with
  | none => simp only [spanCheck, spanCheckOn, found, Bool.false_eq_true] at checked
  | some patch =>
    refine ⟨patch, rfl, ?_⟩
    simp only [spanCheck, spanCheckOn, found, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at checked
    tauto

namespace Controls
private noncomputable def first : Image := ImportedImages.images[0]'(by decide)
private noncomputable def exhausted : Span := (first.spans.find? (fun span => span.kind == "EXHAUSTED_HANDLER")).getD ⟨0, 0, ""⟩
private noncomputable def altered : View := ⟨first.size, fun index =>
  if index = exhausted.offset + 12 then some (5#8) else first.view.read index⟩

theorem exhaustion_checked : spanCheck first exhausted (4#32) = true := by kernel_reflexivity
theorem changed_status_refused : spanCheckOn first altered exhausted (4#32) = false := by kernel_reflexivity
theorem wrong_outcome_refused : spanCheck first exhausted (3#32) = false := by kernel_reflexivity

end Controls
end Mettapedia.Machines.TIsa.NativeFailureProfile

#print axioms Mettapedia.Machines.TIsa.NativeFailureProfile.all_checked
#print axioms Mettapedia.Machines.TIsa.NativeFailureProfile.every_image_has_exhaustion
#print axioms Mettapedia.Machines.TIsa.NativeFailureProfile.bytes_of
#print axioms Mettapedia.Machines.TIsa.NativeFailureProfile.Controls.changed_status_refused
#print axioms Mettapedia.Machines.TIsa.NativeFailureProfile.Controls.wrong_outcome_refused
