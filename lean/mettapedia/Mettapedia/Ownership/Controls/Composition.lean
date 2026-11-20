import Mettapedia.Ownership.Composition
import Mettapedia.Ownership.Controls.InterfaceRefinement

/-!
# Controls: composition

Examples admitted and refused, and the axiom audit of the named theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership.Composition

open Mettapedia.Machines.CMemory.Borrowing
open Mettapedia.Machines.CMemory.PermissionFlow
open Refinement

namespace Controls

private def signature : Signature := ⟨[], false, .value, [], []⟩
private def contract : Contract := ⟨signature, "int(void)", "()", []⟩
private def caller : Assumption := ⟨"value", contract, "The definition meets its declared interface."⟩
private def unresolved : Definition := ⟨"value", contract, true, none, ""⟩
private def nativeBody : Definition := ⟨"value", contract, false, none, "Native implementation."⟩
private def function : Function := ⟨"value", signature, [], [], .value, .ret⟩
private def fixture : Module := ⟨[], [function]⟩
private def body : CheckedBody := ⟨fixture, by decide, function, by simp [fixture]⟩
private def provider : Definition := { unresolved with body := some body }

theorem admitted_definition_closes_call : classify [provider] caller = some (.closed provider) := by rfl

theorem checked_flag_without_admission_refused : classify [unresolved] caller = none := by decide
theorem native_dependency_is_open : classify [] caller = some .native := by rfl
theorem unchecked_dependency_is_open :
    classify [nativeBody] caller = some (.unchecked true) := by rfl
theorem mismatched_unchecked_is_open :
    classify [{ nativeBody with contract := { contract with prototype := "long(void)" } }] caller =
      some (.unchecked false) := by rfl
theorem shared_complete_layout_mismatch_refused :
    recordsAgree [("struct R", "size=8")] [("struct R", "size=16")] = false := by decide
theorem opaque_layout_does_not_invent_a_layout :
    recordsAgree [] [("struct R", "size=16")] = true := by rfl
theorem target_mismatch_refused :
    targetsAgree [("x86-sysv", true), ("aarch64", true)] = false := by decide
theorem char_signedness_mismatch_refused :
    targetsAgree [("x86-sysv", true), ("x86-sysv", false)] = false := by decide

end Controls

#print axioms closed_return_respects_caller
#print axioms resolution_preserves_invocation
#print axioms check_sound

end Mettapedia.Ownership.Composition
