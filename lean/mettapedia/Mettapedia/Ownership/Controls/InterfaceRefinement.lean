import Mettapedia.Ownership.InterfaceRefinement
import Mettapedia.Ownership.Controls.Admission

/-!
# Controls: interface refinement

Examples admitted and refused, and the axiom audit of the named theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership.Refinement

open Mettapedia.Machines.CMemory.Borrowing

namespace Controls

private def required : Signature := ⟨[.borrowed 8 false], false, .borrowed 0 0 8 false false, [], []⟩
private def optional : Signature := { required with result := .borrowed 0 0 8 false true }

theorem nonnull_implements_nullable : signatureRefines required optional = true := by decide
theorem nullable_does_not_implement_nonnull : signatureRefines optional required = false := by decide
theorem different_origin_refused :
    signatureRefines { required with result := .static false } optional = false := by decide
theorem different_extent_refused :
    signatureRefines { required with result := .borrowed 0 0 4 false false } optional = false := by decide
theorem stronger_write_requirement_refused :
    signatureRefines { required with parameters := [.borrowed 8 true] } optional = false := by decide
theorem different_family_refused :
    shapeRefines (.owned 1 false) (.owned 2 true) = false := by decide

end Controls

#print axioms resultRefines_preserves_return
#print axioms instantiate_refinement
#print axioms signatureRefines_invocation

end Mettapedia.Ownership.Refinement
