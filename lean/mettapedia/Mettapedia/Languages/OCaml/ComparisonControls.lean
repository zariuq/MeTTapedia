import Mettapedia.Languages.OCaml.ComparisonPrimitive

/-! Positive and separating source controls for structural comparison.
They distinguish strict-prefix termination from an equal prefix reaching a
function, and constant constructors from payload-carrying constructors.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ComparisonControls

private def integer (number : Int) : Value := .literal (.integer number)
private def closure : Value := .closure (.lambda 0) []

theorem strict_prefix_skips_function :
    Primitive.less.eval [.tuple [integer 0, closure], .tuple [integer 1, closure]] =
      .ok (.ok (.literal (.boolean true))) := rfl

theorem equal_prefix_reaches_function :
    Primitive.equal.eval [.tuple [integer 0, closure], .tuple [integer 0, closure]] =
      .ok (.error .functionalComparison) := rfl

theorem equal_prefix_no_boolean (flag : Bool) :
    Primitive.equal.eval [.tuple [integer 0, closure], .tuple [integer 0, closure]] ≠
      .ok (.ok (.literal (.boolean flag))) := by
  rw [equal_prefix_reaches_function]
  intro same
  cases same

theorem constant_before_block :
    Primitive.less.eval [.variant 0 99 [], .variant 0 0 [integer 0]] =
      .ok (.ok (.literal (.boolean true))) := rfl

theorem different_type_refused :
    ∃ error, Primitive.equal.eval [.variant 0 0 [], .variant 1 0 []] = .error error := ⟨_, rfl⟩

theorem tuple_arity_refused :
    ∃ error, Primitive.equal.eval [.tuple [integer 1], .tuple [integer 1, integer 2]] = .error error := ⟨_, rfl⟩

#print axioms strict_prefix_skips_function
#print axioms equal_prefix_no_boolean
#print axioms constant_before_block
#print axioms different_type_refused

end Mettapedia.Languages.OCaml.ComparisonControls
