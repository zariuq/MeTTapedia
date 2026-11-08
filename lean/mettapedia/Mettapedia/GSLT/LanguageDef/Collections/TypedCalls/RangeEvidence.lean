import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeBoundary

/-!
# Retained instantiated typing evidence for forwarded ranges

A forwarded value can determine a callee's range when its retained typing
observation has exactly one ground result and the relevant formal covers the
range's variables. The observation contains instantiated types, not stored
polymorphic rows. A singleton row index is insufficient evidence.

These are transport rules for typed boundaries. They do not assert that a
native source walker records the required observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeEvidence

variable {Variable Value : Type}

/-- Forwarded argument evidence at both boundaries pins one ground formal
instance. No equality of caller/callee ranges is assumed. -/
theorem range_from_singleton_typing (typing : Value → List (Ty Empty))
    (value : Value) (witness : Ty Empty) (formal range : Ty Variable)
    (caller callee : Variable → Ty Empty)
    (singleton : typing value = [witness])
    (callerRead : formal.bind caller ∈ typing value)
    (calleeRead : formal.bind callee ∈ typing value)
    (covered : ∀ name ∈ range.vars, name ∈ formal.vars) :
    range.bind caller = range.bind callee := by
  have left : formal.bind caller = witness := by simpa [singleton] using callerRead
  have right : formal.bind callee = witness := by simpa [singleton] using calleeRead
  exact RangeBoundary.range_from_formal formal range caller callee covered (left.trans right.symm)

/-- Several forwarded ground observations can jointly cover a range. The
chosen actual values and their observations may differ between positions. -/
theorem range_from_forwarded_typings (typing : Value → List (Ty Empty))
    (formals : List (Ty Variable)) (range : Ty Variable)
    (caller callee : Variable → Ty Empty)
    (observations : ∀ formal ∈ formals, ∃ value witness,
      typing value = [witness] ∧ formal.bind caller ∈ typing value ∧
        formal.bind callee ∈ typing value)
    (covered : ∀ name ∈ range.vars, ∃ formal ∈ formals, name ∈ formal.vars) :
    range.bind caller = range.bind callee := by
  apply RangeBoundary.range_from_formals formals range caller callee covered
  intro formal member
  obtain ⟨value, witness, singleton, left, right⟩ := observations formal member
  have callerType : formal.bind caller = witness := by simpa [singleton] using left
  have calleeType : formal.bind callee = witness := by simpa [singleton] using right
  exact callerType.trans calleeType.symm

namespace Controls

open RangeBoundary.Controls

def numberType : Ty Empty := .app [.sym "List", .sym "Number"]
def stringType : Ty Empty := .app [.sym "List", .sym "String"]

/-- A value with one retained instantiated type safely transports the range. -/
theorem singleton_forwarding (other : String → Ty Empty)
    (observed : listRange.bind other ∈ [numberType]) :
    listRange.bind numbers = listRange.bind other := by
  apply range_from_singleton_typing (fun (_ : Unit) => [numberType]) ()
    numberType listRange listRange numbers other rfl
  · decide
  · exact observed
  · exact fun _ member => member

/-- The same value may have two ground typing results. Merely forwarding
that value then leaves the two frames free to choose different instances. -/
theorem two_typings_break_transport :
    listRange.bind numbers ∈ [numberType, stringType] ∧
    listRange.bind strings ∈ [numberType, stringType] ∧
    listRange.bind numbers ≠ listRange.bind strings := by decide

/-- One stored polymorphic row is not one retained ground typing. The very
same row occurrence has different ground instances in the two frames. -/
theorem one_polymorphic_row_is_not_singleton_evidence :
    ([listRange] : List (Ty String))[0]? = some listRange ∧
    listRange.bind numbers = numberType ∧ listRange.bind strings = stringType ∧
    numberType ≠ stringType := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeEvidence
