import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Compare the fields of an equation in source order using the caller's atom
equality. Identical rows may still occur at different positions in a program. -/
def Equation.decideEq [DecidableEq Atom] : DecidableEq Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧ left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
