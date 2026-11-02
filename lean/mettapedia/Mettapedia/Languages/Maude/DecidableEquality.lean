import Mettapedia.Languages.Maude.Syntax

/-! Constructive structural equality for independent Maude IR. These
instances support proof-producing certificate-link checks over complete
signatures and rows, rather than comparing printed representations. -/

namespace Mettapedia.Languages.Maude

mutual
  def Term.structuralEqual : Term → Term → Bool
    | .var first, .var second => first == second
    | .app first left, .app second right => first == second && structuralEqualList left right
    | _, _ => false

  def Term.structuralEqualList : List Term → List Term → Bool
    | [], [] => true
    | first :: rest, second :: tail => structuralEqual first second && structuralEqualList rest tail
    | _, _ => false
end

theorem Term.structuralEqual_iff (first : Term) :
    ∀ second, first.structuralEqual second = true ↔ first = second := by
  refine Term.rec
    (motive_1 := fun first => ∀ second, first.structuralEqual second = true ↔ first = second)
    (motive_2 := fun first => ∀ second, Term.structuralEqualList first second = true ↔ first = second)
    ?_ ?_ ?_ ?_ first
  · intro name second
    cases second <;> simp [Term.structuralEqual]
  · intro id arguments ih second
    cases second <;> simp [Term.structuralEqual, ih]
  · intro second
    cases second <;> simp [Term.structuralEqualList]
  · intro head tail firstIH restIH second
    cases second <;> simp [Term.structuralEqualList, firstIH, restIH]

instance : DecidableEq Term := fun first second =>
  if same : first.structuralEqual second = true then
    .isTrue ((first.structuralEqual_iff second).mp same)
  else .isFalse (fun equality => same ((first.structuralEqual_iff second).mpr equality))
deriving instance DecidableEq for Attributes
deriving instance DecidableEq for Operator
deriving instance DecidableEq for Signature
deriving instance DecidableEq for Condition
deriving instance DecidableEq for Row
deriving instance DecidableEq for Theory

#print axioms Term.structuralEqual_iff

end Mettapedia.Languages.Maude
