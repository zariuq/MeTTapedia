import Mettapedia.Languages.Maude.Semantics

/-! Separating controls for many-sorted equality. Raw unit schemas alone
admit a reverse step that puts a Nat inside an Element operator. The typed
operational relation refuses that step, while retaining the Element unit law.
Undeclared constructors cannot supply contexts either. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.SortedControls

def zero : Operator := ⟨"zero", "zero", [], "Nat", {constructor := true}⟩
def unit : Operator := ⟨"e0", "e0", [], "Element", {constructor := true}⟩
def combine : Operator := ⟨"combine", "combine", ["Element", "Element"], "Element",
  {associative := true, commutative := true, identity := some (.app "e0" [])}⟩
def signature : Signature := ⟨["Nat", "Element"], [zero, unit, combine]⟩
def theory : Theory := {name := "SORTED-UNIT", signature := signature}
def context : VariableContext := [("n", "Nat"), ("e", "Element")]
def bad : Term := .app "combine" [.app "e0" [], .var "n"]
def good : Term := .app "combine" [.app "e0" [], .var "e"]

#guard signature.check

theorem raw_schema_exposes_escape : AlgebraSchema signature bad (.var "n") := by
  exact .leftUnit (declaration := combine) (by simp [signature]) rfl

theorem bad_not_nat : ¬ HasSort signature context bad "Nat" := by
  intro typed
  have origin := HasSort.operator_origin typed rfl
  obtain ⟨declaration, member, label, result⟩ := origin
  simp [signature] at member
  rcases member with rfl | rfl | rfl <;> simp_all [zero, unit, combine]

theorem unit_sort_escape_refused : ¬ Equivalent theory context "Nat" (.var "n") bad := by
  intro escaped
  exact bad_not_nat escaped.sorted.2

theorem unknown_constructor_not_typed (sort : String) :
    ¬ HasSort signature context (.app "undeclared" [.var "n"]) sort := by
  intro typed
  obtain ⟨declaration, member, label, _⟩ := HasSort.operator_origin typed rfl
  simp [signature] at member
  rcases member with rfl | rfl | rfl <;> simp_all [zero, unit, combine]

theorem unknown_context_refused (sort : String) :
    ¬ Equivalent theory context sort (.var "n") (.app "undeclared" [.var "n"]) := by
  intro escaped
  exact unknown_constructor_not_typed sort escaped.sorted.2

theorem element_typed : HasSort signature context (.var "e") "Element" := .var (by decide)

theorem good_typed : HasSort signature context good "Element" := by
  apply HasSort.app (declaration := combine) (by simp [signature])
  exact .cons (.app (declaration := unit) (by simp [signature]) .nil) (.cons element_typed .nil)

theorem element_unit_fires : Equivalent theory context "Element" good (.var "e") := by
  apply Equivalent.algebra
  exact ⟨.leftUnit (declaration := combine) (by simp [theory, signature]) rfl, good_typed, element_typed⟩

theorem element_unit_reverses : Equivalent theory context "Element" (.var "e") good :=
  .symm element_unit_fires

end Mettapedia.Languages.Maude.SortedControls
