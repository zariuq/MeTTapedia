import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Data

/-! # Data preservation and its necessary vocabulary boundary -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataControls

private def noPrimitives : Host := ⟨fun _ _ => .unhandled⟩

private def guestData : Term := .expr [.sym "GuestApp", .lit "37", .list [.sym "let"]]

theorem guest_constructor_is_passive : PassiveData [] noPrimitives guestData := by
  apply PassiveData.node
  · simp [Special]
  · rfl
  · rfl
  · intro argument member
    simp at member
    rcases member with rfl | rfl
    · exact .lit _
    · apply PassiveData.list
      intro element member
      have same := List.mem_singleton.mp member
      subst element
      exact PassiveData.sym "let"

theorem arbitrary_depth_data_completes {P : Program} {H : Host} {value : Term}
    (data : PassiveData P H value) :
    eval P H (sizeOf value + 1) [] value = .value value :=
  data.eval_eq_value [] _ (Nat.lt_succ_self _)

theorem zero_fuel_is_not_logical_refusal : eval [] noPrimitives 0 [] guestData = .exhausted := rfl

private def collision : Program :=
  [⟨"constructor-collision", "GuestApp", [.var "symbol", .var "arguments"], .sym "changed"⟩]

theorem constructor_collision_changes_the_value :
    eval collision noPrimitives 3 [] guestData = .value (.sym "changed") := rfl

theorem constructor_collision_is_not_passive : ¬ PassiveData collision noPrimitives guestData := by
  intro data
  cases data with
  | node _ undefined _ _ => contradiction

theorem reading_bound_syntax_does_not_execute_it :
    eval collision noPrimitives 1 [("input", guestData)] (.var "input") = .value guestData := rfl

private def nonlinear : Equation :=
  ⟨"repeated-slot", "same", [.var "x", .var "x"], .var "x"⟩

/-- The raw matcher is not nonlinear unification; admission must enforce linearity. -/
theorem raw_matcher_does_not_enforce_repeated_slot_equality :
    matchTerms nonlinear.params [.sym "a", .sym "b"] =
      some [("x", .sym "a"), ("x", .sym "b")] := rfl

theorem repeated_slot_fails_linearity_admission : ¬ LeftLinear [nonlinear] := by
  simp [LeftLinear, nonlinear, patternVarsList, patternVars]

private def activePrimitive : Host := ⟨fun head _ =>
  if head = "GuestApp" then .value (.sym "changed") else .unhandled⟩

theorem primitive_collision_changes_the_value :
    eval [] activePrimitive 3 [] guestData = .value (.sym "changed") := rfl

theorem primitive_collision_is_not_passive : ¬ PassiveData [] activePrimitive guestData := by
  intro data
  cases data with
  | node _ _ unhandled _ => contradiction

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataControls
