import Mettapedia.Languages.Maude.ConditionalMaxBoolPrelude

/-! Soundness of the actual Boolean-ring prelude and its constructor-equality
hooks in the Nat/Bool model. Conditional user equations are checked with
premises from the enlarged theory, including Boolean contexts. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude

theorem evaluate_local {context : VariableContext} {source : Term} {sort : String}
    (typed : HasSort Examples.conditional.signature context source sort)
    (assignment : String → Option Value) : evaluate assignment source = interpret assignment source := by
  refine HasSort.rec
    (motive_1 := fun source _ _ => evaluate assignment source = interpret assignment source)
    (motive_2 := fun sources _ _ => sources.map (evaluate assignment) = sources.map (interpret assignment))
    ?_ ?_ ?_ ?_ typed
  · intro name _ _
    simp only [evaluate_var, interpret]
  · intro declaration arguments member _ ih
    rw [evaluate_app, interpret]
    change finish declaration.id (arguments.map (evaluate assignment)) =
      finishValue declaration.id (arguments.map (interpret assignment))
    rw [ih]
    rcases operators member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl
  · intro first _ rest _ _ _ firstIH restIH
    simp only [List.map_cons, firstIH, restIH]

theorem original_rows_sound (row : Row) (member : row ∈ Examples.conditional.equations)
    (assignment : String → Option Value) (assigned : Assigned row.usedContext assignment)
    (conditions : ∀ condition ∈ row.conditions,
      evaluate assignment condition.left = evaluate assignment condition.right) :
    evaluate assignment row.left = evaluate assignment row.right := by
  have same : evaluate assignment row.left = interpret assignment row.left ∧
      evaluate assignment row.right = interpret assignment row.right ∧
      ∀ condition ∈ row.conditions,
        evaluate assignment condition.left = interpret assignment condition.left ∧
        evaluate assignment condition.right = interpret assignment condition.right := by
    simp only [Examples.conditional, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [Examples.binary, Examples.constant, Examples.numeral, Examples.n, Examples.m,
        evaluate_app, evaluate_var, interpret, List.map_cons, List.map_nil, String.reduceAppend, finish,
        List.not_mem_nil]
  rw [same.1, same.2.1]
  apply interpret_row member assignment assigned
  intro condition inside
  rw [← (same.2.2 condition inside).1, ← (same.2.2 condition inside).2]
  exact conditions condition inside

theorem boolean_rows_sound (row : Row) (member : row ∈ booleanRows)
    (assignment : String → Option Value) (assigned : Assigned row.usedContext assignment) :
    evaluate assignment row.left = evaluate assignment row.right := by
  have boolValue (name : String) (found : row.usedContext.lookup name = some "Bool") :
      ∃ value, assignment name = some (.boolean value) :=
    (fits_boolean_iff _).mp (assigned name "Bool" found)
  simp only [booleanRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    cases vA <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    cases vA <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    cases vA <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    cases vA <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    cases vA <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    obtain ⟨vB, hB⟩ := boolValue "B" (by decide_cbv)
    obtain ⟨vC, hC⟩ := boolValue "C" (by decide_cbv)
    cases vA <;> cases vB <;> cases vC <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA, hB, hC]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    cases vA <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    obtain ⟨vB, hB⟩ := boolValue "B" (by decide_cbv)
    cases vA <;> cases vB <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA, hB]; rfl
  · obtain ⟨vA, hA⟩ := boolValue "A" (by decide_cbv)
    obtain ⟨vB, hB⟩ := boolValue "B" (by decide_cbv)
    cases vA <;> cases vB <;>
      dsimp only [a, b, c, and, xor, not, binary, unary, truth, falsehood]
    all_goals simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, hA, hB]; rfl

theorem branch_rows_sound (sort : String) (known : sort = "Nat" ∨ sort = "Bool")
    (row : Row) (member : row ∈ branchRows sort)
    (assignment : String → Option Value) (assigned : Assigned row.usedContext assignment) :
    evaluate assignment row.left = evaluate assignment row.right := by
  simp only [branchRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases known with rfl | rfl
  all_goals rcases member with rfl | rfl
  · obtain ⟨first, firstSame⟩ := (fits_natural_iff _).mp (assigned "A" "Nat" (by decide_cbv))
    obtain ⟨second, secondSame⟩ := (fits_natural_iff _).mp (assigned "B" "Nat" (by decide_cbv))
    dsimp only [a, b, branch, truth, falsehood]
    simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, firstSame, secondSame]; rfl
  · obtain ⟨first, firstSame⟩ := (fits_natural_iff _).mp (assigned "A" "Nat" (by decide_cbv))
    obtain ⟨second, secondSame⟩ := (fits_natural_iff _).mp (assigned "B" "Nat" (by decide_cbv))
    dsimp only [a, b, branch, truth, falsehood]
    simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, firstSame, secondSame]; rfl
  · obtain ⟨first, firstSame⟩ := (fits_boolean_iff _).mp (assigned "A" "Bool" (by decide_cbv))
    obtain ⟨second, secondSame⟩ := (fits_boolean_iff _).mp (assigned "B" "Bool" (by decide_cbv))
    dsimp only [a, b, branch, truth, falsehood]
    simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, firstSame, secondSame]; rfl
  · obtain ⟨first, firstSame⟩ := (fits_boolean_iff _).mp (assigned "A" "Bool" (by decide_cbv))
    obtain ⟨second, secondSame⟩ := (fits_boolean_iff _).mp (assigned "B" "Bool" (by decide_cbv))
    dsimp only [a, b, branch, truth, falsehood]
    simp only [evaluate_app, evaluate_var, List.map_cons, List.map_nil, firstSame, secondSame]; rfl

end Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude
