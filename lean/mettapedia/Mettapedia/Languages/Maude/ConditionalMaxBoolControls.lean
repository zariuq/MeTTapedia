import Mettapedia.Languages.Maude.ConditionalMaxBoolConservativity

/-! Separating controls for imported Boolean contexts, actual equality hooks,
and sorting. The positive examples use operations outside the retained
runtime signature; the negatives are statements about the whole import. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude

private def andDeclaration := booleanBinary "BOOL.and" "_and_" true
private def equalNatDeclaration : Operator := ⟨"BOOL.eq.Nat", "_==_", ["Nat", "Nat"], "Bool", {}⟩

private theorem and_declared : andDeclaration ∈ signature.operators :=
  List.mem_append_right _ List.mem_cons_self

private theorem equal_nat_declared : equalNatDeclaration ∈ signature.operators := by
  simp [signature, extraOperators, equalNatDeclaration]

theorem boolean_context_commutes : HookedEquivalent theory EqualityHook [] "Bool"
    (and truth falsehood) (and falsehood truth) := by
  have trueTyped := (truth_sorted []).of_operator_subset localEmbedding.operators
  have falseTyped := (falsehood_sorted []).of_operator_subset localEmbedding.operators
  exact .algebra ⟨.commutative and_declared rfl,
    .app and_declared (.cons trueTyped (.cons falseTyped .nil)),
    .app and_declared (.cons falseTyped (.cons trueTyped .nil))⟩

theorem unequal_constructor_hook : HookedEquivalent theory EqualityHook [] "Bool"
    (binary "BOOL.eq.Nat" (numeral 1) (numeral 2)) falsehood := by
  have first := (numeral_sorted [] 1).of_operator_subset localEmbedding.operators
  have second := (numeral_sorted [] 2).of_operator_subset localEmbedding.operators
  have inputTyped : HasSort signature [] (binary "BOOL.eq.Nat" (numeral 1) (numeral 2)) "Bool" :=
    .app (declaration := equalNatDeclaration) equal_nat_declared (.cons first (.cons second .nil))
  exact HookedEquivalent.primitive (theory := theory) (hook := EqualityHook) inputTyped
    ((falsehood_sorted []).of_operator_subset localEmbedding.operators) (.naturalEqual [] 1 2)

theorem ill_sorted_boolean_value : evaluate closedAssignment (and (numeral 0) truth) = none := by
  dsimp only [and, binary, truth]
  simp only [evaluate_app, List.map_cons, List.map_nil, evaluate_numeral]; rfl

theorem ill_sorted_boolean_refused : ¬ HasSort signature [] (and (numeral 0) truth) "Bool" := by
  intro typed
  have assigned : Assigned [] closedAssignment := by
    intro name sort impossible
    cases impossible
  have sorted := interpretation.evaluate_sorted assigned typed
  change FitsSort (evaluate closedAssignment (and (numeral 0) truth)) "Bool" at sorted
  rw [ill_sorted_boolean_value] at sorted
  exact sorted

example : ¬ HookedEquivalent theory EqualityHook [] "Bool" truth falsehood := imported_truth_not_falsehood

example : ¬ HookedEquivalent theory EqualityHook [] "Bool" (le (numeral 2) (numeral 1)) truth := by
  rw [imported_comparison_true_iff]
  omega

#print axioms boolean_context_commutes
#print axioms unequal_constructor_hook
#print axioms ill_sorted_boolean_refused

end Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude
