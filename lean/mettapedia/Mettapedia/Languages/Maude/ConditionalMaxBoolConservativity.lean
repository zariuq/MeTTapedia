import Mettapedia.Languages.Maude.ConditionalMaxBoolHooks
import Mettapedia.Languages.Maude.TheoryEmbedding

/-! BOOL is conservative on all closed, well-sorted terms of the executable
conditional-max signature. The forward implication permits derivations that
leave that signature and use the whole imported conditional relation. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude

theorem localEmbedding : TheoryEmbedding Examples.conditional theory where
  operators declaration member := List.mem_append_left extraOperators member
  equations row member := by
    change row ∈ Examples.conditional.equations ++ booleanRows ++ branchRows "Nat" ++ branchRows "Bool"
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  checked row member _ := by
    simp only [Examples.conditional, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide_cbv

theorem ground_equivalent_iff {source target : Term} {sort : String}
    (sourceTyped : HasSort Examples.conditional.signature [] source sort)
    (targetTyped : HasSort Examples.conditional.signature [] target sort) :
    HookedEquivalent theory EqualityHook [] sort source target ↔
      Equivalent Examples.conditional [] sort source target := by
  constructor
  · intro equivalent
    apply (equivalent_iff_interpretation_eq sourceTyped targetTyped).mpr
    rw [← evaluate_local sourceTyped closedAssignment, ← evaluate_local targetTyped closedAssignment]
    apply equivalent_sound equivalent closedAssignment
    intro name sort impossible
    cases impossible
  · intro equivalent
    exact localEmbedding.equivalent equivalent EqualityHook

theorem imported_comparison_true_iff (first second : Nat) :
    HookedEquivalent theory EqualityHook [] "Bool" (le (numeral first) (numeral second)) truth ↔
      first ≤ second := by
  rw [ground_equivalent_iff (le_sorted (numeral_sorted [] first) (numeral_sorted [] second))
    (truth_sorted []), comparison_true_iff]

theorem imported_numerals_iff (first second : Nat) :
    HookedEquivalent theory EqualityHook [] "Nat" (numeral first) (numeral second) ↔ first = second := by
  rw [ground_equivalent_iff (numeral_sorted [] first) (numeral_sorted [] second), numerals_equivalent_iff]

theorem imported_truth_not_falsehood :
    ¬ HookedEquivalent theory EqualityHook [] "Bool" truth falsehood := by
  rw [ground_equivalent_iff (truth_sorted []) (falsehood_sorted [])]
  exact truth_not_falsehood

theorem canonical_syntax_injective : Function.Injective represent := by
  intro first second same
  apply Option.some.inj
  exact (interpret_represent first).symm.trans
    ((congrArg (interpret closedAssignment) same).trans (interpret_represent second))

example : HookedEquivalent theory EqualityHook [] "Bool" (le (numeral 1) (numeral 2)) truth :=
  (imported_comparison_true_iff 1 2).mpr (by omega)

example : ¬ HookedEquivalent theory EqualityHook [] "Bool" (le (numeral 2) (numeral 1)) truth := by
  rw [imported_comparison_true_iff]
  omega

example : ¬ HookedEquivalent theory EqualityHook [] "Nat" (numeral 1) (numeral 2) := by
  rw [imported_numerals_iff]
  omega

example : theory.check = true := by decide_cbv

#print axioms ground_equivalent_iff
#print axioms imported_comparison_true_iff
#print axioms imported_truth_not_falsehood

end Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude
