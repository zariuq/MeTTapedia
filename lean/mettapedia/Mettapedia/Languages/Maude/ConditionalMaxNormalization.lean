import Mettapedia.Languages.Maude.ConditionalMaxInterpretation

/-! Ground normalization and Church–Rosser evidence for the conditional
max theory. These paths use forward authored equations in typed contexts;
the independent interpretation supplies uniqueness of the result.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace Mettapedia.Languages.Maude.ConditionalMax

theorem comparison_path (left right : Nat) : EquationPath Examples.conditional [] "Bool"
    (le (numeral left) (numeral right)) (if left ≤ right then truth else falsehood) := by
  induction left generalizing right with
  | zero =>
    simpa only [Nat.zero_le, if_true] using Relation.ReflTransGen.single (le_zero_step right)
  | succ left ih =>
    cases right with
    | zero =>
      have unordered : ¬left + 1 ≤ 0 := by omega
      simpa only [if_neg unordered] using Relation.ReflTransGen.single (le_succ_zero_step left)
    | succ right =>
      simpa only [Nat.succ_le_succ_iff] using
        (Relation.ReflTransGen.single (le_succ_succ_step left right)).trans (ih right)

theorem maximum_path (left right : Nat) : EquationPath Examples.conditional [] "Nat"
    (maximum (numeral left) (numeral right)) (numeral (max left right)) := by
  by_cases ordered : right ≤ left
  · simpa only [Nat.max_eq_left ordered] using Relation.ReflTransGen.single (maximum_left_step left right ordered)
  · have other : left ≤ right := by omega
    simpa only [Nat.max_eq_right other] using Relation.ReflTransGen.single (maximum_right_step left right other)

def comparisonLeftFrame (right : Term) (typed : HasSort Examples.conditional.signature [] right "Nat") :
    ArgumentContext Examples.conditional.signature [] "Nat" "Bool" :=
  ⟨leOperator, le_member, [], ["Nat"], [], [right], rfl, rfl, .nil, .cons typed .nil⟩

def comparisonRightFrame (left : Term) (typed : HasSort Examples.conditional.signature [] left "Nat") :
    ArgumentContext Examples.conditional.signature [] "Nat" "Bool" :=
  ⟨leOperator, le_member, ["Nat"], [], [left], [], rfl, rfl, .cons typed .nil, .nil⟩

def represent : SemanticValue → Term
  | .natural value => numeral value
  | .boolean value => if value then truth else falsehood

theorem fits_boolean_iff (value : Option SemanticValue) :
    FitsSort value "Bool" ↔ ∃ boolean, value = some (.boolean boolean) := by
  cases value with
  | none => simp [FitsSort]
  | some value => cases value <;> simp [FitsSort]

theorem interpret_represent (value : SemanticValue) :
    interpret closedAssignment (represent value) = some value := by
  cases value with
  | natural value => exact interpret_numeral closedAssignment value
  | boolean value => cases value <;>
      simp only [represent, Bool.false_eq_true, if_false, if_true,
        truth, falsehood, interpret, List.map_nil, finishValue]

theorem normalize_path (source : Term) (sort : String)
    (typed : HasSort Examples.conditional.signature [] source sort) :
    ∃ value, interpret closedAssignment source = some value ∧
      EquationPath Examples.conditional [] sort source (represent value) := by
  refine HasSort.rec
    (motive_1 := fun source sort _ => ∃ value, interpret closedAssignment source = some value ∧
      EquationPath Examples.conditional [] sort source (represent value))
    (motive_2 := fun sources sorts _ => List.Forall₂ (fun source sort => ∃ value,
      interpret closedAssignment source = some value ∧
        EquationPath Examples.conditional [] sort source (represent value)) sources sorts)
    ?_ ?_ ?_ ?_ typed
  · intro name sort impossible
    cases impossible
  · intro declaration arguments member argumentsTyped ih
    rcases operators member with rfl | rfl | rfl | rfl | rfl | rfl
    · cases ih
      exact ⟨.natural 0, by simp only [zeroOperator, interpret, List.map_nil, finishValue], .refl⟩
    · cases argumentsTyped with
      | @cons child _ _ _ childTyped rest =>
        cases rest
        cases ih with
        | cons childIH tail =>
          obtain ⟨value, observed, path⟩ := childIH
          obtain ⟨number, numberSame⟩ := (fits_natural_iff _).mp
            (interpret_sorted closedAssignment_sorted childTyped)
          rw [observed] at numberSame
          cases Option.some.inj numberSame
          refine ⟨.natural (number + 1), ?_, ?_⟩
          · simp only [successorOperator, interpret, List.map_cons, List.map_nil, observed, finishValue]
          · simpa only [successorOperator, successorFrame, ArgumentContext.plug,
              List.nil_append, represent, numeral, Examples.numeral, String.reduceAppend] using
              path.inArgument successorFrame
    · cases ih
      exact ⟨.boolean true, by simp only [trueOperator, interpret, List.map_nil, finishValue], .refl⟩
    · cases ih
      exact ⟨.boolean false, by simp only [falseOperator, interpret, List.map_nil, finishValue], .refl⟩
    · cases argumentsTyped with
      | @cons left _ _ _ leftTyped tail =>
        cases tail with
        | @cons right _ _ _ rightTyped last =>
          cases last
          cases ih with
          | cons firstIH rest =>
            cases rest with
            | cons secondIH _ =>
              obtain ⟨first, firstObserved, firstPath⟩ := firstIH
              obtain ⟨second, secondObserved, secondPath⟩ := secondIH
              obtain ⟨leftValue, leftSame⟩ := (fits_natural_iff _).mp
                (interpret_sorted closedAssignment_sorted leftTyped)
              obtain ⟨rightValue, rightSame⟩ := (fits_natural_iff _).mp
                (interpret_sorted closedAssignment_sorted rightTyped)
              rw [firstObserved] at leftSame
              rw [secondObserved] at rightSame
              cases Option.some.inj leftSame
              cases Option.some.inj rightSame
              refine ⟨.boolean (decide (leftValue ≤ rightValue)), ?_, ?_⟩
              · simp only [leOperator, interpret, List.map_cons, List.map_nil,
                  firstObserved, secondObserved, finishValue]
              · have firstPlaced := firstPath.inArgument (comparisonLeftFrame right rightTyped)
                have secondPlaced := secondPath.inArgument (comparisonRightFrame (numeral leftValue)
                  (numeral_sorted [] leftValue))
                have finished := comparison_path leftValue rightValue
                simpa only [leOperator, comparisonLeftFrame, comparisonRightFrame, ArgumentContext.plug,
                  List.nil_append, represent, decide_eq_true_eq] using
                  firstPlaced.trans (secondPlaced.trans finished)
    · cases argumentsTyped with
      | @cons left _ _ _ leftTyped tail =>
        cases tail with
        | @cons right _ _ _ rightTyped last =>
          cases last
          cases ih with
          | cons firstIH rest =>
            cases rest with
            | cons secondIH _ =>
              obtain ⟨first, firstObserved, firstPath⟩ := firstIH
              obtain ⟨second, secondObserved, secondPath⟩ := secondIH
              obtain ⟨leftValue, leftSame⟩ := (fits_natural_iff _).mp
                (interpret_sorted closedAssignment_sorted leftTyped)
              obtain ⟨rightValue, rightSame⟩ := (fits_natural_iff _).mp
                (interpret_sorted closedAssignment_sorted rightTyped)
              rw [firstObserved] at leftSame
              rw [secondObserved] at rightSame
              cases Option.some.inj leftSame
              cases Option.some.inj rightSame
              refine ⟨.natural (max leftValue rightValue), ?_, ?_⟩
              · simp only [maxOperator, interpret, List.map_cons, List.map_nil,
                  firstObserved, secondObserved, finishValue]
              · have firstPlaced := firstPath.inArgument (maxLeftFrame right rightTyped)
                have secondPlaced := secondPath.inArgument (maxRightFrame (numeral leftValue)
                  (numeral_sorted [] leftValue))
                simpa only [maxOperator, maxLeftFrame, maxRightFrame, ArgumentContext.plug,
                  List.nil_append, represent] using
                  firstPlaced.trans (secondPlaced.trans (maximum_path leftValue rightValue))
  · exact .nil
  · intro first sort rest sorts _ _ firstIH restIH
    exact .cons firstIH restIH

theorem equivalent_iff_interpretation_eq {source target : Term} {sort : String}
    (sourceTyped : HasSort Examples.conditional.signature [] source sort)
    (targetTyped : HasSort Examples.conditional.signature [] target sort) :
    Equivalent Examples.conditional [] sort source target ↔
      interpret closedAssignment source = interpret closedAssignment target := by
  constructor
  · intro equivalent
    exact equivalent_same_interpretation equivalent closedAssignment closedAssignment_sorted
  · intro same
    obtain ⟨first, firstObserved, firstPath⟩ := normalize_path source sort sourceTyped
    obtain ⟨second, secondObserved, secondPath⟩ := normalize_path target sort targetTyped
    rw [firstObserved, secondObserved] at same
    cases Option.some.inj same
    exact .trans (firstPath.equivalent sourceTyped) (secondPath.equivalent targetTyped).symm

theorem paths_join {source left right : Term} {sort : String}
    (typed : HasSort Examples.conditional.signature [] source sort)
    (first : EquationPath Examples.conditional [] sort source left)
    (second : EquationPath Examples.conditional [] sort source right) :
    ∃ joined, EquationPath Examples.conditional [] sort left joined ∧
      EquationPath Examples.conditional [] sort right joined := by
  have leftMeaning := first.equivalent typed
  have rightMeaning := second.equivalent typed
  obtain ⟨firstValue, firstObserved, firstPath⟩ := normalize_path left sort leftMeaning.sorted.2
  obtain ⟨secondValue, secondObserved, secondPath⟩ := normalize_path right sort rightMeaning.sorted.2
  have same := equivalent_same_interpretation (.trans leftMeaning.symm rightMeaning)
    closedAssignment closedAssignment_sorted
  rw [firstObserved, secondObserved] at same
  cases Option.some.inj same
  exact ⟨represent firstValue, firstPath, secondPath⟩

theorem closed_value_total {source : Term}
    (typed : HasSort Examples.conditional.signature [] source "Nat") :
    ∃ value, value? source = some value := by
  have observed : interpret closedAssignment source = (SemanticValue.natural <$> value? source) := by
    revert typed
    refine Term.rec
      (motive_1 := fun source => HasSort Examples.conditional.signature [] source "Nat" →
        interpret closedAssignment source = (SemanticValue.natural <$> value? source))
      (motive_2 := fun sources => ∀ source ∈ sources,
        HasSort Examples.conditional.signature [] source "Nat" →
        interpret closedAssignment source = (SemanticValue.natural <$> value? source))
      ?_ ?_ ?_ ?_ source
    · intro name impossible
      cases impossible with
      | var found => cases found
    · intro label arguments children typed
      obtain ⟨declaration, member, labelSame, sortSame, argumentsTyped⟩ := HasSort.operator_arguments typed rfl
      rcases operators member with rfl | rfl | rfl | rfl | rfl | rfl
      · subst label
        cases argumentsTyped
        simp only [zeroOperator, interpret, List.map_nil, finishValue, value?]
        change some (.natural 0) = Option.map SemanticValue.natural (some 0)
        rw [Option.map_some]
      · subst label
        cases argumentsTyped with
        | @cons child _ _ _ childTyped rest =>
          cases rest
          have childSame := children child List.mem_cons_self childTyped
          simp only [successorOperator, interpret, List.map_cons, List.map_nil, childSame, value?]
          cases value? child <;> rfl
      · simp [trueOperator] at sortSame
      · simp [falseOperator] at sortSame
      · simp [leOperator] at sortSame
      · subst label
        cases argumentsTyped with
        | @cons left _ _ _ leftTyped rest =>
          cases rest with
          | @cons right _ _ _ rightTyped tail =>
            cases tail
            have leftSame := children left List.mem_cons_self leftTyped
            have rightSame := children right (by simp) rightTyped
            simp only [maxOperator, interpret, List.map_cons, List.map_nil, leftSame, rightSame, value?]
            cases value? left <;> cases value? right <;> rfl
    · intro source impossible
      cases impossible
    · intro first rest firstIH restIH actual member typed
      rcases List.mem_cons.mp member with rfl | member
      · exact firstIH typed
      · exact restIH actual member typed
  obtain ⟨value, same⟩ := (fits_natural_iff _).mp (interpret_sorted closedAssignment_sorted typed)
  rw [observed] at same
  obtain ⟨actual, actualObserved, _⟩ := Option.map_eq_some_iff.mp same
  exact ⟨actual, actualObserved⟩

#print axioms normalize_path
#print axioms equivalent_iff_interpretation_eq
#print axioms paths_join
#print axioms closed_value_total

end Mettapedia.Languages.Maude.ConditionalMax
