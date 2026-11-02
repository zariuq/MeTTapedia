import Mettapedia.Languages.OCaml.ComparisonLaws

/-! Structural comparison can refuse malformed pairs, return an order or
raise functional comparison. It cannot manufacture another source fault.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.OCaml

inductive ComparisonOutcome : Compared → Prop where
  | refused (error : InternalError) : ComparisonOutcome (.error error)
  | functional : ComparisonOutcome (.ok (.error .functionalComparison))
  | ordered (order : Ordering) : ComparisonOutcome (.ok (.ok order))

theorem continue_outcome (first later : Compared) (one : ComparisonOutcome first) (two : ComparisonOutcome later) :
    ComparisonOutcome (continueCompared first later) := by
  cases one with
  | refused error => exact .refused error
  | functional => exact .functional
  | ordered order =>
    cases order with
    | lt => exact .ordered .lt
    | eq => exact two
    | gt => exact .ordered .gt

theorem comparison_outcome (left right : Value) : ComparisonOutcome (compareValue left right) := by
  revert right
  refine Value.rec
    (motive_1 := fun left => ∀ right, ComparisonOutcome (compareValue left right))
    (motive_2 := fun left => ∀ right, ComparisonOutcome (compareFields left right))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro datum right
    cases right with
    | literal other =>
      cases datum <;> cases other <;> simp only [compareValue] <;>
        first | exact .ordered _ | exact .refused _
    | tuple fields => cases datum <;> simp only [compareValue] <;> exact .refused _
    | cons head tail => cases datum <;> simp only [compareValue] <;> first | exact .ordered _ | exact .refused _
    | variant typeId constructor fields => cases datum <;> simp only [compareValue] <;> exact .refused _
    | closure function captured => rw [compare_closure_right]; exact .functional
  · intro fields ih right
    cases right with
    | literal datum => cases datum <;> simp only [compareValue] <;> exact .refused _
    | tuple other =>
      rw [compare_tuple]
      split_ifs
      · exact ih other
      · exact .refused _
    | cons head tail => simp only [compareValue]; exact .refused _
    | variant typeId constructor other => simp only [compareValue]; exact .refused _
    | closure function captured => rw [compare_closure_right]; exact .functional
  · intro head tail first later right
    cases right with
    | literal datum => cases datum <;> simp only [compareValue] <;> first | exact .ordered _ | exact .refused _
    | tuple fields => simp only [compareValue]; exact .refused _
    | cons other rest => rw [compare_cons]; exact continue_outcome _ _ (first other) (later rest)
    | variant typeId constructor fields => simp only [compareValue]; exact .refused _
    | closure function captured => rw [compare_closure_right]; exact .functional
  · intro typeId constructor fields ih right
    cases right with
    | literal datum => cases datum <;> simp only [compareValue] <;> exact .refused _
    | tuple other => simp only [compareValue]; exact .refused _
    | cons head tail => simp only [compareValue]; exact .refused _
    | variant otherType otherConstructor other =>
      rw [compare_variant]
      split_ifs <;> first | exact ih _ | exact .ordered _ | exact .refused _
    | closure function captured => rw [compare_closure_right]; exact .functional
  · intro function captured _ right
    rw [compare_closure_left]
    exact .functional
  · intro right
    cases right <;> simp only [compareFields] <;> exact .ordered _
  · intro head tail first later right
    cases right with
    | nil => simp only [compareFields]; exact .ordered _
    | cons other rest => rw [compare_fields_cons]; exact continue_outcome _ _ (first other) (later rest)

theorem fields_comparison_outcome (left right : List Value) : ComparisonOutcome (compareFields left right) := by
  induction left generalizing right with
  | nil => cases right <;> rw [compareFields] <;> exact .ordered _
  | cons head tail ih =>
    cases right with
    | nil => rw [compareFields]; exact .ordered _
    | cons other rest => rw [compare_fields_cons]; exact continue_outcome _ _ (comparison_outcome head other) (ih rest)

theorem comparison_fault_functional (left right : Value) (fault : Fault)
    (raised : compareValue left right = .ok (.error fault)) : fault = .functionalComparison := by
  have allowed := comparison_outcome left right
  rw [raised] at allowed
  cases allowed
  rfl

theorem fields_fault_functional (left right : List Value) (fault : Fault)
    (raised : compareFields left right = .ok (.error fault)) : fault = .functionalComparison := by
  have allowed := fields_comparison_outcome left right
  rw [raised] at allowed
  cases allowed
  rfl

#print axioms continue_outcome
#print axioms comparison_outcome

end Mettapedia.Languages.OCaml
