import Mettapedia.Languages.Maude.ConditionalMaxNormalization

/-! Every oriented equation of the conditional max theory strictly
decreases constructor size. Together with ground normalization, this gives
termination and a unique completed result for every closed typed input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ConditionalMax

mutual
  def nodeCount : Term → Nat
    | .var _ => 1
    | .app _ arguments => 1 + nodeListCount arguments

  def nodeListCount : List Term → Nat
    | [] => 0
    | first :: rest => nodeCount first + nodeListCount rest
end

theorem nodeCount_positive (source : Term) : 0 < nodeCount source := by
  cases source <;> simp only [nodeCount] <;> omega

theorem nodeListCount_append (first second : List Term) :
    nodeListCount (first ++ second) = nodeListCount first + nodeListCount second := by
  induction first with
  | nil => simp only [List.nil_append, nodeListCount, Nat.zero_add]
  | cons first rest ih => simp only [List.cons_append, nodeListCount, ih, Nat.add_assoc]

theorem context_nodeCount {context : VariableContext} {hole result : String}
    (frame : ArgumentContext Examples.conditional.signature context hole result) (source : Term) :
    nodeCount (frame.plug source) = 1 + nodeListCount frame.before + nodeCount source + nodeListCount frame.after := by
  simp only [ArgumentContext.plug, nodeCount, nodeListCount_append, nodeListCount, Nat.add_assoc]

theorem row_nodeCount_decreases {row : Row} (member : row ∈ Examples.conditional.equations)
    (assignment : Valuation) : nodeCount (row.right.substitute assignment) < nodeCount (row.left.substitute assignment) := by
  simp only [Examples.conditional, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Examples.binary, Examples.constant, Examples.n, Examples.m, Examples.numeral,
      Term.substitute, List.map_cons, List.map_nil, String.reduceAppend, nodeCount, nodeListCount]
    omega

theorem step_nodeCount_decreases {context : VariableContext} {sort : String} {source target : Term}
    (step : EquationReduction Examples.conditional context sort source target) : nodeCount target < nodeCount source := by
  induction step with
  | root assignment member _ _ _ _ _ => exact row_nodeCount_decreases member assignment
  | argument frame _ ih =>
    rw [context_nodeCount, context_nodeCount]
    omega

theorem oriented_wellFounded (context : VariableContext) (sort : String) :
    WellFounded (fun target source => EquationReduction Examples.conditional context sort source target) :=
  Subrelation.wf (fun {_ _} step => step_nodeCount_decreases step) (measure nodeCount).wf

theorem normal_result {source target : Term} {sort : String}
    (typed : HasSort Examples.conditional.signature [] source sort)
    (path : EquationPath Examples.conditional [] sort source target)
    (normal : ∀ next, ¬ EquationReduction Examples.conditional [] sort target next) :
    ∃ value, interpret closedAssignment source = some value ∧ target = represent value := by
  have targetTyped := (path.equivalent typed).sorted.2
  obtain ⟨value, observed, remaining⟩ := normalize_path target sort targetTyped
  have fixed := (Relation.reflTransGen_iff_eq normal).mp remaining
  refine ⟨value, ?_, fixed.symm⟩
  have same := equivalent_same_interpretation (path.equivalent typed) closedAssignment closedAssignment_sorted
  exact same.trans observed

theorem normal_results_equal {source first second : Term} {sort : String}
    (typed : HasSort Examples.conditional.signature [] source sort)
    (firstPath : EquationPath Examples.conditional [] sort source first)
    (secondPath : EquationPath Examples.conditional [] sort source second)
    (firstNormal : ∀ next, ¬ EquationReduction Examples.conditional [] sort first next)
    (secondNormal : ∀ next, ¬ EquationReduction Examples.conditional [] sort second next) : first = second := by
  obtain ⟨firstValue, firstObserved, firstSame⟩ := normal_result typed firstPath firstNormal
  obtain ⟨secondValue, secondObserved, secondSame⟩ := normal_result typed secondPath secondNormal
  have same : firstValue = secondValue := Option.some.inj (firstObserved.symm.trans secondObserved)
  exact firstSame.trans ((congrArg represent same).trans secondSame.symm)

#guard nodeCount (maximum (numeral 2) (numeral 1)) = 6
#guard nodeCount (numeral 2) = 3

#print axioms oriented_wellFounded
#print axioms normal_result
#print axioms normal_results_equal

end Mettapedia.Languages.Maude.ConditionalMax
