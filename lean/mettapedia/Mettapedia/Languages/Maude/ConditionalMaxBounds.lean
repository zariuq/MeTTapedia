import Mettapedia.Languages.Maude.ConditionalMax

/-! Input-derived bounds for the finite equality snapshot. The source
module never creates a successor constructor in a forward equation step.
The bound is a property of the actual input, not a fixed example cutoff.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ConditionalMax

mutual
  def successorCount : Term → Nat
    | .var _ => 0
    | .app label arguments => (if label = "max.succ" then 1 else 0) + argumentCount arguments

  def argumentCount : List Term → Nat
    | [] => 0
    | first :: rest => successorCount first + argumentCount rest
end

theorem count_numeral (value : Nat) : successorCount (numeral value) = value := by
  induction value with
  | zero => simp [numeral, Examples.numeral, Examples.constant, successorCount, argumentCount]
  | succ value ih =>
    simpa only [numeral, Examples.numeral, String.reduceAppend, successorCount, argumentCount,
      if_true, Nat.add_zero, Nat.add_comm 1] using congrArg Nat.succ ih

theorem context_count {context : VariableContext} {hole result : String}
    (frame : ArgumentContext Examples.conditional.signature context hole result) (term : Term) :
    successorCount (frame.plug term) = (if frame.declaration.id = "max.succ" then 1 else 0) +
      argumentCount frame.before + successorCount term + argumentCount frame.after := by
  have append : ∀ left right, argumentCount (left ++ right) = argumentCount left + argumentCount right := by
    intro left right
    induction left with
    | nil => simp only [List.nil_append, argumentCount, Nat.zero_add]
    | cons first rest ih => simp only [List.cons_append, argumentCount, ih, Nat.add_assoc]
  simp only [ArgumentContext.plug, successorCount, append, argumentCount, Nat.add_assoc]

theorem equation_count {row : Row} (member : row ∈ Examples.conditional.equations) (assignment : Valuation) :
    successorCount (row.right.substitute assignment) ≤ successorCount (row.left.substitute assignment) := by
  simp only [Examples.conditional, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [Examples.binary, Examples.constant, Examples.numeral, Examples.n, Examples.m,
      Term.substitute, successorCount, argumentCount]
    <;> omega

theorem equationReduction_count {context : VariableContext} {sort : String} {source target : Term}
    (step : EquationReduction Examples.conditional context sort source target) :
    successorCount target ≤ successorCount source := by
  induction step with
  | root assignment member _ _ _ _ _ => exact equation_count member assignment
  | argument frame _ ih =>
    rw [context_count, context_count]
    omega

theorem equationPath_count {context : VariableContext} {sort : String} {source target : Term}
    (path : EquationPath Examples.conditional context sort source target) :
    successorCount target ≤ successorCount source := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact Nat.le_trans (equationReduction_count step) ih

theorem argument_bounded (label : String) (arguments : List Term) {term : Term}
    (member : term ∈ arguments) : successorCount term ≤ successorCount (.app label arguments) := by
  have inside : successorCount term ≤ argumentCount arguments := by
    induction arguments with
    | nil => cases member
    | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp only [argumentCount]
        omega
      · have bound := ih later
        simp only [argumentCount]
        omega
  simp only [successorCount]
  omega

#print axioms equationPath_count

end Mettapedia.Languages.Maude.ConditionalMax
