import Mettapedia.Languages.Maude.PeanoNormalizationPaths

/-! A positive polynomial weight for the authored Peano equations. Every
forward equation step, including steps in typed contexts, strictly lowers
the weight. This proves termination of all oriented strategies. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Maude.PeanoNormalization

open PeanoEquationRules

private def finishWeight (id : String) (arguments : List Nat) : Nat :=
  match id, arguments with
  | "peano.zero", [] => 1
  | "peano.succ", [value] => value + 1
  | "peano.add", [left, right] => 2 * left + right + 1
  | "peano.mul", [left, right] => (2 * right + 2) * (left + 1)
  | _, _ => arguments.sum + 1

def weight : Term → Nat
  | .var _ => 1
  | .app id arguments => finishWeight id (arguments.map weight)

theorem weight_zero : weight (.app "peano.zero" []) = 1 := by rw [weight]; rfl
theorem weight_succ (term : Term) : weight (.app "peano.succ" [term]) = weight term + 1 := by rw [weight]; rfl
theorem weight_add (left right : Term) :
    weight (.app "peano.add" [left, right]) = 2 * weight left + weight right + 1 := by rw [weight]; rfl
theorem weight_multiply (left right : Term) :
    weight (.app "peano.mul" [left, right]) = (2 * weight right + 2) * (weight left + 1) := by rw [weight]; rfl

theorem row_weight_decreases {row : Row} (declared : row ∈ Examples.peano.equations) (assignment : Valuation) :
    weight (row.right.substitute assignment) < weight (row.left.substitute assignment) := by
  simp only [Examples.peano, List.mem_cons, List.not_mem_nil, or_false] at declared
  rcases declared with rfl | rfl | rfl | rfl
  all_goals
    simp only [Examples.binary, Examples.constant, Examples.n, Examples.m, Examples.numeral,
      Term.substitute, List.map_cons, List.map_nil, String.reduceAppend,
      weight_zero, weight_succ, weight_add, weight_multiply, Nat.mul_add, Nat.mul_one]
    omega

private theorem frame_lengths {context : VariableContext} {hole sort : String}
    (frame : ArgumentContext Examples.peano.signature context hole sort) :
    frame.before.length + 1 + frame.after.length = frame.declaration.arguments.length := by
  have sorts := congrArg List.length frame.argumentSorts
  have before := frame.beforeTyped.length_eq
  have after := frame.afterTyped.length_eq
  simp only [List.length_append, List.length_cons] at sorts
  omega

private theorem unary_frame_decreases {context : VariableContext} {hole sort : String}
    (frame : ArgumentContext Examples.peano.signature context hole sort) (id : String)
    (label : frame.declaration.id = id) (arity : frame.declaration.arguments.length = 1)
    {source target : Term}
    (strict : weight (.app id [target]) < weight (.app id [source])) :
    weight (frame.plug target) < weight (frame.plug source) := by
  have sizes := frame_lengths frame
  rw [arity] at sizes
  have before : frame.before = [] := List.length_eq_zero_iff.mp (by omega)
  have after : frame.after = [] := List.length_eq_zero_iff.mp (by omega)
  simpa only [ArgumentContext.plug, before, after, List.nil_append, label] using strict

private theorem binary_frame_decreases {context : VariableContext} {hole sort : String}
    (frame : ArgumentContext Examples.peano.signature context hole sort) (id : String)
    (label : frame.declaration.id = id) (arity : frame.declaration.arguments.length = 2)
    {source target : Term}
    (first : ∀ other, weight (.app id [target, other]) < weight (.app id [source, other]))
    (second : ∀ other, weight (.app id [other, target]) < weight (.app id [other, source])) :
    weight (frame.plug target) < weight (frame.plug source) := by
  have sizes := frame_lengths frame
  rw [arity] at sizes
  by_cases empty : frame.before = []
  · have length : frame.after.length = 1 := by simp only [empty, List.length_nil] at sizes; omega
    obtain ⟨other, after⟩ := List.length_eq_one_iff.mp length
    simpa only [ArgumentContext.plug, empty, after, List.nil_append, label] using first other
  · have positive : 0 < frame.before.length := List.length_pos_iff.mpr empty
    have length : frame.before.length = 1 := by omega
    obtain ⟨other, before⟩ := List.length_eq_one_iff.mp length
    have after : frame.after = [] := List.length_eq_zero_iff.mp (by omega)
    simpa only [ArgumentContext.plug, before, after, List.cons_append, List.nil_append, label] using second other

theorem frame_weight_decreases {context : VariableContext} {hole sort : String}
    (frame : ArgumentContext Examples.peano.signature context hole sort) {source target : Term}
    (smaller : weight target < weight source) : weight (frame.plug target) < weight (frame.plug source) := by
  rcases operators frame.declared with same | same | same | same
  · have sizes := frame_lengths frame
    rw [same] at sizes
    simp only [zeroOperator, List.length_nil] at sizes
    omega
  · apply unary_frame_decreases frame "peano.succ" (congrArg Operator.id same)
      (by rw [same]; rfl)
    simp only [weight_succ]
    omega
  · apply binary_frame_decreases frame "peano.add" (congrArg Operator.id same)
      (by rw [same]; rfl)
    · intro other
      simp only [weight_add]
      omega
    · intro other
      simp only [weight_add]
      omega
  · apply binary_frame_decreases frame "peano.mul" (congrArg Operator.id same)
      (by rw [same]; rfl)
    · intro other
      simp only [weight_multiply]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    · intro other
      simp only [weight_multiply]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)

theorem step_weight_decreases {context : VariableContext} {sort : String} {source target : Term}
    (step : EquationReduction Examples.peano context sort source target) : weight target < weight source := by
  induction step with
  | root assignment declared _ _ _ _ _ => exact row_weight_decreases declared assignment
  | argument frame _ ih => exact frame_weight_decreases frame ih

theorem oriented_wellFounded (context : VariableContext) (sort : String) :
    WellFounded (fun target source => EquationReduction Examples.peano context sort source target) :=
  Subrelation.wf (fun {_ _} step => step_weight_decreases step) (measure weight).wf

theorem path_weight_le {context : VariableContext} {sort : String} {source target : Term}
    (path : EquationPath Examples.peano context sort source target) : weight target ≤ weight source := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact Nat.le_trans (Nat.le_of_lt (step_weight_decreases step)) ih

theorem reduce_no_step {context : VariableContext} {term target : Term}
    (typed : HasSort Examples.peano.signature context term "Nat") :
    ¬ EquationReduction Examples.peano context "Nat" (reduce term) target := by
  intro step
  have smaller := step_weight_decreases step
  have targetTyped := step.sorted.2
  have same := equivalent_same_reduce step.equivalent
  rw [reduce_idempotent typed] at same
  have returns := reduce_path context target targetTyped
  rw [← same] at returns
  have bounded := path_weight_le returns
  omega

/-- Every completed forward strategy has the same result. Pending paths
need not have reached that result. -/
theorem normal_result_unique {context : VariableContext} {source target : Term}
    (typed : HasSort Examples.peano.signature context source "Nat")
    (path : EquationPath Examples.peano context "Nat" source target)
    (normal : ∀ next, ¬ EquationReduction Examples.peano context "Nat" target next) :
    target = reduce source := by
  have targetTyped := (path.equivalent typed).sorted.2
  have remaining := reduce_path context target targetTyped
  have fixed := (Relation.reflTransGen_iff_eq normal).mp remaining
  exact fixed.symm.trans (path_same_reduce typed path).symm

end Mettapedia.Languages.Maude.PeanoNormalization
