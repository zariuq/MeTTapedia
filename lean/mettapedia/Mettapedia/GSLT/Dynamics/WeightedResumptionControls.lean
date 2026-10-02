import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
import Mettapedia.GSLT.Logic.GradedSupport
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul

/-!
# Interpretation boundaries for weighted resumptions

These controls run the direct frontier and the free handler on repeated
successors, zero coefficients and a silent cycle. Numerical coefficients are
not occurrence counts; complex cancellation is not absence of a contributing
history; Pareto objectives need not be comparable; and matrix coefficients
cannot be reordered without a commutation proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WeightedResumptionControls

open WeightedResumption WeightedBranchingResumption

def duplicateSource {V : Type*} (first second : V) : Coalgebra Nat Nat V
  | 0 => .inr [(1, first), (1, second)]
  | _ + 1 => .inl 7

theorem duplicate_contributions {V : Type*} [Monoid V] (first second : V) :
    contributions (duplicateSource first second) 2 0 =
      [(.inl 7, first), (.inl 7, second)] := by
  simp [contributions, duplicateSource, WeightedResumption.sequence]

theorem duplicate_handler {V : Type*} [Monoid V] (first second : V) :
    interpret catalogue (cut (duplicateSource first second) 2 0) =
      [(.inl 7, first), (.inl 7, second)] := by
  rw [interpret_cut, duplicate_contributions]

/-- Five units of coefficient still arose from two physical alternatives. -/
theorem coefficient_is_not_occurrence_count :
    total (contributions (duplicateSource (2 : Nat) 3) 2 0) = 5 ∧
      (contributions (duplicateSource (2 : Nat) 3) 2 0).length = 2 := by
  rw [duplicate_contributions]
  decide

/-- Before a declared support readout, zero does not delete its occurrence. -/
theorem zero_coefficient_occurrence :
    contributions (duplicateSource (0 : Nat) 1) 2 0 =
      [(.inl 7, 0), (.inl 7, 1)] := duplicate_contributions _ _

def silentCycle : Coalgebra Nat Nat Nat := fun state => .inr [(state, 1)]

/-- No finite budget turns a silent cycle into a completed answer. -/
theorem silent_cycle_remains_open (fuel state : Nat) :
    contributions silentCycle fuel state = [(.inr state, 1)] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [contributions, silentCycle, WeightedResumption.sequence, ih]

theorem disjunction_guards_do_not_cancel :
    total (contributions (duplicateSource (1 : GradedSupport.OrBool) 1) 2 0) = 1 := by
  rw [duplicate_contributions]
  rfl

theorem amplitudes_cancel_but_occurrences_remain :
    total (contributions (duplicateSource (1 : ℂ) (-1)) 2 0) = 0 ∧
      (contributions (duplicateSource (1 : ℂ) (-1)) 2 0).length = 2 := by
  rw [duplicate_contributions]
  constructor
  · simp [total, SemiringTraversal.weightSum]
  · rfl

/-- Born weights contain an interference term, so this is not an additive map. -/
theorem born_readout_not_additive :
    Complex.normSq ((1 : ℂ) + (-1)) ≠
      Complex.normSq (1 : ℂ) + Complex.normSq (-1 : ℂ) := by
  norm_num

abbrev TwoObjectives := Fin 2 → Nat

def firstObjective : TwoObjectives := ![1, 0]
def secondObjective : TwoObjectives := ![0, 1]

theorem pareto_incomparable :
    ¬ firstObjective ≤ secondObjective ∧ ¬ secondObjective ≤ firstObjective := by
  constructor
  · intro ordered
    have impossible := ordered 0
    simp [firstObjective, secondObjective] at impossible
  · intro ordered
    have impossible := ordered 1
    simp [firstObjective, secondObjective] at impossible

/-- Componentwise nonnegative vectors have no additive cancellation but do
have zero divisors. Exact support cannot discard the latter obligation. -/
theorem vector_zero_divisors :
    firstObjective ≠ 0 ∧ secondObjective ≠ 0 ∧ firstObjective * secondObjective = 0 := by
  constructor
  · intro zero
    have impossible := congrFun zero 0
    simp [firstObjective] at impossible
  constructor
  · intro zero
    have impossible := congrFun zero 1
    simp [secondObjective] at impossible
  · ext index
    fin_cases index <;> simp [firstObjective, secondObjective]

abbrev TwoByTwo := Matrix (Fin 2) (Fin 2) Nat

def upper : TwoByTwo := !![1, 1; 0, 1]
def lower : TwoByTwo := !![1, 0; 1, 1]

theorem matrix_composition_is_ordered : upper * lower ≠ lower * upper := by
  intro same
  have impossible := congrArg (fun matrix : TwoByTwo => matrix 0 0) same
  norm_num [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at impossible

theorem matrix_sequence_keeps_order :
    WeightedResumption.sequence [((7 : Nat), upper)] (fun _ => [((8 : Nat), lower)]) =
      [(8, upper * lower)] := rfl

/-- Swapping two scalar-looking grades can change the interpreted result. -/
theorem reordering_matrix_coefficients_changes_answer :
    WeightedResumption.sequence [((7 : Nat), upper)] (fun _ => [((8 : Nat), lower)]) ≠
      WeightedResumption.sequence [((7 : Nat), lower)] (fun _ => [((8 : Nat), upper)]) := by
  intro same
  simp only [WeightedResumption.sequence, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil, List.cons.injEq, Prod.mk.injEq] at same
  exact matrix_composition_is_ordered same.1.2

end Mettapedia.GSLT.Dynamics.WeightedResumptionControls
