import Mettapedia.Cybernetics.HierarchicalComplexity.Finite
import Mettapedia.Enactive.Razor

/-!
# Hierarchical order, completion weakness, quantale weakness, and code length

The four readouts compared here answer different questions:

* Commons's order measures depth created by order-sensitive coordination;
* Bennett's weakness counts admitted completions;
* Goertzel's quantale weakness aggregates weighted pair events;
* description length measures a candidate in an explicit code language.

Mathlib's `Function.FactorsThrough` gives the exact reduction test: a readout
is determined by another when it is constant on every fibre of the latter.
The concrete candidates below use actual finite MHC actions, actual admitted
world sets, an existing quantale weakness instance, and prefix-incomparable
codes.  They prove pairwise non-determination without claiming that no
specialized bridge can ever relate two axes.

Indeed, one important reduction is retained: sending an admitted world set to
its complete pair event makes pair-event cardinality the square of Bennett
weakness.  Weighted quantale aggregation need not preserve that reduction.

References:

- M. L. Commons and A. Pekker, *Presenting the Formal Theory of Hierarchical
  Complexity* (2008).
- M. T. Bennett, *The Wrong Razor* (2026), for weakness versus coding length.
- B. Goertzel, *Weakness Is All You Need: Quantale Weakness as a Unifying
  Principle* (2026), for weighted quantale-valued weakness.
- J. Rissanen, *Modeling by Shortest Data Description* (1978), for an early
  description-length criterion distinct from the other readouts.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.AxisIndependence

open scoped ENNReal
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Cybernetics.HierarchicalComplexity

/-! ## Generic non-determination test -/

/-- One fibre collision suffices to refute factorization. -/
theorem not_factorsThrough_of_collision
    {Candidate LeftValue RightValue : Type*}
    {left : Candidate → LeftValue} {right : Candidate → RightValue}
    {first second : Candidate}
    (sameRight : right first = right second)
    (differentLeft : left first ≠ left second) :
    ¬ left.FactorsThrough right := by
  intro factors
  exact differentLeft (factors sameRight)

/-- Neither readout determines the other. -/
def PairwiseIndependent
    {Candidate LeftValue RightValue : Type*}
    (left : Candidate → LeftValue) (right : Candidate → RightValue) : Prop :=
  ¬ left.FactorsThrough right ∧ ¬ right.FactorsThrough left

/-! ## One integrated semantic candidate space -/

abbrev MHCAction :=
  Mettapedia.Cybernetics.HierarchicalComplexity.Finite.Action.{0, 0} (Fin 2)

/-- A candidate retains the informative object for each axis before any scalar
readout is taken. -/
structure Candidate where
  action : MHCAction
  admittedCompletions : Finset Bool
  code : List Bool

def orderZero : MHCAction :=
  Mettapedia.Cybernetics.HierarchicalComplexity.Finite.Action.simple (Fin 2)

def orderOne : MHCAction :=
  Mettapedia.Cybernetics.HierarchicalComplexity.Finite.Phi.binaryTower 1

/-- A fixed nonuniform quantale valuation.  It is deliberately explicit: the
weighted comparison is relative to this valuation, not presentation-free. -/
def biasedWeight : WeightFunction Bool ℝ≥0∞ where
  μ
    | false => 1
    | true => 2

/-- Commons's finite hierarchical order. -/
noncomputable def hierarchicalOrder (candidate : Candidate) : Nat :=
  candidate.action.order

/-- Bennett's finite admitted-completion count. -/
def completionWeakness (candidate : Candidate) : Nat :=
  bennettWeakness candidate.admittedCompletions

/-- Pair-event cardinality after the complete-pair embedding. -/
def inducedPairCardinality (candidate : Candidate) : Nat :=
  pairDistinctionWeakness
    (inducedPairEvent candidate.admittedCompletions)

/-- Goertzel's quantale weakness on the same induced pair event under the
declared nonuniform valuation. -/
noncomputable def weightedQuantaleWeakness (candidate : Candidate) : ℝ≥0∞ :=
  weakness biasedWeight
    (inducedPairEvent candidate.admittedCompletions)

/-- Length in the explicitly retained code language. -/
def codeLength (candidate : Candidate) : Nat :=
  candidate.code.length

/-! ## Concrete candidates -/

/-- Baseline: order zero, one high-weight completion, and a two-bit code. -/
def baseline : Candidate where
  action := orderZero
  admittedCompletions := {true}
  code := [false, false]

/-- Changes only hierarchical organization. -/
def higherOrder : Candidate where
  action := orderOne
  admittedCompletions := {true}
  code := [false, false]

/-- Adds a lower-weight completion.  Cardinal weakness rises while the
max-join weighted score remains fixed by the high-weight completion. -/
def moreCompletions : Candidate where
  action := orderZero
  admittedCompletions := Finset.univ
  code := [false, false]

/-- Replaces the admitted completion by a lower-weight one.  Cardinal weakness
is unchanged while weighted quantale weakness changes. -/
def lowerWeightCompletion : Candidate where
  action := orderZero
  admittedCompletions := {false}
  code := [false, false]

/-- Changes only the code length. -/
def shorterCode : Candidate where
  action := orderZero
  admittedCompletions := {true}
  code := [true]

/-! ## Exact metric values -/

@[simp] theorem hierarchicalOrder_baseline :
    hierarchicalOrder baseline = 0 := by
  simp [hierarchicalOrder, baseline, orderZero]

@[simp] theorem hierarchicalOrder_higherOrder :
    hierarchicalOrder higherOrder = 1 := by
  simp [hierarchicalOrder, higherOrder, orderOne]

@[simp] theorem hierarchicalOrder_moreCompletions :
    hierarchicalOrder moreCompletions = 0 := by
  simp [hierarchicalOrder, moreCompletions, orderZero]

@[simp] theorem hierarchicalOrder_lowerWeightCompletion :
    hierarchicalOrder lowerWeightCompletion = 0 := by
  simp [hierarchicalOrder, lowerWeightCompletion, orderZero]

@[simp] theorem hierarchicalOrder_shorterCode :
    hierarchicalOrder shorterCode = 0 := by
  simp [hierarchicalOrder, shorterCode, orderZero]

@[simp] theorem completionWeakness_baseline :
    completionWeakness baseline = 1 := by
  simp [completionWeakness, baseline, bennettWeakness]

@[simp] theorem completionWeakness_higherOrder :
    completionWeakness higherOrder = 1 := by
  simp [completionWeakness, higherOrder, bennettWeakness]

@[simp] theorem completionWeakness_moreCompletions :
    completionWeakness moreCompletions = 2 := by
  simp [completionWeakness, moreCompletions, bennettWeakness]

@[simp] theorem completionWeakness_lowerWeightCompletion :
    completionWeakness lowerWeightCompletion = 1 := by
  simp [completionWeakness, lowerWeightCompletion, bennettWeakness]

@[simp] theorem completionWeakness_shorterCode :
    completionWeakness shorterCode = 1 := by
  simp [completionWeakness, shorterCode, bennettWeakness]

@[simp] theorem weightedQuantaleWeakness_baseline :
    weightedQuantaleWeakness baseline = 4 := by
  simp [weightedQuantaleWeakness, baseline, weakness, biasedWeight,
    inducedPairEvent]
  norm_num

@[simp] theorem weightedQuantaleWeakness_higherOrder :
    weightedQuantaleWeakness higherOrder = 4 := by
  simp [weightedQuantaleWeakness, higherOrder, weakness, biasedWeight,
    inducedPairEvent]
  norm_num

@[simp] theorem weightedQuantaleWeakness_moreCompletions :
    weightedQuantaleWeakness moreCompletions = 4 := by
  norm_num [weightedQuantaleWeakness, moreCompletions, weakness,
    biasedWeight, inducedPairEvent]
  rw [show {x : ℝ≥0∞ | (1 = x ∨ 2 = x) ∨ 2 = x ∨ 4 = x} =
      ({1, 2, 4} : Set ℝ≥0∞) by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto]
  norm_num

@[simp] theorem weightedQuantaleWeakness_lowerWeightCompletion :
    weightedQuantaleWeakness lowerWeightCompletion = 1 := by
  simp [weightedQuantaleWeakness, lowerWeightCompletion, weakness,
    biasedWeight, inducedPairEvent]

@[simp] theorem weightedQuantaleWeakness_shorterCode :
    weightedQuantaleWeakness shorterCode = 4 := by
  simp [weightedQuantaleWeakness, shorterCode, weakness, biasedWeight,
    inducedPairEvent]
  norm_num

@[simp] theorem codeLength_baseline : codeLength baseline = 2 := rfl
@[simp] theorem codeLength_higherOrder : codeLength higherOrder = 2 := rfl
@[simp] theorem codeLength_moreCompletions :
    codeLength moreCompletions = 2 := rfl
@[simp] theorem codeLength_lowerWeightCompletion :
    codeLength lowerWeightCompletion = 2 := rfl
@[simp] theorem codeLength_shorterCode : codeLength shorterCode = 1 := rfl

/-- The two codewords used for the strict length comparison are
prefix-incomparable. -/
theorem compared_codewords_prefix_incomparable :
    ¬ baseline.code <+: shorterCode.code ∧
      ¬ shorterCode.code <+: baseline.code := by
  decide

/-! ## Pairwise independence -/

theorem hierarchicalOrder_completionWeakness_independent :
    PairwiseIndependent hierarchicalOrder completionWeakness := by
  constructor
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := higherOrder) (by simp) (by simp)
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := moreCompletions) (by simp) (by simp)

theorem hierarchicalOrder_weightedQuantaleWeakness_independent :
    PairwiseIndependent hierarchicalOrder weightedQuantaleWeakness := by
  constructor
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := higherOrder) (by simp) (by simp)
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := lowerWeightCompletion) (by simp) (by simp)

theorem hierarchicalOrder_codeLength_independent :
    PairwiseIndependent hierarchicalOrder codeLength := by
  constructor
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := higherOrder) (by simp) (by simp)
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := shorterCode) (by simp) (by simp)

theorem completionWeakness_weightedQuantaleWeakness_independent :
    PairwiseIndependent completionWeakness weightedQuantaleWeakness := by
  constructor
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := moreCompletions) (by simp) (by simp)
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := lowerWeightCompletion) (by simp) (by simp)

theorem completionWeakness_codeLength_independent :
    PairwiseIndependent completionWeakness codeLength := by
  constructor
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := moreCompletions) (by simp) (by simp)
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := shorterCode) (by simp) (by simp)

theorem weightedQuantaleWeakness_codeLength_independent :
    PairwiseIndependent weightedQuantaleWeakness codeLength := by
  constructor
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := lowerWeightCompletion) (by simp) (by simp)
  · exact not_factorsThrough_of_collision
      (first := baseline) (second := shorterCode) (by simp) (by simp)

/-- All six unordered pairs admit witnesses in both directions. -/
theorem all_four_axes_pairwise_independent :
    PairwiseIndependent hierarchicalOrder completionWeakness ∧
    PairwiseIndependent hierarchicalOrder weightedQuantaleWeakness ∧
    PairwiseIndependent hierarchicalOrder codeLength ∧
    PairwiseIndependent completionWeakness weightedQuantaleWeakness ∧
    PairwiseIndependent completionWeakness codeLength ∧
    PairwiseIndependent weightedQuantaleWeakness codeLength :=
  ⟨hierarchicalOrder_completionWeakness_independent,
    hierarchicalOrder_weightedQuantaleWeakness_independent,
    hierarchicalOrder_codeLength_independent,
    completionWeakness_weightedQuantaleWeakness_independent,
    completionWeakness_codeLength_independent,
    weightedQuantaleWeakness_codeLength_independent⟩

/-! ## A real reduction under an explicit event construction -/

/-- Complete-pair cardinality is exactly the square of Bennett weakness. -/
theorem inducedPairCardinality_eq_completionWeakness_sq
    (candidate : Candidate) :
    inducedPairCardinality candidate = completionWeakness candidate ^ 2 :=
  pairDistinctionWeakness_inducedPairEvent candidate.admittedCompletions

/-- Consequently this particular pair-event readout factors through Bennett
weakness.  The preceding nonuniform quantale canary shows why the conclusion
does not extend to arbitrary valuations and quantale aggregators. -/
theorem inducedPairCardinality_factorsThrough_completionWeakness :
    inducedPairCardinality.FactorsThrough completionWeakness := by
  intro first second equalWeakness
  rw [inducedPairCardinality_eq_completionWeakness_sq,
    inducedPairCardinality_eq_completionWeakness_sq, equalWeakness]

/-- The square bridge also preserves and reflects the finite weakness order. -/
theorem inducedPairCardinality_le_iff_completionWeakness_le
    (left right : Candidate) :
    inducedPairCardinality left ≤ inducedPairCardinality right ↔
      completionWeakness left ≤ completionWeakness right :=
  pairDistinctionWeakness_inducedPairEvent_le_iff
    left.admittedCompletions right.admittedCompletions

end Mettapedia.Enactive.AxisIndependence

#print axioms Mettapedia.Enactive.AxisIndependence.all_four_axes_pairwise_independent
#print axioms Mettapedia.Enactive.AxisIndependence.inducedPairCardinality_factorsThrough_completionWeakness
#print axioms Mettapedia.Enactive.AxisIndependence.inducedPairCardinality_le_iff_completionWeakness_le
