import Mettapedia.GSLT.Core.DemandExecution

/-!
# Finite occurrence observations from a structural depth bound

A decreasing depth is weaker than the exact remaining-work count used by the
executor.  Finite branching and decreasing depth construct that count and the
finite answer bag.  Their unfolding laws are derived from finite truncations;
they are not assumed as a native correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.WellFoundedSearch

open BranchingTemporal

variable {Node Answer Value : Type*}

structure DepthBound (system : BranchingSystem Node Answer) where
  depth : Node → Nat
  decreases : ∀ node child, child ∈ system.successors node → depth child < depth node

def approximate [AddCommMonoid Value] (system : BranchingSystem Node Answer)
    (output : Node → Value) : Nat → Node → Value
  | 0, _ => 0
  | fuel + 1, node => output node +
      ((system.successors node).map (approximate system output fuel)).sum

/-- Once the structural depth is exhausted, additional truncation allowance
does not change the independently computed finite observation. -/
theorem approximate_stable [AddCommMonoid Value] (system : BranchingSystem Node Answer)
    (bound : DepthBound system) (output : Node → Value) (fuel extra : Nat)
    (node : Node) (enough : bound.depth node < fuel) :
    approximate system output fuel node = approximate system output (fuel + extra) node := by
  induction fuel generalizing node with
  | zero => omega
  | succ fuel ih =>
      simp only [Nat.succ_add, approximate]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro child member
      exact ih child (by have := bound.decreases node child member; omega)

def value [AddCommMonoid Value] (system : BranchingSystem Node Answer)
    (bound : DepthBound system) (output : Node → Value) (node : Node) : Value :=
  approximate system output (bound.depth node + 1) node

theorem approximate_eq_value [AddCommMonoid Value] (system : BranchingSystem Node Answer)
    (bound : DepthBound system) (output : Node → Value) (fuel : Nat)
    (node : Node) (enough : bound.depth node < fuel) :
    approximate system output fuel node = value system bound output node := by
  have sufficient : bound.depth node + 1 ≤ fuel := by omega
  have same := approximate_stable system bound output (bound.depth node + 1)
    (fuel - (bound.depth node + 1)) node (by omega)
  rw [Nat.add_sub_of_le sufficient] at same
  exact same.symm

theorem value_unfold [AddCommMonoid Value] (system : BranchingSystem Node Answer)
    (bound : DepthBound system) (output : Node → Value) (node : Node) :
    value system bound output node = output node +
      ((system.successors node).map (value system bound output)).sum := by
  unfold value
  rw [approximate]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro child member
  exact approximate_eq_value system bound output _ child (bound.decreases node child member)

theorem sum_eq_foldRanks (rank : Node → Nat) (nodes : List Node) :
    (nodes.map rank).sum = foldRanks rank nodes := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp [foldRanks, ih]

theorem sum_eq_foldValues (observation : Node → Multiset Answer) (nodes : List Node) :
    (nodes.map observation).sum = foldValues observation nodes := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp [foldValues, ih]

/-- Construct the exact amount of finite work from the source depth law. -/
def descent (system : BranchingSystem Node Answer) (bound : DepthBound system) :
    DescentCertificate system where
  rank := value system bound (fun _ => 1)
  unfold node := by
    rw [value_unfold, sum_eq_foldRanks]

/-- Derive occurrence-sensitive answer semantics from actual emissions and
successors.  Equal answers from different child positions remain repeated. -/
def denotation (system : BranchingSystem Node Answer) (bound : DepthBound system) :
    AdditiveDenotation system where
  value := value system bound (fun node => optionBag (system.emit node))
  unfold node := by
    rw [value_unfold, sum_eq_foldValues]

theorem completes (system : BranchingSystem Node Answer) (bound : DepthBound system)
    (controller : InferenceControl.Controller Node Answer Value) (roots : List Node) :
    (InferenceControl.Snapshot.run system controller
      (foldRanks (descent system bound).rank roots)
      (InferenceControl.Snapshot.initial controller roots)).search.frontier = [] :=
  InferenceControl.Snapshot.run_completes_at_rank system controller (descent system bound)
    (InferenceControl.Snapshot.initial controller roots)

namespace Controls

def chain : BranchingSystem Nat Nat where
  emit node := some node
  successors
    | 0 => []
    | node + 1 => [node]

def chainDepth : DepthBound chain where
  depth := id
  decreases node child member := by
    cases node <;> simp_all [chain]

example : (descent chain chainDepth).rank 3 = 4 := by decide
example : (denotation chain chainDepth).value 3 = {3, 2, 1, 0} := by
  simp [denotation, value, approximate, chain, chainDepth, optionBag, Multiset.cons_swap]

/-- A productive cycle has no decreasing depth, even though every individual
quantum terminates.  Finite-search exhaustion cannot be used for it. -/
example : ¬ Nonempty (DepthBound (productiveLoopSystem 8)) := by
  rintro ⟨bound⟩
  have impossible := bound.decreases () () (by simp [productiveLoopSystem])
  exact Nat.lt_irrefl _ impossible

end Controls

end Mettapedia.GSLT.Core.WellFoundedSearch
