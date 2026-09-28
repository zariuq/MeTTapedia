import Mettapedia.Machines.DemandSummary

/-!
# Sharing changes the size of the computation being measured

A chain of shared binary constructors has one new node per level, while its
unfolded tree has exponentially many occurrences. These are independent
size measures, not interchangeable inputs to a complexity claim.

The example runs the actual memoizing summary evaluator from `DemandSummary`.
Its summary computes unfolded tree size without constructing that tree. The
number of summary combinations is at most the number of graph nodes. Natural
number arithmetic, cache lookup and edge enumeration have separate costs;
this theorem does not treat an arbitrarily large summary as a machine word.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SharedSpineCost

open DemandSummary

/-- Each level names its predecessor twice. There is no global depth bound. -/
def graph : Graph Unit where
  label _ := ()
  children
    | 0 => []
    | n + 1 => [⟨n, Nat.lt_succ_self n⟩, ⟨n, Nat.lt_succ_self n⟩]

/-- Count occurrences in the unfolded tree, including the constructor. -/
def treeSize (_ : Unit) (children : List Nat) : Nat := 1 + children.sum

theorem eager_zero : eager graph treeSize 0 = 1 := by
  rw [eager]
  rfl

theorem eager_succ (n : Nat) :
    eager graph treeSize (n + 1) = 1 + 2 * eager graph treeSize n := by
  rw [eager]
  simp [graph, treeSize, two_mul]

/-- Exact exponential occurrence count; the graph has only `n+1` nodes. -/
theorem unfolded_size (n : Nat) : eager graph treeSize n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rw [eager_zero]; rfl
  | succ n ih =>
      rw [eager_succ, Nat.pow_succ]
      omega

theorem reachable_exact (n : Nat) : reachable graph n = Finset.range (n + 1) := by
  induction n with
  | zero =>
      rw [reachable]
      change insert 0 (([] : List (Fin 0)).toFinset.biUnion
        (fun child => reachable graph child.val)) = Finset.range 1
      simp
  | succ n ih =>
      rw [reachable]
      change insert (n + 1)
        (([⟨n, Nat.lt_succ_self n⟩, ⟨n, Nat.lt_succ_self n⟩] : List (Fin (n + 1))).toFinset.biUnion
          (fun child => reachable graph child.val)) = _
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_idem,
        Finset.biUnion_insert, Finset.biUnion_empty, Finset.union_empty]
      rw [ih]
      exact (Finset.range_add_one (n := n + 1)).symm

/-- Cached evaluation avoids exponential recomputation through the shared
predecessor. This counts combinations, not all instructions or output bytes. -/
theorem demand_combinations_linear (n : Nat) :
    (demand graph treeSize n (fun _ => none)).computed.length ≤ n + 1 := by
  have bound := demand_combinations_le_uncached_reachable graph treeSize n
    (fun _ => none) (empty_sound graph treeSize)
  simpa [reachable_exact] using bound

theorem demand_value_exact (n : Nat) :
    (demand graph treeSize n (fun _ => none)).value + 1 = 2 ^ (n + 1) := by
  rw [demand_exact graph treeSize n _ (empty_sound graph treeSize)]
  exact unfolded_size n

theorem repeat_has_no_combinations (n : Nat) :
    (demand graph treeSize n (demand graph treeSize n (fun _ => none)).cache).computed = [] := by
  rw [demand_again]

/-- Nine allocated nodes describe 511 tree occurrences. The shared evaluator
combines precisely those nine nodes on this execution. -/
theorem nine_nodes_many_occurrences :
    (demand graph treeSize 8 (fun _ => none)).value = 511 ∧
    (demand graph treeSize 8 (fun _ => none)).computed = List.range 9 := by
  decide +kernel

end Mettapedia.Machines.SharedSpineCost
