import Mettapedia.Machines.Cursor.ReaderOrderedSearch

/-!
# Weight-balanced height and actual ordered-search probes

`NativeBalanced` follows the checked delta-three predicate: subtrees of total
size at most one are exempt; otherwise each child size is at most three times
the other's. It implies the more convenient child-weight inequality with
weight equal to size plus one. This earns the logarithmic growth law for the
actual lower-bound/successor search, including small subtrees.

The gamma-two rotation algorithm is not verified by this file. A native
realization must preserve sizes, ordering, this balance predicate, and valid
storage. Those are construction invariants, not a required full-tree validation
pass at each lookup. Comparison costs for large keys remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderOrderedSearchWeight

open Mettapedia.Machines.CanonicalIndexDirectory
open ReaderOrderedSearch

variable {Key Value : Type}

def NativeBalanced : Tree Key Value → Prop
  | .empty => True
  | .node left _ _ right =>
      NativeBalanced left ∧ NativeBalanced right ∧
        (left.size + right.size ≤ 1 ∨ (left.size ≤ 3 * right.size ∧ right.size ≤ 3 * left.size))

def WeightBalanced : Tree Key Value → Prop
  | .empty => True
  | .node left _ _ right =>
      WeightBalanced left ∧ WeightBalanced right ∧
        left.size + 1 ≤ 3 * (right.size + 1) ∧
        right.size + 1 ≤ 3 * (left.size + 1)

theorem native_implies_weighted (tree : Tree Key Value) (balanced : NativeBalanced tree) :
    WeightBalanced tree := by
  induction tree with
  | empty => trivial
  | node left key value right leftIH rightIH =>
      rcases balanced with ⟨leftBalanced, rightBalanced, sizes⟩
      refine ⟨leftIH leftBalanced, rightIH rightBalanced, ?_, ?_⟩ <;>
        rcases sizes with small | both <;> omega

theorem growth_step (depth child parent : Nat)
    (growth : 4 * child ≤ 3 * parent)
    (bound : 4 ^ depth ≤ 3 ^ depth * child) :
    4 ^ (depth + 1) ≤ 3 ^ (depth + 1) * parent := by
  calc
    4 ^ (depth + 1) = 4 * 4 ^ depth := by rw [pow_succ]; omega
    _ ≤ 4 * (3 ^ depth * child) := Nat.mul_le_mul_left 4 bound
    _ = 3 ^ depth * (4 * child) := by ring
    _ ≤ 3 ^ depth * (3 * parent) := Nat.mul_le_mul_left _ growth
    _ = 3 ^ (depth + 1) * parent := by rw [pow_succ]; ring

theorem weighted_height_bound (tree : Tree Key Value) (balanced : WeightBalanced tree) :
    4 ^ tree.height ≤ 3 ^ tree.height * (tree.size + 1) := by
  induction tree with
  | empty => simp [Mettapedia.Machines.CanonicalIndexDirectory.Tree.height,
      Mettapedia.Machines.CanonicalIndexDirectory.Tree.size]
  | node left key value right leftIH rightIH =>
      rcases balanced with ⟨leftBalanced, rightBalanced, leftWeight, rightWeight⟩
      have first := leftIH leftBalanced
      have second := rightIH rightBalanced
      by_cases taller : left.height ≤ right.height
      · simp only [Mettapedia.Machines.CanonicalIndexDirectory.Tree.height,
          max_eq_right taller, Mettapedia.Machines.CanonicalIndexDirectory.Tree.size]
        exact growth_step right.height (right.size + 1) (left.size + right.size + 2)
          (by omega) second
      · simp only [Mettapedia.Machines.CanonicalIndexDirectory.Tree.height,
          max_eq_left (le_of_not_ge taller),
          Mettapedia.Machines.CanonicalIndexDirectory.Tree.size]
        exact growth_step left.height (left.size + 1) (left.size + right.size + 2)
          (by omega) first

theorem ratio_bound_downward (small large width : Nat) (within : small ≤ large)
    (bound : 4 ^ large ≤ 3 ^ large * width) :
    4 ^ small ≤ 3 ^ small * width := by
  let difference := large - small
  have split : large = small + difference := by dsimp [difference]; omega
  rw [split, pow_add, pow_add] at bound
  have bases : 3 ^ difference ≤ 4 ^ difference := Nat.pow_le_pow_left (by decide) _
  have enlarged := (Nat.mul_le_mul_left (3 ^ small) bases)
  have scaled := Nat.mul_le_mul_right width enlarged
  have budget : 4 ^ small * 4 ^ difference ≤ (3 ^ small * width) * 4 ^ difference := by
    calc
      4 ^ small * 4 ^ difference ≤ (3 ^ small * 3 ^ difference) * width := bound
      _ ≤ (3 ^ small * 4 ^ difference) * width := scaled
      _ = (3 ^ small * width) * 4 ^ difference := by ring
  exact Nat.le_of_mul_le_mul_right budget (by positivity)

theorem native_height_bound (tree : Tree Key Value) (balanced : NativeBalanced tree) :
    4 ^ tree.height ≤ 3 ^ tree.height * (tree.size + 1) :=
  weighted_height_bound tree (native_implies_weighted tree balanced)

/-- This is the actual search's node-probe count, not a tariff attached to a
linear list operation. It does not require the unrelated AVL height predicate. -/
theorem native_probe_bound (qualifies : Key → Bool) (tree : Tree Key Value)
    (balanced : NativeBalanced tree) :
    4 ^ probes qualifies tree ≤ 3 ^ probes qualifies tree * (tree.size + 1) :=
  ratio_bound_downward _ _ _ (probes_le_height qualifies tree) (native_height_bound tree balanced)

example : NativeBalanced (.node .empty (0 : Nat) ()
    (.node .empty 1 () .empty)) := by
  norm_num [NativeBalanced, Mettapedia.Machines.CanonicalIndexDirectory.Tree.size]

example : ¬ NativeBalanced (.node .empty (0 : Nat) ()
    (.node .empty 1 () (.node .empty 2 () .empty))) := by
  norm_num [NativeBalanced, Mettapedia.Machines.CanonicalIndexDirectory.Tree.size]

example : WeightBalanced (.node .empty (0 : Nat) ()
    (.node .empty 1 () (.node .empty 2 () .empty))) := by
  norm_num [WeightBalanced, Mettapedia.Machines.CanonicalIndexDirectory.Tree.size]

example : NativeBalanced ReaderOrderedSearch.sample := by
  norm_num [NativeBalanced, ReaderOrderedSearch.sample,
    Mettapedia.Machines.CanonicalIndexDirectory.Tree.size]

example : 4 ^ probes (fun key => decide (3 ≤ key)) ReaderOrderedSearch.sample ≤
    3 ^ probes (fun key => decide (3 ≤ key)) ReaderOrderedSearch.sample *
      (ReaderOrderedSearch.sample.size + 1) := by decide

end Mettapedia.Machines.Cursor.ReaderOrderedSearchWeight
