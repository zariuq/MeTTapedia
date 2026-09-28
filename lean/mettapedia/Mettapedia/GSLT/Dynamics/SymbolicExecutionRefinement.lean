import Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra
import Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra

/-!
# Refinement obligations for ordered symbolic execution

These small models and counterexamples illustrate obligations for the shared
search path:

* a repeated logical variable is a residual equality on the current image
* a later read sees the current image, and rollback restores the mark
* a shape filter does not discharge a failed residual unification
* a continuation is resumed once per delivered producer answer
* set-level conjunction commutativity does not reorder an ordered observation
* summing trie leaves inspects fewer nodes than a pairwise cursor merge once
  more than three singleton nodes are involved
* a one-key integer filter is complete for exact equality and drops the
  neighbor `2^53 + 1`, which is why HE promotion scans integer keys at and
  above `2^53`

The negative canaries distinguish the specific residual-dropping and replay
variants defined below. They do not establish refinement of the C matcher,
continuation transfer, IEEE-754 conversion, or trie implementation. In
particular, `scanPromotingKeys` takes an acceptance predicate; the numerical
correctness of that predicate is a separate obligation. The operation-count
inequalities concern explicit abstract counting models, not elapsed time or
all work performed by a native implementation. No fixed-point quotient is
introduced or equated with ordered search.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SymbolicExecutionRefinement

open OrderedOccurrenceBodyAlgebra
open SpaceQueryAlgebra

abbrev Image := List (Nat × Nat)

/-- Latest write wins. The list order is the trail. -/
def lookup (image : Image) (var : Nat) : Option Nat :=
  match image.reverse.find? (fun pair => pair.1 == var) with
  | some pair => some pair.2
  | none => none

def write (image : Image) (var value : Nat) : Image :=
  image ++ [(var, value)]

/-- Restore the image that existed when this branch was entered. -/
def rollback (image : Image) (mark : Nat) : Image :=
  image.take mark

theorem second_read_sees_the_current_image :
    lookup (write [] 0 7) 0 = some 7 := by
  decide

theorem rolled_back_sibling_does_not_see_its_write :
    lookup (rollback (write (write [] 0 7) 0 9) 1) 0 = some 7 := by
  decide

/-- Bind `var` to `value` in `image`. With the residual kept, a second value
must equal the first. Dropping the residual overwrites instead. -/
def bindShared (image : Image) (var value : Nat) (keepResidual : Bool) :
    Option Image :=
  match lookup image var with
  | none => some (write image var value)
  | some previous =>
      if previous == value then some image
      else if keepResidual then none
      else some (write image var value)

theorem shared_residual_rejects_incompatible_alias :
    (bindShared [] 0 1 true >>= fun image => bindShared image 0 2 true) =
      none := by
  decide

theorem dropping_shared_residual_accepts_incompatible_alias :
    (bindShared [] 0 1 false >>= fun image => bindShared image 0 2 false) =
      some [(0, 1), (0, 2)] := by
  decide

/-- A candidate that matches a shape still carries a unification residual. -/
structure ShapeFilter where
  shapeAccepts : Bool
  residualHolds : Bool
deriving DecidableEq

def publish (candidate : ShapeFilter) (keepResidual : Bool) : Bool :=
  candidate.shapeAccepts && (!keepResidual || candidate.residualHolds)

theorem residual_unification_rejects_the_candidate :
    publish { shapeAccepts := true, residualHolds := false } true = false := by
  decide

theorem dropping_residual_publishes_the_candidate :
    publish { shapeAccepts := true, residualHolds := false } false = true := by
  decide

theorem duplicate_producer_answers_each_resume_once :
    resumeAfterHole
      (fun (_ : Unit) => ([1, 1] : List Nat))
      (fun (_ : Unit) (value : Nat) => [value + 10])
      () = [11, 11] := by
  rfl

theorem dropping_continuation_loses_the_pending_answer :
    ([1] : List Nat) ≠
      resumeAfterHole
        (fun (_ : Unit) => [1])
        (fun (_ : Unit) (value : Nat) => [value + 1])
        () := by
  decide

theorem replaying_a_delivered_answer_changes_multiplicity :
    ([1] ++ resumeAfterHole
        (fun (_ : Unit) => [1])
        (fun (_ : Unit) (_ : Nat) => ([] : List Nat))
        ()) ≠
      resumeAfterHole
        (fun (_ : Unit) => [1])
        (fun (_ : Unit) (_ : Nat) => ([] : List Nat))
        () := by
  decide

/-- `conj_comm` identifies constraints. It does not identify ordered answer
lists. Swapping `[0, 1]` still changes the observation. -/
theorem set_meet_commutes_while_ordered_search_does_not
    (p q : Query Unit) :
    conj p q = conj q p ∧
      ([0, 1] : Occurrences Nat) ≠ [1, 0] := by
  constructor
  · exact conj_comm p q
  · decide

/-- Exact integer lookup keeps every stored key equal to the query and no
other key. This is the one-branch case below `2^53`. -/
def uniqueIntegerKey (keys : List Nat) (query : Nat) : List Nat :=
  keys.filter (· == query)

theorem unique_key_is_complete_for_exact_equality
    (keys : List Nat) (query : Nat) :
    (∀ key ∈ keys, key = query → key ∈ uniqueIntegerKey keys query) ∧
      (∀ key ∈ uniqueIntegerKey keys query, key = query) := by
  constructor
  · intro key member equal
    subst equal
    exact List.mem_filter.mpr ⟨member, by simp⟩
  · intro key member
    rcases List.mem_filter.mp member with ⟨_, holds⟩
    exact beq_iff_eq.mp holds

/-- An exact single-key filter excludes the neighboring integer. Connecting
this witness to HE promotion additionally requires a floating-point conversion
lemma; this theorem itself is about natural-number equality. -/
theorem one_key_filter_drops_neighbor_at_two_pow_53 :
    (2 ^ 53 + 1) ∉ uniqueIntegerKey [2 ^ 53, 2 ^ 53 + 1] (2 ^ 53) := by
  decide

def scanPromotingKeys (keys : List Nat) (accepts : Nat → Bool) : List Nat :=
  keys.filter accepts

theorem scan_keeps_both_neighbors_at_two_pow_53 :
    scanPromotingKeys [2 ^ 53, 2 ^ 53 + 1]
        (fun key => key == 2 ^ 53 || key == 2 ^ 53 + 1) =
      [2 ^ 53, 2 ^ 53 + 1] := by
  decide

/-- Pairwise merge of `n` singleton cursor nodes inspects one pair per
unordered pair. Summing trie leaves inspects each node once. -/
def pairwiseCursorInspections (n : Nat) : Nat := n * (n - 1) / 2

def trieLeafInspections (n : Nat) : Nat := n

/-- For every `k ≥ 4`, one leaf inspection per node is strictly cheaper than
one inspection per unordered pair of those nodes. -/
theorem trie_leaf_sum_inspects_fewer_than_pairwise_merge
    (k : Nat) (enough : 4 ≤ k) :
    trieLeafInspections k < pairwiseCursorInspections k := by
  simp only [trieLeafInspections, pairwiseCursorInspections]
  match k with
  | 0 | 1 | 2 | 3 => omega
  | 4 => decide
  | k + 5 =>
      have ih :
          k + 4 < (k + 4) * (k + 4 - 1) / 2 :=
        trie_leaf_sum_inspects_fewer_than_pairwise_merge (k + 4) (by omega)
      have split :
          (k + 5) * (k + 4) = 2 * (k + 4) + (k + 4) * (k + 3) := by
        calc
          (k + 5) * (k + 4) = (k + 4) * (k + 5) := Nat.mul_comm _ _
          _ = (k + 4) * ((k + 3) + 2) := by
            rw [show k + 5 = (k + 3) + 2 by
              rw [show (5 : Nat) = 3 + 2 by decide, Nat.add_assoc]]
          _ = (k + 4) * (k + 3) + (k + 4) * 2 := Nat.mul_add _ _ _
          _ = (k + 4) * (k + 3) + 2 * (k + 4) := by
            rw [Nat.mul_comm (k + 4) 2]
          _ = 2 * (k + 4) + (k + 4) * (k + 3) := Nat.add_comm _ _
      have combined :
          (k + 5) * (k + 4) / 2 =
            (k + 4) + (k + 4) * (k + 3) / 2 := by
        rw [split]
        exact Nat.mul_add_div (by decide : 2 > 0) (k + 4) ((k + 4) * (k + 3))
      have grown : k + 5 ≤ (k + 4) * (k + 3) / 2 :=
        Nat.succ_le_of_lt ih
      have room :
          (k + 4) * (k + 3) / 2 <
            (k + 4) + (k + 4) * (k + 3) / 2 :=
        Nat.lt_add_of_pos_left (Nat.succ_pos (k + 3))
      have step :
          k + 5 < (k + 4) + (k + 4) * (k + 3) / 2 :=
        Nat.lt_of_le_of_lt grown room
      have sub : (k + 5) - 1 = k + 4 := by
        rw [show k + 5 = (k + 4) + 1 by
          rw [show (5 : Nat) = 4 + 1 by decide, Nat.add_assoc]]
        exact Nat.add_sub_cancel (k + 4) 1
      rw [sub, combined]
      exact step

#print axioms shared_residual_rejects_incompatible_alias
#print axioms dropping_shared_residual_accepts_incompatible_alias
#print axioms residual_unification_rejects_the_candidate
#print axioms dropping_residual_publishes_the_candidate
#print axioms dropping_continuation_loses_the_pending_answer
#print axioms replaying_a_delivered_answer_changes_multiplicity
#print axioms set_meet_commutes_while_ordered_search_does_not
#print axioms one_key_filter_drops_neighbor_at_two_pow_53
#print axioms trie_leaf_sum_inspects_fewer_than_pairwise_merge

/-- An abstract model of repeated min-scans of singleton cursor nodes. -/
def multiNodeCursorInspections (n : Nat) : Nat := n * n

/-- Consumption of an already flattened frontier visits each saved index once.
This count excludes constructing the frontier, heap comparisons, allocation,
and validation. It is not the total cost of the native flattening algorithm. -/
def flattenedCursorInspections (n : Nat) : Nat := n

theorem flattened_cursor_inspects_fewer_singleton_nodes
    (n : Nat) (enough : 2 ≤ n) :
    flattenedCursorInspections n < multiNodeCursorInspections n := by
  simp only [flattenedCursorInspections, multiNodeCursorInspections]
  have fewer : n * 1 < n * n :=
    Nat.mul_lt_mul_of_pos_left
      (Nat.lt_of_succ_le enough)
      (Nat.zero_lt_of_lt (Nat.lt_of_succ_le enough))
  rw [Nat.mul_one] at fewer
  exact fewer

#print axioms flattened_cursor_inspects_fewer_singleton_nodes

end Mettapedia.GSLT.Dynamics.SymbolicExecutionRefinement
