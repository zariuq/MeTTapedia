import Mettapedia.Algorithms.MonotoneRankEnumeration

/-!
# Lazy Cartesian rank extraction

Each axis refers to a sorted, nonempty child-rank cache.  Initial admission
contains only the all-zero rank vector.  Expanding a vector admits one-step
coordinate increments; the shared visited account removes reconverging rank
paths, not distinct derivations or tied ranks.

The independent source is the complete Cartesian family of valid rank
vectors.  Every vector has an operational path from zero.  Monotone child
costs prove that the actual lazy selector publishes globally best prefixes.
No exhaustive Cartesian family is passed to the selector.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.LazyCartesianRanks

open Mettapedia.GSLT.Core.BranchingTemporal
open MonotoneRankEnumeration

structure Axis where
  count : Nat
  positive : 0 < count
  weight : Fin count → Nat
  ordered : Monotone weight

abbrev Point : List Axis → Type
  | [] => Unit
  | axis :: axes => Fin axis.count × Point axes

instance pointDecidableEq : (axes : List Axis) → DecidableEq (Point axes)
  | [] => inferInstanceAs (DecidableEq Unit)
  | axis :: axes =>
      letI := pointDecidableEq axes
      inferInstanceAs (DecidableEq (Fin axis.count × Point axes))

instance pointFintype : (axes : List Axis) → Fintype (Point axes)
  | [] => inferInstanceAs (Fintype Unit)
  | axis :: axes =>
      letI := pointFintype axes
      inferInstanceAs (Fintype (Fin axis.count × Point axes))

def zero : (axes : List Axis) → Point axes
  | [] => ()
  | axis :: axes => (⟨0, axis.positive⟩, zero axes)

def cost : (axes : List Axis) → Point axes → Nat
  | [], _ => 0
  | axis :: axes, (head, tail) => axis.weight head + cost axes tail

def neighbors : (axes : List Axis) → Point axes → List (Point axes)
  | [], _ => []
  | axis :: axes, (head, tail) =>
      (neighbors axes tail).map (head, ·) ++
        if within : head.val + 1 < axis.count then
          [(⟨head.val + 1, within⟩, tail)] else []

def graph (axes : List Axis) : Graph (Point axes) :=
  ⟨neighbors axes, cost axes⟩

theorem neighbors_monotone (axes : List Axis) : MonotoneRankEnumeration.Monotone (graph axes) := by
  induction axes with
  | nil => intro parent child member; simp [graph, neighbors] at member
  | cons axis axes ih =>
      intro parent child member
      rcases parent with ⟨head, tail⟩
      change child ∈ (neighbors axes tail).map (head, ·) ++
        (if within : head.val + 1 < axis.count then
          [(⟨head.val + 1, within⟩, tail)] else []) at member
      rcases List.mem_append.mp member with changedTail | increment
      · obtain ⟨next, neighbor, same⟩ := List.mem_map.mp changedTail
        subst child
        exact Nat.add_le_add_left (ih tail next neighbor) (axis.weight head)
      · split at increment
        next within =>
          have same : child = (⟨head.val + 1, within⟩, tail) :=
            List.mem_singleton.mp increment
          subst child
          exact Nat.add_le_add_right (axis.ordered (by change head.val ≤ head.val + 1; omega)) _
        next outside => simp at increment

theorem generated_substitute {Node Answer : Type*} (system : BranchingSystem Node Answer)
    (roots intermediate : List Node) {node : Node}
    (covered : ∀ root ∈ intermediate, Generated system roots root)
    (generated : Generated system intermediate node) : Generated system roots node := by
  induction generated with
  | root member => exact covered _ member
  | successor _ member ih => exact .successor ih member

theorem generated_tail (axis : Axis) (axes : List Axis) (head : Fin axis.count)
    {tail : Point axes} (generated : Generated (graph axes).system [zero axes] tail) :
    Generated (graph (axis :: axes)).system [(head, zero axes)] (head, tail) := by
  induction generated with
  | @root node member =>
      have same : node = zero axes := List.mem_singleton.mp member
      subst node
      exact .root (List.mem_singleton.mpr rfl)
  | @successor parent child previous member ih =>
      apply Generated.successor ih
      change (head, child) ∈ (neighbors axes parent).map (head, ·) ++ _
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨child, member, rfl⟩))

theorem generated_head (axis : Axis) (axes : List Axis) (index : Nat)
    (within : index < axis.count) :
    Generated (graph (axis :: axes)).system [zero (axis :: axes)]
      (⟨index, within⟩, zero axes) := by
  induction index with
  | zero => exact .root (List.mem_singleton.mpr rfl)
  | succ index ih =>
      have earlier : index < axis.count := by omega
      apply Generated.successor (ih earlier)
      change ((⟨index + 1, within⟩ : Fin axis.count), zero axes) ∈
        (neighbors axes (zero axes)).map
          (fun tail => ((⟨index, earlier⟩ : Fin axis.count), tail)) ++ _
      apply List.mem_append.mpr
      right
      rw [dif_pos within]
      exact List.mem_singleton.mpr rfl

/-- Every independently specified rank combination is reachable.  The
construction increments one coordinate at a time from the actual root. -/
theorem every_point_reachable (axes : List Axis) (point : Point axes) :
    Source (graph axes) [zero axes] point := by
  induction axes with
  | nil => cases point; exact .root (List.mem_singleton.mpr rfl)
  | cons axis axes ih =>
      rcases point with ⟨head, tail⟩
      apply generated_substitute (graph (axis :: axes)).system [zero (axis :: axes)]
        [(head, zero axes)]
      · intro root included
        have same : root = (head, zero axes) := List.mem_singleton.mp included
        subst root
        exact generated_head axis axes head.val head.isLt
      · exact generated_tail axis axes head (ih tail)

def extract (axes : List Axis) (requested allowance : Nat) : State (Point axes) × Nat :=
  (demandMachine (graph axes) requested).runSlice allowance
    (MonotoneRankEnumeration.initial [zero axes])

/-- Every published prefix is sorted and no omitted combination is cheaper
than one of its members.  Ties preserve distinct rank identities. -/
theorem extract_best (axes : List Axis) (requested allowance : Nat) :
    (extract axes requested allowance).1.published.Nodup ∧
    (extract axes requested allowance).1.published.Pairwise
      (fun first second => cost axes first ≤ cost axes second) ∧
    ∀ first ∈ (extract axes requested allowance).1.published,
      ∀ other : Point axes, other ∉ (extract axes requested allowance).1.published →
        cost axes first ≤ cost axes other := by
  have projection := congrArg Prod.fst
    (demand_is_prefix (graph axes) requested allowance
      (MonotoneRankEnumeration.initial [zero axes]))
  let used := (extract axes requested allowance).2
  change (extract axes requested allowance).1 =
    MonotoneRankEnumeration.run (graph axes) used
      (MonotoneRankEnumeration.initial [zero axes]) at projection
  rw [projection]
  have valid := run_invariant (graph axes) [zero axes] used
    (MonotoneRankEnumeration.initial [zero axes])
    (initial_invariant (graph axes) [zero axes])
  have best := run_best (graph axes) (neighbors_monotone axes) [zero axes] used
  refine ⟨(List.nodup_append.mp valid.distinct).1, best.1, ?_⟩
  intro first member other remaining
  exact best.2 first member other (every_point_reachable axes other) remaining

theorem extract_no_overshoot (axes : List Axis) (requested allowance : Nat) :
    (extract axes requested allowance).1.published.length ≤ requested :=
  demand_no_overshoot (graph axes) requested allowance _
    (by simp [MonotoneRankEnumeration.initial])

/-- The finite source has a proof-only cardinality bound.  Running to closure
enumerates every combination exactly once. -/
theorem complete_extraction (axes : List Axis) :
    let result := run (graph axes) (Fintype.card (Point axes) + 1) (initial [zero axes])
    result.frontier = [] ∧ result.published.Nodup ∧
      ∀ point : Point axes, point ∈ result.published := by
  intro result
  have closed := finite_exhaustion (graph axes) [zero axes] Finset.univ
    (fun _ _ => Finset.mem_univ _)
  have valid := run_invariant (graph axes) [zero axes]
    (Fintype.card (Point axes) + 1) _ (initial_invariant _ _)
  refine ⟨closed, (List.nodup_append.mp valid.distinct).1, ?_⟩
  intro point
  exact (closed_complete (graph axes) (neighbors_monotone axes) [zero axes] result
    valid closed point).mpr (every_point_reachable axes point)

namespace Controls

def twoCosts : Axis where
  count := 2
  positive := by decide
  weight index := index.val
  ordered := fun _ _ order => order

def pointRanks : (axes : List Axis) → Point axes → List Nat
  | [], _ => []
  | _ :: axes, (head, tail) => head.val :: pointRanks axes tail

example : ((extract [twoCosts, twoCosts] 3 3).1.published.map (pointRanks _)).length = 3 := by
  decide

example : ((extract [twoCosts, twoCosts] 4 4).1.published.map (cost _)) = [0, 1, 1, 2] := by
  decide

/-- The equal middle costs belong to different child-rank combinations. -/
example : (extract [twoCosts, twoCosts] 3 3).1.published.Nodup :=
  (extract_best _ 3 3).1

example : (extract [twoCosts, twoCosts] 3 3).1.frontier ≠ [] := by decide

end Controls

end Mettapedia.Algorithms.LazyCartesianRanks
