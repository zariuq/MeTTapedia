import Mettapedia.Algorithms.MonotoneRankEnumeration
import Mettapedia.GSLT.Core.KeyOrder

/-!
# Positive-cost finite-branching path search

Paths retain every child-position occurrence, including repeated visits to a
world state. A finite alphabet bounds branching, while a positive charge per
edge bounds the number of paths below each cost. This constructs the finite
sublevel set used by the actual best-first enumeration theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.PositivePathSearch

open MonotoneRankEnumeration

variable {Edge : Type} [DecidableEq Edge]

structure Problem (Edge : Type) where
  alphabet : List Edge
  charge : Edge → Nat
  positive : ∀ edge ∈ alphabet, 0 < charge edge
  permitted : List Edge → Edge → Bool

def cost (problem : Problem Edge) (path : List Edge) : Nat :=
  (path.map problem.charge).sum

def graph (problem : Problem Edge) : Graph (List Edge) where
  neighbors path := (problem.alphabet.filter (problem.permitted path)).map
    (fun edge => path ++ [edge])
  cost := cost problem

omit [DecidableEq Edge] in
theorem graph_monotone (problem : Problem Edge) : Monotone (graph problem) := by
  intro parent child member
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
  simp only [graph, cost, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]
  omega

omit [DecidableEq Edge] in
theorem generated_symbols (problem : Problem Edge) (path : List Edge)
    (source : Source (graph problem) [[]] path) :
    ∀ edge ∈ path, edge ∈ problem.alphabet := by
  induction source with
  | root member =>
      simp only [List.mem_singleton] at member
      subst member
      simp
  | @successor parent child _ member ih =>
      obtain ⟨edge, admitted, rfl⟩ := List.mem_map.mp member
      have alphabet := (List.mem_filter.mp admitted).1
      intro other present
      rcases List.mem_append.mp present with old | new
      · exact ih other old
      · have same := List.mem_singleton.mp new
        simpa only [same] using alphabet

omit [DecidableEq Edge] in
theorem length_le_cost (problem : Problem Edge) (path : List Edge)
    (symbols : ∀ edge ∈ path, edge ∈ problem.alphabet) :
    path.length ≤ cost problem path := by
  induction path with
  | nil => simp [cost]
  | cons edge rest ih =>
      have positive := problem.positive edge (symbols edge (by simp))
      have tail := ih (fun other member => symbols other (by simp [member]))
      simp only [List.length_cons, cost, List.map_cons, List.sum_cons] at *
      omega

def sublevel (problem : Problem Edge) (bound : Nat) : Finset (List Edge) :=
  (Mettapedia.GSLT.Core.KeyOrder.boundedWords problem.alphabet bound).toFinset

theorem sublevel_contains (problem : Problem Edge) (bound : Nat) (path : List Edge)
    (source : Source (graph problem) [[]] path) (bounded : cost problem path ≤ bound) :
    path ∈ sublevel problem bound := by
  have symbols := generated_symbols problem path source
  apply List.mem_toFinset.mpr
  exact (Mettapedia.GSLT.Core.KeyOrder.mem_boundedWords_iff _ _ _).mpr
    ⟨le_trans (length_le_cost problem path symbols) bounded, symbols⟩

/-- The algorithm finalizes any particular reachable optimum after a finite
number of expansions, even when the underlying transition graph has cycles. -/
theorem eventually_published (problem : Problem Edge) (path : List Edge)
    (source : Source (graph problem) [[]] path) :
    path ∈ (run (graph problem) ((sublevel problem (cost problem path)).card + 1)
      (initial [[]])).published := by
  apply finite_sublevel_reached (graph problem) (graph_monotone problem)
    [[]] path source (sublevel problem (cost problem path))
  intro other allowed bounded
  exact sublevel_contains problem _ other allowed bounded

namespace Controls

def positiveLoop : Problem Unit := ⟨[()], fun _ => 1, by simp, fun _ _ => true⟩

example : cost positiveLoop [(), (), ()] = 3 := rfl
example : (run (graph positiveLoop) 4 (initial [[]])).published =
    [[], [()], [(), ()], [(), (), ()]] := by decide

/-- A zero-cost cycle has infinitely many distinct path occurrences below the
same cost; finite fact support does not supply a finite occurrence sublevel. -/
def zeroGraph : Graph Nat := ⟨fun depth => [depth + 1], fun _ => 0⟩

theorem every_zero_depth (depth : Nat) : Source zeroGraph [0] depth := by
  induction depth with
  | zero => exact .root (by simp)
  | succ depth ih => exact .successor ih (by simp [zeroGraph, Graph.system])

theorem no_finite_zero_sublevel :
    ¬ ∃ domain : Finset Nat, ∀ depth, Source zeroGraph [0] depth →
      zeroGraph.cost depth ≤ 0 → depth ∈ domain := by
  rintro ⟨domain, complete⟩
  have covers : ∀ depth, depth ∈ domain := fun depth =>
    complete depth (every_zero_depth depth) (by simp [zeroGraph])
  have impossible : domain.sup id + 1 ≤ domain.sup id :=
    Finset.le_sup (f := id) (covers (domain.sup id + 1))
  omega

end Controls

end Mettapedia.Algorithms.PositivePathSearch
