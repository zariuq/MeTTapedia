import Mettapedia.Logic.LP.FiniteDependencyClosure
import Mathlib.Tactic

/-!
# Counted roots and opaque resource cycles

The resource graph has container-to-image ownership edges, image-to-resource
retained holds, and explicit base edges. A census subtracts only enumerated
internal holds. Unclassified holds remain external roots; scoped readers,
provider roots and saturated counts also root their nodes.

The count correspondence is an explicit obligation of the native census. This
module proves the resulting classification and finite closure laws; it does
not claim that C root discovery, synchronization or finalization is verified.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OpaqueResourceCycles

open Mettapedia.Logic.LP.FiniteDependencyClosure

variable {Node : Type*} [Fintype Node] [DecidableEq Node]

structure Census (Node : Type*) [DecidableEq Node] where
  dependencies : Node → Finset Node
  internalHolds : Node → Nat
  totalHolds : Node → Nat
  outsideHolds : Node → Nat
  readers : Node → Nat
  protectedRoots : Finset Node

def Census.classifiedRoots (c : Census Node) : Finset Node :=
  Finset.univ.filter fun n =>
    c.totalHolds n ≠ c.internalHolds n ∨ c.readers n > 0 ∨ n ∈ c.protectedRoots

def Census.externalRoots (c : Census Node) : Finset Node :=
  Finset.univ.filter fun n =>
    c.outsideHolds n > 0 ∨ c.readers n > 0 ∨ n ∈ c.protectedRoots

/-- Subtraction is exact when the enumerated internal holds and external
holds partition the actual count. An omitted internal hold conservatively
appears outside; subtracting a nonexistent hold violates this premise. -/
theorem classifiedRoots_eq_externalRoots (c : Census Node)
    (counts : ∀ n, c.totalHolds n = c.internalHolds n + c.outsideHolds n) :
    c.classifiedRoots = c.externalRoots := by
  ext n
  have discrepancy : c.totalHolds n ≠ c.internalHolds n ↔ c.outsideHolds n > 0 := by
    have partition := counts n
    omega
  simp only [Census.classifiedRoots, Census.externalRoots,
    Finset.mem_filter, Finset.mem_univ, true_and, discrepancy]

def Census.survivors (c : Census Node) : Finset Node :=
  closure c.dependencies c.classifiedRoots

inductive Observed (c : Census Node) : Node → Prop where
  | root {n} : n ∈ c.externalRoots → Observed c n
  | step {source target} : Observed c source → target ∈ c.dependencies source → Observed c target

theorem observed_survives (c : Census Node)
    (counts : ∀ n, c.totalHolds n = c.internalHolds n + c.outsideHolds n)
    {n : Node} (observed : Observed c n) : n ∈ c.survivors := by
  induction observed with
  | root member =>
      apply roots_subset c.dependencies c.classifiedRoots
      rwa [classifiedRoots_eq_externalRoots c counts]
  | step _ edge ih => exact closed _ _ ih edge

/-- A surviving node never points into the retired subgraph. This is the
closure property needed before a batch of cyclic allocations is detached. -/
theorem survivor_edges_preserved (c : Census Node) {source target : Node}
    (survives : source ∈ c.survivors) (edge : target ∈ c.dependencies source) :
    target ∈ c.survivors := closed _ _ survives edge

/-- Extra roots can retain garbage, but cannot invalidate an existing reader. -/
theorem conservative_roots (c : Census Node) (extra : Finset Node) :
    c.survivors ⊆ closure c.dependencies (c.classifiedRoots ∪ extra) :=
  closure_mono _ Finset.subset_union_left

namespace Controls

def mutualEdges : Fin 4 → Finset (Fin 4)
  | 0 => {2}
  | 1 => {3}
  | 2 => {1}
  | _ => {0}

def unrooted : Census (Fin 4) where
  dependencies := mutualEdges
  internalHolds := fun _ => 1
  totalHolds := fun _ => 1
  outsideHolds := fun _ => 0
  readers := fun _ => 0
  protectedRoots := ∅

example : unrooted.survivors = ∅ := by decide

def withReader : Census (Fin 4) :=
  { unrooted with readers := fun n => if n = 2 then 1 else 0 }

example : withReader.survivors = Finset.univ := by decide

def withUnclassifiedHold : Census (Fin 4) :=
  { unrooted with
    totalHolds := fun n => if n = 0 then 2 else 1
    outsideHolds := fun n => if n = 0 then 1 else 0 }

example : withUnclassifiedHold.survivors = Finset.univ := by decide

/-- Omitting a real scoped reader loses its entire reachable cycle. -/
example : unrooted.survivors ≠ withReader.survivors := by decide

end Controls

#print axioms classifiedRoots_eq_externalRoots
#print axioms observed_survives
#print axioms survivor_edges_preserved

end Mettapedia.Machines.OpaqueResourceCycles
