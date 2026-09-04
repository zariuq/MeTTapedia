import Mettapedia.GraphTheory.Representation.Basic

/-!
# Neighbour-finset presentation

Neighbour finite sets make membership and set algebra primitive.  Unlike
adjacency rows, they intentionally erase authored order and duplicate
occurrences.  The abstract work model below counts one finite-set membership
operation; a concrete hash/tree/bitset refinement must later justify its own
physical cost.
-/

namespace Mettapedia.GraphTheory.Representation.NeighborFinsets

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation

/-- Symmetric, loop-free neighbour finite sets. -/
structure Rep (n : Nat) where
  row : Fin n → Finset (Fin n)
  symmetric : ∀ source target, target ∈ row source ↔ source ∈ row target
  loopless : ∀ vertex, vertex ∉ row vertex

def denote {n : Nat} (graph : Rep n) : SimpleGraph (Fin n) where
  Adj source target := target ∈ graph.row source
  symm := ⟨fun source target => (graph.symmetric source target).mp⟩
  loopless := ⟨graph.loopless⟩

/-- One abstract finite-set membership operation. -/
def edge {n : Nat} (graph : Rep n) (source target : Fin n) : Measured Bool :=
  ⟨decide (target ∈ graph.row source), 1⟩

def storageCells {n : Nat} (graph : Rep n) : Nat :=
  n + (List.ofFn fun vertex => (graph.row vertex).card).sum

theorem edge_sound {n : Nat} (graph : Rep n) (source target : Fin n) :
    (edge graph source target).value = true ↔
      (denote graph).Adj source target := by
  simp [edge, denote]

def presentation (n : Nat) : Presentation n where
  Carrier := Rep n
  denote := denote
  edge := edge
  edge_sound := edge_sound
  storageCells := storageCells

/-- One-step observer states for primitive finite-set membership. -/
inductive State (n : Nat) where
  | lookup (graph : Rep n) (source target : Fin n)
  | answer (value : Bool)

inductive Step {n : Nat} : State n → State n → Prop where
  | member (graph : Rep n) (source target : Fin n) :
      Step (.lookup graph source target) (.answer (edge graph source target).value)

def theory (n : Nat) : GSLT where
  Term := State n
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Set intersection gives the exact common-neighbour set. -/
def commonNeighbors {n : Nat} (graph : Rep n) (left right : Fin n) :
    Finset (Fin n) :=
  graph.row left ∩ graph.row right

theorem mem_commonNeighbors_iff {n : Nat} (graph : Rep n)
    (left right vertex : Fin n) :
    vertex ∈ commonNeighbors graph left right ↔
      (denote graph).Adj left vertex ∧ (denote graph).Adj right vertex := by
  simp [commonNeighbors, denote]

namespace Canary

def v0 : Fin 3 := ⟨0, by omega⟩
def v1 : Fin 3 := ⟨1, by omega⟩
def v2 : Fin 3 := ⟨2, by omega⟩

/-- Negative canary: finite-set conversion cannot recover authored neighbour
order. -/
theorem different_orders_same_finset :
    [v1, v2] ≠ [v2, v1] ∧
      [v1, v2].toFinset = [v2, v1].toFinset := by
  decide

/-- Multiplicity is erased as well. -/
theorem duplicate_occurrence_erased :
    [v1, v1].toFinset = [v1].toFinset := by
  decide

end Canary

#print axioms edge_sound
#print axioms mem_commonNeighbors_iff
#print axioms Canary.different_orders_same_finset
#print axioms Canary.duplicate_occurrence_erased

end Mettapedia.GraphTheory.Representation.NeighborFinsets
