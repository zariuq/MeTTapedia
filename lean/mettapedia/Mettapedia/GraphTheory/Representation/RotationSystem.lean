import Mettapedia.GraphTheory.Representation.AdjacencyRows

/-!
# Rotation systems are graph enrichments, not interchangeable layouts

A rotation system adds a cyclic order of incident neighbours at every vertex.
Forgetting that order yields an ordinary graph representation, but the map is
not injective.  This is why planar-map and face algorithms must not treat a
rotation system as merely another encoding of the same data.
-/

namespace Mettapedia.GraphTheory.Representation.RotationSystem

open Mettapedia.GraphTheory.Representation

/-- An adjacency-row graph equipped with a permutation of each neighbour row,
read cyclically. -/
structure Rep (n : Nat) where
  graph : AdjacencyRows.Rep n
  rotation : Fin n → List (Fin n)
  sameNeighbors : ∀ vertex, (rotation vertex).Perm (graph.row vertex)

/-- Forget the embedding data. -/
def forget {n : Nat} (system : Rep n) : AdjacencyRows.Rep n :=
  system.graph

private def scanNext {α : Type} [DecidableEq α] (first current : α) :
    List α → Measured (Option α)
  | [] => ⟨none, 0⟩
  | [last] =>
      if last = current then ⟨some first, 1⟩ else ⟨none, 1⟩
  | head :: next :: rest =>
      if head = current then
        ⟨some next, 1⟩
      else
        let tail := scanNext first current (next :: rest)
        ⟨tail.value, tail.work + 1⟩

/-- The cyclic successor of one incident neighbour in the authored rotation. -/
def nextAround {n : Nat} (system : Rep n) (vertex neighbor : Fin n) :
    Measured (Option (Fin n)) :=
  match system.rotation vertex with
  | [] => ⟨none, 0⟩
  | first :: rest => scanNext first neighbor (first :: rest)

namespace Canary

open AdjacencyRows.Canary

/-- Clockwise order around the centre of the star. -/
def clockwise : Rep 5 where
  graph := starAndIsolated
  rotation vertex :=
    if vertex = v0 then [v1, v2, v3]
    else if vertex = v1 then [v0]
    else if vertex = v2 then [v0]
    else if vertex = v3 then [v0]
    else []
  sameNeighbors := by decide

/-- The same abstract graph with the opposite order at its degree-three
centre. -/
def counterclockwise : Rep 5 where
  graph := starAndIsolated
  rotation vertex :=
    if vertex = v0 then [v1, v3, v2]
    else if vertex = v1 then [v0]
    else if vertex = v2 then [v0]
    else if vertex = v3 then [v0]
    else []
  sameNeighbors := by decide

/-- Positive canary: a rotation system answers an embedding-local successor
question. -/
theorem clockwise_successor :
    nextAround clockwise v0 v1 = ⟨some v2, 1⟩ := by
  decide

/-- Negative canary: forgetting rotation identifies two states that give
different answers to the same embedding-local query. -/
theorem forget_not_injective_canary :
    forget clockwise = forget counterclockwise ∧
      (nextAround clockwise v0 v1).value ≠
        (nextAround counterclockwise v0 v1).value := by
  constructor
  · rfl
  · decide

end Canary

#print axioms Canary.clockwise_successor
#print axioms Canary.forget_not_injective_canary

end Mettapedia.GraphTheory.Representation.RotationSystem
