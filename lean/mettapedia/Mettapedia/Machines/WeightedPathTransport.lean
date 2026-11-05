import Mettapedia.Machines.WeightedPathRelaxation

/-!
# Weighted path transport across graph support

Adding authorized edges preserves every existing path with exactly its weight.
Consequently distance is antitone in graph support, and support-equivalent
graphs have equal final distances. This does not identify edge occurrences,
enumeration order, future deletions or source execution counters.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.WeightedRelaxation

variable {Vertex : Type}

def transportPath {first second : List (Arc Vertex)} (included : ∀ edge ∈ first, edge ∈ second)
    {source target : Vertex} (path : Path first source target) : Path second source target := by
  induction path with
  | nil => exact @Quiver.Path.nil Vertex (pathQuiver second) _
  | cons path edge transferred =>
      exact @Quiver.Path.cons Vertex (pathQuiver second) _ _ _
        transferred ⟨edge.1, included edge.1 edge.2.1, edge.2.2⟩

theorem transportPath_weight {first second : List (Arc Vertex)} (included : ∀ edge ∈ first, edge ∈ second)
    {source target : Vertex} (path : Path first source target) :
    pathWeight second (transportPath included path) = pathWeight first path := by
  induction path with
  | nil => simp [transportPath, pathWeight]
  | cons path edge ih =>
      simpa [transportPath, pathWeight] using congrArg (fun value => value + edge.1.weight) ih

theorem distance_antitone_support {first second : List (Arc Vertex)}
    (included : ∀ edge ∈ first, edge ∈ second) (root : Vertex) : distance second root ≤ distance first root := by
  intro vertex
  apply le_iInf
  intro path
  exact (iInf_le (fun path : Path second root vertex => (pathWeight second path : WithTop Nat))
    (transportPath included path)).trans_eq (congrArg (fun weight : Nat => (weight : WithTop Nat)) (transportPath_weight included path))

theorem distance_support_congr {first second : List (Arc Vertex)}
    (same : ∀ edge, edge ∈ first ↔ edge ∈ second) (root : Vertex) : distance first root = distance second root :=
  le_antisymm (distance_antitone_support (fun edge member => (same edge).mpr member) root)
    (distance_antitone_support (fun edge member => (same edge).mp member) root)

theorem distance_perm {first second : List (Arc Vertex)} (same : first.Perm second) (root : Vertex) :
    distance first root = distance second root := distance_support_congr (fun _ => same.mem_iff) root

theorem distance_eraseDups [DecidableEq Vertex] (graph : List (Arc Vertex)) (root : Vertex) :
    distance graph.eraseDups root = distance graph root := distance_support_congr (fun _ => by simp) root

end Mettapedia.Machines.WeightedRelaxation
