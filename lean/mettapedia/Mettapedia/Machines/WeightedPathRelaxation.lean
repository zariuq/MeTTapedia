import Mettapedia.Machines.KeyedImprovement
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Min-plus relaxation against independent weighted paths

Edges carry exact nonnegative natural costs. Missing distance is genuine top,
not a finite sentinel. The reference meaning is the infimum of weights of
Mathlib quiver paths, independently of any relaxation schedule.

A label store is sound when each finite label has an actual source path.
Relaxation preserves this provenance. A closed sound store below the initial
labels is exactly the path distance. This separates quiescence/completeness
from merely performing a bounded number of updates.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.WeightedRelaxation

structure Arc (Vertex : Type) where
  source : Vertex
  target : Vertex
  weight : Nat
  deriving DecidableEq, Repr

variable {Vertex : Type} [DecidableEq Vertex]

abbrev Labels (Vertex : Type) := Vertex → WithTop Nat

def initial (root : Vertex) : Labels Vertex := fun vertex => if vertex = root then 0 else ⊤

def proposal (labels : Labels Vertex) (edge : Arc Vertex) : WithTop Nat :=
  labels edge.source + (edge.weight : WithTop Nat)

def relax (labels : Labels Vertex) (edge : Arc Vertex) : Labels Vertex :=
  KeyedImprovement.lower labels edge.target (proposal labels edge)

@[simp] theorem relax_target (labels : Labels Vertex) (edge : Arc Vertex) :
    relax labels edge edge.target = min (labels edge.target) (proposal labels edge) := by
  simp [relax, KeyedImprovement.lower]

theorem relax_other (labels : Labels Vertex) (edge : Arc Vertex) (vertex : Vertex)
    (apart : vertex ≠ edge.target) : relax labels edge vertex = labels vertex := by
  simp [relax, KeyedImprovement.lower, apart]

theorem relax_le (labels : Labels Vertex) (edge : Arc Vertex) : relax labels edge ≤ labels := by
  intro vertex
  by_cases same : vertex = edge.target
  · subst vertex
    rw [relax_target]
    exact min_le_left _ _
  · rw [relax_other labels edge vertex same]

theorem relax_of_not_better (labels : Labels Vertex) (edge : Arc Vertex)
    (notBetter : ¬ proposal labels edge < labels edge.target) : relax labels edge = labels := by
  funext vertex
  by_cases same : vertex = edge.target
  · subst vertex
    rw [relax_target]
    exact min_eq_left (le_of_not_gt notBetter)
  · exact relax_other labels edge vertex same

theorem relax_lt_of_better (labels : Labels Vertex) (edge : Arc Vertex)
    (better : proposal labels edge < labels edge.target) : relax labels edge < labels := by
  apply lt_of_le_of_ne (relax_le labels edge)
  intro same
  have atTarget := congrFun same edge.target
  rw [relax_target, min_eq_right (le_of_lt better)] at atTarget
  exact (ne_of_lt better) atTarget

theorem relax_mono (edge : Arc Vertex) : Monotone (fun labels : Labels Vertex => relax labels edge) := by
  intro before after ordered vertex
  by_cases same : vertex = edge.target
  · subst vertex
    simp only [relax_target]
    apply min_le_min (ordered _)
    exact add_le_add (ordered edge.source) le_rfl
  · simpa [relax_other _ _ _ same] using ordered vertex

def Closed (graph : List (Arc Vertex)) (labels : Labels Vertex) : Prop :=
  ∀ edge ∈ graph, labels edge.target ≤ proposal labels edge

/-- Edge occurrences are authorized by the graph; parallel weighted edges
are allowed. This construction reuses Mathlib's path type and weight fold. -/
abbrev pathQuiver (graph : List (Arc Vertex)) : Quiver Vertex where
  Hom source target := {edge : Arc Vertex // edge ∈ graph ∧ edge.source = source ∧ edge.target = target}

abbrev Path (graph : List (Arc Vertex)) (source target : Vertex) :=
  @Quiver.Path Vertex (pathQuiver graph) source target

def pathWeight (graph : List (Arc Vertex)) {source target : Vertex} (path : Path graph source target) : Nat :=
  @Quiver.Path.addWeight Vertex (pathQuiver graph) Nat inferInstance (fun {_ _} edge => edge.1.weight) _ _ path

def edgeWitness (graph : List (Arc Vertex)) (edge : Arc Vertex) (member : edge ∈ graph) :
    (pathQuiver graph).Hom edge.source edge.target := ⟨edge, member, rfl, rfl⟩

noncomputable def distance (graph : List (Arc Vertex)) (root vertex : Vertex) : WithTop Nat :=
  ⨅ path : Path graph root vertex, (pathWeight graph path : WithTop Nat)

def PathSound (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex) : Prop :=
  ∀ (vertex : Vertex) (cost : Nat), labels vertex = (cost : WithTop Nat) →
    ∃ path : Path graph root vertex, pathWeight graph path = cost

theorem initial_sound (graph : List (Arc Vertex)) (root : Vertex) : PathSound graph root (initial root) := by
  intro vertex cost held
  by_cases same : vertex = root
  · subst vertex
    have zero : cost = 0 := by simpa [initial] using held.symm
    subst cost
    exact ⟨@Quiver.Path.nil Vertex (pathQuiver graph) root, by simp [pathWeight]⟩
  · simp [initial, same] at held

theorem relax_sound (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex)
    (edge : Arc Vertex) (member : edge ∈ graph) (sound : PathSound graph root labels) :
    PathSound graph root (relax labels edge) := by
  let : Quiver Vertex := pathQuiver graph
  by_cases better : proposal labels edge < labels edge.target
  · intro vertex cost held
    by_cases same : vertex = edge.target
    · subst vertex
      rw [relax_target, min_eq_right (le_of_lt better)] at held
      cases sourceValue : labels edge.source with
      | top => simp [proposal, sourceValue] at held
      | coe previous =>
          have previousEq : labels edge.source = (previous : WithTop Nat) := sourceValue
          obtain ⟨path, weight⟩ := sound edge.source previous previousEq
          have total : previous + edge.weight = cost := by
            simp only [proposal, sourceValue] at held
            change WithTop.some (previous + edge.weight) = WithTop.some cost at held
            exact WithTop.coe_injective held
          refine ⟨path.cons (edgeWitness graph edge member), ?_⟩
          simp only [pathWeight, Quiver.Path.addWeight_cons]
          change pathWeight graph path + edge.weight = cost
          rw [weight]
          exact total
    · exact sound vertex cost (by simpa [relax_other _ _ _ same] using held)
  · rw [relax_of_not_better labels edge better]
    exact sound

omit [DecidableEq Vertex] in
theorem distance_le_of_sound (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex)
    (sound : PathSound graph root labels) : distance graph root ≤ labels := by
  intro vertex
  cases held : labels vertex with
  | top => exact le_top
  | coe cost =>
      have finiteEq : labels vertex = (cost : WithTop Nat) := held
      obtain ⟨path, weight⟩ := sound vertex cost finiteEq
      exact (iInf_le (fun path : Path graph root vertex => (pathWeight graph path : WithTop Nat)) path).trans_eq
        (congrArg (fun value : Nat => (value : WithTop Nat)) weight)

theorem closed_le_path (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex)
    (seedBound : labels ≤ initial root) (closed : Closed graph labels)
    {vertex : Vertex} (path : Path graph root vertex) : labels vertex ≤ (pathWeight graph path : WithTop Nat) := by
  let : Quiver Vertex := pathQuiver graph
  induction path with
  | nil => simpa [initial, pathWeight, Quiver.Path.addWeight] using seedBound root
  | @cons before after path edge ih =>
      have edgeBound := closed edge.1 edge.2.1
      unfold proposal at edgeBound
      rw [edge.2.2.1, edge.2.2.2] at edgeBound
      calc
        labels after ≤ labels before + (edge.1.weight : WithTop Nat) := edgeBound
        _ ≤ (pathWeight graph path : WithTop Nat) + (edge.1.weight : WithTop Nat) := add_le_add ih le_rfl
        _ = (pathWeight graph (path.cons edge) : WithTop Nat) := by
          simp [pathWeight]

theorem closed_le_distance (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex)
    (seedBound : labels ≤ initial root) (closed : Closed graph labels) : labels ≤ distance graph root := by
  intro vertex
  exact le_iInf (fun path => closed_le_path graph root labels seedBound closed path)

/-- Closure plus actual path provenance proves shortest distances independently
of the implementation that reached the store. -/
theorem closed_sound_eq_distance (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex)
    (seedBound : labels ≤ initial root) (closed : Closed graph labels) (sound : PathSound graph root labels) :
    labels = distance graph root :=
  le_antisymm (closed_le_distance graph root labels seedBound closed) (distance_le_of_sound graph root labels sound)

end Mettapedia.Machines.WeightedRelaxation
