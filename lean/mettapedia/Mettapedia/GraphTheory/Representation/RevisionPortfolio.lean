import Mettapedia.GraphTheory.Representation.RevisionQuery
import Mettapedia.GraphTheory.Representation.RepresentationGSLT

/-!
# A revision/query world model over the graph representation portfolio

The canonical rebuild editor is deliberately simple and source-derived:

1. construct the representation's canonical adjacency matrix;
2. edit the two addressed symmetric cells;
3. materialize the same layout again.

For matrices the first and third phases are identities, giving the natural
two-write update.  Other layouts receive a correct baseline, not a claim that
rebuilding is their best native editor.  Future specialized editors can refine
this baseline and compare exact resource accounts.
-/

namespace Mettapedia.GraphTheory.Representation.RevisionPortfolio

open Mettapedia.GraphTheory.Representation
open Mettapedia.GraphTheory.Representation.Transformations
open Mettapedia.GraphTheory.Representation.RepresentationGSLT

set_option autoImplicit false

/-- Does the unordered address select the queried ordered cell? -/
def addressMatches {n : Nat} (edge : EdgeAddress n) (u v : Fin n) : Bool :=
  ((u == edge.first) && (v == edge.second)) ||
    ((u == edge.second) && (v == edge.first))

@[simp] theorem addressMatches_eq_true_iff {n : Nat}
    (edge : EdgeAddress n) (u v : Fin n) :
    addressMatches edge u v = true ↔
      (u = edge.first ∧ v = edge.second) ∨
        (u = edge.second ∧ v = edge.first) := by
  simp [addressMatches, Bool.or_eq_true, Bool.and_eq_true]

theorem addressMatches_comm {n : Nat} (edge : EdgeAddress n) (u v : Fin n) :
    addressMatches edge u v = addressMatches edge v u := by
  rw [Bool.eq_iff_iff]
  simp only [addressMatches_eq_true_iff]
  aesop

@[simp] theorem addressMatches_self {n : Nat} (edge : EdgeAddress n)
    (vertex : Fin n) : addressMatches edge vertex vertex = false := by
  apply Bool.eq_false_iff.mpr
  intro matched
  obtain (⟨first, second⟩ | ⟨first, second⟩) :=
    (addressMatches_eq_true_iff edge vertex vertex).mp matched
  · exact edge.different (first.symm.trans second)
  · exact edge.different (second.symm.trans first)

/-- Direct symmetric matrix-cell edit. -/
def editMatrix {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    EdgeEdit n → AdjacencyMatrix.Rep n
  | .insert selected =>
      { cell := fun u v =>
          if addressMatches selected u v then true else graph.cell u v
        symmetric := by
          intro u v
          rw [addressMatches_comm selected u v, graph.symmetric u v]
        loopless := by
          intro vertex
          simp [graph.loopless vertex] }
  | .erase selected =>
      { cell := fun u v =>
          if addressMatches selected u v then false else graph.cell u v
        symmetric := by
          intro u v
          rw [addressMatches_comm selected u v, graph.symmetric u v]
        loopless := by
          intro vertex
          simp [graph.loopless vertex] }

theorem editMatrix_commutes {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (change : EdgeEdit n) :
    AdjacencyMatrix.denote (editMatrix graph change) =
      applyMeaning (AdjacencyMatrix.denote graph) change := by
  ext u v
  cases change with
  | insert selected =>
      simp [AdjacencyMatrix.denote, editMatrix, addressMatches_eq_true_iff]
      tauto
  | erase selected =>
      simp [AdjacencyMatrix.denote, editMatrix, addressMatches_eq_true_iff]
      tauto

/-- Recover the current layout tag without inspecting semantic meaning. -/
def layoutOf {n : Nat} : State n → Layout
  | .edgeList _ => .edgeList
  | .matrix _ => .matrix
  | .adjacencyRows _ => .adjacencyRows
  | .neighborFinsets _ => .neighborFinsets
  | .incidence _ => .incidence
  | .csr _ => .csr

def stateStorageCells {n : Nat} : State n → Nat
  | .edgeList graph => EdgeList.storageCells graph
  | .matrix graph => AdjacencyMatrix.storageCells graph
  | .adjacencyRows graph => AdjacencyRows.storageCells graph
  | .neighborFinsets graph => NeighborFinsets.storageCells graph
  | .incidence graph => IncidenceMatrix.storageCells graph
  | .csr graph => CSR.storageCells graph

/-- Canonical rebuild editor. -/
def editState {n : Nat} (state : State n) (change : EdgeEdit n) : State n :=
  materialize (layoutOf state) (editMatrix (canonicalMatrix state) change)

/-- The rebuild editor performs exactly the independent graph edit. -/
theorem editState_commutes {n : Nat} (state : State n)
    (change : EdgeEdit n) :
    (editState state change).denote = applyMeaning state.denote change := by
  have materialized :
      (materialize (layoutOf state)
        (editMatrix (canonicalMatrix state) change)).denote =
        AdjacencyMatrix.denote (editMatrix (canonicalMatrix state) change) := by
    have route :=
      (convertPath_commutes
        (State.matrix (editMatrix (canonicalMatrix state) change))
        (layoutOf state)).symm
    change
      (materialize (layoutOf state)
        (editMatrix (canonicalMatrix state) change)).denote =
      AdjacencyMatrix.denote (editMatrix (canonicalMatrix state) change) at route
    exact route
  have canonical :
      AdjacencyMatrix.denote (canonicalMatrix state) = state.denote := by
    have route := (convertPath_commutes state .matrix).symm
    change AdjacencyMatrix.denote (canonicalMatrix state) = state.denote at route
    exact route
  rw [editState, materialized, editMatrix_commutes, canonical]

/-! ## Exact schedule accounting -/

/-- Strictly probing every ordered pair through the current representation. -/
def canonicalizationTime {n : Nat} (state : State n) : Nat :=
  match state with
  | .edgeList graph =>
      (List.ofFn fun u =>
        (List.ofFn fun v => (EdgeList.edge graph u v).work).sum).sum
  | .matrix _ => 0
  | .adjacencyRows graph =>
      (List.ofFn fun u =>
        (List.ofFn fun v => (AdjacencyRows.edge graph u v).work).sum).sum
  | .neighborFinsets _ => n * n
  | .incidence graph =>
      (List.ofFn fun u =>
        (List.ofFn fun v => (IncidenceMatrix.edge graph u v).work).sum).sum
  | .csr graph =>
      (List.ofFn fun u =>
        (List.ofFn fun v => (CSR.edge graph u v).work).sum).sum

/-- Strict target construction schedule after the edited matrix is available.
These counts are structural cell visits, not cache or wall-clock claims. -/
def materializationTime {n : Nat} (layout : Layout)
    (graph : AdjacencyMatrix.Rep n) : Nat :=
  match layout with
  | .matrix => 0
  | .edgeList => n * n
  | .adjacencyRows => n * n
  | .neighborFinsets => n * n
  | .incidence =>
      n * n + n * (matrixToEdgeList graph).entries.length
  | .csr => n * n + (AdjacencyRows.storageCells (matrixToRows graph))

/-- Exact account for the canonical editor's declared strict schedule. -/
def editResources {n : Nat} (state : State n) (change : EdgeEdit n) :
    Resources :=
  match state with
  | .matrix _ =>
      { time := 2, writes := 2 }
  | _ =>
      let target := editState state change
      { time := canonicalizationTime state + 2 +
          materializationTime (layoutOf state)
            (editMatrix (canonicalMatrix state) change)
        reads := canonicalizationTime state
        writes := 2
        allocated := stateStorageCells target
        peakTemporary := stateStorageCells target }

/-- Matrix edits satisfy the structural in-place criterion. -/
theorem matrix_edit_isInPlace {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (change : EdgeEdit n) :
    IsInPlace (editResources (.matrix graph) change) := by
  simp [editResources, IsInPlace]

/-- Any non-matrix rebuild with a nonempty target allocation is not in-place. -/
theorem rebuild_not_inPlace_of_target_storage_positive {n : Nat}
    (state : State n) (change : EdgeEdit n)
    (notMatrix : ∀ graph, state ≠ .matrix graph)
    (positive : 0 < stateStorageCells (editState state change)) :
    ¬ IsInPlace (editResources state change) := by
  cases state with
  | matrix graph => exact (notMatrix graph rfl).elim
  | edgeList graph =>
      intro inPlace
      exact (Nat.ne_of_gt positive) (by
        simpa [editResources, IsInPlace] using inPlace.1)
  | adjacencyRows graph =>
      intro inPlace
      exact (Nat.ne_of_gt positive) (by
        simpa [editResources, IsInPlace] using inPlace.1)
  | neighborFinsets graph =>
      intro inPlace
      exact (Nat.ne_of_gt positive) (by
        simpa [editResources, IsInPlace] using inPlace.1)
  | incidence graph =>
      intro inPlace
      exact (Nat.ne_of_gt positive) (by
        simpa [editResources, IsInPlace] using inPlace.1)
  | csr graph =>
      intro inPlace
      exact (Nat.ne_of_gt positive) (by
        simpa [editResources, IsInPlace] using inPlace.1)

/-! ## Portfolio presentation and WM realization -/

def stateEdgeMeasured {n : Nat} (state : State n) (u v : Fin n) :
    Measured Bool :=
  match state with
  | .edgeList graph => EdgeList.edge graph u v
  | .matrix graph => AdjacencyMatrix.edge graph u v
  | .adjacencyRows graph => AdjacencyRows.edge graph u v
  | .neighborFinsets graph => NeighborFinsets.edge graph u v
  | .incidence graph => IncidenceMatrix.edge graph u v
  | .csr graph => CSR.edge graph u v

theorem stateEdgeMeasured_sound {n : Nat} (state : State n) (u v : Fin n) :
    (stateEdgeMeasured state u v).value = true ↔ state.denote.Adj u v := by
  cases state with
  | edgeList graph => exact EdgeList.edge_sound graph u v
  | matrix graph => exact AdjacencyMatrix.edge_sound graph u v
  | adjacencyRows graph => exact AdjacencyRows.edge_sound graph u v
  | neighborFinsets graph => exact NeighborFinsets.edge_sound graph u v
  | incidence graph => exact IncidenceMatrix.edge_sound graph u v
  | csr graph => exact CSR.edge_sound graph u v

def statePresentation (n : Nat) : Presentation n where
  Carrier := State n
  denote := State.denote
  edge := stateEdgeMeasured
  edge_sound := stateEdgeMeasured_sound
  storageCells := stateStorageCells

def editablePortfolio (n : Nat) : EditablePresentation n :=
  { statePresentation n with
  edit := fun (state : State n) change =>
    ⟨editState state change, editResources state change⟩
  edit_sound := editState_commutes }

/-- Cellwise union of two canonical matrices. -/
def unionMatrix {n : Nat} (first second : AdjacencyMatrix.Rep n) :
    AdjacencyMatrix.Rep n where
  cell := fun u v => first.cell u v || second.cell u v
  symmetric := by
    intro u v
    rw [first.symmetric u v, second.symmetric u v]
  loopless := by
    intro vertex
    simp [first.loopless vertex, second.loopless vertex]

theorem unionMatrix_denote {n : Nat}
    (first second : AdjacencyMatrix.Rep n) :
    AdjacencyMatrix.denote (unionMatrix first second) =
      AdjacencyMatrix.denote first ⊔ AdjacencyMatrix.denote second := by
  ext u v
  simp [AdjacencyMatrix.denote, unionMatrix, Bool.or_eq_true]

/-- Revision keeps the first state's layout and unions the represented graph. -/
def reviseState {n : Nat} (first second : State n) : State n :=
  materialize (layoutOf first)
    (unionMatrix (canonicalMatrix first) (canonicalMatrix second))

theorem reviseState_commutes {n : Nat} (first second : State n) :
    (reviseState first second).denote = first.denote ⊔ second.denote := by
  have materialized :
      (reviseState first second).denote =
        AdjacencyMatrix.denote
          (unionMatrix (canonicalMatrix first) (canonicalMatrix second)) := by
    have route :=
      (convertPath_commutes
        (State.matrix
          (unionMatrix (canonicalMatrix first) (canonicalMatrix second)))
        (layoutOf first)).symm
    change
      (materialize (layoutOf first)
        (unionMatrix (canonicalMatrix first) (canonicalMatrix second))).denote =
      AdjacencyMatrix.denote
        (unionMatrix (canonicalMatrix first) (canonicalMatrix second)) at route
    simpa [reviseState] using route
  have firstCanonical :
      AdjacencyMatrix.denote (canonicalMatrix first) = first.denote := by
    have route := (convertPath_commutes first .matrix).symm
    change AdjacencyMatrix.denote (canonicalMatrix first) = first.denote at route
    exact route
  have secondCanonical :
      AdjacencyMatrix.denote (canonicalMatrix second) = second.denote := by
    have route := (convertPath_commutes second .matrix).symm
    change AdjacencyMatrix.denote (canonicalMatrix second) = second.denote at route
    exact route
  rw [materialized, unionMatrix_denote, firstCanonical, secondCanonical]

def graphWorld (n : Nat) : GraphWorldPresentation n where
  toPresentation := statePresentation n
  edit := fun (state : State n) change =>
    ⟨editState state change, editResources state change⟩
  edit_sound := editState_commutes
  empty := State.matrix (AdjacencyMatrix.empty n)
  revise := fun (first second : State n) => reviseState first second
  empty_sound := by
    exact AdjacencyMatrix.empty_denote n
  revise_sound := reviseState_commutes

namespace Canary

open EdgeList.Canary

def insert02 : EdgeEdit 3 :=
  .insert ⟨v0, v2, by decide⟩

/-- The canonical edit of the edge-list path really adds its missing chord. -/
theorem edgeList_insert_observable :
    (editState (.edgeList path3) insert02).denote.Adj v0 v2 := by
  rw [editState_commutes]
  simp [insert02]

/-- The same edit is a two-write, allocation-free matrix operation. -/
theorem matrix_insert_two_writes :
    (editResources
      (.matrix (canonicalMatrix (.edgeList path3))) insert02).writes = 2 ∧
    (editResources
      (.matrix (canonicalMatrix (.edgeList path3))) insert02).allocated = 0 := by
  decide

/-- Negative control: the canonical edge-list editor is a rebuild, not an
in-place edit. -/
theorem edgeList_insert_not_inPlace :
    ¬ IsInPlace (editResources (.edgeList path3) insert02) := by
  apply rebuild_not_inPlace_of_target_storage_positive
  · intro graph same
    cases same
  · decide

end Canary

#print axioms editMatrix_commutes
#print axioms editState_commutes
#print axioms matrix_edit_isInPlace
#print axioms stateEdgeMeasured_sound
#print axioms reviseState_commutes
#print axioms Canary.edgeList_insert_observable
#print axioms Canary.edgeList_insert_not_inPlace

end Mettapedia.GraphTheory.Representation.RevisionPortfolio
