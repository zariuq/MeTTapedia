import Mettapedia.GraphTheory.Representation.EdgeList
import Mettapedia.GraphTheory.Representation.AdjacencyMatrix
import Mettapedia.GraphTheory.Representation.AdjacencyRows
import Mettapedia.GraphTheory.Representation.NeighborFinsets
import Mettapedia.GraphTheory.Representation.IncidenceMatrix
import Mettapedia.GraphTheory.Representation.CSR

/-!
# Sound transformations between finite graph representations

The constructions in this module are representation rules in the
Essence/Conjure sense, strengthened with commuting theorems.  The matrix is a
useful common materialisation target because every presentation already
supplies a proved Boolean edge observer.  Edge lists and adjacency rows also
have direct matrix refinements, so transformations compose without consulting
an external graph oracle.
-/

namespace Mettapedia.GraphTheory.Representation.Transformations

open Mettapedia.GraphTheory.Representation

/-- Materialise the proved edge observer of any presentation as an adjacency
matrix.  The construction reads representation data; it does not call the
semantic denotation to obtain its cells. -/
def toMatrix {n : Nat} (source : Presentation n)
    (graph : source.Carrier) : AdjacencyMatrix.Rep n where
  cell := fun u v => (source.edge graph u v).value
  symmetric := by
    intro u v
    rw [Bool.eq_iff_iff, source.edge_sound, source.edge_sound]
    exact (source.denote graph).adj_comm u v
  loopless := by
    intro vertex
    cases observed : (source.edge graph vertex vertex).value with
    | false => rfl
    | true =>
        exact ((source.denote graph).loopless.irrefl vertex
          ((source.edge_sound graph vertex vertex).mp observed)).elim

/-- Materialisation commutes with the independent simple-graph meaning. -/
theorem toMatrix_commutes {n : Nat} (source : Presentation n)
    (graph : source.Carrier) :
    AdjacencyMatrix.denote (toMatrix source graph) = source.denote graph := by
  ext u v
  exact source.edge_sound graph u v

/-- Every finite graph presentation has a canonical sound route into the
adjacency-matrix presentation. -/
def toMatrixRule {n : Nat} (source : Presentation n) :
    Refinement source (AdjacencyMatrix.presentation n) where
  map := toMatrix source
  commute := toMatrix_commutes source

/-- Expand each matrix row into the ordered list of vertices whose cell is
true. -/
def matrixToRows {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    AdjacencyRows.Rep n where
  row source := (List.ofFn (id : Fin n → Fin n)).filter
    fun target => graph.cell source target
  symmetric := by
    intro source target
    simp only [List.mem_filter]
    constructor
    · rintro ⟨_, adjacent⟩
      exact ⟨List.mem_ofFn.mpr ⟨source, rfl⟩, by
        rw [← graph.symmetric source target]
        exact adjacent⟩
    · rintro ⟨_, adjacent⟩
      exact ⟨List.mem_ofFn.mpr ⟨target, rfl⟩, by
        rw [graph.symmetric source target]
        exact adjacent⟩
  loopless := by
    intro vertex
    simp [graph.loopless vertex]
  nodup := by
    intro vertex
    have allNodup : (List.ofFn (id : Fin n → Fin n)).Nodup :=
      List.nodup_ofFn.mpr Function.injective_id
    exact allNodup.filter _

theorem matrixToRows_commutes {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    AdjacencyRows.denote (matrixToRows graph) =
      AdjacencyMatrix.denote graph := by
  ext source target
  simp [AdjacencyRows.denote, AdjacencyMatrix.denote, matrixToRows]

def matrixToRowsRule (n : Nat) :
    Refinement (AdjacencyMatrix.presentation n)
      (AdjacencyRows.presentation n) where
  map := matrixToRows
  commute := matrixToRows_commutes

/-- Read row membership back into a Boolean matrix. -/
def rowsToMatrix {n : Nat} (graph : AdjacencyRows.Rep n) :
    AdjacencyMatrix.Rep n where
  cell := fun source target => decide (target ∈ graph.row source)
  symmetric := by
    intro source target
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    exact graph.symmetric source target
  loopless := by
    intro vertex
    simp [graph.loopless vertex]

theorem rowsToMatrix_commutes {n : Nat} (graph : AdjacencyRows.Rep n) :
    AdjacencyMatrix.denote (rowsToMatrix graph) =
      AdjacencyRows.denote graph := by
  ext source target
  simp [AdjacencyMatrix.denote, AdjacencyRows.denote, rowsToMatrix]

def rowsToMatrixRule (n : Nat) :
    Refinement (AdjacencyRows.presentation n)
      (AdjacencyMatrix.presentation n) where
  map := rowsToMatrix
  commute := rowsToMatrix_commutes

/-- Materialise every true matrix cell in the finite neighbour set of its
source.  This is the set-valued sibling of `matrixToRows`: it deliberately
forgets enumeration order while retaining exact adjacency. -/
def matrixToNeighborFinsets {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    NeighborFinsets.Rep n where
  row source := Finset.univ.filter fun target => graph.cell source target
  symmetric := by
    intro source target
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [graph.symmetric source target]
  loopless := by
    intro vertex
    simp [graph.loopless vertex]

theorem matrixToNeighborFinsets_commutes {n : Nat}
    (graph : AdjacencyMatrix.Rep n) :
    NeighborFinsets.denote (matrixToNeighborFinsets graph) =
      AdjacencyMatrix.denote graph := by
  ext source target
  simp [NeighborFinsets.denote, AdjacencyMatrix.denote,
    matrixToNeighborFinsets]

def matrixToNeighborFinsetsRule (n : Nat) :
    Refinement (AdjacencyMatrix.presentation n)
      (NeighborFinsets.presentation n) where
  map := matrixToNeighborFinsets
  commute := matrixToNeighborFinsets_commutes

/-- The matrix/finite-set round trip preserves the complete graph meaning.
This law intentionally does not claim that a concrete finite-set
implementation has the matrix's physical layout or lookup cost. -/
theorem matrix_neighborFinsets_roundTrip_commutes {n : Nat}
    (graph : AdjacencyMatrix.Rep n) :
    AdjacencyMatrix.denote
        (toMatrix (NeighborFinsets.presentation n)
          (matrixToNeighborFinsets graph)) =
      AdjacencyMatrix.denote graph := by
  exact
    (toMatrix_commutes (NeighborFinsets.presentation n)
      (matrixToNeighborFinsets graph)).trans
        (matrixToNeighborFinsets_commutes graph)

/-- Serialize every true directed matrix cell as an edge occurrence.  For a
symmetric simple matrix this contains both orientations.  The edge-list
denotation intentionally forgets that duplication. -/
def matrixToEdgeList {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    EdgeList.Rep n where
  entries := (List.ofFn (id : Fin n → Fin n)).flatMap fun source =>
    ((List.ofFn (id : Fin n → Fin n)).filter
      fun target => graph.cell source target).map fun target =>
        EdgeList.Edge.mk source target

theorem matrixToEdgeList_mem {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    EdgeList.Edge.mk source target ∈ (matrixToEdgeList graph).entries ↔
      graph.cell source target = true := by
  simp [matrixToEdgeList]

theorem matrixToEdgeList_commutes {n : Nat}
    (graph : AdjacencyMatrix.Rep n) :
    EdgeList.denote (matrixToEdgeList graph) =
      AdjacencyMatrix.denote graph := by
  ext source target
  rw [← EdgeList.edge_sound]
  simp only [EdgeList.edge]
  rw [LinearProbe.run_value_eq_any]
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨occurrence, member, accepted⟩
    obtain ⟨different, direct | reverse⟩ :=
      (EdgeList.accepts_eq_true_iff occurrence (source, target)).mp accepted
    · have occurrenceEq : occurrence = EdgeList.Edge.mk source target := by
        cases occurrence
        simp_all
      rw [occurrenceEq, matrixToEdgeList_mem] at member
      exact member
    · have occurrenceEq : occurrence = EdgeList.Edge.mk target source := by
        cases occurrence
        simp_all
      rw [occurrenceEq, matrixToEdgeList_mem] at member
      change graph.cell source target = true
      rw [graph.symmetric source target]
      exact member
  · intro adjacent
    have adjacentCell : graph.cell source target = true := adjacent
    have member : EdgeList.Edge.mk source target ∈
        (matrixToEdgeList graph).entries :=
      (matrixToEdgeList_mem graph source target).mpr adjacentCell
    exact ⟨EdgeList.Edge.mk source target, member,
      (EdgeList.accepts_eq_true_iff _ _).mpr
        ⟨by
          intro equal
          have same : source = target := by simpa using equal
          subst target
          rw [graph.loopless source] at adjacentCell
          contradiction,
        Or.inl ⟨rfl, rfl⟩⟩⟩

def matrixToEdgeListRule (n : Nat) :
    Refinement (AdjacencyMatrix.presentation n)
      (EdgeList.presentation n) where
  map := matrixToEdgeList
  commute := matrixToEdgeList_commutes

/-- Give every serialized directed edge occurrence its own incidence column.
For an undirected matrix the two orientations become two columns.  The
incidence denotation forgets this harmless multiplicity, while the concrete
carrier retains it for occurrence-sensitive clients. -/
def matrixToIncidence {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    (IncidenceMatrix.dependentPresentation n).Carrier :=
  let entries := (matrixToEdgeList graph).entries
  ⟨entries.length,
    { cell := fun vertex column =>
        let occurrence := entries.get column
        decide (vertex = occurrence.source ∨ vertex = occurrence.target)
      columnSimple := by
        intro column
        let occurrence := entries.get column
        have occurrenceMember : occurrence ∈ entries :=
          List.get_mem entries column
        have occurrenceEta :
            EdgeList.Edge.mk occurrence.source occurrence.target = occurrence := by
          cases occurrence
          rfl
        have edgeMember :
            EdgeList.Edge.mk occurrence.source occurrence.target ∈ entries := by
          rw [occurrenceEta]
          exact occurrenceMember
        have adjacent :
            graph.cell occurrence.source occurrence.target = true :=
          (matrixToEdgeList_mem graph occurrence.source occurrence.target).mp
            edgeMember
        have different : occurrence.source ≠ occurrence.target := by
          intro same
          have loop : graph.cell occurrence.target occurrence.target = true := by
            simpa only [same] using adjacent
          rw [graph.loopless occurrence.target] at loop
          contradiction
        refine ⟨occurrence.source, occurrence.target, different, ?_⟩
        intro vertex
        simp [occurrence] }⟩

theorem matrixToIncidence_commutes {n : Nat}
    (graph : AdjacencyMatrix.Rep n) :
    IncidenceMatrix.denote (matrixToIncidence graph).2 =
      AdjacencyMatrix.denote graph := by
  ext source target
  constructor
  · rintro ⟨different, column, sourceCell, targetCell⟩
    let entries := (matrixToEdgeList graph).entries
    let occurrence := entries.get column
    have sourceEndpoint :
        source = occurrence.source ∨ source = occurrence.target := by
      simpa [matrixToIncidence, entries, occurrence] using sourceCell
    have targetEndpoint :
        target = occurrence.source ∨ target = occurrence.target := by
      simpa [matrixToIncidence, entries, occurrence] using targetCell
    have occurrenceMember : occurrence ∈ entries := List.get_mem entries column
    have occurrenceEta :
        EdgeList.Edge.mk occurrence.source occurrence.target = occurrence := by
      cases occurrence
      rfl
    have edgeMember :
        EdgeList.Edge.mk occurrence.source occurrence.target ∈ entries := by
      rw [occurrenceEta]
      exact occurrenceMember
    have adjacent : graph.cell occurrence.source occurrence.target = true :=
      (matrixToEdgeList_mem graph occurrence.source occurrence.target).mp
        edgeMember
    rcases sourceEndpoint with sourceFirst | sourceSecond <;>
      rcases targetEndpoint with targetFirst | targetSecond
    · exact (different (sourceFirst.trans targetFirst.symm)).elim
    · change graph.cell source target = true
      simpa only [sourceFirst, targetSecond] using adjacent
    · change graph.cell source target = true
      have reverse :
          graph.cell occurrence.target occurrence.source = true := by
        rw [← graph.symmetric occurrence.source occurrence.target]
        exact adjacent
      simpa only [sourceSecond, targetFirst] using reverse
    · exact (different (sourceSecond.trans targetSecond.symm)).elim
  · intro adjacent
    change graph.cell source target = true at adjacent
    have sourceTargetDifferent : source ≠ target := by
      intro same
      subst target
      rw [graph.loopless source] at adjacent
      contradiction
    let entries := (matrixToEdgeList graph).entries
    have edgeMember : EdgeList.Edge.mk source target ∈ entries :=
      (matrixToEdgeList_mem graph source target).mpr adjacent
    obtain ⟨column, getEq⟩ := List.get_of_mem edgeMember
    refine ⟨sourceTargetDifferent, column, ?_, ?_⟩
    · change decide
        (source = ((matrixToEdgeList graph).entries.get column).source ∨
          source = ((matrixToEdgeList graph).entries.get column).target) = true
      rw [getEq]
      simp
    · change decide
        (target = ((matrixToEdgeList graph).entries.get column).source ∨
          target = ((matrixToEdgeList graph).entries.get column).target) = true
      rw [getEq]
      simp

def matrixToIncidenceRule (n : Nat) :
    Refinement (AdjacencyMatrix.presentation n)
      (IncidenceMatrix.dependentPresentation n) where
  map := matrixToIncidence
  commute := matrixToIncidence_commutes

/-- Pack ordered adjacency rows into a CSR offset table and payload. -/
def rowsToCSR {n : Nat} (graph : AdjacencyRows.Rep n) : CSR.Rep n where
  offset := CSR.packOffset graph.row
  neighbors := CSR.packRows graph.row
  offset_zero := CSR.packOffset_zero graph.row
  offset_mono := CSR.packOffset_mono graph.row
  offset_last := CSR.packOffset_last graph.row
  symmetric := by
    intro source target
    change target ∈
        ((CSR.packRows graph.row).drop
          (CSR.packOffset graph.row source.castSucc)).take
            (CSR.packOffset graph.row source.succ -
              CSR.packOffset graph.row source.castSucc) ↔
      source ∈
        ((CSR.packRows graph.row).drop
          (CSR.packOffset graph.row target.castSucc)).take
            (CSR.packOffset graph.row target.succ -
              CSR.packOffset graph.row target.castSucc)
    rw [CSR.packedRow_eq, CSR.packedRow_eq]
    exact graph.symmetric source target
  loopless := by
    intro vertex
    change vertex ∉
      ((CSR.packRows graph.row).drop
        (CSR.packOffset graph.row vertex.castSucc)).take
          (CSR.packOffset graph.row vertex.succ -
            CSR.packOffset graph.row vertex.castSucc)
    rw [CSR.packedRow_eq]
    exact graph.loopless vertex
  nodup := by
    intro vertex
    change (((CSR.packRows graph.row).drop
      (CSR.packOffset graph.row vertex.castSucc)).take
        (CSR.packOffset graph.row vertex.succ -
          CSR.packOffset graph.row vertex.castSucc)).Nodup
    rw [CSR.packedRow_eq]
    exact graph.nodup vertex

theorem rowsToCSR_row {n : Nat} (graph : AdjacencyRows.Rep n)
    (vertex : Fin n) :
    CSR.row (rowsToCSR graph) vertex = graph.row vertex := by
  exact CSR.packedRow_eq graph.row vertex

theorem rowsToCSR_commutes {n : Nat} (graph : AdjacencyRows.Rep n) :
    CSR.denote (rowsToCSR graph) = AdjacencyRows.denote graph := by
  ext source target
  simp only [CSR.denote, AdjacencyRows.denote]
  rw [rowsToCSR_row]

def rowsToCSRRule (n : Nat) :
    Refinement (AdjacencyRows.presentation n) (CSR.presentation n) where
  map := rowsToCSR
  commute := rowsToCSR_commutes

/-- Matrix-to-CSR is the lawful composite of row expansion and packing. -/
def matrixToCSRRule (n : Nat) :
    Refinement (AdjacencyMatrix.presentation n) (CSR.presentation n) :=
  (matrixToRowsRule n).comp (rowsToCSRRule n)

/-- Edge-list-to-row refinement obtained by lawful composition through the
matrix waist. -/
def edgeListToRowsRule (n : Nat) :
    Refinement (EdgeList.presentation n) (AdjacencyRows.presentation n) :=
  (toMatrixRule (EdgeList.presentation n)).comp (matrixToRowsRule n)

/-- Incidence-to-row refinement: materialise adjacency, then expose neighbour
rows. -/
def incidenceToRowsRule (n m : Nat) :
    Refinement (IncidenceMatrix.presentation n m)
      (AdjacencyRows.presentation n) :=
  (toMatrixRule (IncidenceMatrix.presentation n m)).comp
    (matrixToRowsRule n)

/-- CSR-to-edge-list refinement composed from two independently proved rules. -/
def csrToEdgeListRule (n : Nat) :
    Refinement (CSR.presentation n) (EdgeList.presentation n) :=
  (toMatrixRule (CSR.presentation n)).comp (matrixToEdgeListRule n)

/-- The fundamental no-invention law for every representation rule. -/
theorem target_adj_iff_source_adj {n : Nat}
    {source target : Presentation n} (rule : Refinement source target)
    (graph : source.Carrier) (u v : Fin n) :
    (target.denote (rule.map graph)).Adj u v ↔
      (source.denote graph).Adj u v := by
  rw [rule.commute]

/-- Composed routes retain the same exact no-invention statement. -/
theorem composed_target_adj_iff_source_adj {n : Nat}
    {first middle last : Presentation n}
    (earlier : Refinement first middle) (later : Refinement middle last)
    (graph : first.Carrier) (u v : Fin n) :
    (last.denote ((earlier.comp later).map graph)).Adj u v ↔
      (first.denote graph).Adj u v :=
  target_adj_iff_source_adj (earlier.comp later) graph u v

#print axioms toMatrix_commutes
#print axioms matrixToRows_commutes
#print axioms rowsToMatrix_commutes
#print axioms matrixToNeighborFinsets_commutes
#print axioms matrix_neighborFinsets_roundTrip_commutes
#print axioms matrixToEdgeList_commutes
#print axioms matrixToIncidence_commutes
#print axioms rowsToCSR_commutes
#print axioms target_adj_iff_source_adj
#print axioms composed_target_adj_iff_source_adj

end Mettapedia.GraphTheory.Representation.Transformations
