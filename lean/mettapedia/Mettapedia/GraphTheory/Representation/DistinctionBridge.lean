import Mettapedia.GraphTheory.Representation.MatrixBridge
import Mettapedia.OSLF.Framework.DistinctionGraph

/-!
# OSLF distinction graphs and finite matrix realizations

Observer distinction is defined semantically by OSLF formulas.  It induces a
standard Mathlib simple graph.  A finite sample can be compiled to the proved
adjacency-matrix GSLT when a decision procedure for the sampled pairs is
supplied.  The Boolean matrix retains the distinction relation but erases the
formula occurrence that witnessed it.
-/

namespace Mettapedia.GraphTheory.Representation.DistinctionBridge

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Formula

set_option autoImplicit false

abbrev Pat := DistinctionGraph.Pat

/-- The standard graph independently induced by OSLF observational
distinguishability. -/
def semanticGraph (R : Pat → Pat → Prop) (I : AtomSem) : SimpleGraph Pat where
  Adj := DistinctionGraph.distinguished R I
  symm := ⟨fun _ _ => DistinctionGraph.distinguished_symm⟩
  loopless := ⟨DistinctionGraph.distinguished_irrefl R I⟩

@[simp] theorem semanticGraph_adj_iff (R : Pat → Pat → Prop)
    (I : AtomSem) (first second : Pat) :
    (semanticGraph R I).Adj first second ↔
      DistinctionGraph.distinguished R I first second :=
  Iff.rfl

/-- Every semantic graph edge reconstructs an actual separating formula. -/
theorem semanticGraph_edge_has_separator {R : Pat → Pat → Prop}
    {I : AtomSem} {first second : Pat}
    (edge : (semanticGraph R I).Adj first second) :
    ∃ formula,
      sem R I formula first ∧ ¬ sem R I formula second :=
  DistinctionGraph.distinguished_has_separator edge

/-- A finite family of observer states together with an explicit decision
procedure for every sampled distinction question. -/
structure Sample (n : Nat) (R : Pat → Pat → Prop) (I : AtomSem) where
  node : Fin n → Pat
  decision : ∀ first second,
    Decidable (DistinctionGraph.distinguished R I (node first) (node second))

/-- The ordinary finite graph induced by a sample. -/
def Sample.graph {n : Nat} {R : Pat → Pat → Prop} {I : AtomSem}
    (sample : Sample n R I) : SimpleGraph (Fin n) where
  Adj first second :=
    DistinctionGraph.distinguished R I (sample.node first) (sample.node second)
  symm := ⟨fun _ _ => DistinctionGraph.distinguished_symm⟩
  loopless := ⟨fun vertex =>
    DistinctionGraph.distinguished_irrefl R I (sample.node vertex)⟩

/-- Compile the sampled semantic relation to a Boolean adjacency matrix. -/
def compile {n : Nat} {R : Pat → Pat → Prop} {I : AtomSem}
    (sample : Sample n R I) : AdjacencyMatrix.Rep n where
  cell first second := @decide
    (DistinctionGraph.distinguished R I
      (sample.node first) (sample.node second))
    (sample.decision first second)
  symmetric := by
    intro first second
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact ⟨DistinctionGraph.distinguished_symm,
      DistinctionGraph.distinguished_symm⟩
  loopless := by
    intro vertex
    rw [decide_eq_false_iff_not]
    exact DistinctionGraph.distinguished_irrefl R I (sample.node vertex)

theorem compile_cell_iff {n : Nat} {R : Pat → Pat → Prop}
    {I : AtomSem} (sample : Sample n R I) (first second : Fin n) :
    (compile sample).cell first second = true ↔
      DistinctionGraph.distinguished R I
        (sample.node first) (sample.node second) := by
  simp [compile]

/-- Compilation commutes with the independent finite distinction graph. -/
theorem compile_commutes {n : Nat} {R : Pat → Pat → Prop}
    {I : AtomSem} (sample : Sample n R I) :
    AdjacencyMatrix.denote (compile sample) = sample.graph := by
  ext first second
  exact compile_cell_iff sample first second

/-! ## Transformation GSLT -/

inductive TransformState (n : Nat) (R : Pat → Pat → Prop) (I : AtomSem)
    where
  | sample (source : Sample n R I)
  | matrix (target : AdjacencyMatrix.Rep n)

inductive TransformStep {n : Nat} {R : Pat → Pat → Prop} {I : AtomSem} :
    TransformState n R I → TransformState n R I → Prop where
  | encode (sample : Sample n R I) :
      TransformStep (.sample sample) (.matrix (compile sample))

def transformTheory (n : Nat) (R : Pat → Pat → Prop) (I : AtomSem) :
    GSLT where
  Term := TransformState n R I
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TransformStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def compilePath {n : Nat} {R : Pat → Pat → Prop} {I : AtomSem}
    (sample : Sample n R I) :
    (transformTheory n R I).RewritePath
      (.sample sample) (.matrix (compile sample)) :=
  .cons (.encode sample) (.nil _)

/-! ## Witness-erasure negative control -/

/-- A relation table may retain a chosen witness for every positive cell. -/
structure WitnessedTable (n : Nat) (Witness : Type*) where
  matrix : AdjacencyMatrix.Rep n
  witness : Fin n → Fin n → Option Witness

/-- Matrix erasure forgets witness identity. -/
def WitnessedTable.erase {n : Nat} {Witness : Type*}
    (table : WitnessedTable n Witness) : AdjacencyMatrix.Rep n :=
  table.matrix

namespace Canary

def empty2 : AdjacencyMatrix.Rep 2 := AdjacencyMatrix.empty 2

def firstWitness : WitnessedTable 2 Bool where
  matrix := empty2
  witness := fun _ _ => some false

def secondWitness : WitnessedTable 2 Bool where
  matrix := empty2
  witness := fun _ _ => some true

/-- Negative: the Boolean relation table alone cannot reconstruct which
separator occurrence justified it. -/
theorem same_matrix_different_witnesses :
    firstWitness.erase = secondWitness.erase ∧
      firstWitness.witness ≠ secondWitness.witness := by
  constructor
  · rfl
  · intro equal
    have cell := congrFun (congrFun equal ⟨0, by omega⟩) ⟨0, by omega⟩
    cases cell

end Canary

#print axioms semanticGraph_edge_has_separator
#print axioms compile_commutes
#print axioms compilePath
#print axioms Canary.same_matrix_different_witnesses

end Mettapedia.GraphTheory.Representation.DistinctionBridge
