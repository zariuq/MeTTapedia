import Mathlib.Combinatorics.SimpleGraph.Operations
import Mettapedia.GraphTheory.Representation.CostModel
import Mettapedia.Logic.WorldModel.Basic

/-!
# Revision and query GSLTs for graph presentations

Each graph layout is a possible realization of one world-model state.  The
abstract edit meaning is defined on `SimpleGraph`; an editable presentation
must construct a carrier update and prove that its denotation performs exactly
that edit.  Queries retain their layout-specific cost.

The workload GSLT interleaves edits and observations.  Its steps compute from
the current representation; they do not carry future answers or revised states
as premises.
-/

namespace Mettapedia.GraphTheory.Representation

open Mettapedia.GSLT

set_option autoImplicit false

/-- A non-loop edge address. -/
structure EdgeAddress (n : Nat) where
  first : Fin n
  second : Fin n
  different : first ≠ second

/-- The elementary revisions shared by finite simple-graph presentations. -/
inductive EdgeEdit (n : Nat) where
  | insert (edge : EdgeAddress n)
  | erase (edge : EdgeAddress n)

abbrev EdgeQuery (n : Nat) := Fin n × Fin n

/-- Independent graph meaning of one edit. -/
def applyMeaning {n : Nat} (graph : SimpleGraph (Fin n)) :
    EdgeEdit n → SimpleGraph (Fin n)
  | .insert edge => graph ⊔ SimpleGraph.edge edge.first edge.second
  | .erase edge => graph \ SimpleGraph.edge edge.first edge.second

@[simp] theorem applyMeaning_insert_adj {n : Nat}
    (graph : SimpleGraph (Fin n)) (edge : EdgeAddress n) (u v : Fin n) :
    (applyMeaning graph (.insert edge)).Adj u v ↔
      graph.Adj u v ∨
        ((u = edge.first ∧ v = edge.second) ∨
          (u = edge.second ∧ v = edge.first)) := by
  simp only [applyMeaning, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (already | ⟨inserted, _⟩)
    · exact Or.inl already
    · exact Or.inr inserted
  · rintro (already | inserted)
    · exact Or.inl already
    · refine Or.inr ⟨inserted, ?_⟩
      rcases inserted with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact edge.different
      · exact edge.different.symm

@[simp] theorem applyMeaning_erase_adj {n : Nat}
    (graph : SimpleGraph (Fin n)) (edge : EdgeAddress n) (u v : Fin n) :
    (applyMeaning graph (.erase edge)).Adj u v ↔
      graph.Adj u v ∧
        ¬((u = edge.first ∧ v = edge.second) ∨
          (u = edge.second ∧ v = edge.first)) := by
  simp [applyMeaning, SimpleGraph.edge_adj]
  aesop

/-- A graph presentation with an executable edit operation and a theorem that
the edit realizes the independently defined simple-graph update. -/
structure EditablePresentation (n : Nat) extends Presentation n where
  edit : Carrier → EdgeEdit n → Accounted Carrier
  edit_sound : ∀ graph change,
    denote (edit graph change).value = applyMeaning (denote graph) change

/-- Turn the common edge observation into the richer resource account used by
mixed workloads.  One abstract probe contributes one time unit and one read. -/
def queryResources {n : Nat} (presentation : Presentation n)
    (graph : presentation.Carrier) (query : EdgeQuery n) : Resources :=
  let observation := presentation.edge graph query.1 query.2
  { time := observation.work, reads := observation.work }

/-- An edit or an edge observation in a versioned graph workload. -/
inductive WorkItem (n : Nat) where
  | edit (change : EdgeEdit n)
  | query (edge : EdgeQuery n)

/-- Observable result of a finite workload. -/
structure WorkloadResult {n : Nat} (presentation : EditablePresentation n) where
  graph : presentation.Carrier
  answers : List Bool
  resources : Resources

/-- Operational state records the exact live graph, remaining work, reversed
answer occurrences, and accumulated resource account. -/
inductive RevisionState {n : Nat} (presentation : EditablePresentation n) where
  | active (graph : presentation.Carrier) (remaining : List (WorkItem n))
      (answersReversed : List Bool) (resources : Resources)
  | finished (result : WorkloadResult presentation)

/-- One workload step either computes one observation, performs one represented
edit, or closes an exhausted schedule. -/
inductive RevisionStep {n : Nat} (presentation : EditablePresentation n) :
    RevisionState presentation → RevisionState presentation → Prop where
  | observe (graph : presentation.Carrier) (query : EdgeQuery n)
      (remaining : List (WorkItem n)) (answersReversed : List Bool)
      (used : Resources) :
      RevisionStep presentation
        (.active graph (.query query :: remaining) answersReversed used)
        (.active graph remaining
          ((presentation.edge graph query.1 query.2).value :: answersReversed)
          (used.seq (queryResources presentation.toPresentation graph query)))
  | revise (graph : presentation.Carrier) (change : EdgeEdit n)
      (remaining : List (WorkItem n)) (answersReversed : List Bool)
      (used : Resources) :
      RevisionStep presentation
        (.active graph (.edit change :: remaining) answersReversed used)
        (.active (presentation.edit graph change).value remaining answersReversed
          (used.seq (presentation.edit graph change).resources))
  | finish (graph : presentation.Carrier) (answersReversed : List Bool)
      (used : Resources) :
      RevisionStep presentation
        (.active graph [] answersReversed used)
        (.finished ⟨graph, answersReversed.reverse, used⟩)

/-- The mixed revision/query GSLT belonging to one editable representation. -/
def revisionTheory {n : Nat} (presentation : EditablePresentation n) : GSLT where
  Term := RevisionState presentation
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := RevisionStep presentation
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Executable normalizer corresponding exactly to the workload steps. -/
def executeAux {n : Nat} (presentation : EditablePresentation n) :
    presentation.Carrier → List (WorkItem n) → List Bool → Resources →
      WorkloadResult presentation
  | graph, [], answersReversed, used =>
      ⟨graph, answersReversed.reverse, used⟩
  | graph, .query query :: remaining, answersReversed, used =>
      executeAux presentation graph remaining
        ((presentation.edge graph query.1 query.2).value :: answersReversed)
        (used.seq (queryResources presentation.toPresentation graph query))
  | graph, .edit change :: remaining, answersReversed, used =>
      executeAux presentation (presentation.edit graph change).value remaining
        answersReversed (used.seq (presentation.edit graph change).resources)

def execute {n : Nat} (presentation : EditablePresentation n)
    (graph : presentation.Carrier) (workload : List (WorkItem n)) :
    WorkloadResult presentation :=
  executeAux presentation graph workload [] Resources.zero

/-- Every finite workload has a proof-relevant path to the exact executable
result. -/
def executeAuxPath {n : Nat} (presentation : EditablePresentation n) :
    (graph : presentation.Carrier) → (workload : List (WorkItem n)) →
    (answersReversed : List Bool) → (used : Resources) →
      (revisionTheory presentation).RewritePath
        (.active graph workload answersReversed used)
        (.finished (executeAux presentation graph workload answersReversed used))
  | graph, [], answersReversed, used =>
      .cons (.finish graph answersReversed used) (.nil _)
  | graph, .query query :: remaining, answersReversed, used =>
      .cons (.observe graph query remaining answersReversed used)
        (executeAuxPath presentation graph remaining
          ((presentation.edge graph query.1 query.2).value :: answersReversed)
          (used.seq (queryResources presentation.toPresentation graph query)))
  | graph, .edit change :: remaining, answersReversed, used =>
      .cons (.revise graph change remaining answersReversed used)
        (executeAuxPath presentation (presentation.edit graph change).value remaining
          answersReversed (used.seq (presentation.edit graph change).resources))

def executePath {n : Nat} (presentation : EditablePresentation n)
    (graph : presentation.Carrier) (workload : List (WorkItem n)) :
    (revisionTheory presentation).RewritePath
      (.active graph workload [] Resources.zero)
      (.finished (execute presentation graph workload)) :=
  executeAuxPath presentation graph workload [] Resources.zero

theorem finished_normal {n : Nat} (presentation : EditablePresentation n)
    (result : WorkloadResult presentation) :
    (revisionTheory presentation).IsNormalForm (.finished result) := by
  rintro ⟨target, step⟩
  cases step

/-! ## World-model interface -/

/-- A layout-level realization of graph union as world-model revision. -/
structure GraphWorldPresentation (n : Nat) extends EditablePresentation n where
  empty : Carrier
  revise : Carrier → Carrier → Carrier
  empty_sound : denote empty = ⊥
  revise_sound : ∀ first second,
    denote (revise first second) = denote first ⊔ denote second

/-- Every graph-world presentation supplies the minimal WM interface.  The
layout changes operational costs, not the abstract `revise`/`extract` roles. -/
@[reducible] def GraphWorldPresentation.toWorldModel {n : Nat}
    (presentation : GraphWorldPresentation n) :
    WorldModel presentation.Carrier (EdgeQuery n) Bool where
  revise := presentation.revise
  empty := presentation.empty
  extract := fun graph query =>
    (presentation.edge graph query.1 query.2).value

theorem GraphWorldPresentation.extract_true_iff {n : Nat}
    (presentation : GraphWorldPresentation n)
    (graph : presentation.Carrier) (query : EdgeQuery n) :
    @WorldModel.extract presentation.Carrier (EdgeQuery n) Bool
        presentation.toWorldModel graph query = true ↔
      (presentation.denote graph).Adj query.1 query.2 :=
  presentation.edge_sound graph query.1 query.2

/-- A world-model refinement preserves both the graph meaning and the authored
revision algebra. -/
structure GraphWorldRefinement {n : Nat}
    (source target : GraphWorldPresentation n)
    extends Refinement source.toPresentation target.toPresentation where
  map_empty : map source.empty = target.empty
  map_revise : ∀ first second,
    map (source.revise first second) = target.revise (map first) (map second)

theorem GraphWorldRefinement.extract_preserved {n : Nat}
    {source target : GraphWorldPresentation n}
    (refinement : GraphWorldRefinement source target)
    (graph : source.Carrier) (query : EdgeQuery n) :
    @WorldModel.extract target.Carrier (EdgeQuery n) Bool
        target.toWorldModel (refinement.map graph) query =
      @WorldModel.extract source.Carrier (EdgeQuery n) Bool
        source.toWorldModel graph query := by
  apply Bool.eq_iff_iff.mpr
  rw [target.extract_true_iff, source.extract_true_iff, refinement.commute]

namespace Canary

def v0 : Fin 2 := ⟨0, by omega⟩
def v1 : Fin 2 := ⟨1, by omega⟩
def edge01 : EdgeAddress 2 := ⟨v0, v1, by decide⟩

/-- Insertion and erasure are observably distinct semantic revisions. -/
theorem insert_then_erase_changes_adjacency
    (graph : SimpleGraph (Fin 2)) :
    (applyMeaning graph (.insert edge01)).Adj v0 v1 ∧
      ¬(applyMeaning (applyMeaning graph (.insert edge01))
        (.erase edge01)).Adj v0 v1 := by
  simp [edge01, v0, v1]

end Canary

#print axioms applyMeaning_insert_adj
#print axioms executePath
#print axioms finished_normal
#print axioms GraphWorldRefinement.extract_preserved
#print axioms Canary.insert_then_erase_changes_adjacency

end Mettapedia.GraphTheory.Representation
