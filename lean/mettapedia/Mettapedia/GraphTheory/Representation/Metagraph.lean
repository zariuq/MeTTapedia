import Mettapedia.GraphTheory.Representation.Hypergraph
import Mathlib.Data.Finset.Sort

/-!
# Directed labeled metagraphs as query and transformation GSLTs

A metagraph's edge objects may themselves be the targets of other edge
objects.  Ordered ports, labels, and enrichments are intensional data.  The
underlying hypergraph forgets those distinctions and therefore cannot serve as
the metagraph's definition; it is a proved projection.
-/

namespace Mettapedia.GraphTheory.Representation.Metagraph

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation

set_option autoImplicit false

/-- One ordered link occurrence leaving an edge object. -/
structure Port (Object Label Enrichment : Type*) where
  target : Object
  label : Label
  enrichment : Enrichment
deriving DecidableEq, Repr

/-- A finite directed labeled metagraph.  Objects with no outgoing ports are
the degenerate edges conventionally called vertices. -/
structure Rep (Object Label Enrichment : Type*) where
  ports : Object → List (Port Object Label Enrichment)

/-- Extensional directed linkage, forgetting port order and annotations. -/
def Linked {Object Label Enrichment : Type*}
    (graph : Rep Object Label Enrichment) (source target : Object) : Prop :=
  ∃ port ∈ graph.ports source, port.target = target

/-- A target probe scans the source object's ports in authored order. -/
def acceptsTarget {Object Label Enrichment : Type} [DecidableEq Object]
    (port : Port Object Label Enrichment) (target : Object) : Bool :=
  decide (port.target = target)

def linked {Object Label Enrichment : Type} [DecidableEq Object]
    (graph : Rep Object Label Enrichment) (source target : Object) :
    Measured Bool :=
  LinearProbe.run acceptsTarget target (graph.ports source)

theorem linked_sound {Object Label Enrichment : Type} [DecidableEq Object]
    (graph : Rep Object Label Enrichment) (source target : Object) :
    (linked graph source target).value = true ↔ Linked graph source target := by
  rw [linked, LinearProbe.run_value_eq_any]
  simp [Linked, acceptsTarget]

/-- Forget direction annotations and port order while retaining each source
object as a named hyperedge occurrence. -/
def underlyingHypergraph {Object Label Enrichment : Type*}
    [DecidableEq Object] (graph : Rep Object Label Enrichment) :
    Hypergraph.Rep Object Object where
  incident source := ((graph.ports source).map Port.target).toFinset

theorem underlying_incident_iff {Object Label Enrichment : Type*}
    [DecidableEq Object] (graph : Rep Object Label Enrichment)
    (target source : Object) :
    target ∈ (underlyingHypergraph graph).incident source ↔
      Linked graph source target := by
  simp [underlyingHypergraph, Linked]

/-! ## Authentic query GSLT -/

inductive QueryState (Object Label Enrichment : Type) where
  | lookup (graph : Rep Object Label Enrichment) (source target : Object)
  | answer (value : Bool)

inductive QueryStep {Object Label Enrichment : Type} [DecidableEq Object] :
    QueryState Object Label Enrichment →
      QueryState Object Label Enrichment → Prop where
  | read (graph : Rep Object Label Enrichment) (source target : Object) :
      QueryStep (.lookup graph source target)
        (.answer (linked graph source target).value)

def queryTheory (Object Label Enrichment : Type) [DecidableEq Object] : GSLT where
  Term := QueryState Object Label Enrichment
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := QueryStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def queryPath {Object Label Enrichment : Type} [DecidableEq Object]
    (graph : Rep Object Label Enrichment) (source target : Object) :
    (queryTheory Object Label Enrichment).RewritePath
      (.lookup graph source target) (.answer (linked graph source target).value) :=
  .cons (.read graph source target) (.nil _)

/-! ## Hypergraph embedding -/

/-- Embed a hypergraph as a metagraph.  Vertex objects are degenerate edges;
each named hyperedge object has one port for every incident vertex. -/
def ofHypergraph {Vertex Edge Label Enrichment : Type*}
    [LinearOrder Vertex] [Inhabited Label] [Inhabited Enrichment]
    (graph : Hypergraph.Rep Vertex Edge) :
    Rep (Sum Vertex Edge) Label Enrichment where
  ports
    | .inl _ => []
    | .inr edge => (graph.incident edge).sort (· ≤ ·) |>.map fun vertex =>
        ⟨.inl vertex, default, default⟩

@[simp] theorem ofHypergraph_vertex_ports
    {Vertex Edge Label Enrichment : Type*}
    [LinearOrder Vertex] [Inhabited Label] [Inhabited Enrichment]
    (graph : Hypergraph.Rep Vertex Edge) (vertex : Vertex) :
    (ofHypergraph graph : Rep (Sum Vertex Edge) Label Enrichment).ports
        (.inl vertex) = [] :=
  rfl

theorem ofHypergraph_incident_iff
    {Vertex Edge Label Enrichment : Type*}
    [LinearOrder Vertex] [Inhabited Label] [Inhabited Enrichment]
    (graph : Hypergraph.Rep Vertex Edge) (vertex : Vertex) (edge : Edge) :
    Linked (ofHypergraph graph : Rep (Sum Vertex Edge) Label Enrichment)
        (.inr edge) (.inl vertex) ↔
      vertex ∈ graph.incident edge := by
  simp [Linked, ofHypergraph]

inductive TransformState (Vertex Edge Label Enrichment : Type) where
  | hypergraph (graph : Hypergraph.Rep Vertex Edge)
  | metagraph (graph : Rep (Sum Vertex Edge) Label Enrichment)

inductive TransformStep {Vertex Edge Label Enrichment : Type}
    [LinearOrder Vertex] [Inhabited Label] [Inhabited Enrichment] :
    TransformState Vertex Edge Label Enrichment →
      TransformState Vertex Edge Label Enrichment → Prop where
  | encode (graph : Hypergraph.Rep Vertex Edge) :
      TransformStep (.hypergraph graph) (.metagraph (ofHypergraph graph))

def transformTheory (Vertex Edge Label Enrichment : Type)
    [LinearOrder Vertex] [Inhabited Label] [Inhabited Enrichment] : GSLT where
  Term := TransformState Vertex Edge Label Enrichment
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

def transformPath {Vertex Edge Label Enrichment : Type}
    [LinearOrder Vertex] [Inhabited Label] [Inhabited Enrichment]
    (graph : Hypergraph.Rep Vertex Edge) :
    (transformTheory Vertex Edge Label Enrichment).RewritePath
      (.hypergraph graph) (.metagraph (ofHypergraph graph)) :=
  .cons (.encode graph) (.nil _)

namespace Canary

def o0 : Fin 3 := ⟨0, by omega⟩
def o1 : Fin 3 := ⟨1, by omega⟩
def o2 : Fin 3 := ⟨2, by omega⟩

def first : Rep (Fin 3) Bool Nat where
  ports object :=
    if object = o0 then [⟨o1, false, 7⟩, ⟨o2, true, 9⟩] else []

def reordered : Rep (Fin 3) Bool Nat where
  ports object :=
    if object = o0 then [⟨o2, false, 99⟩, ⟨o1, true, 42⟩] else []

/-- Positive: the first port is found in one authored probe. -/
theorem first_link_cost : linked first o0 o1 = ⟨true, 1⟩ := by
  decide

/-- Negative: forgetting order, labels, and enrichments yields the same
incidence hypergraph. -/
theorem underlying_forgets_order_and_annotations :
    underlyingHypergraph first = underlyingHypergraph reordered := by
  apply Hypergraph.Rep.ext
  funext source
  fin_cases source <;> ext target <;> fin_cases target <;>
    simp [underlyingHypergraph, first, reordered, o0, o1, o2]

/-- The metagraphs remain intensionally distinct. -/
theorem authored_ports_differ : first.ports o0 ≠ reordered.ports o0 := by
  decide

end Canary

#print axioms linked_sound
#print axioms underlying_incident_iff
#print axioms ofHypergraph_incident_iff
#print axioms transformPath
#print axioms Canary.underlying_forgets_order_and_annotations

end Mettapedia.GraphTheory.Representation.Metagraph
