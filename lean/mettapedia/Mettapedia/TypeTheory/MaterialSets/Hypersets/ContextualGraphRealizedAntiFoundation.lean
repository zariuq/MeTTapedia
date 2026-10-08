import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs

/-!
# Actual contextual graph decoration and future matching uniqueness

Every original-small varying graph has its canonical decoration in the
same untyped graph universe. A decoration is an actual natural reading
whose member receipts satisfy the graph's two-sided equations. Coiteration
constructs the comparison of any such reading with the canonical one.

Uniqueness is future-indexed material equality, with matching evidence;
it is not native equality reflection. This proves the graph-realized
anti-foundation profile at the stated graph bound, not a choice-free
conversion from arbitrary erased covering propositions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedAntiFoundation

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open Mettapedia.TypeTheory.ContextualWitnessCover
universe u
variable {D : Type u} [Category.{u} D]
variable (graph : Diagram D)

structure Decoration where
  reading : NaturalHom graph.nodes (values D)
  forth : ∀ (point : D) (node : graph.nodes.obj point)
    (child : ContextualGraphRealizers.Child graph point node),
      Member (reading.app point child.val) (reading.app point node)
  back : ∀ (point : D) (node : graph.nodes.obj point) (value : Value D point),
    Member value (reading.app point node) →
      Σ child : ContextualGraphRealizers.Child graph point node, Equal value (reading.app point child.val)

def canonical : Decoration graph where
  reading := {
    app _ node := ⟨graph, node⟩
    naturality _ _ := rfl }
  forth point node child := Member.atChild (⟨graph, node⟩ : Value D point) child
  back _ _ _ proof := ⟨proof.1, proof.2⟩

variable (decoration : Decoration graph) (target : Diagram D)

abbrev Comparison (point : D) (first : graph.nodes.obj point) (second : target.nodes.obj point) : Type u :=
  Equal (decoration.reading.app point first) (⟨target, second⟩ : Value D point)

def futureComparison {point later : D} (arrival : point ⟶ later)
    {first : graph.nodes.obj point} {second : target.nodes.obj point}
    (proof : Comparison graph decoration target point first second) :
    Comparison graph decoration target later (graph.nodes.map arrival first) (target.nodes.map arrival second) :=
  (Equal.ofEq (decoration.reading.naturality arrival first)).symm.trans (Equal.restrict arrival proof)

def comparisonForth (point : D) (first : graph.nodes.obj point) (second : target.nodes.obj point)
    (proof : Comparison graph decoration target point first second)
    (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child graph future.1 (graph.nodes.map future.2 first)) :
    Σ matched : ContextualGraphRealizers.Child target future.1 (target.nodes.map future.2 second),
      Comparison graph decoration target future.1 child.val matched.val :=
  let current := futureComparison graph decoration target future.2 proof
  let member := Member.transportParent current
    (decoration.forth future.1 (graph.nodes.map future.2 first) child)
  ⟨member.1, member.2⟩

def comparisonBack (point : D) (first : graph.nodes.obj point) (second : target.nodes.obj point)
    (proof : Comparison graph decoration target point first second)
    (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child target future.1 (target.nodes.map future.2 second)) :
    Σ matched : ContextualGraphRealizers.Child graph future.1 (graph.nodes.map future.2 first),
      Comparison graph decoration target future.1 matched.val child.val :=
  let current := futureComparison graph decoration target future.2 proof
  let value : Value D future.1 := ⟨target, child.val⟩
  let member := Member.transportParent current.symm
    (Member.atChild (⟨target, target.nodes.map future.2 second⟩ : Value D future.1) child)
  let response := decoration.back future.1 (graph.nodes.map future.2 first) value member
  ⟨response.1, response.2.symm⟩

/-- The comparison is constructed over an original-small matching state
carrier, even though the universe of material values is wider. -/
def unique (decoration : Decoration graph) (point : D) (node : graph.nodes.obj point) :
    Equal ((canonical graph).reading.app point node) (decoration.reading.app point node) :=
  ContextualGraphRealizers.corec graph (decoration.reading.app point node).1
    (comparisonForth graph decoration (decoration.reading.app point node).1)
    (comparisonBack graph decoration (decoration.reading.app point node).1)
    (Equal.refl (decoration.reading.app point node))

def decorationsAgree (first second : Decoration graph) (point : D) (node : graph.nodes.obj point) :
    Equal (first.reading.app point node) (second.reading.app point node) :=
  (unique graph first point node).symm.trans (unique graph second point node)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedAntiFoundation
