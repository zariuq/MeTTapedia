import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge

/-!
# Lineage-derived evidence dependence

The evidence bridge previously accepted a packet's transitive ancestors as
data and licensed addition from a pairwise source-disjointness predicate.  A
campaign, however, already publishes a lineage manifest.  This file derives
ancestor sets and independence certificates from that manifest DAG.

Independence here is stronger than pairwise non-ancestry: two sources must
also lack a common ancestor.  The final fork fixture proves why this matters.
If two parent edges are omitted from the reported manifest, the reported DAG
certifies independence while the complete DAG correctly rejects it.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uS uW uL uP uT

/-- Metadata stored for every source/checkpoint in a campaign lineage
manifest.  Parents are immediate training/data dependencies. -/
structure LineageNode (Source : Type uS) (World : Type uW) (Lineage : Type uL) where
  world : World
  lineage : Lineage
  generation : ℕ
  parents : Finset Source

/-- A well-formed lineage DAG.  Immediate dependencies stay within one world
and lineage and point strictly forward in generation. -/
structure LineageDAG (Source : Type uS) (World : Type uW) (Lineage : Type uL)
    [DecidableEq Source] where
  node : Source → LineageNode Source World Lineage
  parentEarlier : ∀ {parent child}, parent ∈ (node child).parents →
    (node parent).generation < (node child).generation
  parentSameWorld : ∀ {parent child}, parent ∈ (node child).parents →
    (node parent).world = (node child).world
  parentSameLineage : ∀ {parent child}, parent ∈ (node child).parents →
    (node parent).lineage = (node child).lineage

namespace LineageDAG

variable {Source : Type uS} {World : Type uW} {Lineage : Type uL}
variable [DecidableEq Source]

/-- Immediate manifest dependency, oriented from parent to child. -/
def ParentOf (graph : LineageDAG Source World Lineage)
    (parent child : Source) : Prop :=
  parent ∈ (graph.node child).parents

/-- Strict transitive ancestry in the manifest DAG. -/
def AncestorOf (graph : LineageDAG Source World Lineage)
    (ancestor descendant : Source) : Prop :=
  Relation.TransGen graph.ParentOf ancestor descendant

def AncestorOrSelf (graph : LineageDAG Source World Lineage)
    (ancestor descendant : Source) : Prop :=
  ancestor = descendant ∨ graph.AncestorOf ancestor descendant

theorem parent_ancestor (graph : LineageDAG Source World Lineage)
    {parent child : Source} (hparent : graph.ParentOf parent child) :
    graph.AncestorOf parent child :=
  Relation.TransGen.single hparent

/-- World labels are preserved along every transitive dependency path. -/
theorem ancestor_sameWorld (graph : LineageDAG Source World Lineage)
    {ancestor descendant : Source}
    (h : graph.AncestorOf ancestor descendant) :
    (graph.node ancestor).world = (graph.node descendant).world := by
  induction h with
  | single hparent => exact graph.parentSameWorld hparent
  | tail _ hparent ih => exact ih.trans (graph.parentSameWorld hparent)

/-- Lineage labels are preserved along every transitive dependency path. -/
theorem ancestor_sameLineage (graph : LineageDAG Source World Lineage)
    {ancestor descendant : Source}
    (h : graph.AncestorOf ancestor descendant) :
    (graph.node ancestor).lineage = (graph.node descendant).lineage := by
  induction h with
  | single hparent => exact graph.parentSameLineage hparent
  | tail _ hparent ih => exact ih.trans (graph.parentSameLineage hparent)

/-- Strict ancestry always increases generation.  This also proves acyclicity
without storing a separate acyclicity axiom. -/
theorem ancestor_generation_lt (graph : LineageDAG Source World Lineage)
    {ancestor descendant : Source}
    (h : graph.AncestorOf ancestor descendant) :
    (graph.node ancestor).generation < (graph.node descendant).generation := by
  induction h with
  | single hparent => exact graph.parentEarlier hparent
  | tail _ hparent ih => exact ih.trans (graph.parentEarlier hparent)

theorem not_ancestor_self (graph : LineageDAG Source World Lineage)
    (source : Source) : ¬ graph.AncestorOf source source := by
  intro h
  exact (Nat.lt_irrefl _ (graph.ancestor_generation_lt h))

/-- Reachability is monotone when every reported parent edge is present in a
second manifest. -/
theorem ancestor_mono
    (reported complete : LineageDAG Source World Lineage)
    (hedges : ∀ {parent child}, reported.ParentOf parent child →
      complete.ParentOf parent child)
    {ancestor descendant : Source}
    (h : reported.AncestorOf ancestor descendant) :
    complete.AncestorOf ancestor descendant := by
  induction h with
  | single hparent => exact Relation.TransGen.single (hedges hparent)
  | tail _ hparent ih => exact Relation.TransGen.tail ih (hedges hparent)

/-- The transitive ancestor set computed from the manifest. -/
noncomputable def ancestorSet [Fintype Source]
    (graph : LineageDAG Source World Lineage) (source : Source) : Finset Source := by
  classical
  exact Finset.univ.filter (fun ancestor ↦ graph.AncestorOf ancestor source)

theorem mem_ancestorSet_iff [Fintype Source]
    (graph : LineageDAG Source World Lineage)
    (ancestor source : Source) :
    ancestor ∈ graph.ancestorSet source ↔ graph.AncestorOf ancestor source := by
  classical
  simp [ancestorSet]

/-- Two sources are graph-independent only if they are distinct, neither is an
ancestor of the other, and they have no common ancestor (including self). -/
def GraphIndependent (graph : LineageDAG Source World Lineage)
    (left right : Source) : Prop :=
  left ≠ right ∧
    ¬ graph.AncestorOf left right ∧
    ¬ graph.AncestorOf right left ∧
    ¬ ∃ common,
      graph.AncestorOrSelf common left ∧ graph.AncestorOrSelf common right

/-- Different registered worlds are independent when every dependency edge is
world-preserving, as required by `LineageDAG`. -/
theorem graphIndependent_of_world_ne
    (graph : LineageDAG Source World Lineage)
    {left right : Source}
    (hworld : (graph.node left).world ≠ (graph.node right).world) :
    graph.GraphIndependent left right := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    exact hworld (congrArg (fun source ↦ (graph.node source).world) heq)
  · intro hancestor
    exact hworld (graph.ancestor_sameWorld hancestor)
  · intro hancestor
    exact hworld (graph.ancestor_sameWorld hancestor).symm
  · rintro ⟨common, hcommonLeft, hcommonRight⟩
    have hleft : (graph.node common).world = (graph.node left).world := by
      rcases hcommonLeft with rfl | hancestor
      · rfl
      · exact graph.ancestor_sameWorld hancestor
    have hright : (graph.node common).world = (graph.node right).world := by
      rcases hcommonRight with rfl | hancestor
      · rfl
      · exact graph.ancestor_sameWorld hancestor
    exact hworld (hleft.symm.trans hright)

/-- A complete generation chain is an independently checkable property of a
manifest: earlier generations in one world/lineage are connected by ancestry. -/
def GenerationComplete (graph : LineageDAG Source World Lineage) : Prop :=
  ∀ earlier later,
    (graph.node earlier).world = (graph.node later).world →
    (graph.node earlier).lineage = (graph.node later).lineage →
    (graph.node earlier).generation < (graph.node later).generation →
    graph.AncestorOf earlier later

end LineageDAG

/-! ## Derived packets and additive-revision licenses -/

section PacketDerivation

variable {Source : Type uS} {World : Type uW} {Lineage : Type uL}
variable {Program : Type uP} {Target : Type uT}
variable [DecidableEq Source] [Fintype Source]

/-- Construct a discovery packet whose transitive dependencies are computed
from the manifest rather than supplied by hand. -/
noncomputable def packetFromLineageDAG
    (graph : LineageDAG Source World Lineage)
    (program : Program) (target : Target) (source : Source) :
    SourcePacket Program Target Source where
  program := program
  target := target
  source := source
  ancestors := graph.ancestorSet source

theorem packetFromLineageDAG_dependsOn_iff
    (graph : LineageDAG Source World Lineage)
    (later earlier : Source) (laterProgram earlierProgram : Program)
    (laterTarget earlierTarget : Target) :
    (packetFromLineageDAG graph laterProgram laterTarget later).DependsOn
        (packetFromLineageDAG graph earlierProgram earlierTarget earlier) ↔
      graph.AncestorOf earlier later := by
  classical
  simp [packetFromLineageDAG, SourcePacket.DependsOn,
    LineageDAG.mem_ancestorSet_iff]

/-- The stronger graph certificate entails the existing pairwise packet
certificate used by `EvidenceBridge`. -/
theorem graphIndependent_implies_sourceDisjoint
    (graph : LineageDAG Source World Lineage)
    (left right : Source) (leftProgram rightProgram : Program)
    (leftTarget rightTarget : Target)
    (h : graph.GraphIndependent left right) :
    (packetFromLineageDAG graph leftProgram leftTarget left).SourceDisjoint
      (packetFromLineageDAG graph rightProgram rightTarget right) := by
  classical
  refine ⟨h.1, ?_, ?_⟩
  · simpa [packetFromLineageDAG, LineageDAG.mem_ancestorSet_iff] using h.2.1
  · simpa [packetFromLineageDAG, LineageDAG.mem_ancestorSet_iff] using h.2.2.1

/-- A lineage-derived independence certificate licenses counts addition in
the existing WM-PLN evidence bridge. -/
theorem graphIndependent_licenses_additiveRevision
    [BEq Program] [BEq Target]
    (graph : LineageDAG Source World Lineage)
    (left right : Source) (leftProgram rightProgram : Program)
    (leftTarget rightTarget : Target)
    (h : graph.GraphIndependent left right) :
    AdditiveRevisionLicense
      (packetFromLineageDAG graph leftProgram leftTarget left)
      (packetFromLineageDAG graph rightProgram rightTarget right) :=
  sourceDisjoint_licenses_additiveRevision _ _
    (graphIndependent_implies_sourceDisjoint graph left right
      leftProgram rightProgram leftTarget rightTarget h)

/-- A lineage-aware license retains the stronger no-common-ancestor proof
alongside the legacy packet-level arithmetic license. -/
structure LineageAdditiveRevisionLicense
    [BEq Program] [BEq Target]
    (graph : LineageDAG Source World Lineage)
    (left right : Source) (leftProgram rightProgram : Program)
    (leftTarget rightTarget : Target) : Prop where
  graphIndependent : graph.GraphIndependent left right
  additiveRevision : AdditiveRevisionLicense
    (packetFromLineageDAG graph leftProgram leftTarget left)
    (packetFromLineageDAG graph rightProgram rightTarget right)

/-- Safe constructor for a lineage-aware additive license. -/
theorem graphIndependent_licenses_lineageAdditiveRevision
    [BEq Program] [BEq Target]
    (graph : LineageDAG Source World Lineage)
    (left right : Source) (leftProgram rightProgram : Program)
    (leftTarget rightTarget : Target)
    (h : graph.GraphIndependent left right) :
    LineageAdditiveRevisionLicense graph left right
      leftProgram rightProgram leftTarget rightTarget :=
  ⟨h, graphIndependent_licenses_additiveRevision graph left right
    leftProgram rightProgram leftTarget rightTarget h⟩

/-- Later generations in a complete lineage are dependencies, never fresh
evidence relative to their ancestors. -/
theorem later_generation_dependsOn
    (graph : LineageDAG Source World Lineage)
    (hcomplete : graph.GenerationComplete)
    (earlier later : Source)
    (hworld : (graph.node earlier).world = (graph.node later).world)
    (hlineage : (graph.node earlier).lineage = (graph.node later).lineage)
    (hgeneration : (graph.node earlier).generation <
      (graph.node later).generation)
    (laterProgram earlierProgram : Program)
    (laterTarget earlierTarget : Target) :
    (packetFromLineageDAG graph laterProgram laterTarget later).DependsOn
      (packetFromLineageDAG graph earlierProgram earlierTarget earlier) :=
  (packetFromLineageDAG_dependsOn_iff graph later earlier
    laterProgram earlierProgram laterTarget earlierTarget).2
      (hcomplete earlier later hworld hlineage hgeneration)

/-- Any actual ancestor relationship rules out pairwise packet freshness. -/
theorem ancestor_not_sourceDisjoint
    (graph : LineageDAG Source World Lineage)
    {earlier later : Source} (hancestor : graph.AncestorOf earlier later)
    (laterProgram earlierProgram : Program)
    (laterTarget earlierTarget : Target) :
    ¬ (packetFromLineageDAG graph earlierProgram earlierTarget earlier).SourceDisjoint
      (packetFromLineageDAG graph laterProgram laterTarget later) := by
  classical
  intro hdisjoint
  exact hdisjoint.2.1 ((LineageDAG.mem_ancestorSet_iff graph earlier later).2 hancestor)

end PacketDerivation

/-! ## Hidden-shared-cause and missing-edge fixtures -/

namespace LineageFixtures

inductive Source where
  | root | left | right | otherWorld
  deriving DecidableEq, Fintype, Repr

inductive World where
  | first | second
  deriving DecidableEq, Repr

inductive Lineage where
  | fork | independent
  deriving DecidableEq, Repr

def reportedNode : Source → LineageNode Source World Lineage
  | .root => ⟨.first, .fork, 0, ∅⟩
  | .left => ⟨.first, .fork, 1, ∅⟩
  | .right => ⟨.first, .fork, 1, ∅⟩
  | .otherWorld => ⟨.second, .independent, 0, ∅⟩

/-- Incomplete manifest: the two fork edges are missing. -/
def reportedDAG : LineageDAG Source World Lineage where
  node := reportedNode
  parentEarlier := by
    intro parent child hparent
    cases child <;> simp [reportedNode] at hparent
  parentSameWorld := by
    intro parent child hparent
    cases child <;> simp [reportedNode] at hparent
  parentSameLineage := by
    intro parent child hparent
    cases child <;> simp [reportedNode] at hparent

def completeNode : Source → LineageNode Source World Lineage
  | .root => ⟨.first, .fork, 0, ∅⟩
  | .left => ⟨.first, .fork, 1, {.root}⟩
  | .right => ⟨.first, .fork, 1, {.root}⟩
  | .otherWorld => ⟨.second, .independent, 0, ∅⟩

/-- Complete manifest: both children record the shared root dependency. -/
def completeDAG : LineageDAG Source World Lineage where
  node := completeNode
  parentEarlier := by
    intro parent child hparent
    cases parent <;> cases child <;> simp [completeNode] at hparent ⊢
  parentSameWorld := by
    intro parent child hparent
    cases parent <;> cases child <;> simp [completeNode] at hparent ⊢
  parentSameLineage := by
    intro parent child hparent
    cases parent <;> cases child <;> simp [completeNode] at hparent ⊢

theorem reported_has_no_parents (parent child : Source) :
    ¬ reportedDAG.ParentOf parent child := by
  intro hparent
  cases child <;>
    simp [LineageDAG.ParentOf, reportedDAG, reportedNode] at hparent

theorem reported_has_no_ancestors (ancestor descendant : Source) :
    ¬ reportedDAG.AncestorOf ancestor descendant := by
  intro hancestor
  induction hancestor with
  | single hparent => exact reported_has_no_parents _ _ hparent
  | tail _ hparent _ => exact reported_has_no_parents _ _ hparent

/-- The incomplete manifest appears to certify the fork children as
independent. -/
theorem reported_left_right_independent :
    reportedDAG.GraphIndependent .left .right := by
  refine ⟨by decide, reported_has_no_ancestors _ _,
    reported_has_no_ancestors _ _, ?_⟩
  rintro ⟨common, hleft, hright⟩
  rcases hleft with hleft | hleft
  · subst common
    rcases hright with hright | hright
    · contradiction
    · exact reported_has_no_ancestors _ _ hright
  · exact reported_has_no_ancestors _ _ hleft

theorem root_ancestor_left : completeDAG.AncestorOf .root .left := by
  exact LineageDAG.parent_ancestor completeDAG (by
    simp [LineageDAG.ParentOf, completeDAG, completeNode])

theorem root_ancestor_right : completeDAG.AncestorOf .root .right := by
  exact LineageDAG.parent_ancestor completeDAG (by
    simp [LineageDAG.ParentOf, completeDAG, completeNode])

/-- The complete manifest rejects independence because the two sources share
the root. -/
theorem complete_left_right_not_independent :
    ¬ completeDAG.GraphIndependent .left .right := by
  intro hindependent
  exact hindependent.2.2.2
    ⟨.root, Or.inr root_ancestor_left, Or.inr root_ancestor_right⟩

/-- Missing two parent edges flips the certificate.  This is the requested
hidden-shared-cause negative fixture. -/
theorem missing_manifest_edges_invalidate_independence :
    reportedDAG.GraphIndependent .left .right ∧
      ¬ completeDAG.GraphIndependent .left .right :=
  ⟨reported_left_right_independent, complete_left_right_not_independent⟩

abbrev Packet := SourcePacket Unit Unit Source

noncomputable def rootPacket : Packet :=
  packetFromLineageDAG completeDAG () () .root

noncomputable def leftPacket : Packet :=
  packetFromLineageDAG completeDAG () () .left

noncomputable def rightPacket : Packet :=
  packetFromLineageDAG completeDAG () () .right

/-- A later child explicitly depends on its training ancestor. -/
theorem descendant_packet_is_not_fresh :
    leftPacket.DependsOn rootPacket ∧ ¬ rootPacket.SourceDisjoint leftPacket := by
  constructor
  · exact (packetFromLineageDAG_dependsOn_iff completeDAG .left .root
      () () () ()).2 root_ancestor_left
  · exact ancestor_not_sourceDisjoint completeDAG root_ancestor_left () () () ()

/-- The older pairwise `SourceDisjoint` predicate misses common causes: the
siblings are pairwise non-ancestors but share `root`.  Graph independence is
therefore the required precondition for new additive licenses. -/
theorem pairwise_sourceDisjoint_misses_common_cause :
    leftPacket.SourceDisjoint rightPacket ∧
      ¬ completeDAG.GraphIndependent .left .right := by
  classical
  constructor
  · refine ⟨by decide, ?_, ?_⟩
    · change Source.left ∉ completeDAG.ancestorSet Source.right
      rw [LineageDAG.mem_ancestorSet_iff]
      intro hancestor
      have := completeDAG.ancestor_generation_lt hancestor
      simp [completeDAG, completeNode] at this
    · change Source.right ∉ completeDAG.ancestorSet Source.left
      rw [LineageDAG.mem_ancestorSet_iff]
      intro hancestor
      have := completeDAG.ancestor_generation_lt hancestor
      simp [completeDAG, completeNode] at this
  · exact complete_left_right_not_independent

/-- Different-world independence is derived from the manifest's edge
invariants, not declared packet-by-packet. -/
theorem different_worlds_are_graph_independent :
    completeDAG.GraphIndependent .left .otherWorld := by
  apply LineageDAG.graphIndependent_of_world_ne
  decide

end LineageFixtures

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
