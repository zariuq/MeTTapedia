import Mettapedia.SetTheory.Profiles.ProfileFiniteScottCollapse

/-!
# Coherent finite quotient comparisons

Closed embeddings identify each source successor fibre with the complete
successor fibre at its image. They induce closed embeddings through the
constructed quotient iterations. Consequently the final equality and
membership readings agree across disjoint comparison carriers.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileFiniteScottCoherence

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open UnfoldingIdentityComparison
open ProfileFiniteScottReadout ConstructiveFinite ProfileFiniteScottCollapse
open ProfileFiniteScottCollapse.FiniteGraph

universe u

/-- An embedding contains every successor of an image node. -/
structure ClosedEmbedding (source target : FiniteGraph.{u}) where
  map : source.Node → target.Node
  injective : Function.Injective map
  children : ∀ node child, target.edge (map node) child ↔
    ∃ original, source.edge node original ∧ map original = child

theorem projection_of_representative (graph : FiniteGraph.{u}) (node : graph.quotient.Node) :
    graph.projection node.val = node := Subtype.ext node.property

namespace ClosedEmbedding

variable {source target : FiniteGraph.{u}}

def refl (graph : FiniteGraph.{u}) : ClosedEmbedding graph graph where
  map := id
  injective := fun _ _ same => same
  children _node child := ⟨fun available => ⟨child, available, rfl⟩,
    fun ⟨_original, available, same⟩ => same ▸ available⟩

def trans {last : FiniteGraph.{u}} (first : ClosedEmbedding source target)
    (second : ClosedEmbedding target last) : ClosedEmbedding source last where
  map node := second.map (first.map node)
  injective := second.injective.comp first.injective
  children node child := by
    rw [second.children]
    constructor
    · rintro ⟨middle, available, same⟩
      obtain ⟨original, originalAvailable, paired⟩ := (first.children node middle).mp available
      exact ⟨original, originalAvailable, (congrArg second.map paired).trans same⟩
    · rintro ⟨original, available, same⟩
      exact ⟨first.map original, (first.children _ _).mpr ⟨original, available, rfl⟩, same⟩

theorem edge_iff (embedding : ClosedEmbedding source target) (node child : source.Node) :
    target.edge (embedding.map node) (embedding.map child) ↔ source.edge node child := by
  constructor
  · intro available
    obtain ⟨original, originalAvailable, same⟩ := (embedding.children _ _).mp available
    exact embedding.injective same ▸ originalAvailable
  · intro available
    exact (embedding.children _ _).mpr ⟨child, available, rfl⟩

/-- The inverse is a search over the actual finite source enumeration. -/
def childInverse (embedding : ClosedEmbedding source target) (node : source.Node)
    (child : Child target.edge (embedding.map node)) : Child source.edge node :=
  let chosen := witness (fun original => source.edge node original ∧ embedding.map original = child.val)
    ((embedding.children node child.val).mp child.property)
  ⟨chosen.val, chosen.property.1⟩

theorem childInverse_spec (embedding : ClosedEmbedding source target) (node : source.Node)
    (child : Child target.edge (embedding.map node)) :
    embedding.map (embedding.childInverse node child).val = child.val := by
  exact (witness (fun original => source.edge node original ∧ embedding.map original = child.val)
    ((embedding.children node child.val).mp child.property)).property.2

def childEquiv (embedding : ClosedEmbedding source target) (node : source.Node) :
    Child source.edge node ≃ Child target.edge (embedding.map node) where
  toFun child := ⟨embedding.map child.val, (embedding.edge_iff node child.val).mpr child.property⟩
  invFun := embedding.childInverse node
  left_inv _child := Subtype.ext (embedding.injective (embedding.childInverse_spec node _))
  right_inv child := Subtype.ext (embedding.childInverse_spec node child)

def unfolding (embedding : ClosedEmbedding source target) (node : source.Node) :
    PresentationIso (unfold source.edge node) (unfold target.edge (embedding.map node)) := by
  let strategy : Strategy (left := source.edge) (right := target.edge)
      (relation := fun first second => embedding.map first = second) := by
    intro first second paired
    subst second
    exact ⟨embedding.childEquiv first, fun _ => rfl⟩
  exact unfoldingIso strategy rfl

theorem raw_iff (embedding : ClosedEmbedding source target) (first second : source.Node) :
    target.rawRelation (embedding.map first) (embedding.map second) ↔ source.rawRelation first second := by
  constructor
  · intro same
    obtain ⟨isomorphism⟩ := (stable_kernel target.edge target.edge _ _).mp same
    exact (stable_kernel source.edge source.edge _ _).mpr
      ⟨(embedding.unfolding first).trans (isomorphism.trans (embedding.unfolding second).symm)⟩
  · intro same
    obtain ⟨isomorphism⟩ := (stable_kernel source.edge source.edge _ _).mp same
    exact (stable_kernel target.edge target.edge _ _).mpr
      ⟨(embedding.unfolding first).symm.trans (isomorphism.trans (embedding.unfolding second))⟩

def quotientMap (embedding : ClosedEmbedding source target) : source.quotient.Node → target.quotient.Node :=
  fun node => target.projection (embedding.map node.val)

theorem quotientMap_projection (embedding : ClosedEmbedding source target) (node : source.Node) :
    embedding.quotientMap (source.projection node) = target.projection (embedding.map node) := by
  apply (target.projection_kernel _ _).mpr
  apply (embedding.raw_iff _ _).mpr
  exact source.rawRelation_equivalence.symm
    (related_representative source.rawRelation source.rawRelation_equivalence node)

theorem quotientMap_injective (embedding : ClosedEmbedding source target) :
    Function.Injective embedding.quotientMap := by
  intro first second same
  have related := (embedding.raw_iff first.val second.val).mp
    ((target.projection_kernel _ _).mp same)
  have projected := (source.projection_kernel _ _).mpr related
  exact (projection_of_representative source first).symm.trans
    (projected.trans (projection_of_representative source second))

theorem quotientMap_children (embedding : ClosedEmbedding source target)
    (node : source.quotient.Node) (child : target.quotient.Node) :
    target.quotient.edge (embedding.quotientMap node) child ↔
      ∃ original, source.quotient.edge node original ∧ embedding.quotientMap original = child := by
  change target.quotient.edge (target.projection (embedding.map node.val)) child ↔ _
  rw [target.projection_edge]
  constructor
  · rintro ⟨middle, available, same⟩
    obtain ⟨original, originalAvailable, paired⟩ := (embedding.children node.val middle).mp available
    refine ⟨source.projection original, ?_, ?_⟩
    · have projected := (source.projection_edge node.val _).mpr ⟨original, originalAvailable, rfl⟩
      rw [projection_of_representative source node] at projected
      exact projected
    · exact (embedding.quotientMap_projection original).trans ((congrArg target.projection paired).trans same)
  · rintro ⟨original, available, same⟩
    have projected : source.quotient.edge (source.projection node.val) original := by
      rw [projection_of_representative source node]
      exact available
    obtain ⟨middle, middleAvailable, paired⟩ := (source.projection_edge node.val _).mp projected
    refine ⟨embedding.map middle, (embedding.edge_iff _ _).mpr middleAvailable, ?_⟩
    exact (embedding.quotientMap_projection middle).symm.trans
      ((congrArg embedding.quotientMap paired).trans same)

def quotient (embedding : ClosedEmbedding source target) :
    ClosedEmbedding source.quotient target.quotient where
  map := embedding.quotientMap
  injective := embedding.quotientMap_injective
  children := embedding.quotientMap_children

def iterate (embedding : ClosedEmbedding source target) :
    (count : Nat) → ClosedEmbedding (source.iterate count) (target.iterate count)
  | 0 => embedding
  | count + 1 => (embedding.iterate count).quotient

theorem iterate_projection (embedding : ClosedEmbedding source target) (count : Nat)
    (node : source.Node) :
    (embedding.iterate count).map (source.iterateProjection count node) =
      target.iterateProjection count (embedding.map node) := by
  induction count with
  | zero => rfl
  | succ count previous =>
    exact ((embedding.iterate count).quotientMap_projection _).trans
      (congrArg (target.iterate count).projection previous)

theorem iterate_projection_kernel (embedding : ClosedEmbedding source target) (count : Nat)
    (first second : source.Node) :
    target.iterateProjection count (embedding.map first) =
        target.iterateProjection count (embedding.map second) ↔
      source.iterateProjection count first = source.iterateProjection count second := by
  rw [← embedding.iterate_projection count first, ← embedding.iterate_projection count second]
  exact (embedding.iterate count).injective.eq_iff

end ClosedEmbedding

namespace FiniteGraph

theorem stopped_after (graph : FiniteGraph.{u}) (count : Nat)
    (unchanged : (graph.iterate count).stopped) (later : Nat) :
    (graph.iterate (count + later)).stopped := by
  induction later with
  | zero => exact unchanged
  | succ later previous => exact ProfileFiniteScottCollapse.FiniteGraph.stopped_quotient _ previous

theorem projection_after_stopped_kernel (graph : FiniteGraph.{u}) (count : Nat)
    (unchanged : (graph.iterate count).stopped) (later : Nat) (first second : graph.Node) :
    graph.iterateProjection (count + later) first = graph.iterateProjection (count + later) second ↔
      graph.iterateProjection count first = graph.iterateProjection count second := by
  induction later with
  | zero => exact Iff.rfl
  | succ later previous =>
    change (graph.iterate (count + later)).projection (graph.iterateProjection (count + later) first) =
        (graph.iterate (count + later)).projection (graph.iterateProjection (count + later) second) ↔ _
    exact ((graph.iterate (count + later)).quotientEquiv
      (stopped_after graph count unchanged later)).injective.eq_iff.trans previous

theorem canonical_at_le (graph : FiniteGraph.{u}) (count : Nat)
    (bound : size (α := graph.Node) ≤ count) (first second : graph.Node) :
    graph.iterateProjection count first = graph.iterateProjection count second ↔
      graph.canonicalProjection first = graph.canonicalProjection second := by
  obtain ⟨later, same⟩ := Nat.exists_eq_add_of_le bound
  subst count
  exact projection_after_stopped_kernel graph _ (ProfileFiniteScottCollapse.FiniteGraph.iterate_stops graph) later first second

end FiniteGraph

namespace ClosedEmbedding

variable {source target : FiniteGraph.{u}}

theorem canonical_kernel (embedding : ClosedEmbedding source target) (first second : source.Node) :
    target.canonicalProjection (embedding.map first) = target.canonicalProjection (embedding.map second) ↔
      source.canonicalProjection first = source.canonicalProjection second := by
  let count := max (size (α := source.Node)) (size (α := target.Node))
  exact (FiniteGraph.canonical_at_le target count (Nat.le_max_right _ _) _ _).symm.trans
    ((embedding.iterate_projection_kernel count first second).trans
      (FiniteGraph.canonical_at_le source count (Nat.le_max_left _ _) first second))

def canonicalMap (embedding : ClosedEmbedding source target) : source.canonicalGraph.Node → target.canonicalGraph.Node :=
  fun node => target.canonicalProjection (embedding.map (source.canonicalOrigin node))

theorem canonicalMap_projection (embedding : ClosedEmbedding source target) (node : source.Node) :
    embedding.canonicalMap (source.canonicalProjection node) = target.canonicalProjection (embedding.map node) :=
  (embedding.canonical_kernel _ _).mpr (source.canonicalProjection_origin _)

theorem canonicalMap_injective (embedding : ClosedEmbedding source target) :
    Function.Injective embedding.canonicalMap := by
  intro first second same
  have projected := (embedding.canonical_kernel _ _).mp same
  simpa only [FiniteGraph.canonicalProjection_origin] using projected

theorem canonicalMap_children (embedding : ClosedEmbedding source target)
    (node : source.canonicalGraph.Node) (child : target.canonicalGraph.Node) :
    target.canonicalGraph.edge (embedding.canonicalMap node) child ↔
      ∃ original, source.canonicalGraph.edge node original ∧ embedding.canonicalMap original = child := by
  change target.canonicalGraph.edge (target.canonicalProjection (embedding.map (source.canonicalOrigin node))) child ↔ _
  rw [target.canonicalProjection_edge]
  constructor
  · rintro ⟨middle, available, same⟩
    obtain ⟨original, originalAvailable, paired⟩ :=
      (embedding.children (source.canonicalOrigin node) middle).mp available
    refine ⟨source.canonicalProjection original, ?_, ?_⟩
    · have projected := (source.canonicalProjection_edge (source.canonicalOrigin node) _).mpr
        ⟨original, originalAvailable, rfl⟩
      simpa only [FiniteGraph.canonicalProjection_origin] using projected
    · exact (embedding.canonicalMap_projection original).trans ((congrArg target.canonicalProjection paired).trans same)
  · rintro ⟨original, available, same⟩
    have projected : source.canonicalGraph.edge (source.canonicalProjection (source.canonicalOrigin node)) original := by
      simpa only [FiniteGraph.canonicalProjection_origin] using available
    obtain ⟨middle, middleAvailable, paired⟩ :=
      (source.canonicalProjection_edge (source.canonicalOrigin node) _).mp projected
    refine ⟨embedding.map middle, (embedding.edge_iff _ _).mpr middleAvailable, ?_⟩
    exact (embedding.canonicalMap_projection middle).symm.trans
      ((congrArg embedding.canonicalMap paired).trans same)

def canonical (embedding : ClosedEmbedding source target) :
    ClosedEmbedding source.canonicalGraph target.canonicalGraph where
  map := embedding.canonicalMap
  injective := embedding.canonicalMap_injective
  children := embedding.canonicalMap_children

end ClosedEmbedding

namespace ClosedEmbedding

def inl (left right : FiniteGraph.{u}) :
    ClosedEmbedding left (FiniteGraph.disjointUnion left right) where
  map := Sum.inl
  injective := Sum.inl_injective
  children node child := by
    cases child with
    | inl child => exact ⟨fun available => ⟨child, available, rfl⟩,
        fun ⟨original, available, same⟩ => Sum.inl_injective same ▸ available⟩
    | inr child =>
      constructor
      · exact False.elim
      · rintro ⟨original, _, impossible⟩
        cases impossible

def inr (left right : FiniteGraph.{u}) :
    ClosedEmbedding right (FiniteGraph.disjointUnion left right) where
  map := Sum.inr
  injective := Sum.inr_injective
  children node child := by
    cases child with
    | inl child =>
      constructor
      · exact False.elim
      · rintro ⟨original, _, impossible⟩
        cases impossible
    | inr child => exact ⟨fun available => ⟨child, available, rfl⟩,
        fun ⟨original, available, same⟩ => Sum.inr_injective same ▸ available⟩

/-- Rooted image unfoldings can be compared in any Scott-extensional carrier. -/
theorem image_eq_iff_unfolding {left right target : FiniteGraph.{u}}
    (first : ClosedEmbedding left target) (second : ClosedEmbedding right target)
    (extensional : ScottExtensional target.edge) (a : left.Node) (b : right.Node) :
    first.map a = second.map b ↔ Nonempty (PresentationIso (unfold left.edge a) (unfold right.edge b)) := by
  constructor
  · intro same
    have isomorphism : PresentationIso (unfold left.edge a) (unfold target.edge (second.map b)) := by
      simpa only [same] using first.unfolding a
    exact ⟨isomorphism.trans (second.unfolding b).symm⟩
  · rintro ⟨isomorphism⟩
    exact (extensional _ _).mp
      ⟨(first.unfolding a).symm.trans (isomorphism.trans (second.unfolding b))⟩

end ClosedEmbedding

namespace FiniteGraph

/-- Independently canonical rooted graphs determine the pair reading. -/
theorem normalizedEqual_unfolding_kernel (left right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (first : left.Node) (second : right.Node) :
    normalizedEqual left right first second = true ↔
      Nonempty (PresentationIso
        (unfold left.canonicalGraph.edge (left.canonicalProjection first))
        (unfold right.canonicalGraph.edge (right.canonicalProjection second))) := by
  let firstEmbedding := ClosedEmbedding.inl left right
  let secondEmbedding := ClosedEmbedding.inr left right
  have comparison := ClosedEmbedding.image_eq_iff_unfolding firstEmbedding.canonical secondEmbedding.canonical
    (canonicalGraph_scottExtensional (disjointUnion left right))
    (left.canonicalProjection first) (right.canonicalProjection second)
  have firstImage : firstEmbedding.canonical.map (left.canonicalProjection first) =
      (disjointUnion left right).canonicalProjection (.inl first) := firstEmbedding.canonicalMap_projection first
  have secondImage : secondEmbedding.canonical.map (right.canonicalProjection second) =
      (disjointUnion left right).canonicalProjection (.inr second) := secondEmbedding.canonicalMap_projection second
  rw [firstImage, secondImage] at comparison
  exact (normalizedEqual_kernel left right first second).trans comparison

theorem normalizedEqual_refl (graph : ProfileFiniteScottCollapse.FiniteGraph.{u}) (node : graph.Node) :
    normalizedEqual graph graph node node = true :=
  (normalizedEqual_unfolding_kernel graph graph node node).mpr ⟨PresentationIso.refl _⟩

theorem normalizedEqual_symm (left right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (first : left.Node) (second : right.Node) :
    normalizedEqual left right first second = true ↔ normalizedEqual right left second first = true := by
  rw [normalizedEqual_unfolding_kernel, normalizedEqual_unfolding_kernel]
  exact ⟨fun ⟨isomorphism⟩ => ⟨isomorphism.symm⟩, fun ⟨isomorphism⟩ => ⟨isomorphism.symm⟩⟩

theorem normalizedEqual_trans (left middle right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (first : left.Node) (second : middle.Node) (third : right.Node)
    (before : normalizedEqual left middle first second = true)
    (after : normalizedEqual middle right second third = true) :
    normalizedEqual left right first third = true := by
  obtain ⟨firstIso⟩ := (normalizedEqual_unfolding_kernel _ _ _ _).mp before
  obtain ⟨secondIso⟩ := (normalizedEqual_unfolding_kernel _ _ _ _).mp after
  exact (normalizedEqual_unfolding_kernel _ _ _ _).mpr ⟨firstIso.trans secondIso⟩

theorem normalizedEqual_same_graph (graph : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (first second : graph.Node) :
    normalizedEqual graph graph first second = true ↔ graph.canonicalEquivalent first second = true := by
  exact (normalizedEqual_unfolding_kernel graph graph first second).trans
    (canonicalEquivalent_unfolding_kernel graph first second).symm

theorem canonicalEquivalent_closed (source target : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (embedding : ClosedEmbedding source target) (first second : source.Node) :
    target.canonicalEquivalent (embedding.map first) (embedding.map second) = true ↔
      source.canonicalEquivalent first second = true :=
  (canonicalEquivalent_kernel target _ _).trans
    ((embedding.canonical_kernel first second).trans (canonicalEquivalent_kernel source _ _).symm)

theorem normalizedEqual_disjoint_padding (left right extra : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (first : left.Node) (second : right.Node) :
    (disjointUnion (disjointUnion left right) extra).canonicalEquivalent
      (.inl (.inl first)) (.inl (.inr second)) = true ↔ normalizedEqual left right first second = true :=
  canonicalEquivalent_closed _ _ (ClosedEmbedding.inl _ _) _ _

end FiniteGraph

namespace ClosedEmbedding

variable {source target : ProfileFiniteScottCollapse.FiniteGraph.{u}}

def canonicalUnfolding (embedding : ClosedEmbedding source target) (node : source.Node) :
    PresentationIso (unfold source.canonicalGraph.edge (source.canonicalProjection node))
      (unfold target.canonicalGraph.edge (target.canonicalProjection (embedding.map node))) := by
  have isomorphism := embedding.canonical.unfolding (source.canonicalProjection node)
  have same : embedding.canonical.map (source.canonicalProjection node) =
      target.canonicalProjection (embedding.map node) := embedding.canonicalMap_projection node
  rw [same] at isomorphism
  exact isomorphism

end ClosedEmbedding

namespace FiniteGraph

theorem normalizedEqual_left_closed (source target right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (embedding : ClosedEmbedding source target) (first : source.Node) (second : right.Node) :
    normalizedEqual target right (embedding.map first) second = true ↔ normalizedEqual source right first second = true := by
  rw [normalizedEqual_unfolding_kernel, normalizedEqual_unfolding_kernel]
  exact ⟨fun ⟨isomorphism⟩ => ⟨(embedding.canonicalUnfolding first).trans isomorphism⟩,
    fun ⟨isomorphism⟩ => ⟨(embedding.canonicalUnfolding first).symm.trans isomorphism⟩⟩

theorem normalizedEqual_right_closed (left source target : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (embedding : ClosedEmbedding source target) (first : left.Node) (second : source.Node) :
    normalizedEqual left target first (embedding.map second) = true ↔ normalizedEqual left source first second = true := by
  rw [normalizedEqual_unfolding_kernel, normalizedEqual_unfolding_kernel]
  exact ⟨fun ⟨isomorphism⟩ => ⟨isomorphism.trans (embedding.canonicalUnfolding second).symm⟩,
    fun ⟨isomorphism⟩ => ⟨isomorphism.trans (embedding.canonicalUnfolding second)⟩⟩

theorem normalizedMember_same_graph (graph : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (member set : graph.Node) :
    normalizedMember graph graph member set = true ↔
      graph.canonicalMember (graph.canonicalProjection member) (graph.canonicalProjection set) := by
  rw [normalizedMember_eq_true]
  constructor
  · rintro ⟨child, available, same⟩
    have paired := (canonicalEquivalent_kernel graph _ _).mp
      ((normalizedEqual_same_graph graph member child).mp same)
    exact (graph.canonicalProjection_edge set _).mpr ⟨child, available, paired.symm⟩
  · intro available
    obtain ⟨child, childAvailable, same⟩ := (graph.canonicalProjection_edge set _).mp available
    exact ⟨child, childAvailable, (normalizedEqual_same_graph graph member child).mpr
      ((canonicalEquivalent_kernel graph _ _).mpr same.symm)⟩

/-- Pair membership uses the complete member fibre of the independently
canonical right graph, with full unfolding identity on its elements. -/
theorem normalizedMember_unfolding_kernel (left right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (member : left.Node) (set : right.Node) :
    normalizedMember left right member set = true ↔
      ∃ child : right.canonicalGraph.Node,
        right.canonicalMember child (right.canonicalProjection set) ∧
        Nonempty (PresentationIso (unfold left.canonicalGraph.edge (left.canonicalProjection member))
          (unfold right.canonicalGraph.edge child)) := by
  rw [normalizedMember_eq_true]
  constructor
  · rintro ⟨child, available, same⟩
    refine ⟨right.canonicalProjection child,
      (right.canonicalProjection_edge set _).mpr ⟨child, available, rfl⟩, ?_⟩
    exact (normalizedEqual_unfolding_kernel left right member child).mp same
  · rintro ⟨child, available, isomorphism⟩
    obtain ⟨original, originalAvailable, paired⟩ := (right.canonicalProjection_edge set child).mp available
    exact ⟨original, originalAvailable, (normalizedEqual_unfolding_kernel left right member original).mpr
      (paired.symm ▸ isomorphism)⟩

theorem normalizedMember_left_closed (source target right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (embedding : ClosedEmbedding source target) (member : source.Node) (set : right.Node) :
    normalizedMember target right (embedding.map member) set = true ↔ normalizedMember source right member set = true := by
  rw [normalizedMember_eq_true, normalizedMember_eq_true]
  constructor
  · rintro ⟨child, available, same⟩
    exact ⟨child, available, (normalizedEqual_left_closed _ _ _ embedding member child).mp same⟩
  · rintro ⟨child, available, same⟩
    exact ⟨child, available, (normalizedEqual_left_closed _ _ _ embedding member child).mpr same⟩

theorem normalizedMember_right_closed (left source target : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (embedding : ClosedEmbedding source target) (member : left.Node) (set : source.Node) :
    normalizedMember left target member (embedding.map set) = true ↔ normalizedMember left source member set = true := by
  rw [normalizedMember_eq_true, normalizedMember_eq_true]
  constructor
  · rintro ⟨child, available, same⟩
    obtain ⟨original, originalAvailable, paired⟩ := (embedding.children set child).mp available
    exact ⟨original, originalAvailable, (normalizedEqual_right_closed _ _ _ embedding member original).mp
      (paired.symm ▸ same)⟩
  · rintro ⟨child, available, same⟩
    exact ⟨embedding.map child, (embedding.edge_iff set child).mpr available,
      (normalizedEqual_right_closed _ _ _ embedding member child).mpr same⟩

/-- Equality of set readings matches every original member in the other
presentation, without requiring a bijection of their original occurrences. -/
theorem normalizedEqual_children (left right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (first : left.Node) (second : right.Node)
    (same : normalizedEqual left right first second = true)
    (child : left.Node) (available : left.edge first child) :
    ∃ reply, right.edge second reply ∧ normalizedEqual left right child reply = true := by
  let joint := disjointUnion left right
  have paired := (normalizedEqual_kernel left right first second).mp same
  have projected : joint.canonicalGraph.edge (joint.canonicalProjection (.inl first))
      (joint.canonicalProjection (.inl child)) :=
    (joint.canonicalProjection_edge (.inl first) _).mpr ⟨.inl child, available, rfl⟩
  rw [paired] at projected
  obtain ⟨reply, replyAvailable, replyMatched⟩ :=
    (joint.canonicalProjection_edge (.inr second) _).mp projected
  cases reply with
  | inl reply => exact False.elim replyAvailable
  | inr reply => exact ⟨reply, replyAvailable,
      (normalizedEqual_kernel left right child reply).mpr replyMatched.symm⟩

theorem normalizedMember_left_equal (left other right : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (first : left.Node) (second : other.Node) (set : right.Node)
    (same : normalizedEqual left other first second = true) :
    normalizedMember left right first set = true ↔ normalizedMember other right second set = true := by
  rw [normalizedMember_eq_true, normalizedMember_eq_true]
  constructor
  · rintro ⟨child, available, matched⟩
    exact ⟨child, available, normalizedEqual_trans other left right second first child
      ((normalizedEqual_symm left other first second).mp same) matched⟩
  · rintro ⟨child, available, matched⟩
    exact ⟨child, available, normalizedEqual_trans left other right first second child same matched⟩

theorem normalizedMember_right_equal (left right other : ProfileFiniteScottCollapse.FiniteGraph.{u})
    (member : left.Node) (first : right.Node) (second : other.Node)
    (same : normalizedEqual right other first second = true) :
    normalizedMember left right member first = true ↔ normalizedMember left other member second = true := by
  rw [normalizedMember_eq_true, normalizedMember_eq_true]
  constructor
  · rintro ⟨child, available, matched⟩
    obtain ⟨reply, replyAvailable, replyMatched⟩ := normalizedEqual_children right other first second same child available
    exact ⟨reply, replyAvailable, normalizedEqual_trans left right other member child reply matched replyMatched⟩
  · rintro ⟨child, available, matched⟩
    obtain ⟨reply, replyAvailable, replyMatched⟩ := normalizedEqual_children other right second first
      ((normalizedEqual_symm right other first second).mp same) child available
    exact ⟨reply, replyAvailable, normalizedEqual_trans left other right member child reply matched replyMatched⟩

end FiniteGraph

namespace Presentations

open ProfileGraphReadout.Presentations

/-- Rerooting retains every authored row. -/
def reroot (presentation : Checked) (node : Node presentation) : Checked :=
  ⟨⟨node.val, presentation.val.rows⟩, node.isLt, presentation.property.2⟩

def rerootEmbedding (presentation : Checked) (node : Node presentation) :
    ClosedEmbedding (ProfileFiniteScottCollapse.Presentations.graph (reroot presentation node))
      (ProfileFiniteScottCollapse.Presentations.graph presentation) where
  map := fun child => child
  injective := fun _ _ same => same
  children _node child := ⟨fun available => ⟨child, available, rfl⟩,
    fun ⟨_original, available, same⟩ => same ▸ available⟩

theorem equal_refl (presentation : Checked) : ProfileFiniteScottCollapse.Presentations.equal presentation presentation = true :=
  FiniteGraph.normalizedEqual_refl _ _

theorem equal_symm (first second : Checked) :
    ProfileFiniteScottCollapse.Presentations.equal first second = true ↔
      ProfileFiniteScottCollapse.Presentations.equal second first = true :=
  FiniteGraph.normalizedEqual_symm _ _ _ _

theorem equal_trans (first middle last : Checked)
    (before : ProfileFiniteScottCollapse.Presentations.equal first middle = true)
    (after : ProfileFiniteScottCollapse.Presentations.equal middle last = true) :
    ProfileFiniteScottCollapse.Presentations.equal first last = true :=
  FiniteGraph.normalizedEqual_trans _ _ _ _ _ _ before after

theorem equal_equivalence : Equivalence (fun first second : Checked =>
    ProfileFiniteScottCollapse.Presentations.equal first second = true) :=
  ⟨equal_refl, fun {_ _} same => equal_symm _ _ |>.mp same,
    fun {_ _ _} before after => equal_trans _ _ _ before after⟩

theorem member_left_equal (first second set : Checked)
    (same : ProfileFiniteScottCollapse.Presentations.equal first second = true) :
    ProfileFiniteScottCollapse.Presentations.member first set = true ↔
      ProfileFiniteScottCollapse.Presentations.member second set = true :=
  FiniteGraph.normalizedMember_left_equal _ _ _ _ _ _ same

theorem member_right_equal (element first second : Checked)
    (same : ProfileFiniteScottCollapse.Presentations.equal first second = true) :
    ProfileFiniteScottCollapse.Presentations.member element first = true ↔
      ProfileFiniteScottCollapse.Presentations.member element second = true :=
  FiniteGraph.normalizedMember_right_equal _ _ _ _ _ _ same

theorem reroot_member_support (presentation : Checked) (child : Node presentation) :
    ProfileFiniteScottCollapse.Presentations.member (reroot presentation child) presentation = true ↔
      (ProfileFiniteScottCollapse.Presentations.graph presentation).canonicalMember
        ((ProfileFiniteScottCollapse.Presentations.graph presentation).canonicalProjection child)
        ((ProfileFiniteScottCollapse.Presentations.graph presentation).canonicalProjection (root presentation)) := by
  have comparison := FiniteGraph.normalizedMember_left_closed _ _
    (ProfileFiniteScottCollapse.Presentations.graph presentation) (rerootEmbedding presentation child)
    (root (reroot presentation child)) (root presentation)
  exact comparison.symm.trans (FiniteGraph.normalizedMember_same_graph _ _ _)

theorem reroot_member_selected_support (presentation : Checked) (child : Node presentation) :
    ProfileFiniteScottCollapse.Presentations.member (reroot presentation child) presentation = true ↔
      (ProfileFiniteScottCollapse.Presentations.graph presentation).canonicalProjection child ∈
        (ProfileFiniteScottCollapse.Presentations.selectedChildren presentation).map
          (ProfileFiniteScottCollapse.Presentations.graph presentation).canonicalProjection :=
  (reroot_member_support presentation child).trans
    (ProfileFiniteScottCollapse.Presentations.selectedChildren_support presentation child).symm

theorem equal_reroot_iff (element presentation : Checked) (child : Node presentation) :
    ProfileFiniteScottCollapse.Presentations.equal element (reroot presentation child) = true ↔
      normalizedEqual (ProfileFiniteScottCollapse.Presentations.graph element)
        (ProfileFiniteScottCollapse.Presentations.graph presentation) (root element) child = true := by
  exact (FiniteGraph.normalizedEqual_right_closed
    (ProfileFiniteScottCollapse.Presentations.graph element) _ _ (rerootEmbedding presentation child)
    (root element) (root (reroot presentation child))).symm

/-- The native first-row witnesses cover exactly pairwise material membership. -/
theorem member_selected_children (element presentation : Checked) :
    ProfileFiniteScottCollapse.Presentations.member element presentation = true ↔
      ∃ child ∈ ProfileFiniteScottCollapse.Presentations.selectedChildren presentation,
        ProfileFiniteScottCollapse.Presentations.equal element (reroot presentation child) = true := by
  rw [ProfileFiniteScottCollapse.Presentations.member_eq_true]
  constructor
  · rintro ⟨child, available, same⟩
    have supported := ((ProfileFiniteScottCollapse.Presentations.graph presentation).canonicalProjection_edge
      (root presentation) _).mpr ⟨child, available, rfl⟩
    obtain ⟨selected, listed, paired⟩ := List.mem_map.mp
      ((ProfileFiniteScottCollapse.Presentations.selectedChildren_support presentation child).mpr supported)
    have within := (FiniteGraph.normalizedEqual_same_graph
      (ProfileFiniteScottCollapse.Presentations.graph presentation) child selected).mpr
        ((canonicalEquivalent_kernel _ _ _).mpr paired.symm)
    have changed := FiniteGraph.normalizedEqual_trans
      (ProfileFiniteScottCollapse.Presentations.graph element)
      (ProfileFiniteScottCollapse.Presentations.graph presentation)
      (ProfileFiniteScottCollapse.Presentations.graph presentation)
      (root element) child selected same within
    exact ⟨selected, listed, (equal_reroot_iff element presentation selected).mpr changed⟩
  · rintro ⟨child, selected, same⟩
    exact ⟨child, ProfileFiniteScottCollapse.Presentations.selectedChildren_edge presentation child selected,
      (equal_reroot_iff element presentation child).mp same⟩

end Presentations

namespace Controls

abbrev leaves : ProfileFiniteScottCollapse.FiniteGraph := ofEdges (fun (_ _ : Fin 2) => False)
abbrev leafLoop : ProfileFiniteScottCollapse.FiniteGraph :=
  ofEdges (fun (source target : Fin 2) => source = 1 ∧ target = 1)

theorem leaves_raw_identifies : leaves.rawRelation 0 1 := by decide +kernel

theorem leafLoop_stopped : leafLoop.stopped := by decide +kernel

/-- Injectivity and preservation of old edges alone omit new successors. -/
theorem edge_preservation_alone_is_insufficient :
    Function.Injective (fun node : Fin 2 => node) ∧
      (∀ source target, leaves.edge source target → leafLoop.edge source target) ∧
      leaves.canonicalEquivalent 0 1 = true ∧ leafLoop.canonicalEquivalent 0 1 ≠ true := by
  refine ⟨fun _ _ same => same, fun _ _ impossible => False.elim impossible,
    canonicalEquivalent_of_raw leaves 0 1 leaves_raw_identifies, ?_⟩
  intro same
  have impossible := (canonicalEquivalent_of_stopped leafLoop leafLoop_stopped 0 1).mp same
  exact (by decide : (0 : Fin 2) ≠ 1) impossible

theorem missing_successor :
    leafLoop.edge 1 1 ∧ ¬ ∃ child, leaves.edge 1 child ∧ child = (1 : Fin 2) := by decide +kernel

/-- Agreement within one graph survives the actual tagged pair comparator. -/
theorem recount_pair_identifies :
    normalizedEqual ProfileFiniteScottCollapse.Controls.recount ProfileFiniteScottCollapse.Controls.recount 0 3 = true :=
  (FiniteGraph.normalizedEqual_same_graph _ _ _).mpr ProfileFiniteScottCollapse.Controls.recount_final_identifies

theorem recount_padding_identifies :
    (disjointUnion (disjointUnion ProfileFiniteScottCollapse.Controls.recount ProfileFiniteScottCollapse.Controls.recount)
      ProfileFiniteScottCollapse.Controls.scott).canonicalEquivalent (.inl (.inl 0)) (.inl (.inr 3)) = true :=
  (FiniteGraph.normalizedEqual_disjoint_padding _ _ _ _ _).mpr recount_pair_identifies

end Controls

end Mettapedia.SetTheory.Profiles.ProfileFiniteScottCoherence
