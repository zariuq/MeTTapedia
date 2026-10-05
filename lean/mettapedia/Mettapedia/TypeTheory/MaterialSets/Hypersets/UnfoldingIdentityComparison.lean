import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentationIdentityComparison

/-!
# Unfolding-tree identity and anti-foundation comparison

Finite paths construct the full unfolding tree of a graph, retaining each
path occurrence. Isomorphism of these trees is distinct from isomorphism of
the original graph and from ordinary bisimilarity. Scott extensionality says
that equality of original nodes is exactly isomorphism of their unfoldings.

A concrete Scott-extensional graph has one unary cyclic node and one binary
cyclic node. Their unfolding trees cannot be isomorphic, while ordinary
bisimilarity identifies them. Consequently no injective decoration of this
graph exists in the Aczel hyperset model. This proves a difference between
the two anti-foundation requirements; it does not claim a complete Scott
model from a graph-isomorphism quotient.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.UnfoldingIdentityComparison

open AccessiblePointedGraph

universe u

/-- A path retains every intermediate occurrence and its terminal vertex. -/
inductive Path {α : Type u} (edge : α → α → Prop) (root : α) : α → Type u where
  | nil : Path edge root root
  | snoc {source target : α} (path : Path edge root source) (step : edge source target) :
      Path edge root target

abbrev PathNode {α : Type u} (edge : α → α → Prop) (root : α) : Type u :=
  Σ target, Path edge root target

inductive PathEdge {α : Type u} (edge : α → α → Prop) (root : α) :
    PathNode edge root → PathNode edge root → Prop where
  | extend {source target : α} (path : Path edge root source) (step : edge source target) :
      PathEdge edge root ⟨source, path⟩ ⟨target, .snoc path step⟩

theorem path_reachable {α : Type u} {edge : α → α → Prop} {root target : α}
    (path : Path edge root target) :
    Relation.ReflTransGen (PathEdge edge root) ⟨root, .nil⟩ ⟨target, path⟩ := by
  induction path with
  | nil => exact .refl
  | snoc earlier step reachable => exact reachable.tail (.extend earlier step)

/-- The full unfolding contains all finite paths, not a finite truncation. -/
def unfold {α : Type u} (edge : α → α → Prop) (root : α) : AccessiblePointedGraph.{u} where
  Node := PathNode edge root
  edge := PathEdge edge root
  point := ⟨root, .nil⟩
  reachable node := path_reachable node.2

private theorem rootChild_iff {α : Type u} {edge : α → α → Prop} {root : α}
    (child : PathNode edge root) :
    PathEdge edge root ⟨root, .nil⟩ child ↔
      ∃ step : edge root child.1, child.2 = Path.snoc Path.nil step := by
  constructor
  · intro available
    cases available with
    | extend path step => exact ⟨step, rfl⟩
  · rintro ⟨step, same⟩
    rcases child with ⟨target, path⟩
    change path = Path.snoc Path.nil step at same
    rw [same]
    exact .extend .nil step

/-- An actual root occurrence of the unfolding is exactly one original
successor. Both inverse operations are explicitly constructed. -/
def unfoldOccurrencesEquiv {α : Type u} (edge : α → α → Prop) (root : α) :
    Occurrence (unfold edge root) ≃ {target : α // edge root target} where
  toFun occurrence := ⟨occurrence.1.1, by
    obtain ⟨step, _⟩ := (rootChild_iff occurrence.1).mp occurrence.2
    exact step⟩
  invFun successor := ⟨⟨successor.val, .snoc .nil successor.property⟩, .extend .nil successor.property⟩
  left_inv occurrence := by
    apply Subtype.ext
    obtain ⟨step, same⟩ := (rootChild_iff occurrence.1).mp occurrence.2
    exact Sigma.ext rfl (heq_of_eq same.symm)
  right_inv successor := Subtype.ext rfl

/-- Scott extensionality compares original vertices with full unfolding
tree isomorphism. It does not replace unfolding trees by the original graph. -/
def ScottExtensional {α : Type u} (edge : α → α → Prop) : Prop :=
  ∀ first second, Nonempty (PresentationIso (unfold edge first) (unfold edge second)) ↔ first = second

namespace UnaryBinary

/-- The unary node only loops on itself; the binary node reaches both. -/
def edge (source target : ULift.{u, 0} Bool) : Prop :=
  source.down = true ∨ target.down = false

def graph : AccessiblePointedGraph.{u} where
  Node := ULift.{u, 0} Bool
  edge := edge
  point := ⟨true⟩
  reachable
    | ⟨true⟩ => .refl
    | ⟨false⟩ => .single (Or.inl rfl)

private theorem unary_successors_subsingleton :
    Subsingleton {target : ULift.{u, 0} Bool // edge ⟨false⟩ target} := by
  constructor
  intro first second
  apply Subtype.ext
  apply ULift.ext
  have firstFalse : first.val.down = false :=
    first.property.elim (fun impossible => Bool.noConfusion impossible) id
  have secondFalse : second.val.down = false :=
    second.property.elim (fun impossible => Bool.noConfusion impossible) id
  exact firstFalse.trans secondFalse.symm

private theorem no_binary_unary_successor_equiv :
    ¬ Nonempty
      ({target : ULift.{u, 0} Bool // edge ⟨true⟩ target} ≃
        {target : ULift.{u, 0} Bool // edge ⟨false⟩ target}) := by
  rintro ⟨equivalence⟩
  let first : {target : ULift.{u, 0} Bool // edge ⟨true⟩ target} := ⟨⟨true⟩, Or.inl rfl⟩
  let second : {target : ULift.{u, 0} Bool // edge ⟨true⟩ target} := ⟨⟨false⟩, Or.inl rfl⟩
  have same : first = second := equivalence.injective
    (unary_successors_subsingleton.allEq _ _)
  exact Bool.noConfusion (congrArg (fun value => value.val.down) same)

theorem no_binary_unary_unfolding_iso :
    ¬ Nonempty (PresentationIso (unfold edge ⟨true⟩) (unfold edge ⟨false⟩)) := by
  rintro ⟨isomorphism⟩
  exact no_binary_unary_successor_equiv
    ⟨(unfoldOccurrencesEquiv edge ⟨true⟩).symm.trans
      (isomorphism.occurrenceTransport.trans (unfoldOccurrencesEquiv edge ⟨false⟩))⟩

theorem scottExtensional : ScottExtensional edge.{u} := by
  rintro ⟨first⟩ ⟨second⟩
  constructor
  · rintro ⟨isomorphism⟩
    cases first <;> cases second
    · rfl
    · exact (no_binary_unary_unfolding_iso ⟨isomorphism.symm⟩).elim
    · exact (no_binary_unary_unfolding_iso ⟨isomorphism⟩).elim
    · rfl
  · intro same
    have sameDown : first = second := congrArg ULift.down same
    cases sameDown
    exact ⟨PresentationIso.refl _⟩

/-- Ordinary bisimulation forgets the unary/binary branching difference. -/
theorem all_nodes_bisimilar (first second : ULift.{u, 0} Bool) :
    Bisimilar edge edge first second := by
  refine ⟨fun _ _ => True, ?_, True.intro⟩
  intro left right _
  constructor
  · intro target _
    exact ⟨⟨false⟩, Or.inr rfl, True.intro⟩
  · intro target _
    exact ⟨⟨false⟩, Or.inr rfl, True.intro⟩

theorem afa_decoration_collapses : HSet.decorate edge.{u} ⟨true⟩ = HSet.decorate edge ⟨false⟩ :=
  HSet.decorate_eq_of_bisimilar (all_nodes_bisimilar _ _)

/-- Even though this graph is Scott extensional, the AFA carrier cannot
supply Scott's injective-decoration clause for it. -/
theorem no_injective_afa_decoration :
    ¬ ∃ decoration : ULift.{u, 0} Bool → HSet.{u},
      HSet.IsDecoration edge decoration ∧ Function.Injective decoration := by
  rintro ⟨decoration, lawful, injective⟩
  have same : decoration ⟨true⟩ = decoration ⟨false⟩ := by
    rw [lawful.eq_decorate]
    exact afa_decoration_collapses
  exact Bool.noConfusion (congrArg ULift.down (injective same))

theorem profile_separation : ScottExtensional edge.{u} ∧
    ¬ ∃ decoration : ULift.{u, 0} Bool → HSet.{u},
      HSet.IsDecoration edge decoration ∧ Function.Injective decoration :=
  ⟨scottExtensional, no_injective_afa_decoration⟩

end UnaryBinary

#print axioms unfoldOccurrencesEquiv
#print axioms UnaryBinary.scottExtensional
#print axioms UnaryBinary.afa_decoration_collapses
#print axioms UnaryBinary.profile_separation

end Mettapedia.TypeTheory.MaterialSets.Hypersets.UnfoldingIdentityComparison
