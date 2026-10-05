import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.KuratowskiPair
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet

/-!
# Constructive universe lifting and collection of hypersets

Lifting the nodes of a presentation gives an injective, membership-preserving
map from `HSet.{u}` to `HSet.{u + 1}`. At the larger level, the membership graph
of the entire smaller carrier is small. Its generated subgraph gives a uniform
presentation of each lifted value, without selecting quotient representatives.

Consequently every family of smaller hypersets indexed by `Type (u + 1)` has
an actual range at the larger graph bound. The level increase is part of the
construction: this does not assert same-level collection or a universal set
at any fixed level.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

namespace AccessiblePointedGraph

def liftRelation {α : Type u} (r : α → α → Prop)
    (left right : ULift.{u + 1, u} α) : Prop := r left.down right.down

theorem liftRelation_reachable {α : Type u} {r : α → α → Prop} {a b : α}
    (reachable : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen (liftRelation r) (ULift.up a) (ULift.up b) := by
  induction reachable with
  | refl => exact .refl
  | tail _ edge earlier => exact earlier.tail edge

/-- The lifted graph retains every node and edge. -/
def lift (G : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u + 1} where
  Node := ULift.{u + 1, u} G.Node
  edge := liftRelation G.edge
  point := ULift.up G.point
  reachable node := liftRelation_reachable (G.reachable node.down)

theorem bisimilar_liftRelation {α : Type u} (r : α → α → Prop) (a : α) :
    Bisimilar r (liftRelation r) a (ULift.up a) :=
  bisimilar_apply (r := r) (s := liftRelation r) (f := ULift.up)
    (fun _ _ edge => edge) (fun _ b edge => ⟨b.down, edge, rfl⟩) a

/-- Lifting reflects bisimilarity as well as preserving it. -/
theorem lift_equiv_lift_iff {G H : AccessiblePointedGraph.{u}} :
    G.lift ≈ H.lift ↔ G ≈ H := by
  constructor
  · intro related
    exact (bisimilar_liftRelation G.edge G.point).trans
      (related.trans (bisimilar_liftRelation H.edge H.point).symm)
  · intro related
    exact (bisimilar_liftRelation G.edge G.point).symm.trans
      (related.trans (bisimilar_liftRelation H.edge H.point))

end AccessiblePointedGraph

namespace HSet

open AccessiblePointedGraph

/-- Lift a material hyperset by lifting a presentation. The quotient map
uses a proved bisimilarity preservation law, without choosing a presentation. -/
def lift : HSet.{u} → HSet.{u + 1} :=
  Quotient.map AccessiblePointedGraph.lift fun _ _ related =>
    AccessiblePointedGraph.lift_equiv_lift_iff.mpr related

@[simp] theorem lift_mk (G : AccessiblePointedGraph.{u}) :
    lift (mk G) = mk G.lift := rfl

theorem lift_injective : Function.Injective lift.{u} := by
  intro x y same
  induction x using HSet.ind with | mk G =>
    induction y using HSet.ind with | mk H =>
      exact sound (lift_equiv_lift_iff.mp (mk_eq_mk_iff.mp same))

/-- Lifting commutes with decorating any small graph. -/
theorem lift_decorate {α : Type u} (r : α → α → Prop) (a : α) :
    lift (decorate r a) = decorate (liftRelation r) (ULift.up a) := by
  change mk (AccessiblePointedGraph.lift (generated r a)) = _
  rw [mk_eq_decorate]
  apply decorate_eq_of_bisimilar
  exact (bisimilar_liftRelation (generated r a).edge (generated r a).point).symm.trans
    ((bisimilar_generated r a (generated r a).point).trans
      (bisimilar_liftRelation r a))

/-- Every member of a lifted value is itself lifted, with exactly the
original membership relation. No inverse representative is selected. -/
theorem mem_lift_iff {X : HSet.{u}} {y : HSet.{u + 1}} :
    y ∈ lift X ↔ ∃ x : HSet.{u}, x ∈ X ∧ lift x = y := by
  induction X using HSet.ind with | mk G =>
    rw [lift_mk, mem_mk]
    constructor
    · rintro ⟨node, edge, same⟩
      exact ⟨decorate G.edge node.down, mem_mk.mpr ⟨node.down, edge, rfl⟩,
        (lift_decorate G.edge node.down).trans same⟩
    · rintro ⟨x, member, same⟩
      obtain ⟨node, edge, pictured⟩ := mem_mk.mp member
      exact ⟨ULift.up node, edge,
        (lift_decorate G.edge node).symm.trans ((congrArg lift pictured).trans same)⟩

@[simp] theorem lift_mem_lift_iff {x X : HSet.{u}} :
    lift x ∈ lift X ↔ x ∈ X := by
  constructor
  · intro member
    obtain ⟨y, original, same⟩ := mem_lift_iff.mp member
    exact lift_injective same ▸ original
  · intro member
    exact mem_lift_iff.mpr ⟨x, member, rfl⟩

@[simp] theorem lift_empty : lift (∅ : HSet.{u}) = ∅ := by
  apply eq_empty_iff.mpr
  intro y member
  obtain ⟨x, impossible, _⟩ := mem_lift_iff.mp member
  exact notMem_empty x impossible

@[simp] theorem lift_insert (x X : HSet.{u}) :
    lift (insert x X) = insert (lift x) (lift X) := by
  ext y
  rw [mem_lift_iff, mem_insert_iff]
  constructor
  · rintro ⟨z, member, same⟩
    rcases mem_insert_iff.mp member with rfl | original
    · exact Or.inl same.symm
    · exact Or.inr (mem_lift_iff.mpr ⟨z, original, same⟩)
  · rintro (rfl | member)
    · exact ⟨x, mem_insert_iff.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨z, original, same⟩ := mem_lift_iff.mp member
      exact ⟨z, mem_insert_iff.mpr (Or.inr original), same⟩

@[simp] theorem lift_singleton (x : HSet.{u}) :
    lift ({x} : HSet.{u}) = {lift x} := by
  change lift (insert x ∅) = insert (lift x) ∅
  rw [lift_insert, lift_empty]

@[simp] theorem lift_kpair (x y : HSet.{u}) :
    lift (kpair x y) = kpair (lift x) (lift y) := by
  simp only [kpair, lift_insert, lift_singleton]

/-- A uniform graph for a lifted value: the smaller membership carrier is
an actual small graph at the next level. -/
def presentationUp (x : HSet.{u}) : AccessiblePointedGraph.{u + 1} :=
  generated (fun a b : HSet.{u} => b ∈ a) x

private theorem liftedGraph_to_membership (G : AccessiblePointedGraph.{u}) :
    IsBoundedMorphism G.lift.edge (fun a b : HSet.{u} => b ∈ a)
      (fun node => decorate G.edge node.down) where
  map _ _ edge := decorate_mem_decorate edge
  lift node y member := by
    obtain ⟨child, edge, same⟩ := mem_decorate.mp member
    exact ⟨ULift.up child, edge, same⟩

/-- The uniform presentation is proved to picture the lifted value. Its
construction and its correctness use no graph selector. -/
theorem mk_presentationUp (x : HSet.{u}) : mk (presentationUp x) = lift x := by
  induction x using HSet.ind with | mk G =>
    have comparison := congrFun (liftedGraph_to_membership G).decorate_comp G.lift.point
    change decorate (fun a b : HSet.{u} => b ∈ a) (mk G) = mk G.lift
    calc
      decorate (fun a b : HSet.{u} => b ∈ a) (mk G) =
          decorate (fun a b : HSet.{u} => b ∈ a) (decorate G.edge G.point) := by
            rw [mk_eq_decorate G]
      _ = decorate G.lift.edge G.lift.point := comparison
      _ = mk G.lift := (mk_eq_decorate G.lift).symm

/-- An actual collecting graph for every family at the specified raised
bound. No presentation or section carrier is an input. -/
def imageUpGraph {I : Type (u + 1)} (family : I → HSet.{u}) :
    AccessiblePointedGraph.{u + 1} := sup (fun index => presentationUp (family index))

def imageUp {I : Type (u + 1)} (family : I → HSet.{u}) : HSet.{u + 1} :=
  mk (imageUpGraph family)

theorem mem_imageUp_iff {I : Type (u + 1)} {family : I → HSet.{u}}
    {y : HSet.{u + 1}} : y ∈ imageUp family ↔ ∃ index, lift (family index) = y := by
  change y ∈ range (fun index => presentationUp (family index)) ↔ _
  rw [mem_range]
  exact exists_congr fun index => by rw [mk_presentationUp]

theorem lift_mem_imageUp {I : Type (u + 1)} (family : I → HSet.{u}) (index : I) :
    lift (family index) ∈ imageUp family := mem_imageUp_iff.mpr ⟨index, rfl⟩

/-- At this bound the image is genuinely constructed, not postulated by
a collection or replacement interface. -/
theorem exists_image_at_successor {I : Type (u + 1)} (family : I → HSet.{u}) :
    ∃ Y : HSet.{u + 1}, ∀ y, y ∈ Y ↔ ∃ index, lift (family index) = y :=
  ⟨imageUp family, fun _ => mem_imageUp_iff⟩

/-- Lifting preserves a genuine non-well-founded value. -/
theorem lift_quineAtom : lift quineAtom.{u} = quineAtom.{u + 1} := by
  apply eq_quineAtom_of_eq_singleton
  rw [← lift_singleton, ← quineAtom_eq_singleton]

/-- The larger collection of all smaller values cannot lie in the image
of a smaller hyperset: a same-level universal set would follow. -/
theorem not_surjective_lift : ¬ Function.Surjective lift.{u} := by
  intro surjective
  obtain ⟨X, same⟩ := surjective (imageUp (id : HSet.{u} → HSet.{u}))
  apply not_exists_universal
  refine ⟨X, fun x => ?_⟩
  apply lift_mem_lift_iff.mp
  rw [same]
  exact lift_mem_imageUp id x

#print axioms lift_injective
#print axioms mk_presentationUp
#print axioms exists_image_at_successor
#print axioms lift_quineAtom

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
