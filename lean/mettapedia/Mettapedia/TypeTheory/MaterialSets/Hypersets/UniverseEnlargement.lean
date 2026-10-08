import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLiftCoherence

/-!
# Coherent material embeddings at arbitrary larger bounds

The target bound is the maximum of the source graph bound and a declared
external bound. Nodes and edges are retained explicitly. The induced
material embedding is injective, preserves and reflects membership, and
has a constructed inverse on the members of each known source set.

Successive embeddings agree with the direct maximum-bound embedding.
This permits code and parameter bounds to differ from the member bound;
it does not assume a same-level enclosing universe or collapse a successor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u v w

namespace AccessiblePointedGraph

def enlargedRelation {A : Type u} (relation : A → A → Prop)
    (first second : ULift.{v, u} A) : Prop := relation first.down second.down

theorem enlargedRelation_reachable {A : Type u} {relation : A → A → Prop} {a b : A}
    (path : Relation.ReflTransGen relation a b) :
    Relation.ReflTransGen (enlargedRelation.{u,v} relation) (ULift.up a) (ULift.up b) := by
  induction path with
  | refl => exact .refl
  | tail _ edge earlier => exact earlier.tail edge

def enlarge (graph : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{max u v} where
  Node := ULift.{v, u} graph.Node
  edge := enlargedRelation graph.edge
  point := ULift.up graph.point
  reachable node := enlargedRelation_reachable (graph.reachable node.down)

theorem bisimilar_enlargedRelation {A : Type u} (relation : A → A → Prop) (a : A) :
    Bisimilar relation (enlargedRelation.{u,v} relation) a (ULift.up a) :=
  bisimilar_apply (r := relation) (s := enlargedRelation.{u,v} relation) (f := ULift.up) (fun _ _ edge => edge)
    (fun _ child edge => ⟨child.down, edge, rfl⟩) a

theorem enlarge_equiv_iff {first second : AccessiblePointedGraph.{u}} :
    first.enlarge.{u,v} ≈ second.enlarge.{u,v} ↔ first ≈ second := by
  constructor
  · intro related
    exact (bisimilar_enlargedRelation first.edge first.point).trans
      (related.trans (bisimilar_enlargedRelation second.edge second.point).symm)
  · intro related
    exact (bisimilar_enlargedRelation first.edge first.point).symm.trans
      (related.trans (bisimilar_enlargedRelation second.edge second.point))

end AccessiblePointedGraph

namespace HSet

open AccessiblePointedGraph

def enlarge : HSet.{u} → HSet.{max u v} :=
  Quotient.map AccessiblePointedGraph.enlarge fun _ _ related => enlarge_equiv_iff.mpr related

@[simp] theorem enlarge_mk (graph : AccessiblePointedGraph.{u}) :
    enlarge.{u,v} (mk graph) = mk graph.enlarge := rfl

theorem enlarge_injective : Function.Injective enlarge.{u,v} := by
  intro first second same
  induction first using HSet.ind with | mk left =>
    induction second using HSet.ind with | mk right =>
      exact sound (enlarge_equiv_iff.mp (mk_eq_mk_iff.mp same))

theorem enlarge_decorate {A : Type u} (relation : A → A → Prop) (a : A) :
    enlarge.{u,v} (decorate relation a) =
      decorate (enlargedRelation.{u,v} relation) (ULift.up a) := by
  change mk (AccessiblePointedGraph.enlarge (generated relation a)) = _
  rw [mk_eq_decorate]
  apply decorate_eq_of_bisimilar
  exact (bisimilar_enlargedRelation (generated relation a).edge (generated relation a).point).symm.trans
    ((bisimilar_generated relation a (generated relation a).point).trans
      (bisimilar_enlargedRelation relation a))

theorem mem_enlarge_iff {bound : HSet.{u}} {value : HSet.{max u v}} :
    value ∈ enlarge.{u,v} bound ↔ ∃ original : HSet.{u}, original ∈ bound ∧ enlarge original = value := by
  induction bound using HSet.ind with | mk graph =>
    rw [enlarge_mk, mem_mk]
    constructor
    · rintro ⟨node, edge, same⟩
      exact ⟨decorate graph.edge node.down, mem_mk.mpr ⟨node.down, edge, rfl⟩,
        (enlarge_decorate graph.edge node.down).trans same⟩
    · rintro ⟨original, member, same⟩
      obtain ⟨node, edge, pictured⟩ := mem_mk.mp member
      exact ⟨ULift.up node, edge,
        (enlarge_decorate graph.edge node).symm.trans ((congrArg enlarge pictured).trans same)⟩

@[simp] theorem enlarge_mem_enlarge_iff {value bound : HSet.{u}} :
    enlarge.{u,v} value ∈ enlarge.{u,v} bound ↔ value ∈ bound := by
  constructor
  · intro member
    obtain ⟨original, belongs, same⟩ := mem_enlarge_iff.mp member
    exact enlarge_injective same ▸ belongs
  · intro member
    exact mem_enlarge_iff.mpr ⟨value, member, rfl⟩

theorem enlarge_comp (value : HSet.{u}) :
    enlarge.{max u v,w} (enlarge.{u,v} value) = enlarge.{u,max v w} value := by
  induction value using HSet.ind with | mk graph =>
    apply sound
    exact (bisimilar_enlargedRelation graph.enlarge.edge graph.enlarge.point).symm.trans
      ((bisimilar_enlargedRelation graph.edge graph.point).symm.trans
        (bisimilar_enlargedRelation graph.edge graph.point))

theorem enlarge_self (value : HSet.{u}) : enlarge.{u,u} value = value := by
  induction value using HSet.ind with | mk graph =>
    exact sound (bisimilar_enlargedRelation graph.edge graph.point).symm

theorem enlarge_successor (value : HSet.{u}) : enlarge.{u,u+1} value = lift value := rfl

@[simp] theorem enlarge_empty : enlarge.{u,v} (∅ : HSet.{u}) = ∅ := by
  apply eq_empty_iff.mpr
  intro value member
  obtain ⟨original, impossible, _⟩ := mem_enlarge_iff.mp member
  exact notMem_empty original impossible

@[simp] theorem enlarge_insert (value bound : HSet.{u}) :
    enlarge.{u,v} (insert value bound) = insert (enlarge value) (enlarge bound) := by
  ext candidate
  rw [mem_enlarge_iff, mem_insert_iff]
  constructor
  · rintro ⟨original, member, same⟩
    rcases mem_insert_iff.mp member with rfl | belongs
    · exact Or.inl same.symm
    · exact Or.inr (mem_enlarge_iff.mpr ⟨original, belongs, same⟩)
  · rintro (rfl | member)
    · exact ⟨value, mem_insert_iff.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨original, belongs, same⟩ := mem_enlarge_iff.mp member
      exact ⟨original, mem_insert_iff.mpr (Or.inr belongs), same⟩

@[simp] theorem enlarge_singleton (value : HSet.{u}) :
    enlarge.{u,v} ({value} : HSet.{u}) = {enlarge value} := by
  change enlarge (insert value ∅) = insert (enlarge value) ∅
  rw [enlarge_insert, enlarge_empty]

@[simp] theorem enlarge_kpair (first second : HSet.{u}) :
    enlarge.{u,v} (kpair first second) = kpair (enlarge first) (enlarge second) := by
  simp only [kpair, enlarge_insert, enlarge_singleton]

/-- Recover a member within its supplied original bound by a separated row. -/
def recoverEnlargedMember (bound : HSet.{u}) (value : HSet.{max u v}) : HSet.{u} :=
  sUnion (HSet.sep (fun original => enlarge original = value) bound)

theorem recoverEnlargedMember_enlarge {bound value : HSet.{u}} (belongs : value ∈ bound) :
    recoverEnlargedMember bound (enlarge.{u,v} value) = value := by
  have separated : HSet.sep (fun original => enlarge.{u,v} original = enlarge value) bound = {value} := by
    ext original
    rw [mem_sep, mem_singleton]
    exact ⟨fun row => enlarge_injective row.2,
      fun same => ⟨same ▸ belongs, congrArg enlarge same⟩⟩
  rw [recoverEnlargedMember, separated, sUnion_singleton]

theorem recoverEnlargedMember_mem {bound : HSet.{u}} {value : HSet.{max u v}}
    (belongs : value ∈ enlarge bound) : recoverEnlargedMember bound value ∈ bound := by
  obtain ⟨original, member, same⟩ := mem_enlarge_iff.mp belongs
  rw [← same, recoverEnlargedMember_enlarge member]
  exact member

theorem enlarge_recoverEnlargedMember {bound : HSet.{u}} {value : HSet.{max u v}}
    (belongs : value ∈ enlarge bound) : enlarge (recoverEnlargedMember bound value) = value := by
  obtain ⟨original, member, same⟩ := mem_enlarge_iff.mp belongs
  rw [← same, recoverEnlargedMember_enlarge member]

def enlargedMembersEquiv (bound : HSet.{u}) :
    {value : HSet.{u} // value ∈ bound} ≃ {value : HSet.{max u v} // value ∈ enlarge bound} where
  toFun value := ⟨enlarge value.val, enlarge_mem_enlarge_iff.mpr value.property⟩
  invFun value := ⟨recoverEnlargedMember bound value.val, recoverEnlargedMember_mem value.property⟩
  left_inv value := Subtype.ext (recoverEnlargedMember_enlarge.{u,v} value.property)
  right_inv value := Subtype.ext (enlarge_recoverEnlargedMember.{u,v} value.property)

theorem enlargedMembersEquiv_value (bound : HSet.{u}) (value : {value : HSet.{u} // value ∈ bound}) :
    (enlargedMembersEquiv.{u,v} bound value).val = enlarge value.val := rfl

theorem enlargedMembersEquiv_comp_value (bound : HSet.{u}) (value : {value : HSet.{u} // value ∈ bound}) :
    (enlargedMembersEquiv.{max u v,w} (enlarge.{u,v} bound)
      (enlargedMembersEquiv.{u,v} bound value)).val =
        (enlargedMembersEquiv.{u,max v w} bound value).val := enlarge_comp value.val

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
