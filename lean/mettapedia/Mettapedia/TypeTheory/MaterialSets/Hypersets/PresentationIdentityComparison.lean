import Mettapedia.TypeTheory.MaterialSets.Hypersets.Presentations
import Mettapedia.TypeTheory.GroupoidIdentityElimination

/-!
# Presentation identity and material extensional equality

Pointed graph isomorphisms retain actual node and occurrence transport. They
form a groupoid with a constructed inverse. Its node and occurrence families
are genuine functors; dependent identity elimination for coherent motives
therefore applies to these witnesses without reducing them to propositions.

Every isomorphism preserves the pictured hyperset. The converse fails: two
and one occurrences can picture the same set. Parallel isomorphisms can also
act differently on occurrences while preserving every material value. Thus
this comparison neither supplies equality reflection nor identifies parallel
witnesses. It is a presentation identity profile, distinct from bisimilarity
and from a completed interpretation of native type-theory syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open CategoryTheory
open AccessiblePointedGraph
open Mettapedia.TypeTheory.GroupoidIdentityElimination

universe u

/-- Actual pointed graph isomorphisms, including occurrence transport. -/
structure PresentationIso (G H : AccessiblePointedGraph.{u}) where
  nodes : G.Node ≃ H.Node
  edge_iff : ∀ source target, G.edge source target ↔ H.edge (nodes source) (nodes target)
  point : nodes G.point = H.point

namespace PresentationIso

variable {G H K : AccessiblePointedGraph.{u}}

@[ext] theorem ext {first second : PresentationIso G H} (nodes : first.nodes = second.nodes) :
    first = second := by
  cases first
  cases second
  cases nodes
  rfl

def refl (G : AccessiblePointedGraph.{u}) : PresentationIso G G where
  nodes := Equiv.refl G.Node
  edge_iff _ _ := Iff.rfl
  point := rfl

def trans (first : PresentationIso G H) (second : PresentationIso H K) : PresentationIso G K where
  nodes := first.nodes.trans second.nodes
  edge_iff source target := (first.edge_iff source target).trans
    (second.edge_iff (first.nodes source) (first.nodes target))
  point := (congrArg second.nodes first.point).trans second.point

def symm (path : PresentationIso G H) : PresentationIso H G where
  nodes := path.nodes.symm
  edge_iff source target := by
    simpa only [Equiv.apply_symm_apply] using
      (path.edge_iff (path.nodes.symm source) (path.nodes.symm target)).symm
  point := (congrArg path.nodes.symm path.point.symm).trans (path.nodes.symm_apply_apply G.point)

@[simp] theorem refl_trans (path : PresentationIso G H) : (refl G).trans path = path := by
  apply ext
  apply Equiv.ext
  intro node
  rfl

@[simp] theorem trans_refl (path : PresentationIso G H) : path.trans (refl H) = path := by
  apply ext
  apply Equiv.ext
  intro node
  rfl

theorem trans_assoc {L : AccessiblePointedGraph.{u}} (first : PresentationIso G H)
    (second : PresentationIso H K) (third : PresentationIso K L) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  apply ext
  apply Equiv.ext
  intro node
  rfl

@[simp] theorem symm_trans (path : PresentationIso G H) : path.symm.trans path = refl H := by
  apply ext
  apply Equiv.ext
  exact path.nodes.apply_symm_apply

@[simp] theorem trans_symm (path : PresentationIso G H) : path.trans path.symm = refl G := by
  apply ext
  apply Equiv.ext
  exact path.nodes.symm_apply_apply

/-- The isomorphism supplies a genuine bounded morphism, with explicit
edge lifts through its inverse node map. -/
def toHom (path : PresentationIso G H) : AccessiblePointedGraph.Hom G H where
  toFun := path.nodes
  map_point := path.point
  isBoundedMorphism := {
    map := fun {_ _} edge => (path.edge_iff _ _).mp edge
    lift := fun {source target} edge =>
      ⟨path.nodes.symm target,
        (path.edge_iff source _).mpr (by simpa only [Equiv.apply_symm_apply] using edge),
        path.nodes.apply_symm_apply target⟩ }

/-- Material equality is a proved observation of an isomorphism witness. -/
theorem picture_eq (path : PresentationIso G H) : G.picture = H.picture :=
  path.toHom.picture_eq.symm

theorem material_eq (path : PresentationIso G H) : HSet.mk G = HSet.mk H :=
  HSet.sound path.toHom.equiv

def occurrenceTransport (path : PresentationIso G H) : Occurrence G ≃ Occurrence H where
  toFun := path.toHom.mapOccurrence
  invFun := path.symm.toHom.mapOccurrence
  left_inv occurrence := Subtype.ext (path.nodes.symm_apply_apply occurrence.val)
  right_inv occurrence := Subtype.ext (path.nodes.apply_symm_apply occurrence.val)

theorem occurrence_picture (path : PresentationIso G H) (occurrence : Occurrence G) :
    (path.occurrenceTransport occurrence).picture = occurrence.picture :=
  path.toHom.picture_mapOccurrence occurrence

end PresentationIso

/-- The inverse includes the actual inverse node map. -/
instance presentationGroupoid : Groupoid.{u} AccessiblePointedGraph.{u} where
  Hom := PresentationIso
  id := PresentationIso.refl
  comp := PresentationIso.trans
  id_comp := PresentationIso.refl_trans
  comp_id := PresentationIso.trans_refl
  assoc := PresentationIso.trans_assoc
  inv := PresentationIso.symm
  inv_comp := PresentationIso.symm_trans
  comp_inv := PresentationIso.trans_symm

/-- Node fibres vary with the entire presentation. -/
def presentationNodes : AccessiblePointedGraph.{u} ⥤ Type u where
  obj graph := graph.Node
  map path := ↾path.nodes
  map_id graph := by rfl
  map_comp first second := by rfl

/-- Occurrence fibres retain their actual transport, independently of the
proposition-valued material membership observation. -/
def presentationOccurrences : AccessiblePointedGraph.{u} ⥤ Type u where
  obj graph := Occurrence graph
  map path := ↾path.occurrenceTransport
  map_id graph := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply Subtype.ext
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply Subtype.ext
    rfl

/-- Point selection is a natural dependent section of the node family. -/
def pointSection : NaturalSection presentationNodes where
  value graph := graph.point
  natural path := path.point

/-- The motive retains endpoint occurrence types and the witness's actual
commuting-square transport. It is not a constant family of host types. -/
def occurrenceMotive : Arrow AccessiblePointedGraph.{u} ⥤ Type u where
  obj witness := Occurrence witness.right
  map square := ↾square.right.occurrenceTransport
  map_id witness := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply Subtype.ext
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply Subtype.ext
    rfl

/-! ## Explicit presentation symmetries -/

namespace PresentationIdentityControls

def constantSupNodes {I J : Type u} (graph : AccessiblePointedGraph.{u}) (indices : I ≃ J) :
    (sup (fun _ : I => graph)).Node ≃ (sup (fun _ : J => graph)).Node where
  toFun
    | none => none
    | some ⟨index, node⟩ => some ⟨indices index, node⟩
  invFun
    | none => none
    | some ⟨index, node⟩ => some ⟨indices.symm index, node⟩
  left_inv node := by
    cases node with
    | none => rfl
    | some pair =>
        rcases pair with ⟨index, node⟩
        change (some ⟨indices.symm (indices index), node⟩ : Option (Σ _ : I, graph.Node)) =
          some ⟨index, node⟩
        rw [Equiv.symm_apply_apply]
  right_inv node := by
    cases node with
    | none => rfl
    | some pair =>
        rcases pair with ⟨index, node⟩
        change (some ⟨indices (indices.symm index), node⟩ : Option (Σ _ : J, graph.Node)) =
          some ⟨index, node⟩
        rw [Equiv.apply_symm_apply]

private theorem constantSupEdges {I J : Type u} (graph : AccessiblePointedGraph.{u})
    (indices : I ≃ J) {source target : (sup (fun _ : I => graph)).Node}
    (edge : (sup (fun _ : I => graph)).edge source target) :
    (sup (fun _ : J => graph)).edge
      (constantSupNodes graph indices source) (constantSupNodes graph indices target) := by
  cases edge with
  | point index => exact SupEdge.point (indices index)
  | edge index available => exact SupEdge.edge (indices index) available

def constantSupIso {I J : Type u} (graph : AccessiblePointedGraph.{u}) (indices : I ≃ J) :
    PresentationIso (sup (fun _ : I => graph)) (sup (fun _ : J => graph)) where
  nodes := constantSupNodes graph indices
  point := rfl
  edge_iff source target := by
    constructor
    · exact constantSupEdges graph indices
    · intro edge
      have mapped := constantSupEdges graph indices.symm edge
      have inverse : constantSupNodes graph indices.symm = (constantSupNodes graph indices).symm := rfl
      simpa only [inverse, Equiv.symm_apply_apply] using mapped

def flipBool : ULift.{u, 0} Bool ≃ ULift.{u, 0} Bool where
  toFun b := ⟨!b.down⟩
  invFun b := ⟨!b.down⟩
  left_inv b := by cases b; simp
  right_inv b := by cases b; simp

/-- A nonidentity automorphism exchanging two actual occurrences. -/
def swapOccurrences : PresentationIso twoChildren.{u} twoChildren.{u} :=
  constantSupIso empty flipBool

theorem swap_true_occurrence :
    swapOccurrences.occurrenceTransport (twoChildrenOccurrence true) =
      twoChildrenOccurrence false := rfl

theorem swap_not_reflexivity : swapOccurrences.{u} ≠ PresentationIso.refl twoChildren := by
  intro same
  have applied := congrArg (fun path : PresentationIso twoChildren.{u} twoChildren =>
    path.occurrenceTransport (twoChildrenOccurrence true)) same
  exact twoChildrenOccurrence_ne applied.symm

/-- Identity witnesses at fixed endpoints are not globally proof-irrelevant. -/
theorem not_parallelWitness_UIP :
    ¬ ∀ G H : AccessiblePointedGraph.{u}, Subsingleton (PresentationIso G H) := by
  intro uip
  exact swap_not_reflexivity ((uip twoChildren twoChildren).allEq _ _)

theorem witness_transport_distinguishes :
    swapOccurrences.occurrenceTransport (twoChildrenOccurrence true) ≠
      (PresentationIso.refl twoChildren).occurrenceTransport (twoChildrenOccurrence true) := by
  exact twoChildrenOccurrence_ne.symm

/-- Dependent based elimination computes the nontrivial witness transport. -/
theorem basedJ_swaps_occurrence :
    basedJ occurrenceMotive (twoChildrenOccurrence.{u} true) swapOccurrences =
      twoChildrenOccurrence false := rfl

theorem basedJ_reflexivity_preserves_occurrence :
    basedJ occurrenceMotive (twoChildrenOccurrence.{u} true) (PresentationIso.refl twoChildren) =
      twoChildrenOccurrence true := basedJ_beta _ _

/-- Coherent motives admit J, while unrestricted raw motives would erase
the exhibited parallel witnesses. No such operation exists at this origin. -/
theorem no_rawBasedElimination : ¬ Nonempty (RawBasedElimination twoChildren.{u}) := by
  rintro ⟨eliminate⟩
  exact swap_not_reflexivity (rawBasedElimination_loopUIP eliminate swapOccurrences)

/-- The occurrence motive genuinely varies: the two- and one-occurrence
identity contexts cannot even have equivalent fibre carriers. -/
theorem occurrenceMotive_nonconstant :
    ¬ Nonempty
      (occurrenceMotive.obj (Arrow.mk (PresentationIso.refl twoChildren.{u})) ≃
        occurrenceMotive.obj (Arrow.mk (PresentationIso.refl (oneChild empty.{u})))) := by
  change ¬ Nonempty (Occurrence twoChildren.{u} ≃ Occurrence (oneChild empty.{u}))
  rintro ⟨equivalence⟩
  exact twoChildrenOccurrence_ne
    (equivalence.injective (Subsingleton.elim _ _))

/-- The same material member is returned by both transports. -/
theorem material_reading_agrees :
    (swapOccurrences.occurrenceTransport (twoChildrenOccurrence true)).picture =
      ((PresentationIso.refl twoChildren).occurrenceTransport (twoChildrenOccurrence true)).picture :=
  (PresentationIso.occurrence_picture _ _).trans (PresentationIso.occurrence_picture _ _).symm

/-- Equal pictures do not supply even one presentation isomorphism. -/
theorem no_two_to_one_identity :
    ¬ Nonempty (PresentationIso twoChildren.{u} (oneChild empty)) := by
  rintro ⟨path⟩
  have collapsed : path.occurrenceTransport (twoChildrenOccurrence true) =
      path.occurrenceTransport (twoChildrenOccurrence false) := Subsingleton.elim _ _
  exact twoChildrenOccurrence_ne (path.occurrenceTransport.injective collapsed)

theorem material_equality_without_presentationIdentity :
    HSet.mk twoChildren.{u} = HSet.mk (oneChild empty) ∧
      ¬ Nonempty (PresentationIso twoChildren (oneChild empty)) :=
  ⟨by rw [← picture_eq_mk, ← picture_eq_mk, picture_twoChildren, picture_oneChild_empty],
    no_two_to_one_identity⟩

end PresentationIdentityControls

#print axioms presentationGroupoid
#print axioms presentationOccurrences
#print axioms PresentationIso.occurrenceTransport
#print axioms PresentationIdentityControls.not_parallelWitness_UIP
#print axioms PresentationIdentityControls.material_equality_without_presentationIdentity
#print axioms PresentationIdentityControls.basedJ_swaps_occurrence
#print axioms PresentationIdentityControls.no_rawBasedElimination

end Mettapedia.TypeTheory.MaterialSets.Hypersets
