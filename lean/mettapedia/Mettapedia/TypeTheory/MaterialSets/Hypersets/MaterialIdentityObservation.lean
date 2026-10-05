import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentationIdentityComparison
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Material observation of dependent identity transport

Presentation isomorphisms act on actual occurrences. Their material readout
lands in the discrete category of hypersets: the value equality records no
nontrivial action of an identity witness. Actual material member families
factor through this readout, and coherent dependent J commutes with it.

A general obstruction applies even to descent up to natural isomorphism:
a family descending through a discrete observation must have trivial action
on every loop. The two-occurrence symmetry violates that condition. This is
a comparison between constructed identity models, not an adoption of native
equality reflection or a construction of a complete groupoid CwF.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialIdentityObservation

open CategoryTheory AccessiblePointedGraph
open Mettapedia.TypeTheory.GroupoidIdentityElimination

universe u v w z

/-- The actual extensional value observation of presentation identities. -/
def readout : AccessiblePointedGraph.{u} ⥤ Discrete HSet.{u} where
  obj graph := Discrete.mk (HSet.mk graph)
  map path := Discrete.eqToHom path.material_eq
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Every discrete-observed loop has the same observed witness as reflexivity. -/
theorem readout_loop {graph : AccessiblePointedGraph.{u}}
    (loop : PresentationIso graph graph) : readout.map loop = 𝟙 (readout.obj graph) :=
  Subsingleton.elim _ _

/-- An actual material member, including its membership evidence. -/
abbrev Members (value : HSet.{u}) := {member : HSet.{u} // member ∈ value}

/-- The material member family has genuine, nonconstant fibres. Its arrows
transport membership evidence along the observed equality. -/
def members : Discrete HSet.{u} ⥤ Type (u + 1) where
  obj value := Members value.as
  map arrow := TypeCat.ofHom (fun member =>
    ⟨member.val, (Discrete.eq_of_hom arrow) ▸ member.property⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro member
    apply Subtype.ext
    rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro member
    apply Subtype.ext
    rfl

theorem members_map_value {first second : Discrete HSet.{u}}
    (arrow : first ⟶ second) (member : members.obj first) :
    (members.map arrow member).val = member.val := rfl

def presentationMembers : AccessiblePointedGraph.{u} ⥤ Type (u + 1) :=
  compose readout members

/-- The occurrence family at the material member carrier's explicit bound.
The lift changes the host type's size, retaining every occurrence and action. -/
def liftedOccurrences : AccessiblePointedGraph.{u} ⥤ Type (u + 1) where
  obj graph := ULift.{u + 1} (Occurrence graph)
  map path := TypeCat.ofHom (fun occurrence => ⟨path.occurrenceTransport occurrence.down⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply ULift.ext
    apply Subtype.ext
    rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply ULift.ext
    apply Subtype.ext
    rfl

/-- Occurrences have a natural material membership reading, without selecting
an occurrence to represent a member. -/
def occurrenceMember (graph : AccessiblePointedGraph.{u}) (occurrence : Occurrence graph) :
    Members (HSet.mk graph) :=
  ⟨occurrence.picture, by
    rw [← picture_eq_mk]
    exact mem_picture_iff_occurrence.mpr ⟨occurrence, rfl⟩⟩

def occurrenceReading : NatTrans liftedOccurrences presentationMembers where
  app graph := TypeCat.ofHom (fun occurrence : ULift.{u + 1} (Occurrence graph) =>
    occurrenceMember graph occurrence.down)
  naturality _ _ path := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply Subtype.ext
    exact path.occurrence_picture occurrence.down

/-- All material members have occurrence witnesses propositionally. This is
surjectivity of the readout, not a chosen inverse function. -/
theorem occurrenceReading_surjective (graph : AccessiblePointedGraph.{u}) :
    Function.Surjective (occurrenceReading.app graph) := by
  intro member
  have belongs : member.val ∈ graph.picture := picture_eq_mk graph ▸ member.property
  obtain ⟨occurrence, same⟩ := mem_picture_iff_occurrence.mp belongs
  exact ⟨⟨occurrence⟩, Subtype.ext same⟩

/-- Naturality and the inverse comparison force every erased loop to act
trivially, even when descent is requested only up to natural isomorphism. -/
structure NaturalEquivalence {C : Type v} [Category.{w} C]
    (first second : C ⥤ Type u) where
  fibre : (point : C) → first.obj point ≃ second.obj point
  natural : ∀ {source target : C} (arrow : source ⟶ target) (element : first.obj source),
    fibre target (first.map arrow element) = second.map arrow (fibre source element)

namespace NaturalEquivalence

variable {C : Type v} [Category.{w} C] {first second : C ⥤ Type u}

def forward (comparison : NaturalEquivalence first second) : NatTrans first second where
  app point := TypeCat.ofHom (comparison.fibre point)
  naturality _ _ arrow := by
    apply ConcreteCategory.hom_ext
    exact comparison.natural arrow

/-- Inverse naturality follows from the recorded forward naturality and
the actual fibre inverse, without choosing an inverse from an IsIso proof. -/
def backward (comparison : NaturalEquivalence first second) : NatTrans second first where
  app point := TypeCat.ofHom (comparison.fibre point).symm
  naturality source target arrow := by
    apply ConcreteCategory.hom_ext
    intro element
    apply (comparison.fibre target).injective
    change comparison.fibre target ((comparison.fibre target).symm (second.map arrow element)) =
      comparison.fibre target (first.map arrow ((comparison.fibre source).symm element))
    rw [Equiv.apply_symm_apply, comparison.natural, Equiv.apply_symm_apply]

theorem backward_forward (comparison : NaturalEquivalence first second)
    (point : C) (element : first.obj point) :
    comparison.backward.app point (comparison.forward.app point element) = element :=
  (comparison.fibre point).symm_apply_apply element

theorem forward_backward (comparison : NaturalEquivalence first second)
    (point : C) (element : second.obj point) :
    comparison.forward.app point (comparison.backward.app point element) = element :=
  (comparison.fibre point).apply_symm_apply element

end NaturalEquivalence

theorem loop_action_trivial_of_discrete_descent {C : Type v} [Category.{w} C]
    {D : Type z} (observe : C ⥤ Discrete D)
    (family : C ⥤ Type u) (observedFamily : Discrete D ⥤ Type u)
    (comparison : NaturalEquivalence family (compose observe observedFamily))
    {point : C} (loop : point ⟶ point) (element : family.obj point) :
    family.map loop element = element := by
  have erased : observe.map loop = 𝟙 (observe.obj point) := Subsingleton.elim _ _
  apply (comparison.fibre point).injective
  have naturality := comparison.natural loop element
  change comparison.fibre point (family.map loop element) =
    observedFamily.map (observe.map loop) (comparison.fibre point element) at naturality
  rw [erased, observedFamily.map_id_apply] at naturality
  exact naturality

/-- Dependent J on every coherent observed motive commutes with the actual
material observation, including its reflexivity-boundary comparison. -/
theorem J_readout (motive : Arrow (Discrete HSet.{u}) ⥤ Type v)
    (atReflexivity : NaturalSection (compose diagonal motive)) :
    J (compose readout.mapArrow motive)
        (reindexReflexivity readout motive atReflexivity) =
      (J motive atReflexivity).reindex readout.mapArrow :=
  J_sub_section readout motive atReflexivity

/-- The material member motive observes the right endpoint, with actual
membership fibres and equality transport. -/
def memberMotive : Arrow (Discrete HSet.{u}) ⥤ Type (u + 1) where
  obj witness := members.obj witness.right
  map square := members.map square.right
  map_id witness := by exact members.map_id witness.right
  map_comp first second := by exact members.map_comp first.right second.right

theorem basedJ_member_value {origin endpoint : Discrete HSet.{u}}
    (member : Members origin.as) (witness : origin ⟶ endpoint) :
    (basedJ memberMotive member witness).val = member.val := rfl

namespace Controls

open PresentationIdentityControls

theorem members_nonconstant :
    IsEmpty (members.obj (Discrete.mk (∅ : HSet.{u}))) ∧
      Nonempty (members.obj (Discrete.mk ({∅} : HSet.{u}))) :=
  ⟨⟨fun member => HSet.notMem_empty member.val member.property⟩,
    ⟨⟨∅, HSet.mem_singleton_self ∅⟩⟩⟩

theorem occurrenceReading_not_injective :
    ¬ Function.Injective (occurrenceReading.app twoChildren.{u}) := by
  intro injective
  have same : occurrenceReading.app twoChildren ⟨twoChildrenOccurrence true⟩ =
      occurrenceReading.app twoChildren ⟨twoChildrenOccurrence false⟩ :=
    Subtype.ext ((twoChildrenOccurrence_picture true).trans
      (twoChildrenOccurrence_picture false).symm)
  exact twoChildrenOccurrence_ne (congrArg ULift.down (injective same))

/-- Forgetting the symmetry cannot reproduce its dependent occurrence
transport, even by changing to naturally isomorphic fibres. -/
theorem occurrences_no_material_descent :
    ¬ ∃ family : Discrete HSet.{u} ⥤ Type u,
      Nonempty (NaturalEquivalence presentationOccurrences (compose readout family)) := by
  rintro ⟨family, ⟨comparison⟩⟩
  have trivial := loop_action_trivial_of_discrete_descent readout
    presentationOccurrences family comparison swapOccurrences (twoChildrenOccurrence true)
  exact twoChildrenOccurrence_ne (swap_true_occurrence.symm.trans trivial).symm

theorem identity_witness_erased_but_transport_retained :
    readout.map swapOccurrences.{u} = readout.map (PresentationIso.refl twoChildren) ∧
      basedJ occurrenceMotive (twoChildrenOccurrence true) swapOccurrences ≠
        basedJ occurrenceMotive (twoChildrenOccurrence true) (PresentationIso.refl twoChildren) := by
  constructor
  · exact Subsingleton.elim _ _
  · rw [basedJ_swaps_occurrence, basedJ_reflexivity_preserves_occurrence]
    exact twoChildrenOccurrence_ne.symm

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialIdentityObservation
