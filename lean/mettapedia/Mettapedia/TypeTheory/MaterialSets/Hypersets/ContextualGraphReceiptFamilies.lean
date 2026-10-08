import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverse

/-!
# Literal member families in the varying contextual graph universe

The fibre over a rooted graph value retains its actual small child
occurrences. Transport acts on those occurrences through the graph's node
functor. This gives an authored native family on the entire varying,
one-level-wider universe, with a natural child-value observation and a
constructed code in the universe of complete small future families.

Literal receipts and future matching evidence have distinct roles.
Reading a literal receipt yields material membership evidence; this does
not assert that arbitrary dependent consumers descend through matching.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies

open CategoryTheory ContextualWitnessCover ContextualGraphDiagrams
open ContextualSmallFamilyUniverse

universe u v
variable (D : Type u) [Category.{u} D]

theorem child_heq {point : D} {first second : Value D point}
    (same : first = second) (left : Child D first) (right : Child D second)
    (nodes : HEq left.val right.val) : HEq left right := by
  cases same
  exact heq_of_eq (Subtype.ext (eq_of_heq nodes))

theorem moveChild_id_heq (point : D) (parent : Value D point) (child : Child D parent) :
    HEq (moveChild D (𝟙 point) parent child) child := by
  apply child_heq D (move_identity D point parent)
  change HEq (parent.1.nodes.map (𝟙 point) child.val) child.val
  exact heq_of_eq (parent.1.nodes.map_id_apply point child.val)

theorem moveChild_comp_heq {first middle last : D} (earlier : first ⟶ middle)
    (later : middle ⟶ last) (parent : Value D first) (child : Child D parent) :
    HEq (moveChild D (earlier ≫ later) parent child)
      (moveChild D later (move D earlier parent) (moveChild D earlier parent child)) := by
  apply child_heq D (move_composition D earlier later parent)
  change HEq (parent.1.nodes.map (earlier ≫ later) child.val)
    (parent.1.nodes.map later (parent.1.nodes.map earlier child.val))
  exact heq_of_eq (parent.1.nodes.map_comp_apply earlier later child.val)

theorem moveChild_heq {first second : D} (arrival : first ⟶ second)
    {parent other : Value D first} (same : parent = other)
    (child : Child D parent) (otherChild : Child D other)
    (receipts : HEq child otherChild) :
    HEq (moveChild D arrival parent child) (moveChild D arrival other otherChild) := by
  cases same
  cases eq_of_heq receipts
  rfl

/-- The literal child family has original-small fibres over the actual
one-level-wider universe of varying graph values. -/
def family : (values D).Elements ⥤ Type u where
  obj point := Child D point.2
  map {first second} step := TypeCat.ofHom fun child =>
    cast (congrArg (Child D) step.2) (moveChild D step.1 first.2 child)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro child
    apply eq_of_heq
    exact (ContextualSmallFamilyUniverse.cast_heq _ _).trans (moveChild_id_heq D point.1 point.2 child)
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro child
    apply eq_of_heq
    have earlierChild : HEq
        (cast (congrArg (Child D) earlier.2) (moveChild D earlier.1 first.2 child))
        (moveChild D earlier.1 first.2 child) := ContextualSmallFamilyUniverse.cast_heq _ _
    exact (ContextualSmallFamilyUniverse.cast_heq _ _).trans ((moveChild_comp_heq D earlier.1 later.1 first.2 child).trans
      ((moveChild_heq D later.1 earlier.2.symm _ _ earlierChild).symm.trans
        (ContextualSmallFamilyUniverse.cast_heq _ _).symm))

theorem family_map_heq {first second : (values D).Elements} (step : first ⟶ second)
    (child : Child D first.2) :
    HEq ((family D).map step child) (moveChild D step.1 first.2 child) :=
  ContextualSmallFamilyUniverse.cast_heq _ _

theorem childValue_cast {point : D} {first second : Value D point}
    (same : first = second) (child : Child D first) :
    childValue D second (cast (congrArg (Child D) same) child) =
      childValue D first child := by
  cases same
  rfl

theorem childValue_map {first second : (values D).Elements} (step : first ⟶ second)
    (child : Child D first.2) :
    childValue D second.2 ((family D).map step child) =
      move D step.1 (childValue D first.2 child) :=
  childValue_cast D step.2 (moveChild D step.1 first.2 child)

/-- Comprehension retains the parent and its literal child occurrence.
This second projection reads the child as a value in the same universe. -/
def childReading : NaturalHom (total (family D)) (values D) where
  app _ receipt := childValue D receipt.1 receipt.2
  naturality {first second} arrival receipt :=
    (childValue_map D (CategoryOfElements.homMk (F := values D)
      ⟨first, receipt.1⟩ ⟨second, move D arrival receipt.1⟩ arrival rfl) receipt.2).symm

def parentReading : NaturalHom (total (family D)) (values D) := projection (family D)

def membership (point : D) (receipt : (total (family D)).obj point) :
    ContextualRealizedGraphs.Member
      ((childReading D).app point receipt) ((parentReading D).app point receipt) :=
  ContextualRealizedGraphs.Member.atChild receipt.1 receipt.2

def classifier : NaturalHom (values D) (universeFamily (D := D)) :=
  ContextualSmallFamilyUniverse.classifier (family D)

/-- The generated decoder recovers both fibres and the complete context
action, without selecting representatives from material equality. -/
theorem decoded_classifier : decodedFamily (classifier D) = family D :=
  decoded_classifier_eq (family D)

variable {D}

def along {base : D ⥤ Type v} (parent : NaturalHom base (values D)) :
    base.Elements ⥤ Type u := restrict (elementMap parent) (family D)

/-- A whole literal selection is a natural map to actual comprehension,
whose first projection is the specified parent family. -/
abbrev Selection {base : D ⥤ Type v} (parent : NaturalHom base (values D)) :=
  {selection : NaturalHom base (total (family D)) //
    ∀ point value, (selection.app point value).1 = parent.app point value}

def selectionOfSection {base : D ⥤ Type v} (parent : NaturalHom base (values D))
    (term : (along parent).sections) : Selection parent :=
  ⟨{
    app point value := ⟨parent.app point value, term.val ⟨point, value⟩⟩
    naturality := by
      intro first second arrival value
      apply Sigma.ext (parent.naturality arrival value)
      let step := CategoryOfElements.homMk (F := base)
        ⟨first, value⟩ ⟨second, base.map arrival value⟩ arrival rfl
      let rawStep := CategoryOfElements.homMk (F := values D)
        ⟨first, parent.app first value⟩
        ⟨second, move D arrival (parent.app first value)⟩ arrival rfl
      exact (family_map_heq D rawStep (term.val ⟨first, value⟩)).trans
        ((family_map_heq D ((elementMap parent).map step) (term.val ⟨first, value⟩)).symm.trans
          (heq_of_eq (term.property step))) },
    fun _ _ => rfl⟩

def sectionOfSelection {base : D ⥤ Type v} (parent : NaturalHom base (values D))
    (selection : Selection parent) : (along parent).sections :=
  ⟨fun point => cast (congrArg (Child D) (selection.property point.1 point.2))
      (selection.val.app point.1 point.2).2, by
    intro first second step
    apply eq_of_heq
    have sameTotal := selection.val.naturality step.1 first.2
    have sameTarget := congrArg (selection.val.app second.1) step.2
    have receipts := (Sigma.mk.inj_iff.mp (sameTotal.trans sameTarget)).2
    let rawStep := CategoryOfElements.homMk (F := values D)
      ⟨first.1, (selection.val.app first.1 first.2).1⟩
      ⟨second.1, move D step.1 (selection.val.app first.1 first.2).1⟩ step.1 rfl
    exact (family_map_heq D ((elementMap parent).map step) _).trans
      ((moveChild_heq D step.1 (selection.property first.1 first.2).symm _ _
        (ContextualSmallFamilyUniverse.cast_heq _ _)).trans
          ((family_map_heq D rawStep _).symm.trans
            (receipts.trans (ContextualSmallFamilyUniverse.cast_heq _ _).symm)))⟩

theorem section_selection {base : D ⥤ Type v} (parent : NaturalHom base (values D))
    (term : (along parent).sections) :
    sectionOfSelection parent (selectionOfSection parent term) = term := by
  apply Subtype.ext
  rfl

theorem selection_section {base : D ⥤ Type v} (parent : NaturalHom base (values D))
    (selection : Selection parent) :
    selectionOfSection parent (sectionOfSelection parent selection) = selection := by
  apply Subtype.ext
  apply NaturalHom.ext
  intro point value
  apply Sigma.ext (selection.property point value).symm
  exact ContextualSmallFamilyUniverse.cast_heq _ _

/-- Both inverse laws compare complete natural selections and sections. -/
def wholeSectionEquiv {base : D ⥤ Type v} (parent : NaturalHom base (values D)) :
    (along parent).sections ≃ Selection parent where
  toFun := selectionOfSection parent
  invFun := sectionOfSelection parent
  left_inv := section_selection parent
  right_inv := selection_section parent

/-- A compatible literal section yields a natural child value, not merely
an unrelated family of current observations. -/
def sectionReading {base : D ⥤ Type v} (parent : NaturalHom base (values D))
    (term : (along parent).sections) : NaturalHom base (values D) where
  app point value := childValue D (parent.app point value) (term.val ⟨point, value⟩)
  naturality {first second} arrival value := by
    let step := CategoryOfElements.homMk (F := base)
      ⟨first, value⟩ ⟨second, base.map arrival value⟩ arrival rfl
    exact (childValue_map D ((elementMap parent).map step) (term.val ⟨first, value⟩)).symm.trans
      (congrArg (childValue D (parent.app second (base.map arrival value))) (term.property step))

def sectionMembership {base : D ⥤ Type v} (parent : NaturalHom base (values D))
    (term : (along parent).sections) (point : D) (value : base.obj point) :
    ContextualRealizedGraphs.Member ((sectionReading parent term).app point value)
      (parent.app point value) :=
  ContextualRealizedGraphs.Member.atChild _ (term.val ⟨point, value⟩)

theorem sectionReading_selection {base : D ⥤ Type v}
    (parent : NaturalHom base (values D)) (term : (along parent).sections) :
    sectionReading parent term = (selectionOfSection parent term).val.comp (childReading D) := by
  apply NaturalHom.ext
  intro point value
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies
