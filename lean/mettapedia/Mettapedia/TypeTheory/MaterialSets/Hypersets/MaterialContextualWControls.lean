import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWTypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualMaterialization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafIdentityWitness

/-!
# Material contextual W controls with parallel future arrows

The shape carrier has two actual material members, empty and singleton empty.
The former is terminal and the latter has one position at every future arrow.
Worlds and histories use the existing infinite category of labelled paths.
Actual leaf and branch trees are encoded with all future addresses retained.
A raw tree whose branch shape changes when an arrow is extended is excluded
by hereditary contextual naturality despite having natural children.

No host Boolean decoder is inferred from the material shape carrier. The two
control shapes are authored particular members of its actual graph.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWControls

open CategoryTheory
open AccessiblePointedGraph
open LabelledContextPaths
open ContextualWTypes (RawTree NaturalTree Position)
open PowerClassFamilyDescent.Controls

def selectedShape (tag : Bool) : PowerMemberClass alternatives :=
  (powerMemberEquiv alternatives).symm ⟨HSet.mk (selectedGraph tag), by
    rw [picture_eq_mk]
    exact HSet.mem_range.mpr ⟨⟨tag⟩, rfl⟩⟩

abbrev shapeModel := PowerClassContextualMaterialization.powerClassModel alternatives

theorem selectedShape_value (tag : Bool) : shapeModel.value (selectedShape tag) = HSet.mk (selectedGraph tag) :=
  congrArg Subtype.val ((powerMemberEquiv alternatives).apply_symm_apply _)

theorem terminal_branch_shapes_distinct : selectedShape false ≠ selectedShape true := by
  intro same
  have values := (selectedShape_value false).symm.trans
    ((congrArg shapeModel.value same).trans (selectedShape_value true))
  change HSet.mk empty = HSet.mk (oneChild empty) at values
  have singleton : HSet.mk (oneChild empty) = ({∅} : HSet) :=
    (picture_eq_mk _).symm.trans picture_oneChild_empty
  exact HSet.empty_ne_singleton_empty (HSet.mk_empty.symm.trans (values.trans singleton))

def shapes : World ⥤ Type where
  obj _ := PowerMemberClass alternatives
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def positions : shapes.Elements ⥤ Type where
  obj point := PresheafIdentityWitness.Witness point.2 (selectedShape true)
  map {first second} arrow := TypeCat.ofHom fun witness =>
    PresheafIdentityWitness.encode (arrow.property.symm.trans (PresheafIdentityWitness.decode witness))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro witness
    apply (PresheafIdentityWitness.witnessEquiv point.2 (selectedShape true)).injective
    exact Subsingleton.elim _ _
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro witness
    apply (PresheafIdentityWitness.witnessEquiv last.2 (selectedShape true)).injective
    exact Subsingleton.elim _ _

def shapeModels (_world : World) : PresentedType (shapes.obj _world) := shapeModel
def positionModels (point : shapes.Elements) : PresentedType (positions.obj point) :=
  PowerClassContextualMaterialization.powerClassModel (PresheafIdentityWitness.graph point.2 (selectedShape true))

def leafRaw (X : World) : RawTree shapes positions X :=
  .sup (selectedShape false) (fun _ _ branch =>
    False.elim (terminal_branch_shapes_distinct (PresheafIdentityWitness.decode branch)))

theorem leaf_restrict {X Y : World} (arrow : X ⟶ Y) :
    ContextualWTypes.restrict shapes positions arrow (leafRaw X) = leafRaw Y := by
  apply RawTree.sup_eq_of_cast rfl
  intro Z later branch
  exact False.elim (terminal_branch_shapes_distinct (PresheafIdentityWitness.decode branch))

theorem leaf_natural (X : World) : ContextualWTypes.Natural shapes positions (leafRaw X) := by
  constructor
  · intro Y arrow branch
    exact False.elim (terminal_branch_shapes_distinct (PresheafIdentityWitness.decode branch))
  · intro Y Z first later branch
    exact False.elim (terminal_branch_shapes_distinct (PresheafIdentityWitness.decode branch))

def leaf (X : World) : NaturalTree shapes positions X := ⟨leafRaw X, leaf_natural X⟩

def node (X : World) : NaturalTree shapes positions X :=
  ContextualWTypes.sup shapes positions (selectedShape true) (fun Y _ _ => leaf Y)
    (fun _Y _Z _first later _branch => leaf_restrict later)

abbrev model (X : World) :=
  MaterialContextualWTypes.naturalModel shapes positions worlds arrows shapeModels positionModels X

theorem leaf_node_values_distinct (X : World) : (model X).value (leaf X) ≠ (model X).value (node X) := by
  intro same
  have trees := congrArg Subtype.val ((model X).value_injective same)
  have roots := congrArg (fun tree : RawTree shapes positions X => match tree with | .sup label _ => label) trees
  exact terminal_branch_shapes_distinct roots

theorem actual_leaf_and_node_members (X : World) :
    (model X).value (leaf X) ∈ (model X).carrier ∧
      (model X).value (node X) ∈ (model X).carrier ∧
      (model X).value (leaf X) ≠ (model X).value (node X) :=
  ⟨(model X).value_mem _, (model X).value_mem _, leaf_node_values_distinct X⟩

def branchEntry (label : Nat) : HSet :=
  HSet.kpair (ContextualWLabels.positionTag shapes positions worlds arrows shapeModels positionModels
      ⟨initial, selectedShape true⟩ ⟨next, extension label, PresheafIdentityWitness.encode rfl⟩)
    ((model next).value (leaf next))

theorem branchEntry_mem (label : Nat) : branchEntry label ∈ (model initial).value (node initial) :=
  MaterialContextualWTypes.natural_sup_branch_entry shapes positions worlds arrows shapeModels positionModels
    (selectedShape true) (fun Y _ _ => leaf Y)
    (fun _Y _Z _first later _branch => leaf_restrict later)
    (extension label) (PresheafIdentityWitness.encode rfl)

/-- Two branches with identical endpoints and child values are still distinct
actual material rows when their retained future arrows differ. -/
theorem parallel_branch_entries_distinct {first second : Nat} (different : first ≠ second) :
    branchEntry first ≠ branchEntry second := by
  intro same
  have tags := (HSet.kpair_inj.mp same).1
  have labels := (HSet.kpair_inj.mp (HSet.kpair_inj.mp tags).2).2
  have branches := (ContextualWLabels.branchCoding shapes positions worlds arrows positionModels (selectedShape true)).injective labels
  have arrows := congrArg (fun branch => branch.2.1.val) branches
  change [first] = [second] at arrows
  exact different (List.cons.inj arrows).1

/-- Every immediate child is natural, but the selected child at a composite
history disagrees with the later restriction of the selected child. -/
def badRaw : RawTree shapes positions initial :=
  .sup (selectedShape true) (fun Y arrow _ => if arrow.val = [1] then (node Y).val else (leaf Y).val)

theorem bad_children_natural :
    ∀ (Y : World) (arrow : initial ⟶ Y) (_branch : Position shapes positions (selectedShape true) arrow),
      ContextualWTypes.Natural shapes positions
        (if arrow.val = [1] then (node Y).val else (leaf Y).val) := by
  intro Y arrow _branch
  split
  · exact (node Y).property
  · exact (leaf Y).property

theorem badRaw_not_natural : ¬ ContextualWTypes.Natural shapes positions badRaw := by
  intro natural
  have law := natural.2 next two (extension 1) (laterExtension 2) (PresheafIdentityWitness.encode rfl)
  change ContextualWTypes.restrict shapes positions (laterExtension 2)
    (if [1] = [1] then (node next).val else (leaf next).val) =
      (if [1, 2] = [1] then (node two).val else (leaf two).val) at law
  have roots := congrArg (fun tree : RawTree shapes positions two => match tree with | .sup label _ => label) law
  exact terminal_branch_shapes_distinct roots.symm

theorem badRaw_excluded :
    MaterialContextualWTypes.encode shapes positions worlds arrows shapeModels positionModels badRaw ∉
      (model initial).carrier :=
  MaterialContextualWTypes.excluded_nonnatural shapes positions worlds arrows shapeModels positionModels badRaw badRaw_not_natural

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWControls
