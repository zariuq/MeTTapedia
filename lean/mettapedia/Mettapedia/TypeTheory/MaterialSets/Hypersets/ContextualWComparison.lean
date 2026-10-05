import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes

/-!+# Contextual polynomial branches and full dependent sections

The branch object of the constructed contextual W-type is equivalent to
the existing full dependent-section object over positions. The comparison
retains every future arrow and argument. Empty positions yield actual
leaves; an everywhere unary polynomial has no well-founded tree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWComparison

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open ContextualWTypes

universe u
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)

def branchTarget (target : D ⥤ Type u) : position.Elements ⥤ Type u :=
  overElements position (overElements shape target)

private theorem elementArrow_heq {X : shape.Elements} {Y : D}
    {first second : shape.obj Y} (same : first = second)
    (left : X ⟶ (⟨Y, first⟩ : shape.Elements)) (right : X ⟶ (⟨Y, second⟩ : shape.Elements))
    (arrows : left.1 = right.1) : HEq left right := by
  cases same
  exact heq_of_eq (Subtype.ext arrows)

private theorem sectionApp_heq (target : D ⥤ Type u) {X : shape.Elements}
    (sectionValue : DependentSection position (branchTarget shape position target) X)
    {Y Z : shape.Elements} (points : Y = Z) (first : X ⟶ Y) (second : X ⟶ Z)
    (arrows : HEq first second) (left : position.obj Y) (right : position.obj Z)
    (arguments : HEq left right) : HEq (sectionValue.app Y first left) (sectionValue.app Z second right) := by
  cases points
  cases eq_of_heq arrows
  cases eq_of_heq arguments
  rfl

def toSection (target : D ⥤ Type u) {X : D} {label : shape.obj X}
    (branches : Branches shape position target label) :
    DependentSection position (branchTarget shape position target) ⟨X, label⟩ where
  app point arrow argument := branches.app point.1 arrow.1
    (cast (congrArg (fun value => position.obj ⟨point.1, value⟩) arrow.2.symm) argument)
  naturality {first second} step restriction argument := by
    rcases first with ⟨Y, firstLabel⟩
    rcases second with ⟨Z, secondLabel⟩
    rcases step with ⟨later, laterLabel⟩
    rcases restriction with ⟨earlier, earlierLabel⟩
    change Y ⟶ Z at later
    change X ⟶ Y at earlier
    change shape.map later firstLabel = secondLabel at laterLabel
    change shape.map earlier label = firstLabel at earlierLabel
    subst secondLabel
    let transported := cast (congrArg (fun value => position.obj ⟨Y, value⟩) earlierLabel.symm) argument
    refine (branches.naturality Y Z earlier later transported).trans ?_
    apply branches.app_eq rfl
    exact (cast_heq _ _).trans
      ((position_map_heq shape position later earlierLabel transported argument (cast_heq _ _)).trans
        (cast_heq _ _).symm)

def fromSection (target : D ⥤ Type u) {X : D} {label : shape.obj X}
    (sectionValue : DependentSection position (branchTarget shape position target) ⟨X, label⟩) :
    Branches shape position target label where
  app Y arrow branch := sectionValue.app ⟨Y, shape.map arrow label⟩ (argumentMap shape arrow label) branch
  naturality Y Z first later branch := by
    refine (sectionValue.naturality (argumentMap shape later (shape.map first label))
      (argumentMap shape first label) branch).trans ?_
    exact eq_of_heq (sectionApp_heq shape position target sectionValue
      (congrArg (Sigma.mk Z) (shape.map_comp_apply first later label).symm)
      ((argumentMap shape first label) ≫ (argumentMap shape later (shape.map first label)))
      (argumentMap shape (first ≫ later) label)
      (elementArrow_heq shape (shape.map_comp_apply first later label).symm _ _ rfl)
      _ _ (cast_heq _ _).symm)

/-- This is the full contextual Pi carrier already used by the displayed
family semantics, with its complete future-index naturality predicate. -/
def branchEquiv (target : D ⥤ Type u) (X : D) (label : shape.obj X) :
    Branches shape position target label ≃
      DependentSection position (branchTarget shape position target) ⟨X, label⟩ where
  toFun := toSection shape position target
  invFun := fromSection shape position target
  left_inv branches := Branches.ext fun _ _ _ => rfl
  right_inv sectionValue := by
    apply DependentSection.ext
    rintro ⟨Y, nextLabel⟩ ⟨arrow, labels⟩ argument
    exact eq_of_heq (sectionApp_heq shape position target sectionValue
      (congrArg (Sigma.mk Y) labels)
      (argumentMap shape arrow label) ⟨arrow, labels⟩
      (elementArrow_heq shape labels _ _ rfl) _ _ (cast_heq _ _))

theorem branchEquiv_value (target : D ⥤ Type u) (X : D) (label : shape.obj X)
    (branches : Branches shape position target label) (Y : D) (arrow : X ⟶ Y)
    (branch : Position shape position label arrow) :
    (branchEquiv shape position target X label branches).app
      ⟨Y, shape.map arrow label⟩ (argumentMap shape arrow label) branch = branches.app Y arrow branch := rfl

theorem branchEquiv_restrict (target : D ⥤ Type u) {X Y : D} (arrow : X ⟶ Y)
    (label : shape.obj X) (branches : Branches shape position target label) :
    branchEquiv shape position target Y (shape.map arrow label) (branches.restrict arrow) =
      DependentSection.restrict position (branchTarget shape position target)
        (argumentMap shape arrow label) (branchEquiv shape position target X label branches) := by
  apply DependentSection.ext
  rintro ⟨Z, nextLabel⟩ ⟨later, labels⟩ argument
  apply branches.app_eq rfl
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)

def emptyPositions : shape.Elements ⥤ Type u where
  obj _ := ULift.{u, 0} Empty
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def leaf {X : D} (label : shape.obj X) : NaturalTree shape (emptyPositions shape) X :=
  sup shape (emptyPositions shape) label (fun _ _ branch => Empty.elim branch.down)
    (fun _ _ _ _ branch => Empty.elim branch.down)

theorem leaf_label_injective {X : D} {first second : shape.obj X}
    (same : leaf shape first = leaf shape second) : first = second := by
  have roots := congrArg Subtype.val same
  exact (RawTree.sup.inj roots).1

def unitPositions : shape.Elements ⥤ Type u where
  obj _ := ULift.{u, 0} PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A perpetual unary branch cannot occur in a well-founded contextual
tree, even though its branch type is inhabited at every context. -/
theorem no_unary_tree {X : D} (tree : RawTree shape (unitPositions shape) X) : False := by
  induction tree with
  | @sup X _ _ ih => exact ih X (𝟙 X) (ULift.up PUnit.unit)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWComparison
