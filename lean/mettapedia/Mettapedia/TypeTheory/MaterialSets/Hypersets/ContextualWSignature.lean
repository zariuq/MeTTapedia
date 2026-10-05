import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes

/-!
# Indexed contextual W transport from dependent signature maps

The supplied data compare only the shape and dependent-position functors.
Full future-position transport, raw tree recursion, restriction and
hereditary naturality are constructed from those maps. In particular, no
tree comparison, recursion operator or W operation law is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignature

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open ContextualWTypes (RawTree Position Natural NaturalTree Branches)

universe u
variable {D : Type u} [Category.{u} D]
variable {shape nextShape : D ⥤ Type u}
variable {position : shape.Elements ⥤ Type u} {nextPosition : nextShape.Elements ⥤ Type u}

/-- Natural shape and dependent-position equivalences. The position law
retains its endpoint transport rather than erasing it to support. -/
structure Signature where
  shapes : (X : D) → shape.obj X ≃ nextShape.obj X
  shape_natural : ∀ {X Y : D} (arrow : X ⟶ Y) (label : shape.obj X),
    shapes Y (shape.map arrow label) = nextShape.map arrow (shapes X label)
  positions : (X : D) → (label : shape.obj X) →
    position.obj ⟨X, label⟩ ≃ nextPosition.obj ⟨X, shapes X label⟩
  position_natural : ∀ {X Y : D} (arrow : X ⟶ Y) (label : shape.obj X)
    (branch : position.obj ⟨X, label⟩),
    HEq (positions Y (shape.map arrow label) (position.map (argumentMap shape arrow label) branch))
      (nextPosition.map (argumentMap nextShape arrow (shapes X label)) (positions X label branch))

variable (signature : Signature (shape := shape) (nextShape := nextShape)
  (position := position) (nextPosition := nextPosition))

private def equalityEquiv {A B : Type u} (same : A = B) : A ≃ B := by
  cases same
  exact Equiv.refl A

private theorem equalityEquiv_apply_heq {A B : Type u} (same : A = B) (value : A) :
    HEq (equalityEquiv same value) value := by
  cases same
  rfl

private theorem value_heq {A : Type u} (family : A → Type u) {first second : A}
    (same : first = second) (operation : (index : A) → family index) :
    HEq (operation first) (operation second) := by
  cases same
  rfl

theorem positions_heq {X : D} {first second : shape.obj X} (same : first = second)
    (left : position.obj ⟨X, first⟩) (right : position.obj ⟨X, second⟩) (branches : HEq left right) :
    HEq (signature.positions X first left) (signature.positions X second right) := by
  cases same
  cases eq_of_heq branches
  rfl

/-- Every original future position has a corresponding position at the
same actual world and arrow. -/
def forwardPosition {X Y : D} (label : shape.obj X) (arrow : X ⟶ Y) :
    Position shape position label arrow ≃
      Position nextShape nextPosition (signature.shapes X label) arrow :=
  (signature.positions Y (shape.map arrow label)).trans
    (equalityEquiv (congrArg (fun label => nextPosition.obj ⟨Y, label⟩) (signature.shape_natural arrow label)))

theorem forwardPosition_heq {X Y : D} (label : shape.obj X) (arrow : X ⟶ Y)
    (branch : Position shape position label arrow) :
    HEq (forwardPosition signature label arrow branch)
      (signature.positions Y (shape.map arrow label) branch) :=
  equalityEquiv_apply_heq _ _

theorem forwardPosition_labels_heq {X Y : D} {first second : shape.obj X} (same : first = second)
    (arrow : X ⟶ Y) (left : Position shape position first arrow) (right : Position shape position second arrow)
    (branches : HEq left right) :
    HEq (forwardPosition signature first arrow left) (forwardPosition signature second arrow right) := by
  cases same
  cases eq_of_heq branches
  rfl

theorem forwardPosition_composite {X Y Z : D} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position (shape.map first label) later) :
    HEq (forwardPosition signature label (first ≫ later)
      (ContextualWTypes.compositePosition shape position label first later branch))
      (ContextualWTypes.compositePosition nextShape nextPosition (signature.shapes X label) first later
        (cast (congrArg (fun label => Position nextShape nextPosition label later)
          (signature.shape_natural first label))
          (forwardPosition signature (shape.map first label) later branch))) := by
  refine (forwardPosition_heq signature _ _ _).trans ?_
  refine (positions_heq signature (shape.map_comp_apply first later label) _ _ (cast_heq _ _)).trans ?_
  exact (forwardPosition_heq signature _ _ _).symm.trans ((cast_heq _ _).trans (cast_heq _ _)).symm

theorem forwardPosition_along {X Y Z : D} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position label first) :
    forwardPosition signature label (first ≫ later)
        (ContextualWTypes.positionAlong shape position label first later branch) =
      ContextualWTypes.positionAlong nextShape nextPosition (signature.shapes X label) first later
        (forwardPosition signature label first branch) := by
  apply eq_of_heq
  refine (forwardPosition_heq signature _ _ _).trans ?_
  refine (positions_heq signature (shape.map_comp_apply first later label) _ _ (cast_heq _ _)).trans ?_
  refine (signature.position_natural later (shape.map first label) branch).trans ?_
  refine (ContextualWTypes.position_map_heq nextShape nextPosition later
    (signature.shape_natural first label) _ _ (forwardPosition_heq signature label first branch).symm).trans ?_
  exact (cast_heq _ _).symm

/-- A full future-position equivalence is used inversely when forming each
new child. Thus no future world, parallel arrow or position is dropped. -/
noncomputable def mapRaw {X : D} (tree : RawTree shape position X) : RawTree nextShape nextPosition X :=
  RawTree.rec (motive := fun X _ => RawTree nextShape nextPosition X)
    (fun {X} label _children earlier => .sup (signature.shapes X label)
      (fun Y arrow branch => earlier Y arrow ((forwardPosition signature label arrow).symm branch))) tree

theorem mapRaw_sup {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y) :
    mapRaw signature (.sup label children) = .sup (signature.shapes X label)
      (fun Y arrow branch => mapRaw signature (children Y arrow ((forwardPosition signature label arrow).symm branch))) := rfl

theorem backwardPosition_composite {X Y Z : D} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position nextShape nextPosition (signature.shapes Y (shape.map first label)) later) :
    (forwardPosition signature label (first ≫ later)).symm
        (ContextualWTypes.compositePosition nextShape nextPosition (signature.shapes X label) first later
          (cast (congrArg (fun label => Position nextShape nextPosition label later)
            (signature.shape_natural first label)) branch)) =
      ContextualWTypes.compositePosition shape position label first later
        ((forwardPosition signature (shape.map first label) later).symm branch) := by
  apply (forwardPosition signature label (first ≫ later)).injective
  refine ((forwardPosition signature label (first ≫ later)).apply_symm_apply _).trans ?_
  exact (eq_of_heq ((forwardPosition_composite signature label first later
    ((forwardPosition signature (shape.map first label) later).symm branch)).trans
      (heq_of_eq (congrArg (fun entry => ContextualWTypes.compositePosition nextShape nextPosition
        (signature.shapes X label) first later (cast (congrArg (fun label => Position nextShape nextPosition label later)
          (signature.shape_natural first label)) entry))
        ((forwardPosition signature (shape.map first label) later).apply_symm_apply branch))))).symm

theorem mapRaw_restrict {X Y : D} (arrow : X ⟶ Y) (tree : RawTree shape position X) :
    mapRaw signature (ContextualWTypes.restrict shape position arrow tree) =
      ContextualWTypes.restrict nextShape nextPosition arrow (mapRaw signature tree) := by
  cases tree with
  | sup label children =>
    apply RawTree.sup_eq_of_cast (signature.shape_natural arrow label)
    intro Z later branch
    apply congrArg (mapRaw signature)
    apply congrArg (children Z (arrow ≫ later))
    exact (backwardPosition_composite signature label arrow later branch).symm

theorem backwardPosition_along {X Y Z : D} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position nextShape nextPosition (signature.shapes X label) first) :
    ContextualWTypes.positionAlong shape position label first later
        ((forwardPosition signature label first).symm branch) =
      (forwardPosition signature label (first ≫ later)).symm
        (ContextualWTypes.positionAlong nextShape nextPosition (signature.shapes X label) first later branch) := by
  apply (forwardPosition signature label (first ≫ later)).injective
  exact (forwardPosition_along signature label first later _).trans
    ((congrArg (ContextualWTypes.positionAlong nextShape nextPosition (signature.shapes X label) first later)
      ((forwardPosition signature label first).apply_symm_apply branch)).trans
      ((forwardPosition signature label (first ≫ later)).apply_symm_apply _).symm)

theorem mapRaw_natural {X : D} (tree : RawTree shape position X) (natural : Natural shape position tree) :
    Natural nextShape nextPosition (mapRaw signature tree) := by
  induction tree with
  | @sup X label children earlier =>
    constructor
    · intro Y arrow branch
      exact earlier Y arrow _ (natural.1 Y arrow _)
    · intro Y Z first later branch
      refine (mapRaw_restrict signature later _).symm.trans ?_
      refine (congrArg (mapRaw signature) (natural.2 Y Z first later _)).trans ?_
      exact congrArg (fun original => mapRaw signature (children Z (first ≫ later) original))
        (backwardPosition_along signature label first later branch)

noncomputable def mapNatural {X : D} (tree : NaturalTree shape position X) : NaturalTree nextShape nextPosition X :=
  ⟨mapRaw signature tree.val, mapRaw_natural signature tree.val tree.property⟩

theorem mapNatural_restrict {X Y : D} (arrow : X ⟶ Y) (tree : NaturalTree shape position X) :
    mapNatural signature ((ContextualWTypes.family shape position).map arrow tree) =
      (ContextualWTypes.family nextShape nextPosition).map arrow (mapNatural signature tree) :=
  Subtype.ext (mapRaw_restrict signature arrow tree.val)

noncomputable def treeMap : NatTrans (ContextualWTypes.family shape position)
    (ContextualWTypes.family nextShape nextPosition) where
  app X := TypeCat.ofHom (mapNatural signature (X := X))
  naturality _X _Y arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact mapNatural_restrict signature arrow tree

variable (target : D ⥤ Type u)

def mapBranches {X : D} (label : shape.obj X) (branches : Branches shape position target label) :
    Branches nextShape nextPosition target (signature.shapes X label) where
  app Y arrow branch := branches.app Y arrow ((forwardPosition signature label arrow).symm branch)
  naturality Y Z first later branch :=
    (branches.naturality Y Z first later _).trans
      (congrArg (branches.app Z (first ≫ later)) (backwardPosition_along signature label first later branch))

def unmapBranches {X : D} (label : shape.obj X)
    (branches : Branches nextShape nextPosition target (signature.shapes X label)) :
    Branches shape position target label where
  app Y arrow branch := branches.app Y arrow (forwardPosition signature label arrow branch)
  naturality Y Z first later branch :=
    (branches.naturality Y Z first later _).trans
      (congrArg (branches.app Z (first ≫ later)) (forwardPosition_along signature label first later branch).symm)

theorem unmap_map_branches {X : D} (label : shape.obj X) (branches : Branches shape position target label) :
    unmapBranches signature target label (mapBranches signature target label branches) = branches := by
  apply Branches.ext
  intro Y arrow branch
  exact congrArg (branches.app Y arrow) ((forwardPosition signature label arrow).symm_apply_apply branch)

theorem map_unmap_branches {X : D} (label : shape.obj X)
    (branches : Branches nextShape nextPosition target (signature.shapes X label)) :
    mapBranches signature target label (unmapBranches signature target label branches) = branches := by
  apply Branches.ext
  intro Y arrow branch
  exact congrArg (branches.app Y arrow) ((forwardPosition signature label arrow).apply_symm_apply branch)

def branchEquiv {X : D} (label : shape.obj X) : Branches shape position target label ≃
    Branches nextShape nextPosition target (signature.shapes X label) where
  toFun := mapBranches signature target label
  invFun := unmapBranches signature target label
  left_inv := unmap_map_branches signature target label
  right_inv := map_unmap_branches signature target label

/-- A natural algebra on the new signature acts on the original signature
by the constructed complete branch comparison. -/
def pullAlgebra (algebra : ContextualWTypes.Algebra nextShape nextPosition target) :
    ContextualWTypes.Algebra shape position target where
  make X label branches := algebra.make X (signature.shapes X label) (mapBranches signature target label branches)
  naturality X Y arrow label branches := by
    refine (algebra.naturality X Y arrow (signature.shapes X label) (mapBranches signature target label branches)).trans ?_
    apply Eq.symm
    apply ContextualWTypes.Algebra.make_eq_of_cast nextShape nextPosition algebra (signature.shape_natural arrow label)
    intro Z later branch
    exact congrArg (branches.app Z (arrow ≫ later)) (backwardPosition_composite signature label arrow later branch).symm

theorem map_evaluates (algebra : ContextualWTypes.Algebra nextShape nextPosition target)
    {X : D} {tree : RawTree shape position X} {value : target.obj X}
    (evaluation : ContextualWTypes.Evaluates shape position (pullAlgebra signature target algebra) tree value) :
    ContextualWTypes.Evaluates nextShape nextPosition algebra (mapRaw signature tree) value := by
  induction evaluation with
  | @sup X label children branches values earlier =>
    exact ContextualWTypes.Evaluates.sup (signature.shapes X label)
      (fun Y arrow branch => mapRaw signature (children Y arrow ((forwardPosition signature label arrow).symm branch)))
      (mapBranches signature target label branches)
      (fun Y arrow branch => earlier Y arrow ((forwardPosition signature label arrow).symm branch))

theorem fold_map (algebra : ContextualWTypes.Algebra nextShape nextPosition target)
    {X : D} (tree : NaturalTree shape position X) :
    ContextualWTypes.fold nextShape nextPosition algebra (mapNatural signature tree) =
      ContextualWTypes.fold shape position (pullAlgebra signature target algebra) tree :=
  ContextualWTypes.evaluates_unique nextShape nextPosition algebra
    (ContextualWTypes.fold_evaluates nextShape nextPosition algebra _)
    (map_evaluates signature target algebra
      (ContextualWTypes.fold_evaluates shape position (pullAlgebra signature target algebra) tree))

theorem constructor_map {X : D} (label : shape.obj X)
    (branches : Branches shape position (ContextualWTypes.family shape position) label) :
    mapNatural signature ((ContextualWTypes.treeAlgebra shape position).make X label branches) =
      (ContextualWTypes.treeAlgebra nextShape nextPosition).make X (signature.shapes X label)
        ((mapBranches signature (ContextualWTypes.family shape position) label branches).map (treeMap signature)) :=
  Subtype.ext rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignature
