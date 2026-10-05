import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes
import Mettapedia.TypeTheory.WiderPresheafDependentFunctions

/-!
# Wider algebras on the existing contextual W carrier

Shapes, positions and contextual trees remain at the original universe.
The compatible branch values and algebra results may inhabit an independent
larger universe. Indexed recursion constructs all restricted fold values
and proves their evaluation and naturality together.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderContextualWAlgebras

open CategoryTheory MaterialSets.Hypersets.ContextualWTypes
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u h k
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)

/-- The polynomial branch object contains a compatible value at every
future world, arrow and transported position. -/
structure Branches (target : D ⥤ Type h) {X : D} (label : shape.obj X) where
  app : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → target.obj Y
  naturality : ∀ (Y Z : D) (first : X ⟶ Y) (later : Y ⟶ Z) branch,
    target.map later (app Y first branch) =
      app Z (first ≫ later) (positionAlong shape position label first later branch)

namespace Branches

variable {shape position} {target : D ⥤ Type h}

@[ext] theorem ext {X : D} {label : shape.obj X}
    {left right : Branches shape position target label}
    (values : ∀ Y arrow branch, left.app Y arrow branch = right.app Y arrow branch) :
    left = right := by
  cases left
  cases right
  have same := funext fun Y => funext fun arrow => funext fun branch => values Y arrow branch
  cases same
  rfl

theorem app_eq {X Y : D} {label : shape.obj X}
    (branches : Branches shape position target label)
    {first second : X ⟶ Y} (arrows : first = second)
    (left : Position shape position label first) (right : Position shape position label second)
    (positions : HEq left right) : branches.app Y first left = branches.app Y second right := by
  cases arrows
  cases eq_of_heq positions
  rfl

def restrict {X Y : D} {label : shape.obj X} (branches : Branches shape position target label)
    (arrow : X ⟶ Y) : Branches shape position target (shape.map arrow label) where
  app Z later branch := branches.app Z (arrow ≫ later)
    (compositePosition shape position label arrow later branch)
  naturality Z W first later branch := by
    refine (branches.naturality Z W (arrow ≫ first) later
      (compositePosition shape position label arrow first branch)).trans ?_
    exact branches.app_eq (Category.assoc arrow first later)
      (positionAlong shape position label (arrow ≫ first) later
        (compositePosition shape position label arrow first branch))
      (compositePosition shape position label arrow (first ≫ later)
        (positionAlong shape position (shape.map arrow label) first later branch))
      (positionAlong_composite shape position label arrow first later branch)

def map {other : D ⥤ Type k} (change : WiderPresheafDependentFunctions.Hom target other) {X : D}
    {label : shape.obj X} (branches : Branches shape position target label) :
    Branches shape position other label where
  app Y arrow branch := change.app Y (branches.app Y arrow branch)
  naturality Y Z first later branch := by
    exact (change.naturality later (branches.app Y first branch)).trans
      (congrArg (change.app Z) (branches.naturality Y Z first later branch))

theorem pair_eq_of_cast {X : D} {first second : shape.obj X}
    (same : first = second) (left : Branches shape position target first)
    (right : Branches shape position target second)
    (values : ∀ Y arrow branch, left.app Y arrow branch =
      right.app Y arrow (cast (congrArg (fun label => Position shape position label arrow) same) branch)) :
    (⟨first, left⟩ : Σ label : shape.obj X, Branches shape position target label) = ⟨second, right⟩ := by
  cases same
  exact congrArg (Sigma.mk first) (Branches.ext values)

end Branches

/-- The full polynomial acts on the actual presheaf branch objects. -/
def polynomial (target : D ⥤ Type h) : D ⥤ Type (max u h) where
  obj X := Σ label : shape.obj X, Branches shape position target label
  map arrow := TypeCat.ofHom fun node => ⟨shape.map arrow node.1, node.2.restrict arrow⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨label, branches⟩
    apply Branches.pair_eq_of_cast (shape.map_id_apply X label)
    intro Y arrow branch
    exact branches.app_eq (Category.id_comp arrow)
      (compositePosition shape position label (𝟙 X) arrow branch)
      (cast (congrArg (fun label => Position shape position label arrow) (shape.map_id_apply X label)) branch)
      ((cast_heq _ _).trans (cast_heq _ _).symm)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    rintro ⟨label, branches⟩
    apply Branches.pair_eq_of_cast (shape.map_comp_apply first later label)
    intro W arrow branch
    exact branches.app_eq (Category.assoc first later arrow)
      (compositePosition shape position label (first ≫ later) arrow branch)
      (compositePosition shape position label first (later ≫ arrow)
        (compositePosition shape position (shape.map first label) later arrow
          (cast (congrArg (fun label => Position shape position label arrow)
            (shape.map_comp_apply first later label)) branch)))
      ((cast_heq _ _).trans ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))).symm)

/-- An algebra for the full contextual polynomial. Its naturality law
compares the actual reindexing of every future branch. -/
structure Algebra (target : D ⥤ Type h) where
  make : (X : D) → (label : shape.obj X) → Branches shape position target label → target.obj X
  naturality : ∀ (X Y : D) (arrow : X ⟶ Y) label branches,
    target.map arrow (make X label branches) =
      make Y (shape.map arrow label) (branches.restrict arrow)

/-- Evaluation records all children, rather than only the root label. -/
inductive Evaluates {target : D ⥤ Type h} (algebra : Algebra shape position target) :
    {X : D} → RawTree shape position X → target.obj X → Prop where
  | sup {X : D} (label : shape.obj X)
      (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y)
      (branches : Branches shape position target label)
      (values : ∀ Y arrow branch, Evaluates algebra (children Y arrow branch) (branches.app Y arrow branch)) :
      Evaluates algebra (.sup label children) (algebra.make X label branches)

theorem evaluates_unique {target : D ⥤ Type h} (algebra : Algebra shape position target)
    {X : D} {tree : RawTree shape position X} {left right : target.obj X}
    (first : Evaluates shape position algebra tree left)
    (second : Evaluates shape position algebra tree right) : left = right := by
  induction first with
  | sup label children branches values ih =>
    cases second with
    | sup _ _ other otherValues =>
      exact congrArg (algebra.make _ label) (Branches.ext fun Y arrow branch => ih Y arrow branch (otherValues Y arrow branch))

/-- Values and their evaluation derivations exist uniformly at every
restriction. The law is proved together with the recursive construction. -/
structure FoldData {target : D ⥤ Type h} (algebra : Algebra shape position target)
    {X : D} (tree : RawTree shape position X) where
  value : (Y : D) → (arrow : X ⟶ Y) → target.obj Y
  evaluates : ∀ Y arrow, Evaluates shape position algebra (restrict shape position arrow tree) (value Y arrow)
  naturality : ∀ (Y Z : D) (first : X ⟶ Y) (later : Y ⟶ Z),
    target.map later (value Y first) = value Z (first ≫ later)

namespace FoldData

variable {shape position} {target : D ⥤ Type h} {algebra : Algebra shape position target}

theorem current_evaluates {X : D} {tree : RawTree shape position X}
    (data : FoldData shape position algebra tree) :
    Evaluates shape position algebra tree (data.value X (𝟙 X)) := by
  simpa only [restrict_id] using data.evaluates X (𝟙 X)

theorem value_eq {X Y : D} {first second : RawTree shape position X}
    (left : FoldData shape position algebra first) (right : FoldData shape position algebra second)
    (trees : first = second) (arrow : X ⟶ Y) : left.value Y arrow = right.value Y arrow := by
  cases trees
  exact evaluates_unique shape position algebra (left.evaluates Y arrow) (right.evaluates Y arrow)

end FoldData

theorem Algebra.make_eq_of_cast {target : D ⥤ Type h}
    (algebra : Algebra shape position target) {X : D} {first second : shape.obj X}
    (same : first = second) (left : Branches shape position target first)
    (right : Branches shape position target second)
    (values : ∀ Y arrow branch, left.app Y arrow branch =
      right.app Y arrow (cast (congrArg (fun label => Position shape position label arrow) same) branch)) :
    algebra.make X first left = algebra.make X second right := by
  cases same
  exact congrArg (algebra.make X first) (Branches.ext values)

/-- Structural recursion constructs the compatible branch values and their
derivations simultaneously. Evaluation uniqueness compares the children
reached by the two actual restriction paths. -/
noncomputable def foldData {target : D ⥤ Type h} (algebra : Algebra shape position target) :
    {X : D} → (tree : RawTree shape position X) → Natural shape position tree →
      FoldData shape position algebra tree := by
  intro X tree
  induction tree with
  | @sup X label children ih =>
    intro natural
    let data := fun Y arrow branch => ih Y arrow branch (natural.1 Y arrow branch)
    let branchValues := fun (Y : D) (arrow : X ⟶ Y) =>
      fun (Z : D) (later : Y ⟶ Z) branch =>
        (data Z (arrow ≫ later) (compositePosition shape position label arrow later branch)).value Z (𝟙 Z)
    have branchNatural : ∀ (Y : D) (arrow : X ⟶ Y),
        ∀ (Z W : D) (first : Y ⟶ Z) (later : Z ⟶ W) branch,
          target.map later (branchValues Y arrow Z first branch) =
            branchValues Y arrow W (first ≫ later)
              (positionAlong shape position (shape.map arrow label) first later branch) := by
      intro Y arrow Z W first later branch
      let firstData := data Z (arrow ≫ first) (compositePosition shape position label arrow first branch)
      let secondData := data W (arrow ≫ first ≫ later)
        (compositePosition shape position label arrow (first ≫ later)
          (positionAlong shape position (shape.map arrow label) first later branch))
      have trees : restrict shape position later
          (children Z (arrow ≫ first) (compositePosition shape position label arrow first branch)) =
          children W (arrow ≫ first ≫ later)
            (compositePosition shape position label arrow (first ≫ later)
              (positionAlong shape position (shape.map arrow label) first later branch)) := by
        refine (natural.2 Z W (arrow ≫ first) later
          (compositePosition shape position label arrow first branch)).trans ?_
        exact RawTree.children_eq label children (Category.assoc arrow first later)
          (positionAlong shape position label (arrow ≫ first) later
            (compositePosition shape position label arrow first branch))
          (compositePosition shape position label arrow (first ≫ later)
            (positionAlong shape position (shape.map arrow label) first later branch))
          (positionAlong_composite shape position label arrow first later branch)
      have evaluations : firstData.value W later = secondData.value W (𝟙 W) :=
        evaluates_unique shape position algebra (trees ▸ firstData.evaluates W later)
          secondData.current_evaluates
      have naturalValue : target.map later (firstData.value Z (𝟙 Z)) = firstData.value W later := by
        simpa only [Category.id_comp] using firstData.naturality Z W (𝟙 Z) later
      exact naturalValue.trans evaluations
    let branches := fun Y arrow => (show Branches shape position target (shape.map arrow label) from
      ⟨branchValues Y arrow, branchNatural Y arrow⟩)
    refine {
      value := fun Y arrow => algebra.make Y (shape.map arrow label) (branches Y arrow)
      evaluates := ?_
      naturality := ?_ }
    · intro Y arrow
      exact Evaluates.sup (shape.map arrow label)
        (fun Z later branch => children Z (arrow ≫ later) (compositePosition shape position label arrow later branch))
        (branches Y arrow) (fun Z later branch =>
          (data Z (arrow ≫ later) (compositePosition shape position label arrow later branch)).current_evaluates)
    · intro Y Z first later
      refine (algebra.naturality Y Z later (shape.map first label) (branches Y first)).trans ?_
      apply Algebra.make_eq_of_cast shape position algebra (shape.map_comp_apply first later label).symm
      intro W arrow branch
      let firstData := data W (first ≫ later ≫ arrow)
        (compositePosition shape position label first (later ≫ arrow)
          (compositePosition shape position (shape.map first label) later arrow branch))
      let secondData := data W ((first ≫ later) ≫ arrow)
        (compositePosition shape position label (first ≫ later) arrow
          (cast (congrArg (fun label => Position shape position label arrow)
            (shape.map_comp_apply first later label).symm) branch))
      apply firstData.value_eq secondData ?_ (𝟙 W)
      exact RawTree.children_eq label children (Category.assoc first later arrow).symm
        _ _ ((cast_heq _ _).trans ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)).symm))

/-- The fold is defined on the actual natural tree carrier. -/
noncomputable def fold {target : D ⥤ Type h} (algebra : Algebra shape position target)
    {X : D} (tree : NaturalTree shape position X) : target.obj X :=
  (foldData shape position algebra tree.val tree.property).value X (𝟙 X)

theorem fold_evaluates {target : D ⥤ Type h} (algebra : Algebra shape position target)
    {X : D} (tree : NaturalTree shape position X) :
    Evaluates shape position algebra tree.val (fold shape position algebra tree) :=
  (foldData shape position algebra tree.val tree.property).current_evaluates

theorem fold_natural {target : D ⥤ Type h} (algebra : Algebra shape position target)
    {X Y : D} (arrow : X ⟶ Y) (tree : NaturalTree shape position X) :
    target.map arrow (fold shape position algebra tree) =
      fold shape position algebra ((family shape position).map arrow tree) := by
  let data := foldData shape position algebra tree.val tree.property
  have laterValues := data.evaluates Y arrow
  have restrictedValues := fold_evaluates shape position algebra ((family shape position).map arrow tree)
  have naturalValue : target.map arrow (data.value X (𝟙 X)) = data.value Y arrow := by
    simpa only [Category.id_comp] using data.naturality X Y (𝟙 X) arrow
  exact naturalValue.trans (evaluates_unique shape position algebra laterValues restrictedValues)

noncomputable def foldMap {target : D ⥤ Type h} (algebra : Algebra shape position target) :
    WiderPresheafDependentFunctions.Hom (family shape position) target where
  app _ tree := fold shape position algebra tree
  naturality arrow tree := fold_natural shape position algebra arrow tree

/-- The constructor is a natural algebra on the actual tree presheaf. -/
def treeAlgebra : Algebra shape position (family shape position) where
  make _X label branches := sup shape position label branches.app
    (fun Y Z first later branch => congrArg Subtype.val (branches.naturality Y Z first later branch))
  naturality _X _Y _arrow _label _branches := Subtype.ext rfl

def constructor : NatTrans (polynomial shape position (family shape position)) (family shape position) where
  app X := TypeCat.ofHom fun node => (treeAlgebra shape position).make X node.1 node.2
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro node
    exact ((treeAlgebra shape position).naturality X Y arrow node.1 node.2).symm

theorem fold_beta {target : D ⥤ Type h} (algebra : Algebra shape position target)
    {X : D} (label : shape.obj X) (branches : Branches shape position (family shape position) label) :
    fold shape position algebra ((treeAlgebra shape position).make X label branches) =
      algebra.make X label (branches.map (foldMap shape position algebra)) := by
  apply evaluates_unique shape position algebra
    (fold_evaluates shape position algebra ((treeAlgebra shape position).make X label branches))
  exact Evaluates.sup label (fun Y arrow branch => (branches.app Y arrow branch).val)
    (branches.map (foldMap shape position algebra))
    (fun Y arrow branch => fold_evaluates shape position algebra (branches.app Y arrow branch))

theorem morphism_evaluates {target : D ⥤ Type h} (algebra : Algebra shape position target)
    (change : WiderPresheafDependentFunctions.Hom (family shape position) target)
    (constructorLaw : ∀ (X : D) label branches,
      change.app X ((treeAlgebra shape position).make X label branches) =
        algebra.make X label (branches.map change)) :
    ∀ {X : D} (tree : RawTree shape position X) (natural : Natural shape position tree),
      Evaluates shape position algebra tree (change.app X ⟨tree, natural⟩) := by
  intro X tree
  induction tree with
  | @sup X label children ih =>
    intro natural
    let branches : Branches shape position (family shape position) label := {
      app Y arrow branch := ⟨children Y arrow branch, natural.1 Y arrow branch⟩
      naturality Y Z first later branch := Subtype.ext (natural.2 Y Z first later branch) }
    have evaluation := Evaluates.sup label children (branches.map change)
      (fun Y arrow branch => ih Y arrow branch (natural.1 Y arrow branch))
    exact (constructorLaw X label branches).symm ▸ evaluation

/-- Every natural algebra morphism is the constructed fold. -/
theorem fold_unique {target : D ⥤ Type h} (algebra : Algebra shape position target)
    (change : WiderPresheafDependentFunctions.Hom (family shape position) target)
    (constructorLaw : ∀ (X : D) label branches,
      change.app X ((treeAlgebra shape position).make X label branches) =
        algebra.make X label (branches.map change)) :
    change = foldMap shape position algebra := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro X tree
  exact evaluates_unique shape position algebra
    (morphism_evaluates shape position algebra change constructorLaw tree.val tree.property)
    (fold_evaluates shape position algebra tree)


end Mettapedia.TypeTheory.WiderContextualWAlgebras
