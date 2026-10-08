import Mettapedia.CategoryTheory.StrictTwoArrow
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# The two-category of fibrations with varying bases

Objects are actual fibered functors. One-cells are strictly commuting
squares whose total functor preserves Cartesian arrows. Two-cells are
compatible pairs of natural transformations at the total and base levels.
The construction forgets faithfully and locally fully to the strict arrow
two-category of Cat. No logical constructors or comprehension adjunctions
are included in this bundle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.FibrationTwoCategory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe u v

set_option linter.checkUnivs false in
structure Fibration where
  projection : StrictTwoArrow Cat.{v,u}
  fibered : projection.arrow.toFunctor.IsFibered

attribute [instance] Fibration.fibered

universe c s t b

/-- The complete Cartesian property can be read over a supplied named
base arrow once its actual lifting identifications have been proved. -/
theorem cartesian_of_homLift {Total : Type c} {Base : Type s}
    [Category.{t} Total] [Category.{b} Base] (projection : Total ⥤ Base)
    {baseFirst baseSecond : Base} (baseArrow : baseFirst ⟶ baseSecond)
    {first second : Total} (arrow : first ⟶ second)
    [projection.IsHomLift baseArrow arrow]
    [projection.IsCartesian (projection.map arrow) arrow] :
    projection.IsCartesian baseArrow arrow := by
  subst_hom_lift projection baseArrow arrow
  infer_instance

namespace Fibration

abbrev Total (source : Fibration.{u,v}) := source.projection.source
abbrev Base (source : Fibration.{u,v}) := source.projection.target
abbrev functor (source : Fibration.{u,v}) : source.Total ⥤ source.Base :=
  source.projection.arrow.toFunctor

/-- Cartesian preservation is the local admission condition on a
commuting square, stated for complete actual total-category arrows. -/
def PreservesCartesian {source target : Fibration.{u,v}}
    (square : source.projection ⟶ target.projection) : Prop :=
  ∀ {first second : source.Total} (arrow : first ⟶ second),
    source.functor.IsCartesian (source.functor.map arrow) arrow →
      target.functor.IsCartesian (target.functor.map (square.left.toFunctor.map arrow))
        (square.left.toFunctor.map arrow)

@[ext] structure Hom (source target : Fibration.{u,v}) where
  square : source.projection ⟶ target.projection
  cartesian : PreservesCartesian square

instance categoryStruct : CategoryStruct Fibration.{u,v} where
  Hom := Hom
  id source := ⟨𝟙 source.projection, fun _ supplied => supplied⟩
  comp first second := ⟨first.square ≫ second.square,
    fun arrow supplied => second.cartesian _ (first.cartesian arrow supplied)⟩

instance category : Category Fibration.{u,v} where
  id_comp := by intros; apply Hom.ext; exact _root_.CategoryTheory.Category.id_comp _
  comp_id := by intros; apply Hom.ext; exact _root_.CategoryTheory.Category.comp_id _
  assoc := by intros; apply Hom.ext; exact _root_.CategoryTheory.Category.assoc _ _ _

@[ext] structure Cell {source target : Fibration.{u,v}} (first second : source ⟶ target) where
  hom : first.square ⟶ second.square

instance homCategory (source target : Fibration.{u,v}) : Category (source ⟶ target) where
  Hom := Cell
  id first := ⟨𝟙 first.square⟩
  comp earlier later := ⟨earlier.hom ≫ later.hom⟩
  id_comp := by intros; apply Cell.ext; exact _root_.CategoryTheory.Category.id_comp _
  comp_id := by intros; apply Cell.ext; exact _root_.CategoryTheory.Category.comp_id _
  assoc := by intros; apply Cell.ext; exact _root_.CategoryTheory.Category.assoc _ _ _

@[simp] theorem id_square (source : Fibration.{u,v}) :
    (𝟙 source : source ⟶ source).square = 𝟙 source.projection := rfl

@[simp] theorem comp_square {source middle target : Fibration.{u,v}}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).square = first.square ≫ second.square := rfl

@[simp] theorem eqToHom_square {source target : Fibration.{u,v}}
    {first second : source ⟶ target} (same : first = second) :
    (eqToHom same : first ⟶ second).hom = eqToHom (congrArg Hom.square same) := by
  cases same
  rfl

@[simp] theorem cell_id_hom {source target : Fibration.{u,v}} (route : source ⟶ target) :
    (𝟙 route : route ⟶ route).hom = 𝟙 route.square := rfl

@[simp] theorem cell_comp_hom {source target : Fibration.{u,v}}
    {first second third : source ⟶ target} (earlier : first ⟶ second) (later : second ⟶ third) :
    (earlier ≫ later).hom = earlier.hom ≫ later.hom := rfl

def whiskerLeft {source middle target : Fibration.{u,v}}
    (route : source ⟶ middle) {first second : middle ⟶ target} (change : first ⟶ second) :
    route ≫ first ⟶ route ≫ second := ⟨route.square ◁ change.hom⟩

def whiskerRight {source middle target : Fibration.{u,v}}
    {first second : source ⟶ middle} (change : first ⟶ second) (route : middle ⟶ target) :
    first ≫ route ⟶ second ≫ route := ⟨change.hom ▷ route.square⟩

@[simp] theorem whiskerLeft_hom {source middle target : Fibration.{u,v}}
    (route : source ⟶ middle) {first second : middle ⟶ target} (change : first ⟶ second) :
    (whiskerLeft route change).hom = route.square ◁ change.hom := rfl

@[simp] theorem whiskerRight_hom {source middle target : Fibration.{u,v}}
    {first second : source ⟶ middle} (change : first ⟶ second) (route : middle ⟶ target) :
    (whiskerRight change route).hom = change.hom ▷ route.square := rfl

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

instance bicategory : Bicategory Fibration.{u,v} where
  toCategoryStruct := categoryStruct
  homCategory := homCategory
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator first second third := eqToIso (_root_.CategoryTheory.Category.assoc first second third)
  leftUnitor first := eqToIso (_root_.CategoryTheory.Category.id_comp first)
  rightUnitor first := eqToIso (_root_.CategoryTheory.Category.comp_id first)
  whiskerLeft_id := by intros; apply Cell.ext; simp
  whiskerLeft_comp := by intros; apply Cell.ext; simp
  id_whiskerLeft := by intros; apply Cell.ext; simp
  comp_whiskerLeft := by intros; apply Cell.ext; simp
  id_whiskerRight := by intros; apply Cell.ext; simp
  comp_whiskerRight := by intros; apply Cell.ext; simp
  whiskerRight_id := by intros; apply Cell.ext; simp
  whiskerRight_comp := by intros; apply Cell.ext; simp
  whisker_assoc := by intros; apply Cell.ext; simp
  whisker_exchange := by
    intros; apply Cell.ext
    simpa using _root_.CategoryTheory.Bicategory.whisker_exchange _ _
  pentagon := by
    intros; apply Cell.ext; apply StrictTwoArrow.Cell.ext <;> simp
    all_goals apply Cat.Hom₂.ext; apply NatTrans.ext; funext object; rfl
  triangle := by
    intros; apply Cell.ext; apply StrictTwoArrow.Cell.ext <;> simp
    all_goals apply Cat.Hom₂.ext; apply NatTrans.ext; funext object; rfl

instance strict : Bicategory.Strict Fibration.{u,v} where
  id_comp := _root_.CategoryTheory.Category.id_comp
  comp_id := _root_.CategoryTheory.Category.comp_id
  assoc := _root_.CategoryTheory.Category.assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

@[simp] theorem left_whisker_hom {source middle target : Fibration.{u,v}}
    (route : source ⟶ middle) {first second : middle ⟶ target} (change : first ⟶ second) :
    (route ◁ change).hom = route.square ◁ change.hom := rfl

@[simp] theorem right_whisker_hom {source middle target : Fibration.{u,v}}
    {first second : source ⟶ middle} (change : first ⟶ second) (route : middle ⟶ target) :
    (change ▷ route).hom = change.hom ▷ route.square := rfl

def forget : StrictPseudofunctor Fibration.{u,v} (StrictTwoArrow Cat.{v,u}) :=
  StrictPseudofunctor.mk'' {
    obj source := source.projection
    map route := route.square
    map₂ change := change.hom
    map₂_whisker_left := by intros; simp
    map₂_whisker_right := by intros; simp }

instance localFaithful (source target : Fibration.{u,v}) :
    (forget.mapFunctor source target).Faithful where
  map_injective same := Cell.ext same

instance localFull (source target : Fibration.{u,v}) :
    (forget.mapFunctor source target).Full where
  map_surjective change := ⟨⟨change⟩, rfl⟩

/-- The base and total transformations satisfy the actual component square. -/
theorem two_cell_square {source target : Fibration.{u,v}}
    {first second : source ⟶ target} (change : first ⟶ second) :
    source.projection.arrow ◁ change.hom.right ≫ eqToHom second.square.comm =
      eqToHom first.square.comm ≫ change.hom.left ▷ target.projection.arrow :=
  StrictTwoArrow.compatible_square change.hom

/-- Preservation supplies the full Cartesian universal property after a
change of base, not only the identity of the image arrow. -/
theorem map_cartesian {source target : Fibration.{u,v}} (route : source ⟶ target)
    {first second : source.Total} (arrow : first ⟶ second)
    [source.functor.IsCartesian (source.functor.map arrow) arrow] :
    target.functor.IsCartesian (target.functor.map (route.square.left.toFunctor.map arrow))
      (route.square.left.toFunctor.map arrow) :=
  route.cartesian arrow inferInstance

theorem map_stronglyCartesian {source target : Fibration.{u,v}} (route : source ⟶ target)
    {first second : source.Total} (arrow : first ⟶ second)
    [source.functor.IsCartesian (source.functor.map arrow) arrow] :
    target.functor.IsStronglyCartesian
      (target.functor.map (route.square.left.toFunctor.map arrow))
      (route.square.left.toFunctor.map arrow) := by
  let := map_cartesian route arrow
  infer_instance

/-- The total and base functors commute as actual functors. -/
theorem projection_square {source target : Fibration.{u,v}} (route : source ⟶ target) :
    source.functor ⋙ route.square.right.toFunctor =
      route.square.left.toFunctor ⋙ target.functor :=
  congrArg Cat.Hom.toFunctor route.square.comm

/-- A supplied lift of an independently named base arrow is still a lift
of the mapped base arrow, including its domain and codomain identifications. -/
theorem map_homLift {source target : Fibration.{u,v}} (route : source ⟶ target)
    {baseFirst baseSecond : source.Base} (baseArrow : baseFirst ⟶ baseSecond)
    {first second : source.Total} (arrow : first ⟶ second)
    [source.functor.IsHomLift baseArrow arrow] :
    target.functor.IsHomLift (route.square.right.toFunctor.map baseArrow)
      (route.square.left.toFunctor.map arrow) := by
  subst_hom_lift source.functor baseArrow arrow
  exact IsHomLift.of_fac target.functor _ _
    (Functor.congr_obj (projection_square route) first).symm
    (Functor.congr_obj (projection_square route) second).symm
    (Functor.congr_hom (projection_square route) arrow)

/-- Cartesian preservation holds over every supplied named base arrow.
The theorem retains the full universal property through the same square. -/
theorem map_lifted_cartesian {source target : Fibration.{u,v}} (route : source ⟶ target)
    {baseFirst baseSecond : source.Base} (baseArrow : baseFirst ⟶ baseSecond)
    {first second : source.Total} (arrow : first ⟶ second)
    [source.functor.IsCartesian baseArrow arrow] :
    target.functor.IsCartesian (route.square.right.toFunctor.map baseArrow)
      (route.square.left.toFunctor.map arrow) := by
  subst_hom_lift source.functor baseArrow arrow
  let := map_cartesian route arrow
  let := map_homLift route (source.functor.map arrow) arrow
  exact cartesian_of_homLift target.functor _ _

theorem map_lifted_stronglyCartesian {source target : Fibration.{u,v}}
    (route : source ⟶ target)
    {baseFirst baseSecond : source.Base} (baseArrow : baseFirst ⟶ baseSecond)
    {first second : source.Total} (arrow : first ⟶ second)
    [source.functor.IsCartesian baseArrow arrow] :
    target.functor.IsStronglyCartesian (route.square.right.toFunctor.map baseArrow)
      (route.square.left.toFunctor.map arrow) := by
  let := map_lifted_cartesian route baseArrow arrow
  infer_instance

end Fibration
end Mettapedia.CategoryTheory.FibrationTwoCategory
