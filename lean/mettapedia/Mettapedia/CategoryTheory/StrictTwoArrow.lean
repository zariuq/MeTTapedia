import Mettapedia.CategoryTheory.StrictTwoCoslice

/-!
# The strict arrow two-category

Objects are arrows of a strict two-category. One-cells are strictly
commuting squares, and two-cells are pairs of actual endpoint two-cells
whose whiskerings agree across that square. In particular, neither a
lax commuting cell nor a freely chosen square comparison is admitted.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B] [Bicategory.Strict B]

structure StrictTwoArrow where
  source : B
  target : B
  arrow : source ⟶ target

namespace StrictTwoArrow

variable {B}

@[ext] structure Hom (source target : StrictTwoArrow B) where
  left : source.source ⟶ target.source
  right : source.target ⟶ target.target
  comm : source.arrow ≫ right = left ≫ target.arrow

instance categoryStruct : CategoryStruct (StrictTwoArrow B) where
  Hom := Hom
  id source := ⟨𝟙 source.source, 𝟙 source.target, by simp⟩
  comp {source middle target} first second := ⟨first.left ≫ second.left,
    first.right ≫ second.right, by
      calc
        source.arrow ≫ (first.right ≫ second.right) =
            (source.arrow ≫ first.right) ≫ second.right :=
          (_root_.CategoryTheory.Category.assoc _ _ _).symm
        _ = (first.left ≫ middle.arrow) ≫ second.right := by rw [first.comm]
        _ = first.left ≫ (middle.arrow ≫ second.right) :=
          _root_.CategoryTheory.Category.assoc _ _ _
        _ = first.left ≫ (second.left ≫ target.arrow) := by rw [second.comm]
        _ = (first.left ≫ second.left) ≫ target.arrow :=
          (_root_.CategoryTheory.Category.assoc _ _ _).symm⟩

instance category : Category (StrictTwoArrow B) where
  id_comp := by intros; apply Hom.ext <;> exact _root_.CategoryTheory.Category.id_comp _
  comp_id := by intros; apply Hom.ext <;> exact _root_.CategoryTheory.Category.comp_id _
  assoc := by intros; apply Hom.ext <;> exact _root_.CategoryTheory.Category.assoc _ _ _

structure Cell {source target : StrictTwoArrow B} (first second : source ⟶ target) where
  left : first.left ⟶ second.left
  right : first.right ⟶ second.right
  compatible : HEq (source.arrow ◁ right) (left ▷ target.arrow)

@[ext] theorem Cell.ext {source target : StrictTwoArrow B}
    {first second : source ⟶ target} {earlier later : Cell first second}
    (left : earlier.left = later.left) (right : earlier.right = later.right) :
    earlier = later := by
  cases earlier
  cases later
  cases left
  cases right
  rfl

instance homCategory (source target : StrictTwoArrow B) : Category (source ⟶ target) where
  Hom := Cell
  id first := ⟨𝟙 first.left, 𝟙 first.right, by
    rw [whiskerLeft_id, id_whiskerRight]
    exact congr_arg_heq (fun arrow => 𝟙 arrow) first.comm⟩
  comp {first second third} earlier later :=
    ⟨earlier.left ≫ later.left, earlier.right ≫ later.right, by
      rw [whiskerLeft_comp, comp_whiskerRight]
      exact heq_comp first.comm second.comm third.comm earlier.compatible later.compatible⟩
  id_comp := by intros; apply Cell.ext <;> exact _root_.CategoryTheory.Category.id_comp _
  comp_id := by intros; apply Cell.ext <;> exact _root_.CategoryTheory.Category.comp_id _
  assoc := by intros; apply Cell.ext <;> exact _root_.CategoryTheory.Category.assoc _ _ _

@[simp] theorem id_left (source : StrictTwoArrow B) :
    (𝟙 source : source ⟶ source).left = 𝟙 source.source := rfl
@[simp] theorem id_right (source : StrictTwoArrow B) :
    (𝟙 source : source ⟶ source).right = 𝟙 source.target := rfl
@[simp] theorem comp_left {source middle target : StrictTwoArrow B}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).left = first.left ≫ second.left := rfl
@[simp] theorem comp_right {source middle target : StrictTwoArrow B}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).right = first.right ≫ second.right := rfl
@[simp] theorem cell_id_left {source target : StrictTwoArrow B} (first : source ⟶ target) :
    (𝟙 first : first ⟶ first).left = 𝟙 first.left := rfl
@[simp] theorem cell_id_right {source target : StrictTwoArrow B} (first : source ⟶ target) :
    (𝟙 first : first ⟶ first).right = 𝟙 first.right := rfl
@[simp] theorem cell_comp_left {source target : StrictTwoArrow B}
    {first second third : source ⟶ target} (earlier : first ⟶ second) (later : second ⟶ third) :
    (earlier ≫ later).left = earlier.left ≫ later.left := rfl
@[simp] theorem cell_comp_right {source target : StrictTwoArrow B}
    {first second third : source ⟶ target} (earlier : first ⟶ second) (later : second ⟶ third) :
    (earlier ≫ later).right = earlier.right ≫ later.right := rfl
@[simp] theorem eqToHom_left {source target : StrictTwoArrow B}
    {first second : source ⟶ target} (same : first = second) :
    (eqToHom same).left = eqToHom (congrArg Hom.left same) := by cases same; rfl
@[simp] theorem eqToHom_right {source target : StrictTwoArrow B}
    {first second : source ⟶ target} (same : first = second) :
    (eqToHom same).right = eqToHom (congrArg Hom.right same) := by cases same; rfl

def whiskerLeft {source middle target : StrictTwoArrow B}
    (first : source ⟶ middle) {earlier later : middle ⟶ target}
    (change : earlier ⟶ later) : first ≫ earlier ⟶ first ≫ later where
  left := first.left ◁ change.left
  right := first.right ◁ change.right
  compatible :=
    (StrictTwoWhiskering.left_assoc source.arrow first.right change.right).symm.trans
      ((StrictTwoWhiskering.left_heq first.comm rfl rfl HEq.rfl).trans
        ((StrictTwoWhiskering.left_assoc first.left middle.arrow change.right).trans
          ((StrictTwoWhiskering.left_heq rfl earlier.comm later.comm change.compatible).trans
            (StrictTwoWhiskering.mixed_assoc first.left change.left target.arrow).symm)))

def whiskerRight {source middle target : StrictTwoArrow B}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later)
    (last : middle ⟶ target) : earlier ≫ last ⟶ later ≫ last where
  left := change.left ▷ last.left
  right := change.right ▷ last.right
  compatible :=
    (StrictTwoWhiskering.mixed_assoc source.arrow change.right last.right).symm.trans
      ((StrictTwoWhiskering.right_heq earlier.comm later.comm change.compatible rfl).trans
        ((StrictTwoWhiskering.right_assoc change.left middle.arrow last.right).symm.trans
          ((StrictTwoWhiskering.right_heq rfl rfl HEq.rfl last.comm).trans
            (StrictTwoWhiskering.right_assoc change.left last.left target.arrow))))

@[simp] theorem whiskerLeft_left {source middle target : StrictTwoArrow B}
    (first : source ⟶ middle) {earlier later : middle ⟶ target} (change : earlier ⟶ later) :
    (whiskerLeft first change).left = first.left ◁ change.left := rfl
@[simp] theorem whiskerLeft_right {source middle target : StrictTwoArrow B}
    (first : source ⟶ middle) {earlier later : middle ⟶ target} (change : earlier ⟶ later) :
    (whiskerLeft first change).right = first.right ◁ change.right := rfl
@[simp] theorem whiskerRight_left {source middle target : StrictTwoArrow B}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later) (last : middle ⟶ target) :
    (whiskerRight change last).left = change.left ▷ last.left := rfl
@[simp] theorem whiskerRight_right {source middle target : StrictTwoArrow B}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later) (last : middle ⟶ target) :
    (whiskerRight change last).right = change.right ▷ last.right := rfl

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

instance bicategory : Bicategory (StrictTwoArrow B) where
  toCategoryStruct := categoryStruct
  homCategory := homCategory
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator first second third := eqToIso (_root_.CategoryTheory.Category.assoc first second third)
  leftUnitor first := eqToIso (_root_.CategoryTheory.Category.id_comp first)
  rightUnitor first := eqToIso (_root_.CategoryTheory.Category.comp_id first)
  whiskerLeft_id := by intros; apply Cell.ext <;> simp
  whiskerLeft_comp := by intros; apply Cell.ext <;> simp
  id_whiskerLeft := by intros; apply Cell.ext <;> simp
  comp_whiskerLeft := by intros; apply Cell.ext <;> simp
  id_whiskerRight := by intros; apply Cell.ext <;> simp
  comp_whiskerRight := by intros; apply Cell.ext <;> simp
  whiskerRight_id := by intros; apply Cell.ext <;> simp
  whiskerRight_comp := by intros; apply Cell.ext <;> simp
  whisker_assoc := by intros; apply Cell.ext <;> simp
  whisker_exchange := by
    intros; apply Cell.ext <;>
      simpa using _root_.CategoryTheory.Bicategory.whisker_exchange _ _
  pentagon := by intros; apply Cell.ext <;> simp
  triangle := by intros; apply Cell.ext <;> simp

instance strict : Bicategory.Strict (StrictTwoArrow B) where
  id_comp := _root_.CategoryTheory.Category.id_comp
  comp_id := _root_.CategoryTheory.Category.comp_id
  assoc := _root_.CategoryTheory.Category.assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

@[simp] theorem left_whisker_left {source middle target : StrictTwoArrow B}
    (first : source ⟶ middle) {earlier later : middle ⟶ target} (change : earlier ⟶ later) :
    (first ◁ change).left = first.left ◁ change.left := rfl
@[simp] theorem left_whisker_right {source middle target : StrictTwoArrow B}
    (first : source ⟶ middle) {earlier later : middle ⟶ target} (change : earlier ⟶ later) :
    (first ◁ change).right = first.right ◁ change.right := rfl
@[simp] theorem right_whisker_left {source middle target : StrictTwoArrow B}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later) (last : middle ⟶ target) :
    (change ▷ last).left = change.left ▷ last.left := rfl
@[simp] theorem right_whisker_right {source middle target : StrictTwoArrow B}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later) (last : middle ⟶ target) :
    (change ▷ last).right = change.right ▷ last.right := rfl

def domain : StrictPseudofunctor (StrictTwoArrow B) B :=
  StrictPseudofunctor.mk'' {
    obj source := source.source
    map route := route.left
    map₂ change := change.left
    map₂_whisker_left := by intros; simp
    map₂_whisker_right := by intros; simp }

def codomain : StrictPseudofunctor (StrictTwoArrow B) B :=
  StrictPseudofunctor.mk'' {
    obj source := source.target
    map route := route.right
    map₂ change := change.right
    map₂_whisker_left := by intros; simp
    map₂_whisker_right := by intros; simp }

/-- The compatibility square, expressed without heterogeneous notation. -/
theorem compatible_square {source target : StrictTwoArrow B}
    {first second : source ⟶ target} (change : first ⟶ second) :
    source.arrow ◁ change.right ≫ eqToHom second.comm =
      eqToHom first.comm ≫ change.left ▷ target.arrow := by
  exact (comp_eqToHom_iff second.comm _ _).mpr
    (by simpa only [_root_.CategoryTheory.Category.assoc] using
      (conj_eqToHom_iff_heq _ _ first.comm second.comm).mpr change.compatible)

end StrictTwoArrow
end Mettapedia.CategoryTheory
