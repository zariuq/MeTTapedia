import Mettapedia.CategoryTheory.StrictTwoWhiskering

/-!
# The strict coslice two-category

A one-cell is a strictly commuting triangle. Its two-cells are the actual
two-cells between the outgoing legs whose restriction to the fixed base
is the identity. The latter condition distinguishes the strict coslice
from a lax or pseudo coslice.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B] [Bicategory.Strict B]

structure StrictTwoCoslice (base : B) where
  target : B
  leg : base ⟶ target

namespace StrictTwoCoslice

variable {B} {base : B}

@[ext] structure Hom (source target : StrictTwoCoslice B base) where
  hom : source.target ⟶ target.target
  comm : source.leg ≫ hom = target.leg

instance categoryStruct : CategoryStruct (StrictTwoCoslice B base) where
  Hom := Hom
  id source := ⟨𝟙 source.target, _root_.CategoryTheory.Category.comp_id _⟩
  comp first second := ⟨first.hom ≫ second.hom, by
    rw [← _root_.CategoryTheory.Category.assoc, first.comm, second.comm]⟩

instance category : Category (StrictTwoCoslice B base) where
  id_comp := by intros; apply Hom.ext; exact _root_.CategoryTheory.Category.id_comp _
  comp_id := by intros; apply Hom.ext; exact _root_.CategoryTheory.Category.comp_id _
  assoc := by intros; apply Hom.ext; exact _root_.CategoryTheory.Category.assoc _ _ _

structure Cell {source target : StrictTwoCoslice B base} (first second : source ⟶ target) where
  hom : first.hom ⟶ second.hom
  fixed : HEq (source.leg ◁ hom) (𝟙 target.leg)

@[ext] theorem Cell.ext {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target} {earlier later : Cell first second}
    (same : earlier.hom = later.hom) : earlier = later := by
  cases earlier
  cases later
  cases same
  rfl

instance homCategory (source target : StrictTwoCoslice B base) : Category (source ⟶ target) where
  Hom := Cell
  id first := ⟨𝟙 first.hom, by
    rw [whiskerLeft_id]
    exact congr_arg_heq (fun leg => 𝟙 leg) first.comm⟩
  comp {first second third} earlier later := ⟨earlier.hom ≫ later.hom, by
    rw [whiskerLeft_comp]
    exact (heq_comp first.comm second.comm third.comm earlier.fixed later.fixed).trans
      (heq_of_eq (_root_.CategoryTheory.Category.id_comp (𝟙 target.leg)))⟩
  id_comp := by intros; apply Cell.ext; exact _root_.CategoryTheory.Category.id_comp _
  comp_id := by intros; apply Cell.ext; exact _root_.CategoryTheory.Category.comp_id _
  assoc := by intros; apply Cell.ext; exact _root_.CategoryTheory.Category.assoc _ _ _

@[simp] theorem id_hom (source : StrictTwoCoslice B base) :
    (𝟙 source : source ⟶ source).hom = 𝟙 source.target := rfl

@[simp] theorem comp_hom {source middle target : StrictTwoCoslice B base}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).hom = first.hom ≫ second.hom := rfl

@[simp] theorem cell_id_hom {source target : StrictTwoCoslice B base}
    (first : source ⟶ target) : (𝟙 first : first ⟶ first).hom = 𝟙 first.hom := rfl

@[simp] theorem cell_comp_hom {source target : StrictTwoCoslice B base}
    {first second third : source ⟶ target} (earlier : first ⟶ second) (later : second ⟶ third) :
    (earlier ≫ later).hom = earlier.hom ≫ later.hom := rfl

@[simp] theorem eqToHom_hom {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target} (same : first = second) :
    (eqToHom same).hom = eqToHom (congrArg Hom.hom same) := by
  cases same
  rfl

def whiskerLeft {source middle target : StrictTwoCoslice B base}
    (first : source ⟶ middle) {earlier later : middle ⟶ target}
    (change : earlier ⟶ later) : first ≫ earlier ⟶ first ≫ later where
  hom := first.hom ◁ change.hom
  fixed := (StrictTwoWhiskering.left_assoc source.leg first.hom change.hom).symm.trans
    ((StrictTwoWhiskering.left_heq first.comm rfl rfl HEq.rfl).trans change.fixed)

def whiskerRight {source middle target : StrictTwoCoslice B base}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later)
    (last : middle ⟶ target) : earlier ≫ last ⟶ later ≫ last where
  hom := change.hom ▷ last.hom
  fixed := (StrictTwoWhiskering.mixed_assoc source.leg change.hom last.hom).symm.trans
    ((StrictTwoWhiskering.right_heq earlier.comm later.comm change.fixed rfl).trans
      ((heq_of_eq (id_whiskerRight middle.leg last.hom)).trans
        (congr_arg_heq (fun leg => 𝟙 leg) last.comm)))

@[simp] theorem whiskerLeft_hom {source middle target : StrictTwoCoslice B base}
    (first : source ⟶ middle) {earlier later : middle ⟶ target} (change : earlier ⟶ later) :
    (whiskerLeft first change).hom = first.hom ◁ change.hom := rfl

@[simp] theorem whiskerRight_hom {source middle target : StrictTwoCoslice B base}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later) (last : middle ⟶ target) :
    (whiskerRight change last).hom = change.hom ▷ last.hom := rfl

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

instance bicategory : Bicategory (StrictTwoCoslice B base) where
  toCategoryStruct := categoryStruct
  homCategory := homCategory
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator first second third := eqToIso (_root_.CategoryTheory.Category.assoc first second third)
  leftUnitor first := eqToIso (_root_.CategoryTheory.Category.id_comp first)
  rightUnitor first := eqToIso (_root_.CategoryTheory.Category.comp_id first)
  whiskerLeft_id := by intros; apply Cell.ext; simp
  whiskerLeft_comp := by intros; apply Cell.ext; simp
  id_whiskerLeft := by
    intros; apply Cell.ext
    simp
  comp_whiskerLeft := by
    intros; apply Cell.ext
    simp
  id_whiskerRight := by intros; apply Cell.ext; simp
  comp_whiskerRight := by intros; apply Cell.ext; simp
  whiskerRight_id := by
    intros; apply Cell.ext
    simp
  whiskerRight_comp := by
    intros; apply Cell.ext
    simp
  whisker_assoc := by
    intros; apply Cell.ext
    simp
  whisker_exchange := by
    intros; apply Cell.ext
    simpa using _root_.CategoryTheory.Bicategory.whisker_exchange _ _
  pentagon := by
    intros; apply Cell.ext
    simp
  triangle := by
    intros; apply Cell.ext
    simp

@[simp] theorem left_whisker_hom {source middle target : StrictTwoCoslice B base}
    (first : source ⟶ middle) {earlier later : middle ⟶ target} (change : earlier ⟶ later) :
    (first ◁ change).hom = first.hom ◁ change.hom := rfl

@[simp] theorem right_whisker_hom {source middle target : StrictTwoCoslice B base}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later) (last : middle ⟶ target) :
    (change ▷ last).hom = change.hom ▷ last.hom := rfl

instance strict : Bicategory.Strict (StrictTwoCoslice B base) where
  id_comp := _root_.CategoryTheory.Category.id_comp
  comp_id := _root_.CategoryTheory.Category.comp_id
  assoc := _root_.CategoryTheory.Category.assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

def forget : StrictPseudofunctor (StrictTwoCoslice B base) B :=
  StrictPseudofunctor.mk'' {
    obj source := source.target
    map route := route.hom
    map₂ change := change.hom
    map₂_whisker_left := by intros; simp
    map₂_whisker_right := by intros; simp }

/-- Identity restriction, in an ordinary equality with all endpoint transports visible. -/
theorem fixed_base {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target} (change : first ⟶ second) :
    source.leg ◁ change.hom = eqToHom first.comm ≫ eqToHom second.comm.symm := by
  simpa using (conj_eqToHom_iff_heq (source.leg ◁ change.hom) (𝟙 target.leg)
    first.comm second.comm).mpr change.fixed

end StrictTwoCoslice
end Mettapedia.CategoryTheory
