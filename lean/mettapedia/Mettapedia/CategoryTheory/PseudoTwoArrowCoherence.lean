import Mettapedia.CategoryTheory.PseudoTwoArrow

/-!
# Pasting of invertibly commuting squares

The endpoint whiskerings and structural isomorphisms retain the complete
comparison square. Their coherence gives a bicategory of actual arrow
objects and invertibly commuting squares.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PseudoTwoArrow

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u
variable {B : Type u} [Bicategory.{w,v} B]

def whiskerLeft {source middle target : PseudoTwoArrow B}
    (route : source ⟶ middle) {first second : middle ⟶ target} (change : first ⟶ second) :
    route ≫ first ⟶ route ≫ second where
  left := route.left ◁ change.left
  right := route.right ◁ change.right
  compatible := by
    change source.arrow ◁ (route.right ◁ change.right) ≫
        rightAdjointSquare.vcomp route.comm.hom second.comm.hom =
      rightAdjointSquare.vcomp route.comm.hom first.comm.hom ≫
        (route.left ◁ change.left) ▷ target.arrow
    calc
      _ = 𝟙 _ ⊗≫
          ((source.arrow ≫ route.right) ◁ change.right ≫
            route.comm.hom ▷ second.right) ⊗≫
          route.left ◁ second.comm.hom ⊗≫ 𝟙 _ := by
        dsimp only [rightAdjointSquare.vcomp]
        bicategory
      _ = (α_ source.arrow route.right first.right).inv ≫
          route.comm.hom ▷ first.right ≫ (α_ route.left middle.arrow first.right).hom ≫
          route.left ◁ (middle.arrow ◁ change.right ≫ second.comm.hom) ≫
          (α_ route.left second.left target.arrow).inv := by
        rw [whiskerLeft_comp]
        rw [whisker_exchange]
        bicategory
      _ = (α_ source.arrow route.right first.right).inv ≫
          route.comm.hom ▷ first.right ≫ (α_ route.left middle.arrow first.right).hom ≫
          route.left ◁ (first.comm.hom ≫ change.left ▷ target.arrow) ≫
          (α_ route.left second.left target.arrow).inv := by rw [change.compatible]
      _ = _ := by dsimp only [rightAdjointSquare.vcomp]; rw [whiskerLeft_comp]; bicategory

def whiskerRight {source middle target : PseudoTwoArrow B}
    {first second : source ⟶ middle} (change : first ⟶ second) (route : middle ⟶ target) :
    first ≫ route ⟶ second ≫ route where
  left := change.left ▷ route.left
  right := change.right ▷ route.right
  compatible := by
    change source.arrow ◁ (change.right ▷ route.right) ≫
        rightAdjointSquare.vcomp second.comm.hom route.comm.hom =
      rightAdjointSquare.vcomp first.comm.hom route.comm.hom ≫
        (change.left ▷ route.left) ▷ target.arrow
    calc
      _ = (α_ source.arrow first.right route.right).inv ≫
          (source.arrow ◁ change.right ≫ second.comm.hom) ▷ route.right ≫
          (α_ second.left middle.arrow route.right).hom ≫
          second.left ◁ route.comm.hom ≫ (α_ second.left route.left target.arrow).inv := by
        dsimp only [rightAdjointSquare.vcomp]
        rw [comp_whiskerRight]
        bicategory
      _ = (α_ source.arrow first.right route.right).inv ≫
          (first.comm.hom ≫ change.left ▷ middle.arrow) ▷ route.right ≫
          (α_ second.left middle.arrow route.right).hom ≫
          second.left ◁ route.comm.hom ≫ (α_ second.left route.left target.arrow).inv := by
        rw [change.compatible]
      _ = _ := by
        dsimp only [rightAdjointSquare.vcomp]
        calc
          _ = 𝟙 _ ⊗≫ first.comm.hom ▷ route.right ⊗≫
              (change.left ▷ (middle.arrow ≫ route.right) ≫
                second.left ◁ route.comm.hom) ⊗≫ 𝟙 _ := by
            rw [comp_whiskerRight]
            bicategory
          _ = _ := by rw [← whisker_exchange]; bicategory

@[simp] theorem whiskerLeft_left {source middle target : PseudoTwoArrow B}
    (route : source ⟶ middle) {first second : middle ⟶ target} (change : first ⟶ second) :
    (whiskerLeft route change).left = route.left ◁ change.left := rfl
@[simp] theorem whiskerLeft_right {source middle target : PseudoTwoArrow B}
    (route : source ⟶ middle) {first second : middle ⟶ target} (change : first ⟶ second) :
    (whiskerLeft route change).right = route.right ◁ change.right := rfl
@[simp] theorem whiskerRight_left {source middle target : PseudoTwoArrow B}
    {first second : source ⟶ middle} (change : first ⟶ second) (route : middle ⟶ target) :
    (whiskerRight change route).left = change.left ▷ route.left := rfl
@[simp] theorem whiskerRight_right {source middle target : PseudoTwoArrow B}
    {first second : source ⟶ middle} (change : first ⟶ second) (route : middle ⟶ target) :
    (whiskerRight change route).right = change.right ▷ route.right := rfl

def isoMk {source target : PseudoTwoArrow B} {first second : source ⟶ target}
    (left : first.left ≅ second.left) (right : first.right ≅ second.right)
    (compatible : source.arrow ◁ right.hom ≫ second.comm.hom =
      first.comm.hom ≫ left.hom ▷ target.arrow) : first ≅ second where
  hom := ⟨left.hom, right.hom, compatible⟩
  inv := ⟨left.inv, right.inv, by
    apply (cancel_epi (source.arrow ◁ right.hom)).mp
    rw [← Category.assoc, ← whiskerLeft_comp, right.hom_inv_id, whiskerLeft_id,
      Category.id_comp, ← Category.assoc, compatible, Category.assoc,
      ← comp_whiskerRight, left.hom_inv_id, id_whiskerRight, Category.comp_id]⟩
  hom_inv_id := by apply Cell.ext <;> simp
  inv_hom_id := by apply Cell.ext <;> simp

@[simp] theorem isoMk_hom_left {source target : PseudoTwoArrow B}
    {first second : source ⟶ target} (left : first.left ≅ second.left)
    (right : first.right ≅ second.right) (compatible) :
    (isoMk left right compatible).hom.left = left.hom := rfl
@[simp] theorem isoMk_hom_right {source target : PseudoTwoArrow B}
    {first second : source ⟶ target} (left : first.left ≅ second.left)
    (right : first.right ≅ second.right) (compatible) :
    (isoMk left right compatible).hom.right = right.hom := rfl
@[simp] theorem isoMk_inv_left {source target : PseudoTwoArrow B}
    {first second : source ⟶ target} (left : first.left ≅ second.left)
    (right : first.right ≅ second.right) (compatible) :
    (isoMk left right compatible).inv.left = left.inv := rfl
@[simp] theorem isoMk_inv_right {source target : PseudoTwoArrow B}
    {first second : source ⟶ target} (left : first.left ≅ second.left)
    (right : first.right ≅ second.right) (compatible) :
    (isoMk left right compatible).inv.right = right.inv := rfl

def associator {a b c d : PseudoTwoArrow B}
    (first : a ⟶ b) (second : b ⟶ c) (third : c ⟶ d) :
    (first ≫ second) ≫ third ≅ first ≫ (second ≫ third) :=
  isoMk (α_ first.left second.left third.left) (α_ first.right second.right third.right) (by
    simp only [comp_comm_hom, comp_left, comp_right]
    dsimp only [rightAdjointSquare.vcomp]
    bicategory)

def leftUnitor {source target : PseudoTwoArrow B} (route : source ⟶ target) :
    𝟙 source ≫ route ≅ route :=
  isoMk (λ_ route.left) (λ_ route.right) (by
    simp only [comp_comm_hom, id_comm_hom, id_left, id_right]
    dsimp only [rightAdjointSquare.vcomp]
    bicategory)

def rightUnitor {source target : PseudoTwoArrow B} (route : source ⟶ target) :
    route ≫ 𝟙 target ≅ route :=
  isoMk (ρ_ route.left) (ρ_ route.right) (by
    simp only [comp_comm_hom, id_comm_hom, id_left, id_right]
    dsimp only [rightAdjointSquare.vcomp]
    bicategory)

instance bicategory : Bicategory (PseudoTwoArrow B) where
  toCategoryStruct := categoryStruct
  homCategory := homCategory
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id := by intros; apply Cell.ext <;> simp
  whiskerLeft_comp := by intros; apply Cell.ext <;> simp
  id_whiskerLeft := by intros; apply Cell.ext <;> simp [leftUnitor]
  comp_whiskerLeft := by intros; apply Cell.ext <;> simp [associator]
  id_whiskerRight := by intros; apply Cell.ext <;> simp
  comp_whiskerRight := by intros; apply Cell.ext <;> simp
  whiskerRight_id := by intros; apply Cell.ext <;> simp [rightUnitor]
  whiskerRight_comp := by intros; apply Cell.ext <;> simp [associator]
  whisker_assoc := by intros; apply Cell.ext <;> simp [associator]
  whisker_exchange := by
    intros; apply Cell.ext <;>
      simpa using _root_.CategoryTheory.Bicategory.whisker_exchange _ _
  pentagon := by
    intros; apply Cell.ext <;> simp [associator]
  triangle := by
    intros; apply Cell.ext <;> simp [associator, leftUnitor, rightUnitor]

def domain : StrictPseudofunctor (PseudoTwoArrow B) B :=
  StrictPseudofunctor.mk' {
    obj source := source.source
    map route := route.left
    map₂ change := change.left
    map₂_whisker_left := by intros; simp; rfl
    map₂_whisker_right := by intros; simp; rfl
    map₂_left_unitor := by intros; simp; rfl
    map₂_right_unitor := by intros; simp; rfl
    map₂_associator := by intros; simp; rfl }

def codomain : StrictPseudofunctor (PseudoTwoArrow B) B :=
  StrictPseudofunctor.mk' {
    obj source := source.target
    map route := route.right
    map₂ change := change.right
    map₂_whisker_left := by intros; simp; rfl
    map₂_whisker_right := by intros; simp; rfl
    map₂_left_unitor := by intros; simp; rfl
    map₂_right_unitor := by intros; simp; rfl
    map₂_associator := by intros; simp; rfl }

end Mettapedia.CategoryTheory.PseudoTwoArrow
