import Mettapedia.CategoryTheory.InternalCategory
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Internal categories from complete category-valued diagrams

Both objects and the total space of arrows are actual functors. The
composition arrow is constructed on the chosen presheaf pullback; matching
endpoints are read from its complete cone equation. All internal category
laws follow from the supplied diagram's ordinary categorical laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryDiagram

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {B : Type u} [Category.{v} B]

abbrev Arrow (D : Cat.{w,w}) := (source : D) × (target : D) × (source ⟶ target)

namespace Arrow

variable {D E : Cat.{w,w}}

def source (arrow : Arrow D) : D := arrow.1
def target (arrow : Arrow D) : D := arrow.2.1

def map (F : D ⥤ E) (arrow : Arrow D) : Arrow E :=
  ⟨F.obj arrow.1, F.obj arrow.2.1, F.map arrow.2.2⟩

def unit (object : D) : Arrow D := ⟨object, object, 𝟙 object⟩

def compose (first second : Arrow D) (matching : target first = source second) : Arrow D :=
  ⟨first.1, second.2.1, first.2.2 ≫ eqToHom matching ≫ second.2.2⟩

theorem compose_congr {first first' second second' : Arrow D}
    (firstEq : first = first') (secondEq : second = second')
    (matching : target first = source second) (matching' : target first' = source second') :
    compose first second matching = compose first' second' matching' := by
  subst first'
  subst second'
  rfl

@[simp] theorem map_id (arrow : Arrow D) : map (𝟭 D) arrow = arrow := rfl

@[simp] theorem map_comp (F : D ⥤ E) {K : Cat.{w,w}} (G : E ⥤ K) (arrow : Arrow D) :
    map (F ⋙ G) arrow = map G (map F arrow) := rfl

@[simp] theorem map_unit (F : D ⥤ E) (object : D) :
    map F (unit object) = unit (F.obj object) := by
  dsimp only [map, unit]
  rw [F.map_id]

theorem map_compose (F : D ⥤ E) (first second : Arrow D)
    (matching : target first = source second) :
    map F (compose first second matching) =
      compose (map F first) (map F second) (congrArg F.obj matching) := by
  rcases first with ⟨firstSource, firstTarget, firstArrow⟩
  rcases second with ⟨secondSource, secondTarget, secondArrow⟩
  change firstTarget = secondSource at matching
  subst secondSource
  dsimp only [map, compose]
  simp only [eqToHom_refl, Category.id_comp, Functor.map_comp]

@[simp] theorem compose_source (first second : Arrow D)
    (matching : target first = source second) : source (compose first second matching) = source first := rfl

@[simp] theorem compose_target (first second : Arrow D)
    (matching : target first = source second) : target (compose first second matching) = target second := rfl

@[simp] theorem unit_left (arrow : Arrow D) : compose (unit (source arrow)) arrow rfl = arrow := by
  rcases arrow with ⟨source, target, arrow⟩
  dsimp only [compose, unit, Arrow.source]
  simp only [eqToHom_refl, Category.id_comp]

@[simp] theorem unit_right (arrow : Arrow D) : compose arrow (unit (target arrow)) rfl = arrow := by
  rcases arrow with ⟨source, target, arrow⟩
  dsimp only [compose, unit, Arrow.target]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem compose_assoc (first second third : Arrow D)
    (firstMatch : target first = source second) (secondMatch : target second = source third) :
    compose (compose first second firstMatch) third secondMatch =
      compose first (compose second third secondMatch) firstMatch := by
  rcases first with ⟨firstSource, firstTarget, firstArrow⟩
  rcases second with ⟨secondSource, secondTarget, secondArrow⟩
  rcases third with ⟨thirdSource, thirdTarget, thirdArrow⟩
  change firstTarget = secondSource at firstMatch
  change secondTarget = thirdSource at secondMatch
  subst secondSource
  subst thirdSource
  dsimp only [compose]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc]

end Arrow

variable (diagram : B ⥤ Cat.{w,w})

def vertices : B ⥤ Type w where
  obj X := diagram.obj X
  map f := TypeCat.ofHom (diagram.map f).toFunctor.obj
  map_id X := by
    have same := congrArg Cat.Hom.toFunctor (diagram.map_id X)
    apply ConcreteCategory.hom_ext
    intro object
    exact congrArg (fun F => F.obj object) same
  map_comp f g := by
    have same := congrArg Cat.Hom.toFunctor (diagram.map_comp f g)
    apply ConcreteCategory.hom_ext
    intro object
    exact congrArg (fun F => F.obj object) same

def arrows : B ⥤ Type w where
  obj X := Arrow (diagram.obj X)
  map f := TypeCat.ofHom (Arrow.map (diagram.map f).toFunctor)
  map_id X := by
    have same := congrArg Cat.Hom.toFunctor (diagram.map_id X)
    apply ConcreteCategory.hom_ext
    intro arrow
    rw [show (diagram.map (𝟙 X)).toFunctor = 𝟭 (diagram.obj X) from same]
    rfl
  map_comp f g := by
    have same := congrArg Cat.Hom.toFunctor (diagram.map_comp f g)
    apply ConcreteCategory.hom_ext
    intro arrow
    change Arrow.map (diagram.map (f ≫ g)).toFunctor arrow =
      Arrow.map (diagram.map g).toFunctor (Arrow.map (diagram.map f).toFunctor arrow)
    rw [show (diagram.map (f ≫ g)).toFunctor =
      (diagram.map f).toFunctor ⋙ (diagram.map g).toFunctor from same]
    rfl

def source : arrows diagram ⟶ vertices diagram where
  app _ := TypeCat.ofHom Arrow.source
  naturality _ _ _ := rfl

def target : arrows diagram ⟶ vertices diagram where
  app _ := TypeCat.ofHom Arrow.target
  naturality _ _ _ := rfl

def unit : vertices diagram ⟶ arrows diagram where
  app X := TypeCat.ofHom Arrow.unit
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro object
    exact (Arrow.map_unit (diagram.map f).toFunctor object).symm

def graph : InternalGraph (B ⥤ Type w) :=
  ⟨vertices diagram, arrows diagram, source diagram, target diagram⟩

abbrev Pairs := pullback (target diagram) (source diagram)

def first (X : B) (pair : (Pairs diagram).obj X) : Arrow (diagram.obj X) :=
  (pullback.fst (target diagram) (source diagram)).app X pair

def second (X : B) (pair : (Pairs diagram).obj X) : Arrow (diagram.obj X) :=
  (pullback.snd (target diagram) (source diagram)).app X pair

theorem matching (X : B) (pair : (Pairs diagram).obj X) :
    Arrow.target (first diagram X pair) = Arrow.source (second diagram X pair) :=
  congrArg (fun (map : Pairs diagram ⟶ vertices diagram) => map.app X pair)
    (pullback.condition (f := target diagram) (g := source diagram))

def composition : Pairs diagram ⟶ arrows diagram where
  app X := TypeCat.ofHom (fun pair =>
    Arrow.compose (first diagram X pair) (second diagram X pair) (matching diagram X pair))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro pair
    have firstRead := NatTrans.naturality_apply
      (pullback.fst (target diagram) (source diagram)) f pair
    have secondRead := NatTrans.naturality_apply
      (pullback.snd (target diagram) (source diagram)) f pair
    change first diagram Y ((Pairs diagram).map f pair) =
      Arrow.map (diagram.map f).toFunctor (first diagram X pair) at firstRead
    change second diagram Y ((Pairs diagram).map f pair) =
      Arrow.map (diagram.map f).toFunctor (second diagram X pair) at secondRead
    change Arrow.compose (first diagram Y ((Pairs diagram).map f pair))
        (second diagram Y ((Pairs diagram).map f pair)) _ =
      Arrow.map (diagram.map f).toFunctor
        (Arrow.compose (first diagram X pair) (second diagram X pair) _)
    exact (Arrow.compose_congr firstRead secondRead _ _).trans
      (Arrow.map_compose (diagram.map f).toFunctor _ _ _).symm

theorem composeWith_apply {X : B ⥤ Type w} (left right : X ⟶ arrows diagram)
    (match_ : left ≫ target diagram = right ≫ source diagram) (stage : B) (value : X.obj stage) :
    ((graph diagram).composeWith (composition diagram) left right match_).app stage value =
      Arrow.compose (left.app stage value) (right.app stage value)
        (congrArg (fun (map : X ⟶ vertices diagram) => map.app stage value) match_) := by
  have firstRead := congrArg (fun (map : X ⟶ arrows diagram) => map.app stage value)
    (pullback.lift_fst left right match_)
  have secondRead := congrArg (fun (map : X ⟶ arrows diagram) => map.app stage value)
    (pullback.lift_snd left right match_)
  change Arrow.compose
    (first diagram stage ((pullback.lift left right match_).app stage value))
    (second diagram stage ((pullback.lift left right match_).app stage value)) _ = _
  exact Arrow.compose_congr
    (show first diagram stage ((pullback.lift left right match_).app stage value) =
      left.app stage value from firstRead)
    (show second diagram stage ((pullback.lift left right match_).app stage value) =
      right.app stage value from secondRead) _ _

/-- The complete internal category, with its actual presheaf pullback domain. -/
def category : InternalCategory (B ⥤ Type w) where
  toInternalGraph := graph diagram
  unit := unit diagram
  composition := composition diagram
  unit_source := by ext X value; rfl
  unit_target := by ext X value; rfl
  composition_source := by ext X value; rfl
  composition_target := by ext X value; rfl
  unit_left := by
    ext X arrow
    exact (composeWith_apply diagram _ _ _ X arrow).trans (Arrow.unit_left arrow)
  unit_right := by
    ext X arrow
    exact (composeWith_apply diagram _ _ _ X arrow).trans (Arrow.unit_right arrow)
  associativity := by
    intro X first second third firstMatch secondMatch
    ext stage value
    have firstRead := composeWith_apply diagram first second firstMatch stage value
    have secondRead := composeWith_apply diagram second third secondMatch stage value
    have firstValueMatch := congrArg
      (fun (map : X ⟶ vertices diagram) => map.app stage value) firstMatch
    have secondValueMatch := congrArg
      (fun (map : X ⟶ vertices diagram) => map.app stage value) secondMatch
    exact (composeWith_apply diagram _ _ _ stage value).trans
      ((Arrow.compose_congr firstRead rfl _ _).trans
        ((Arrow.compose_assoc _ _ _ firstValueMatch secondValueMatch).trans
          ((Arrow.compose_congr rfl secondRead.symm _ _).trans
            (composeWith_apply diagram _ _ _ stage value).symm)))

end Mettapedia.CategoryTheory.InternalCategoryDiagram
