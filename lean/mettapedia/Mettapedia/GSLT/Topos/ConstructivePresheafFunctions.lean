import Mettapedia.GSLT.Topos.ConstructivePresheafOperations
import Mathlib.CategoryTheory.Functor.FunctorHom
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Constructive function objects of standard presheaves

The sections use Mathlib's `Functor.HomObj` carrier. A section assigns a
function at every future restriction and respects further restriction.
Explicit functor and naturality laws avoid selecting categorical helper
proofs that use classical contradiction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf

open CategoryTheory

universe u
variable {C : Type u} [Category.{u} C]

/-- The covariant representable, with its laws stated directly. -/
def representable (X : C) : C ⥤ Type u where
  obj Y := X ⟶ Y
  map f := TypeCat.ofHom (fun g => g ≫ f)
  map_id Y := by
    apply ConcreteCategory.hom_ext
    intro g
    exact Category.comp_id g
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    exact (Category.assoc h f g).symm

variable (F G : C ⥤ Type u)

abbrev FunctionSection (X : C) := Functor.HomObj F G (representable X)

def FunctionSection.restrict {X Y : C} (f : X ⟶ Y) (value : FunctionSection F G X) :
    FunctionSection F G Y where
  app Z g := value.app Z (f ≫ g)
  naturality {Z W} h g := by
    change Y ⟶ Z at g
    change F.map h ≫ value.app W (f ≫ g ≫ h) = value.app Z (f ≫ g) ≫ G.map h
    rw [← Category.assoc]
    exact value.naturality h (f ≫ g)

theorem FunctionSection.restrict_id {X : C} (value : FunctionSection F G X) :
    FunctionSection.restrict F G (𝟙 X) value = value := by
  apply Functor.HomObj.ext
  funext Y g
  change X ⟶ Y at g
  change value.app Y (𝟙 X ≫ g) = value.app Y g
  rw [Category.id_comp]

theorem FunctionSection.restrict_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (value : FunctionSection F G X) :
    FunctionSection.restrict F G g (FunctionSection.restrict F G f value) =
      FunctionSection.restrict F G (f ≫ g) value := by
  apply Functor.HomObj.ext
  funext W h
  change Z ⟶ W at h
  change value.app W (f ≫ g ≫ h) = value.app W ((f ≫ g) ≫ h)
  rw [Category.assoc]

def functions : C ⥤ Type u where
  obj X := FunctionSection F G X
  map f := TypeCat.ofHom (FunctionSection.restrict F G f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro value
    exact FunctionSection.restrict_id F G value
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (FunctionSection.restrict_comp F G f g value).symm

/-- Evaluation uses the function's component at the current world. -/
def evaluate : NatTrans (FunctorToTypes.prod F (functions F G)) G where
  app X := TypeCat.ofHom (fun pair => pair.2.app X (𝟙 X) pair.1)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, value⟩
    change value.app Y (f ≫ 𝟙 Y) (F.map f x) = G.map f (value.app X (𝟙 X) x)
    rw [Category.comp_id]
    have naturally := congrArg (fun h : F.obj X ⟶ G.obj Y => h x)
      (value.naturality f (𝟙 X))
    change value.app Y (𝟙 X ≫ f) (F.map f x) = _ at naturally
    rw [Category.id_comp] at naturally
    exact naturally

variable {F G} {H : C ⥤ Type u}

/-- Transpose a natural operation; its parameter is carried to every future world. -/
def curryFunction (operation : NatTrans (FunctorToTypes.prod F H) G) :
    NatTrans H (functions F G) where
  app X := TypeCat.ofHom (fun parameter =>
    { app Y restriction := TypeCat.ofHom
        (fun argument => operation.app Y (argument, H.map restriction parameter))
      naturality {Y Z} step restriction := by
        change X ⟶ Y at restriction
        apply ConcreteCategory.hom_ext
        intro argument
        change operation.app Z (F.map step argument, H.map (restriction ≫ step) parameter) =
          G.map step (operation.app Y (argument, H.map restriction parameter))
        rw [H.map_comp_apply]
        exact congrArg (fun h : (FunctorToTypes.prod F H).obj Y ⟶ G.obj Z =>
          h (argument, H.map restriction parameter)) (operation.naturality step) })
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro parameter
    apply Functor.HomObj.ext
    funext Z restriction
    change Y ⟶ Z at restriction
    apply ConcreteCategory.hom_ext
    intro argument
    change operation.app Z (argument, H.map restriction (H.map step parameter)) =
      operation.app Z (argument, H.map (step ≫ restriction) parameter)
    rw [H.map_comp_apply]

/-- Apply a natural family of functions to its argument. -/
def uncurryFunction (operation : NatTrans H (functions F G)) :
    NatTrans (FunctorToTypes.prod F H) G where
  app X := TypeCat.ofHom (fun pair => (operation.app X pair.2).app X (𝟙 X) pair.1)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, parameter⟩
    change (operation.app Y (H.map step parameter)).app Y (𝟙 Y) (F.map step argument) =
      G.map step ((operation.app X parameter).app X (𝟙 X) argument)
    have naturally := congrArg (fun h : H.obj X ⟶ (functions F G).obj Y => h parameter)
      (operation.naturality step)
    change operation.app Y (H.map step parameter) =
      FunctionSection.restrict F G step (operation.app X parameter) at naturally
    rw [naturally]
    exact congrArg (fun h : (FunctorToTypes.prod F (functions F G)).obj X ⟶ G.obj Y =>
      h (argument, operation.app X parameter)) ((evaluate F G).naturality step)

theorem uncurry_curryFunction (operation : NatTrans (FunctorToTypes.prod F H) G) :
    uncurryFunction (curryFunction operation) = operation := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  rintro ⟨argument, parameter⟩
  change operation.app X (argument, H.map (𝟙 X) parameter) = operation.app X (argument, parameter)
  rw [H.map_id_apply]

theorem curry_uncurryFunction (operation : NatTrans H (functions F G)) :
    curryFunction (uncurryFunction operation) = operation := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro parameter
  apply Functor.HomObj.ext
  funext Y restriction
  change X ⟶ Y at restriction
  apply ConcreteCategory.hom_ext
  intro argument
  change (operation.app Y (H.map restriction parameter)).app Y (𝟙 Y) argument =
    (operation.app X parameter).app Y restriction argument
  have naturally := congrArg (fun h : H.obj X ⟶ (functions F G).obj Y => h parameter)
    (operation.naturality restriction)
  change operation.app Y (H.map restriction parameter) =
    FunctionSection.restrict F G restriction (operation.app X parameter) at naturally
  rw [naturally]
  change (operation.app X parameter).app Y (restriction ≫ 𝟙 Y) argument = _
  rw [Category.comp_id]

/-- The function object's defining hom-set equivalence. -/
def functionHomEquiv (F G H : C ⥤ Type u) :
    NatTrans (FunctorToTypes.prod F H) G ≃ NatTrans H (functions F G) where
  toFun := curryFunction
  invFun := uncurryFunction
  left_inv := uncurry_curryFunction
  right_inv := curry_uncurryFunction

end Mettapedia.GSLT.Topos.ConstructivePresheaf
