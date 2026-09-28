import Mettapedia.GSLT.Topos.ConstructivePresheafFamilies

/-!
# Dependent sections over parameterized worlds

A dependent section supplies a value in the argument's own family at every
future world. Its restriction law retains the actual arrow and argument.
The construction is right adjoint to restriction along the category-of-elements
projection. No representative of an inhabited fibre is chosen.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable (F : C ⥤ Type u) (G : F.Elements ⥤ Type u)

def argumentMap {X Y : C} (step : X ⟶ Y) (argument : F.obj X) :
    F.elementsMk X argument ⟶ F.elementsMk Y (F.map step argument) :=
  CategoryOfElements.homMk _ _ step rfl

structure DependentSection (X : C) where
  app : ∀ Y, (X ⟶ Y) → (argument : F.obj Y) → G.obj ⟨Y, argument⟩
  naturality : ∀ {Y Z} (step : Y ⟶ Z) (restriction : X ⟶ Y) (argument : F.obj Y),
    G.map (argumentMap F step argument) (app Y restriction argument) =
      app Z (restriction ≫ step) (F.map step argument)

namespace DependentSection

theorem ext {X : C} (first second : DependentSection F G X)
    (equal : ∀ Y restriction argument,
      first.app Y restriction argument = second.app Y restriction argument) :
    first = second := by
  cases first with
  | mk first first_law =>
      cases second with
      | mk second second_law =>
          have same : first = second := funext fun Y => funext fun restriction => funext fun argument =>
            equal Y restriction argument
          cases same
          rfl

def restrict {X Y : C} (step : X ⟶ Y) (value : DependentSection F G X) :
    DependentSection F G Y where
  app Z restriction argument := value.app Z (step ≫ restriction) argument
  naturality {Z W} later restriction argument := by
    rw [← Category.assoc]
    exact value.naturality later (step ≫ restriction) argument

theorem restrict_id {X : C} (value : DependentSection F G X) :
    restrict F G (𝟙 X) value = value := by
  apply ext
  intro Y restriction argument
  change value.app Y (𝟙 X ≫ restriction) argument = value.app Y restriction argument
  rw [Category.id_comp]

theorem restrict_comp {X Y Z : C} (step : X ⟶ Y) (later : Y ⟶ Z)
    (value : DependentSection F G X) :
    restrict F G later (restrict F G step value) = restrict F G (step ≫ later) value := by
  apply ext
  intro W restriction argument
  change value.app W (step ≫ later ≫ restriction) argument =
    value.app W ((step ≫ later) ≫ restriction) argument
  rw [Category.assoc]

end DependentSection

def dependentFunctions : C ⥤ Type u where
  obj X := DependentSection F G X
  map step := TypeCat.ofHom (DependentSection.restrict F G step)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro value
    exact DependentSection.restrict_id F G value
  map_comp step later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (DependentSection.restrict_comp F G step later value).symm

variable {F G} {H : C ⥤ Type u}

def curry (operation : NatTrans (overElements F H) G) :
    NatTrans H (dependentFunctions F G) where
  app X := TypeCat.ofHom (fun parameter =>
    { app Y restriction argument := operation.app ⟨Y, argument⟩ (H.map restriction parameter)
      naturality {Y Z} step restriction argument := by
        rw [H.map_comp_apply]
        exact (congrArg (fun h => h (H.map restriction parameter))
          (operation.naturality (argumentMap F step argument))).symm })
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro parameter
    apply DependentSection.ext
    intro Z restriction argument
    change operation.app ⟨Z,argument⟩ (H.map restriction (H.map step parameter)) =
      operation.app ⟨Z,argument⟩ (H.map (step ≫ restriction) parameter)
    rw [H.map_comp_apply]

def uncurry (operation : NatTrans H (dependentFunctions F G)) :
    NatTrans (overElements F H) G where
  app X := TypeCat.ofHom (fun parameter => (operation.app X.1 parameter).app X.1 (𝟙 X.1) X.2)
  naturality X Y restriction := by
    rcases X with ⟨X, argument⟩
    rcases Y with ⟨Y, nextArgument⟩
    rcases restriction with ⟨step, at_argument⟩
    change X ⟶ Y at step
    change F.map step argument = nextArgument at at_argument
    subst nextArgument
    apply ConcreteCategory.hom_ext
    intro parameter
    change (operation.app Y (H.map step parameter)).app Y (𝟙 Y) (F.map step argument) =
      G.map (argumentMap F step argument) ((operation.app X parameter).app X (𝟙 X) argument)
    have natural := congrArg (fun h => h parameter) (operation.naturality step)
    change operation.app Y (H.map step parameter) =
      DependentSection.restrict F G step (operation.app X parameter) at natural
    rw [natural]
    change (operation.app X parameter).app Y (step ≫ 𝟙 Y) (F.map step argument) = _
    rw [Category.comp_id]
    have value_natural := (operation.app X parameter).naturality step (𝟙 X) argument
    rw [Category.id_comp] at value_natural
    exact value_natural.symm

theorem uncurry_curry (operation : NatTrans (overElements F H) G) :
    uncurry (curry operation) = operation := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨X, argument⟩
  apply ConcreteCategory.hom_ext
  intro parameter
  change H.obj X at parameter
  exact congrArg (operation.app ⟨X,argument⟩) (H.map_id_apply X parameter)

theorem curry_uncurry (operation : NatTrans H (dependentFunctions F G)) :
    curry (uncurry operation) = operation := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro parameter
  apply DependentSection.ext
  intro Y restriction argument
  change (operation.app Y (H.map restriction parameter)).app Y (𝟙 Y) argument =
    (operation.app X parameter).app Y restriction argument
  have natural := congrArg (fun h => h parameter) (operation.naturality restriction)
  change operation.app Y (H.map restriction parameter) =
    DependentSection.restrict F G restriction (operation.app X parameter) at natural
  rw [natural]
  change (operation.app X parameter).app Y (restriction ≫ 𝟙 Y) argument = _
  rw [Category.comp_id]

def dependentHomEquiv (F : C ⥤ Type u) (G : F.Elements ⥤ Type u) (H : C ⥤ Type u) :
    NatTrans (overElements F H) G ≃ NatTrans H (dependentFunctions F G) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

def evaluate (F : C ⥤ Type u) (G : F.Elements ⥤ Type u) :
    NatTrans (overElements F (dependentFunctions F G)) G := uncurry
      { app X := 𝟙 _
        naturality X Y f := by rw [Category.comp_id, Category.id_comp] }

def identity (H : C ⥤ Type u) : NatTrans H H where
  app X := 𝟙 _
  naturality X Y f := by rw [Category.comp_id, Category.id_comp]

def compose {A B D : C ⥤ Type u} (first : NatTrans A B) (second : NatTrans B D) :
    NatTrans A D where
  app X := first.app X ≫ second.app X
  naturality X Y f := by
    rw [← Category.assoc, first.naturality, Category.assoc, second.naturality,
      ← Category.assoc]

def overMap {A B : C ⥤ Type u} (first : NatTrans A B) :
    NatTrans (overElements F A) (overElements F B) where
  app X := first.app X.1
  naturality _ _ f := first.naturality f.val

def mapFamily {G' : F.Elements ⥤ Type u} (transformation : NatTrans G G') :
    NatTrans (dependentFunctions F G) (dependentFunctions F G') where
  app X := TypeCat.ofHom (fun value =>
    { app Y restriction argument := transformation.app ⟨Y,argument⟩ (value.app Y restriction argument)
      naturality {Y Z} step restriction argument := by
        have natural := congrArg (fun h => h (value.app Y restriction argument))
          (transformation.naturality (argumentMap F step argument))
        change transformation.app ⟨Z,F.map step argument⟩
          (G.map (argumentMap F step argument) (value.app Y restriction argument)) = _ at natural
        rw [value.naturality] at natural
        exact natural.symm })
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro value
    apply DependentSection.ext
    intro Z restriction argument
    rfl

theorem mapFamily_identity :
    mapFamily (identity G) = identity (dependentFunctions F G) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro value
  apply DependentSection.ext
  intro Y restriction argument
  rfl

theorem mapFamily_compose {G' G'' : F.Elements ⥤ Type u}
    (first : NatTrans G G') (second : NatTrans G' G'') :
    mapFamily (compose first second) = compose (mapFamily first) (mapFamily second) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro value
  apply DependentSection.ext
  intro Y restriction argument
  rfl

theorem curry_natural_left {H' : C ⥤ Type u}
    (first : NatTrans H' H) (operation : NatTrans (overElements F H) G) :
    curry (compose (overMap first) operation) = compose first (curry operation) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro parameter
  apply DependentSection.ext
  intro Y restriction argument
  change operation.app ⟨Y,argument⟩ (first.app Y (H'.map restriction parameter)) =
    operation.app ⟨Y,argument⟩ (H.map restriction (first.app X parameter))
  exact congrArg (operation.app ⟨Y,argument⟩)
    (congrArg (fun h => h parameter) (first.naturality restriction))

theorem curry_natural_right {G' : F.Elements ⥤ Type u}
    (operation : NatTrans (overElements F H) G) (later : NatTrans G G') :
    curry (compose operation later) = compose (curry operation) (mapFamily later) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro parameter
  apply DependentSection.ext
  intro Y restriction argument
  rfl

#print axioms dependentFunctions
#print axioms dependentHomEquiv
#print axioms evaluate
#print axioms curry_natural_left
#print axioms curry_natural_right

end Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
