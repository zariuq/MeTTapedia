import Mettapedia.TypeTheory.PresheafSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts

/-!
# Independently formed contextual products and sums on raised sites

The product comparison ranges over every future world, actual arrow and
argument. It is not a comparison of pointwise functions. The sum comparison
retains its first coordinate and dependent second coordinate. Both directions
are authored operations with inverse and natural restriction laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafSiteLiftTypeFormers

open CategoryTheory
open PresheafSiteLift
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u
variable {C : Type u} [Category.{u} C]
variable (P : Cᵒᵖ ⥤ Type u) (A : P.Elements ⥤ Type u) (B : A.Elements ⥤ Type u)

namespace Pi

def lower (point : (base P).Elements) (function : DependentSection (family P A) (body P A B) point) :
    DependentSection A B ((elementsDown P).obj point) where
  app next arrow argument := (function.app ((elementsUp P).obj next) ((elementsUp P).map arrow) (ULift.up argument)).down
  naturality {_Y _Z} step restriction argument :=
    congrArg ULift.down (function.naturality ((elementsUp P).map step) ((elementsUp P).map restriction) (ULift.up argument))

def raise (point : (base P).Elements) (function : DependentSection A B ((elementsDown P).obj point)) :
    DependentSection (family P A) (body P A B) point where
  app next arrow argument := ULift.up (function.app ((elementsDown P).obj next) ((elementsDown P).map arrow) argument.down)
  naturality {_Y _Z} step restriction argument :=
    congrArg ULift.up (function.naturality ((elementsDown P).map step) ((elementsDown P).map restriction) argument.down)

theorem lower_raise (point : (base P).Elements) (function : DependentSection A B ((elementsDown P).obj point)) :
    lower P A B point (raise P A B point function) = function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem raise_lower (point : (base P).Elements) (function : DependentSection (family P A) (body P A B) point) :
    raise P A B point (lower P A B point function) = function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

def equiv (point : (base P).Elements) :
    DependentSection (family P A) (body P A B) point ≃ DependentSection A B ((elementsDown P).obj point) where
  toFun := lower P A B point
  invFun := raise P A B point
  left_inv := raise_lower P A B point
  right_inv := lower_raise P A B point

theorem lower_restrict {first second : (base P).Elements} (step : first ⟶ second)
    (function : DependentSection (family P A) (body P A B) first) :
    lower P A B second (DependentSection.restrict (family P A) (body P A B) step function) =
      DependentSection.restrict A B ((elementsDown P).map step) (lower P A B first function) := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem raise_restrict {first second : (base P).Elements} (step : first ⟶ second)
    (function : DependentSection A B ((elementsDown P).obj first)) :
    raise P A B second (DependentSection.restrict A B ((elementsDown P).map step) function) =
      DependentSection.restrict (family P A) (body P A B) step (raise P A B first function) := by
  apply DependentSection.ext
  intro _ _ _
  rfl

def comparison : NatTrans (dependentFunctions (family P A) (body P A B)) (family P (dependentFunctions A B)) where
  app point := TypeCat.ofHom fun function => ULift.up (lower P A B point function)
  naturality {first second} step := by
    apply ConcreteCategory.hom_ext
    intro function
    exact congrArg ULift.up (lower_restrict P A B step function)

def inverse : NatTrans (family P (dependentFunctions A B)) (dependentFunctions (family P A) (body P A B)) where
  app point := TypeCat.ofHom fun function => raise P A B point function.down
  naturality {first second} step := by
    apply ConcreteCategory.hom_ext
    intro function
    exact raise_restrict P A B step function.down

theorem comparison_left : compose (comparison P A B) (inverse P A B) = Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact raise_lower P A B point

theorem comparison_right : compose (inverse P A B) (comparison P A B) = Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro function
  exact congrArg ULift.up (lower_raise P A B point function.down)

theorem evaluation (point : (base P).Elements) (function : DependentSection (family P A) (body P A B) point)
    (next : (base P).Elements) (arrow : point ⟶ next) (argument : (family P A).obj next) :
    (function.app next arrow argument).down =
      (lower P A B point function).app ((elementsDown P).obj next) ((elementsDown P).map arrow) argument.down := rfl

end Pi

namespace Sigma

abbrev upper := PowerClassPresheafProducts.IndexedSigma.family (family P A) (body P A B)
abbrev lowerFamily := PowerClassPresheafProducts.IndexedSigma.family A B

def lower (point : (base P).Elements) (pair : (upper P A B).obj point) :
    (lowerFamily P A B).obj ((elementsDown P).obj point) := ⟨pair.1.down, pair.2.down⟩

def raise (point : (base P).Elements) (pair : (lowerFamily P A B).obj ((elementsDown P).obj point)) :
    (upper P A B).obj point := ⟨ULift.up pair.1, ULift.up pair.2⟩

def equiv (point : (base P).Elements) : (upper P A B).obj point ≃ (lowerFamily P A B).obj ((elementsDown P).obj point) where
  toFun := lower P A B point
  invFun := raise P A B point
  left_inv _ := rfl
  right_inv _ := rfl

def comparison : NatTrans (upper P A B) (family P (lowerFamily P A B)) where
  app point := TypeCat.ofHom fun pair => ULift.up (lower P A B point pair)
  naturality {first second} step := by
    apply ConcreteCategory.hom_ext
    intro pair
    rfl

def inverse : NatTrans (family P (lowerFamily P A B)) (upper P A B) where
  app point := TypeCat.ofHom fun pair => raise P A B point pair.down
  naturality {first second} step := by
    apply ConcreteCategory.hom_ext
    intro pair
    rfl

theorem comparison_left : compose (comparison P A B) (inverse P A B) = Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro pair
  rfl

theorem comparison_right : compose (inverse P A B) (comparison P A B) = Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro pair
  rfl

theorem first_value (point : (base P).Elements) (pair : (upper P A B).obj point) :
    (lower P A B point pair).1 = pair.1.down := rfl

theorem second_value (point : (base P).Elements) (pair : (upper P A B).obj point) :
    (lower P A B point pair).2 = pair.2.down := rfl

end Sigma

end Mettapedia.TypeTheory.PresheafSiteLiftTypeFormers
