import Mettapedia.TypeTheory.ContextualFutureSiteLift
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction

/-!
# Independent dependent products and sums across the actual site equivalence

The parameter universe is independent of the original world and member
bounds. Both native product maps retain every future context arrow and
typed argument. Their inverse, evaluation and naturality laws are proved
from the actual site maps. Compression then compares the independently
formed original-small and successor-small products.

Dependent sums retain both their first member and dependent second member.
These constructions concern transported authored signatures; a separate
member-signature comparison connects them to actual material model bodies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualFutureSiteProducts

open CategoryTheory
open ContextualFutureSiteLift
open WiderPresheafDependentFunctions

universe u v
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (A : P.Elements ⥤ Type u) (B : A.Elements ⥤ Type u)

namespace Pi

def lower (point : (base P).Elements)
    (function : DependentSection (family P A) (body P A B) point) :
    DependentSection A B ((elementsDown P).obj point) where
  app next arrow argument :=
    (function.app ((elementsUp P).obj next) ((elementsUp P).map arrow) (ULift.up argument)).down
  naturality step arrival argument :=
    congrArg ULift.down (function.naturality ((elementsUp P).map step) ((elementsUp P).map arrival) (ULift.up argument))

def raise (point : (base P).Elements) (function : DependentSection A B ((elementsDown P).obj point)) :
    DependentSection (family P A) (body P A B) point where
  app next arrow argument := ULift.up (function.app ((elementsDown P).obj next) ((elementsDown P).map arrow) argument.down)
  naturality step arrival argument :=
    congrArg ULift.up (function.naturality ((elementsDown P).map step) ((elementsDown P).map arrival) argument.down)

theorem lower_raise (point : (base P).Elements) (function : DependentSection A B ((elementsDown P).obj point)) :
    lower A B point (raise A B point function) = function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem raise_lower (point : (base P).Elements)
    (function : DependentSection (family P A) (body P A B) point) :
    raise A B point (lower A B point function) = function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

def nativeEquiv (point : (base P).Elements) :
    DependentSection (family P A) (body P A B) point ≃ DependentSection A B ((elementsDown P).obj point) where
  toFun := lower A B point
  invFun := raise A B point
  left_inv := raise_lower A B point
  right_inv := lower_raise A B point

theorem lower_restrict {first second : (base P).Elements} (step : first ⟶ second)
    (function : DependentSection (family P A) (body P A B) first) :
    lower A B second (DependentSection.restrict (family P A) (body P A B) step function) =
      DependentSection.restrict A B ((elementsDown P).map step) (lower A B first function) := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem raise_restrict {first second : (base P).Elements} (step : first ⟶ second)
    (function : DependentSection A B ((elementsDown P).obj first)) :
    raise A B second (DependentSection.restrict A B ((elementsDown P).map step) function) =
      DependentSection.restrict (family P A) (body P A B) step (raise A B first function) := by
  apply DependentSection.ext
  intro _ _ _
  rfl

def comparison : Hom (dependentFunctions (family P A) (body P A B))
    (PresheafSiteLift.compose (elementsDown P) (dependentFunctions A B)) where
  app := lower A B
  naturality step function := lower_restrict A B step function

def inverse : Hom (PresheafSiteLift.compose (elementsDown P) (dependentFunctions A B))
    (dependentFunctions (family P A) (body P A B)) where
  app := raise A B
  naturality step function := raise_restrict A B step function

theorem comparison_inverse : (comparison A B).comp (inverse A B) = Hom.identity _ := by
  apply Hom.ext
  intro point function
  exact raise_lower A B point function

theorem inverse_comparison : (inverse A B).comp (comparison A B) = Hom.identity _ := by
  apply Hom.ext
  intro point function
  exact lower_raise A B point function

theorem evaluation (point next : (base P).Elements)
    (function : DependentSection (family P A) (body P A B) point)
    (arrow : point ⟶ next) (argument : (family P A).obj next) :
    (function.app next arrow argument).down =
      (lower A B point function).app ((elementsDown P).obj next) ((elementsDown P).map arrow) argument.down := rfl

abbrev upperSmall := ContextualSmallFamilyTypeFormers.pi (family P A) (body P A B)
abbrev oldSmall := ContextualSmallFamilyTypeFormers.pi A B

def smallEquiv (point : (base P).Elements) :
    (upperSmall A B).obj point ≃ (oldSmall A B).obj ((elementsDown P).obj point) :=
  (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (family P A) (body P A B) point).symm.trans
    ((nativeEquiv A B point).trans
      (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv A B ((elementsDown P).obj point)))

end Pi

namespace Sigma

abbrev upper := ContextualSmallFamilyTypeFormers.sigma (family P A) (body P A B)
abbrev old := ContextualSmallFamilyTypeFormers.sigma A B

def lower (point : (base P).Elements) (term : (upper A B).obj point) :
    (old A B).obj ((elementsDown P).obj point) := ⟨term.1.down, term.2.down⟩

def raise (point : (base P).Elements) (term : (old A B).obj ((elementsDown P).obj point)) :
    (upper A B).obj point := ⟨ULift.up term.1, ULift.up term.2⟩

def equiv (point : (base P).Elements) : (upper A B).obj point ≃ (old A B).obj ((elementsDown P).obj point) where
  toFun := lower A B point
  invFun := raise A B point
  left_inv _ := rfl
  right_inv _ := rfl

def comparison : Hom (upper A B) (PresheafSiteLift.compose (elementsDown P) (old A B)) where
  app := lower A B
  naturality _ _ := rfl

def inverse : Hom (PresheafSiteLift.compose (elementsDown P) (old A B)) (upper A B) where
  app := raise A B
  naturality _ _ := rfl

theorem first_value (point : (base P).Elements) (term : (upper A B).obj point) :
    (lower A B point term).1 = term.1.down := rfl

theorem second_value (point : (base P).Elements) (term : (upper A B).obj point) :
    (lower A B point term).2 = term.2.down := rfl

end Sigma

end Mettapedia.TypeTheory.ContextualFutureSiteProducts
