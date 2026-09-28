import Mettapedia.OSLF.Syntax.CartesianModelReflection
import Mettapedia.OSLF.Syntax.RhoCartesianModelOrthogonality

/-!
# Cartesian reflection for the authored rho substitution category

The generic reflection is instantiated on the name/process context category
of the reflective rho presentation. Its universal property applies to every
set-valued interpretation of those authored contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelReflection

open CategoryTheory
open Mettapedia.OSLF.Binding.RhoCartesianContextModels
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

private instance : CategoryTheory.Limits.HasFiniteProducts Contexts :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

noncomputable def rhoCartesianReflection :
    CovariantPresheaf Contexts ⥤ Models Contexts :=
  cartesianReflection Contexts

noncomputable def rhoCartesianizationMonad :
    Monad (CovariantPresheaf Contexts) :=
  cartesianizationMonad Contexts

/-- An arbitrary interpretation of the authored rho contexts maps to a
cartesian model exactly through its reflection. -/
noncomputable def rhoCartesianReflectionHomEquiv
    (F : CovariantPresheaf Contexts) (M : Models Contexts) :
    ((rhoCartesianReflection.obj F) ⟶ M) ≃
      (F ⟶ (ProductModel Contexts).ι.obj M) :=
  cartesianReflectionHomEquiv Contexts F M

theorem rhoCartesianizationMonad_mul_isIso :
    IsIso rhoCartesianizationMonad.μ :=
  cartesianizationMonad_mul_isIso Contexts

/-- The authored name model is already cartesian, so its reflection unit is
an isomorphism. -/
theorem nameModel_unit_isIso :
    IsIso ((cartesianReflectionAdjunction Contexts).unit.app
      ((ProductModel Contexts).ι.obj nameModel)) :=
  cartesianReflection_model_unit_isIso Contexts nameModel

/-- The constant Boolean interpretation of rho contexts genuinely changes
under cartesian reflection. -/
theorem bool_unit_not_isIso :
    ¬ IsIso ((cartesianReflectionAdjunction Contexts).unit.app
      ((Functor.const Contexts).obj Bool)) :=
  cartesianReflection_bool_unit_not_isIso Contexts

end Mettapedia.OSLF.Binding.RhoCartesianModelReflection
