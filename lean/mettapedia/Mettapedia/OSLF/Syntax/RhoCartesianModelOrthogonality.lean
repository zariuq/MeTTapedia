import Mettapedia.OSLF.Syntax.CartesianModelOrthogonality
import Mettapedia.OSLF.Syntax.RhoCartesianContextModels

/-!
# The cartesian locality law for the authored rho contexts

The name and process contexts of the reflective rho presentation are an
actual pair in its substitution category. Its represented name model
satisfies the product equation, while the constant Boolean interpretation
does not.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelOrthogonality

open CategoryTheory
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoCartesianContextModels
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

private instance : CategoryTheory.Limits.HasFiniteProducts Contexts :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

private abbrev NameContext : Contexts := Syntactic.single Srt.nm
private abbrev ProcessContext : Contexts := Syntactic.single Srt.pr

/-- The authored name model satisfies the equation imposed by the name-process
product context. -/
theorem name_model_local_at_name_process :
    (MorphismProperty.single
      (productLocalizingMap Contexts NameContext ProcessContext)).isLocal
        nameModel.1 :=
  product_model_local_at_pair Contexts nameModel NameContext ProcessContext

/-- The same authored product detects a non-cartesian interpretation. -/
theorem bool_not_local_at_name_process :
    ¬ (MorphismProperty.single
      (productLocalizingMap Contexts NameContext ProcessContext)).isLocal
        ((Functor.const Contexts).obj Bool) :=
  constantBool_not_local_at_pair Contexts NameContext ProcessContext

/-- For the actual two-sort rho substitution category, the terminal and all
binary locality equations characterize precisely its cartesian models. -/
theorem rho_model_iff_local_generators (F : CovariantPresheaf Contexts) :
    ProductModel Contexts F ↔
      (MorphismProperty.single (terminalLocalizingMap Contexts)).isLocal F ∧
        ∀ X Y : Contexts,
          (MorphismProperty.single
            (productLocalizingMap Contexts X Y)).isLocal F :=
  product_model_iff_local_generators Contexts F

theorem rho_model_iff_cartesian_local (F : CovariantPresheaf Contexts) :
    ProductModel Contexts F ↔ (cartesianLaws Contexts).isLocal F :=
  product_model_iff_cartesian_local Contexts F

end Mettapedia.OSLF.Binding.RhoCartesianModelOrthogonality
