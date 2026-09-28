import Mettapedia.OSLF.Syntax.CartesianModelSiftedColimits
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema
import Mettapedia.OSLF.Syntax.TermCloneCategoryComparison
import Mathlib.CategoryTheory.Limits.Lattice

/-!
# Cartesian semantic interpretations of authored rho contexts

The actual name and process contexts of the reflective presentation enter the
category of product-preserving set-valued models through covariant Yoneda.
That category has finite limits computed in the surrounding functor category.
The constant two-element presheaf is a negative control: it does not preserve
the empty authored context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianContextModels

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.CartesianContextModels

abbrev Contexts := Syntactic.Ctxt sig

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

theorem models_haveFiniteLimits : HasFiniteLimits (Models Contexts) := inferInstance

/-- Every natural-number chain of rho context models has a colimit in the
model category, computed pointwise in the ambient functor category. -/
theorem models_haveNatChainColimits : HasColimitsOfShape Nat (Models Contexts) :=
  inferInstance

/-- The rho model category has these filtered colimits, but its inclusion
does not preserve all binary coproducts. -/
theorem inclusion_not_preservesBinaryCoproducts :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (ProductModel Contexts).ι :=
  CartesianContextModels.inclusion_not_preservesBinaryCoproducts Contexts

noncomputable def emptyContext_is_initial :
    IsInitial ((representedContext Contexts).obj (Opposite.op (⊤_ Contexts))) :=
  CartesianContextModels.represented_terminal_is_initial Contexts

noncomputable def nameProcessProduct_isCoproduct :
    IsColimit (representedProductCofan Contexts
      (Syntactic.single Srt.nm) (Syntactic.single Srt.pr)) :=
  representedProductCofan_isColimit Contexts
    (Syntactic.single Srt.nm) (Syntactic.single Srt.pr)

theorem contextRepresentation_preservesFiniteProducts :
    PreservesFiniteProducts (representedContext Contexts).rightOp :=
  representedBase_preservesFiniteProducts Contexts

/-- The actual two-sort rho context category enters the product-preserving
semantic category with its substitutions and chosen products intact. -/
def contextModel : Contexts ⥤ (Models Contexts)ᵒᵖ :=
  authoredContextModel Contexts

theorem contextModel_preservesFiniteProducts :
    PreservesFiniteProducts contextModel :=
  authoredContextModel_preservesFiniteProducts Contexts

def nameModel : Models Contexts :=
  (representedContext Contexts).obj (Opposite.op (Syntactic.single Srt.nm))

def processModel : Models Contexts :=
  (representedContext Contexts).obj (Opposite.op (Syntactic.single Srt.pr))

theorem nameModel_underlying :
    (ProductModel Contexts).ι.obj nameModel =
      coyoneda.obj (Opposite.op (Syntactic.single Srt.nm)) := rfl

theorem processModel_underlying :
    (ProductModel Contexts).ι.obj processModel =
      coyoneda.obj (Opposite.op (Syntactic.single Srt.pr)) := rfl

theorem bool_presheaf_not_model :
    ¬ ProductModel Contexts ((Functor.const Contexts).obj Bool) :=
  constantBool_not_model Contexts

theorem represented_coprod_not_model :
    ¬ ProductModel Contexts
      (coyoneda.obj (Opposite.op (⊤_ Contexts)) ⨿
       coyoneda.obj (Opposite.op (⊤_ Contexts))) :=
  CartesianContextModels.represented_coprod_not_model Contexts

end Mettapedia.OSLF.Binding.RhoCartesianContextModels
