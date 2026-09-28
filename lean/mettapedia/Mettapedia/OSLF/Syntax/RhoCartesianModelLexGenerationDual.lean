import Mettapedia.OSLF.Syntax.CartesianModelLexGenerationDual
import Mettapedia.OSLF.Syntax.RhoCartesianModelFiniteGeneration

/-!
# Finite-limit generation for authored rho contexts

The general dual generation theorem specializes to the actual two-sorted rho
context category, retaining its authored context-product equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelLexGenerationDual

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem rho_finiteModels_op_eq_authoredContexts_finiteLimitClosure :
    (isCardinalPresentable.{0} (Models Contexts) Cardinal.aleph0.{0}).op =
      (authoredContexts Contexts).op.limitsClosure
        (fun a : SmallCategoryCardinalLT Cardinal.aleph0.{0} =>
          (SmallCategoryCardinalLT.categoryFamily Cardinal.aleph0.{0} a)ᵒᵖ) :=
  finiteModels_op_eq_authoredContexts_finiteLimitClosure Contexts

end Mettapedia.OSLF.Binding.RhoCartesianModelLexGenerationDual
