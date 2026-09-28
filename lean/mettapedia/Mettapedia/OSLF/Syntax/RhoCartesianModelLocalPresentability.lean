import Mettapedia.OSLF.Syntax.CartesianModelFormalComparison
import Mettapedia.OSLF.Syntax.RhoCartesianContextModels

/-!
# Locally finite presentability for authored rho contexts

The general construction applies to the name/process context category of the
reflective rho presentation.  The name and process representations are
finitely presentable model objects.  The constant Boolean presheaf remains
an explicit nonmodel control: it violates the authored context-product laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelLocalPresentability

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels

attribute [local instance] Cardinal.fact_isRegular_aleph0

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

theorem rho_models_locally_finitely_presentable :
    IsCardinalLocallyPresentable (Models Contexts) Cardinal.aleph0.{0} :=
  models_locally_finitely_presentable Contexts

theorem nameModel_finitely_presentable :
    IsCardinalPresentable nameModel Cardinal.aleph0.{0} :=
  represented_model_presentable Contexts _

theorem processModel_finitely_presentable :
    IsCardinalPresentable processModel Cardinal.aleph0.{0} :=
  represented_model_presentable Contexts _

theorem rho_finitePresentationObjects_haveFiniteLimits :
    HasFiniteLimits (FinitePresentationObjects Contexts) := inferInstance

theorem rho_authoredContext_full :
    (authoredContext Contexts).Full := inferInstance

theorem rho_authoredContext_faithful :
    (authoredContext Contexts).Faithful := inferInstance

theorem rho_authoredContext_preservesFiniteProducts :
    PreservesFiniteProducts (authoredContext Contexts) :=
  authoredContext_preservesFiniteProducts Contexts

theorem no_formal_equivalence_over_rho_contexts :
    ¬ ∃ e : Mettapedia.OSLF.FormalFiniteLimits.Objects Contexts ≌
        FinitePresentationObjects Contexts,
      Nonempty (Mettapedia.OSLF.FormalFiniteLimits.base Contexts ⋙ e.functor ≅
        authoredContext Contexts) :=
  no_formal_equivalence_over_authored_context Contexts

/-- The constant two-element interpretation is outside the rho model
category, so finite-presentability claims about rho models cannot be
mistaken for assertions about all set-valued interpretations. -/
theorem bool_not_rho_model :
    ¬ ProductModel Contexts ((Functor.const Contexts).obj Bool) :=
  bool_presheaf_not_model

end Mettapedia.OSLF.Binding.RhoCartesianModelLocalPresentability
