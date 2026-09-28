import Mettapedia.OSLF.Syntax.CartesianModelFiniteGeneration
import Mettapedia.OSLF.Syntax.RhoCartesianModelLocalPresentability

/-!
# Finite presentations from the authored rho contexts

The general finite-generation theorem specializes to the actual two-sorted
name/process context category. The represented name and process contexts are
members of the generating family. The constant Boolean interpretation is a
negative control because it violates the empty-context product law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelFiniteGeneration

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels
open Mettapedia.OSLF.Binding.RhoSchema

attribute [local instance] Cardinal.fact_isRegular_aleph0

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- Finitely presented rho cartesian models are exactly the finite-colimit
closure of represented authored name/process contexts. -/
theorem rho_finiteModels_eq_authoredContexts_closure :
    isCardinalPresentable.{0} (Models Contexts) Cardinal.aleph0.{0} =
      (authoredContexts Contexts).colimitsCardinalClosure Cardinal.aleph0.{0} :=
  finiteModels_eq_authoredContexts_closure Contexts

theorem rho_finitePresentationInclusion_dense :
    ((isCardinalPresentable.{0} (Models Contexts) Cardinal.aleph0.{0}).ι).IsDense :=
  finitePresentationInclusion_dense Contexts

theorem nameModel_is_authoredContext :
    authoredContexts Contexts nameModel := by
  exact ⟨Opposite.op (Syntactic.single Srt.nm : Contexts)⟩

theorem processModel_is_authoredContext :
    authoredContexts Contexts processModel := by
  exact ⟨Opposite.op (Syntactic.single Srt.pr : Contexts)⟩

theorem bool_is_not_rho_cartesian_model :
    ¬ ProductModel Contexts ((Functor.const Contexts).obj Bool) :=
  bool_presheaf_not_model

end Mettapedia.OSLF.Binding.RhoCartesianModelFiniteGeneration
