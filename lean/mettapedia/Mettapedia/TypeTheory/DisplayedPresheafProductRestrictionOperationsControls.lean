import Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionOperations
import Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherenceControls

/-!
# Operation preservation without product invertibility

The actual supplied global functions remain different in the source
theory. An initial-world restriction collapses them while preserving
abstraction and all available applications. A route exchanging the two
future arrows retains the distinguishing future argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionOperationsControls

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryRestrictionAction DependentProductNativeComparison
open DisplayedPresheafIndexedCwfBridge
open DisplayedPresheafProductRestrictionOperations
open DisplayedPresheafLogicalActionCoherence
open DisplayedPresheafLogicalActionCoherenceControls
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

def body (value : Bool) : results.sections where
  val _ := value
  property _ := rfl

noncomputable def function (value : Bool) : (piDisplayed arguments results).sections :=
  lamDisplayed (body value)

theorem source_functions_distinct : function false ≠ function true := by
  intro same
  have readout := congrArg (fun valueSection =>
    ((((nativeIso arguments).hom.app (displayedToTotalElements arguments ⋙ results)).app
      future (valueSection.val future)).app future (𝟙 future) PUnit.unit)) same
  change ((((nativeIso arguments).hom.app (displayedToTotalElements arguments ⋙ results)).app
      future ((lamDisplayed (body false)).val future)).app future (𝟙 future) PUnit.unit) =
    ((((nativeIso arguments).hom.app (displayedToTotalElements arguments ⋙ results)).app
      future ((lamDisplayed (body true)).val future)).app future (𝟙 future) PUnit.unit) at readout
  have first := abstraction_readout arguments results (body false) future future (𝟙 future) PUnit.unit
  have second := abstraction_readout arguments results (body true) future future (𝟙 future) PUnit.unit
  exact Bool.false_ne_true (first.symm.trans (readout.trans second))

set_option backward.isDefEq.respectTransparency false in
theorem initial_restriction_collapses :
    restrictFunction initialOnly base arguments results (function false) =
      restrictFunction initialOnly base arguments results (function true) := by
  apply Functor.sections_ext_iff.mpr
  intro point
  let restricted := restrictFamily initialOnly base arguments
  let output := displayedToTotalElements restricted ⋙
    (codomainFunctor initialOnly base arguments).obj results
  apply (((nativeIso restricted).app output).app point).toEquiv.injective
  apply DependentSection.ext
  intro futurePoint arrow argument
  exact PEmpty.elim argument

/-- Preservation of abstraction can hold even when information about
genuine source functions is lost. -/
theorem collapsed_abstractions_are_restrictions (value : Bool) :
    restrictFunction initialOnly base arguments results (function value) =
      lamDisplayed (reindexDisplayedSection (totalComparison initialOnly base arguments).hom
        (restrictFamily initialOnly (totalSpace arguments) results)
        (restrictTerm initialOnly (totalSpace arguments) results (body value))) :=
  abstraction initialOnly base arguments results (body value)

set_option backward.isDefEq.respectTransparency false in
theorem exchanged_future_application (value : Bool) :
    ((((nativeIso (restrictFamily exchange base arguments)).hom.app
      (displayedToTotalElements (restrictFamily exchange base arguments) ⋙
        (codomainFunctor exchange base arguments).obj results)).app exchangeOrigin
      ((restrictFunction exchange base arguments results (function value)).val exchangeOrigin)).app
      exchangeFuture exchangeArrow PUnit.unit) = value := by
  change ((((nativeIso (restrictFamily exchange base arguments)).hom.app
      (displayedToTotalElements (restrictFamily exchange base arguments) ⋙
        (codomainFunctor exchange base arguments).obj results)).app exchangeOrigin
      ((productComparison exchange base arguments results).app exchangeOrigin
        ((function value).val ((Functor.Elements.precomp exchange.op base).obj exchangeOrigin)))).app
      exchangeFuture exchangeArrow PUnit.unit) = value
  rw [productComparison_readout]
  exact abstraction_readout arguments results (body value) _ _ _ _

theorem exchange_restriction_retains_distinction :
    restrictFunction exchange base arguments results (function false) ≠
      restrictFunction exchange base arguments results (function true) := by
  intro same
  have readout := congrArg (fun valueSection =>
    ((((nativeIso (restrictFamily exchange base arguments)).hom.app
      (displayedToTotalElements (restrictFamily exchange base arguments) ⋙
        (codomainFunctor exchange base arguments).obj results)).app exchangeOrigin
      (valueSection.val exchangeOrigin)).app exchangeFuture exchangeArrow PUnit.unit)) same
  rw [exchanged_future_application, exchanged_future_application] at readout
  exact Bool.false_ne_true readout

end Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionOperationsControls
