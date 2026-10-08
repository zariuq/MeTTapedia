import Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherence
import Mettapedia.TypeTheory.DependentProductRestrictionControls
import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherenceControls

/-!
# Function-sensitive controls for logical theory action

The supplied functions differ on a genuine future argument. Restricting
only to the initial world loses that argument and collapses their selected
native representations. A nonidentity change exchanging the two routes
still transports their actual application values by the canonical map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherenceControls

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafIndexedCwfBridge DisplayedPresheafPi
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafLogicalActionCoherence DependentProductNativeComparison
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

abbrev Callers := Discrete Unit
abbrev Worlds := WalkingParallelPairᵒᵖ

def base : Worldsᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

def arguments : DisplayedFamily base :=
  CategoryOfElements.π base ⋙ (opOpEquivalence WalkingParallelPair).functor ⋙
    DependentProductRestrictionControls.argumentFamily

def results : DisplayedFamily (totalSpace arguments) := (Functor.const _).obj Bool

def origin : base.Elements := ⟨Opposite.op (Opposite.op WalkingParallelPair.zero), PUnit.unit⟩
def future : base.Elements := ⟨Opposite.op (Opposite.op WalkingParallelPair.one), PUnit.unit⟩

def futureArrow : origin ⟶ future :=
  CategoryOfElements.homMk _ _
    (Quiver.Hom.op (Quiver.Hom.op
      (WalkingParallelPairHom.left : WalkingParallelPair.zero ⟶ WalkingParallelPair.one))) rfl

def suppliedSection (value : Bool) :
    DependentSection arguments (displayedToTotalElements arguments ⋙ results) origin where
  app _ _ _ := value
  naturality _ _ _ := rfl

noncomputable def suppliedFunction (value : Bool) :
    (piDisplayed arguments results).obj origin :=
  ((nativeIso arguments).inv.app (displayedToTotalElements arguments ⋙ results)).app origin
    (suppliedSection value)

theorem suppliedFunction_readout (value : Bool) :
    ((((nativeIso arguments).hom.app (displayedToTotalElements arguments ⋙ results)).app origin
      (suppliedFunction value)).app future futureArrow PUnit.unit) = value := by
  have inverse := congrArg (fun operation => operation.app origin (suppliedSection value))
    ((nativeIso arguments).inv_hom_id_app (displayedToTotalElements arguments ⋙ results))
  have result := congrArg (fun valueSection :
      DependentSection arguments (displayedToTotalElements arguments ⋙ results) origin =>
    valueSection.app future futureArrow PUnit.unit) inverse
  exact result

theorem suppliedFunctions_distinct : suppliedFunction false ≠ suppliedFunction true := by
  intro same
  have readout := congrArg (fun function =>
    (((nativeIso arguments).hom.app (displayedToTotalElements arguments ⋙ results)).app origin
      function).app future futureArrow PUnit.unit) same
  rw [suppliedFunction_readout, suppliedFunction_readout] at readout
  exact Bool.false_ne_true readout

def initialOnly : Callers ⥤ Worlds :=
  (Functor.const Callers).obj (Opposite.op WalkingParallelPair.zero)

def caller : (initialOnly.op ⋙ base).Elements :=
  ⟨Opposite.op (Discrete.mk ()), PUnit.unit⟩

set_option backward.isDefEq.respectTransparency false in
/-- The canonical selected product map loses information even though its
identity and composition laws hold. -/
theorem selected_comparison_collapses :
    (productComparison initialOnly base arguments results).app caller (suppliedFunction false) =
      (productComparison initialOnly base arguments results).app caller (suppliedFunction true) := by
  let restricted := restrictFamily initialOnly base arguments
  let body := displayedToTotalElements restricted ⋙
    (codomainFunctor initialOnly base arguments).obj results
  apply (((nativeIso restricted).app body).app caller).toEquiv.injective
  apply DependentSection.ext
  intro point arrow argument
  exact PEmpty.elim argument

theorem selected_comparison_not_injective :
    ¬ Function.Injective ((productComparison initialOnly base arguments results).app caller) := by
  intro injective
  exact suppliedFunctions_distinct (injective selected_comparison_collapses)

/-- This theory route genuinely exchanges the two future arrows. -/
def exchange : Worlds ⥤ Worlds :=
  DisplayedPresheafTheoryTransformationCoherenceControls.exchange.op

def exchangeOrigin : (exchange.op ⋙ base).Elements := origin
def exchangeFuture : (exchange.op ⋙ base).Elements := future
def exchangeArrow : exchangeOrigin ⟶ exchangeFuture := futureArrow

set_option backward.isDefEq.respectTransparency false in
theorem exchange_selected_readout (value : Bool) :
    ((((nativeIso (restrictFamily exchange base arguments)).hom.app
      (displayedToTotalElements (restrictFamily exchange base arguments) ⋙
        (codomainFunctor exchange base arguments).obj results)).app exchangeOrigin
      ((productComparison exchange base arguments results).app exchangeOrigin
        (suppliedFunction value))).app exchangeFuture exchangeArrow PUnit.unit) = value := by
  rw [productComparison_readout]
  have inverse := congrArg (fun operation => operation.app origin (suppliedSection value))
    ((nativeIso arguments).inv_hom_id_app (displayedToTotalElements arguments ⋙ results))
  have result := congrArg (fun valueSection :
      DependentSection arguments (displayedToTotalElements arguments ⋙ results) origin =>
    valueSection.app future ((Functor.Elements.precomp exchange.op base).map exchangeArrow) PUnit.unit) inverse
  exact result


/-- The positive route retains a distinction actually lost by the initial
world restriction. Both statements concern the same selected Π map. -/
theorem exchange_selected_functions_distinct :
    (productComparison exchange base arguments results).app exchangeOrigin (suppliedFunction false) ≠
      (productComparison exchange base arguments results).app exchangeOrigin (suppliedFunction true) := by
  intro same
  have readout := congrArg (fun function =>
    (((nativeIso (restrictFamily exchange base arguments)).hom.app
      (displayedToTotalElements (restrictFamily exchange base arguments) ⋙
        (codomainFunctor exchange base arguments).obj results)).app exchangeOrigin
      function).app exchangeFuture exchangeArrow PUnit.unit) same
  rw [exchange_selected_readout, exchange_selected_readout] at readout
  exact Bool.false_ne_true readout

end Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherenceControls
