import Mettapedia.TypeTheory.IdentityRouteCapabilities
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation

/-!
# Mode-comparison thinness is independent of identity-route structure

Two unrelated uses of “thin” must not be conflated:

* local thinness of a globular mode sector says that parallel comparison
  cells between fixed translations are unique;
* route UIP says that parallel identity-shaped routes between fixed terms are
  unique.

Endpoint reflection is a third property: an identity-shaped route forces its
source and target terms to be equal.  This module combines existing concrete
models into a choice matrix.  The actual locally thin
operational/intensional/extensional comparison sector coexists with all four
combinations of route UIP and endpoint reflection.  Conversely, both UIP and
non-UIP route layers coexist with a thick selected mode-cell fibre.

These are non-implication results.  A one-object Boolean route groupoid is a
finite discriminator, not an implementation of cubical identity or an
infinite groupoid tower.  The matrix therefore keeps the object-language
identity discipline open while preventing the current mode-sector theorem
from selecting it accidentally.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality

open Mettapedia.CategoryTheory.Higher
open Mettapedia.CategoryTheory.Higher.GlobularSet
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.IdentityRouteCapabilities.Canary

universe uCell uObject uRoute

/-- One selected mode-cell boundary and one independent identity-route
layer. -/
structure Profile where
  tower : GlobularSet.{uCell}
  dimension : Nat
  Object : Type uObject
  identity : Layer.{uObject, uRoute} Object

namespace Profile

def ModeThin (profile : Profile) : Prop :=
  profile.tower.LocallyThinAt profile.dimension

def IdentityUIP (profile : Profile) : Prop :=
  RouteUIP profile.identity

def ReflectsEndpoints (profile : Profile) : Prop :=
  EndpointReflection profile.identity

end Profile

/-! ## Reusable thin and thick mode selections -/

/-- Pair any identity-route layer with the actual locally thin O/I/E
two-cell sector. -/
def withThinOIE
    {Object : Type uObject} (identity : Layer.{uObject, uRoute} Object) :
    Profile.{0, uObject, uRoute} where
  tower :=
    Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.tower
  dimension := 1
  Object := Object
  identity := identity

/-- Pair the same identity-route layer with a globular tower whose selected
two-cell fibre is constructively thick. -/
def withThickComparison
    {Object : Type uObject} (identity : Layer.{uObject, uRoute} Object) :
    Profile.{0, uObject, uRoute} where
  tower := ThinBelowThickNext.tower 1
  dimension := 1
  Object := Object
  identity := identity

theorem withThinOIE_modeThin
    {Object : Type uObject} (identity : Layer.{uObject, uRoute} Object) :
    (withThinOIE identity).ModeThin :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.locallyThinAt_twoCells

theorem withThickComparison_not_modeThin
    {Object : Type uObject} (identity : Layer.{uObject, uRoute} Object) :
    ¬ (withThickComparison identity).ModeThin :=
  ThinBelowThickNext.not_locallyThinAt_horizon 1

/-! ## The full UIP/reflection matrix over the thin O/I/E core -/

def thinReflectingPlural : Profile.{0, 0, 0} :=
  withThinOIE reflectedPlural

def thinNonreflectingSubsingleton : Profile.{0, 0, 0} :=
  withThinOIE indiscreteSubsingleton

def thinReflectingSubsingleton : Profile.{0, 0, 0} :=
  withThinOIE liftedEquality

def thinNonreflectingPlural : Profile.{0, 0, 0} :=
  withThinOIE indiscretePlural

/-- Every Boolean combination of route UIP and endpoint reflection is
compatible with the same locally thin mode-comparison sector. -/
theorem thin_mode_identity_four_cells :
    (thinReflectingPlural.ModeThin ∧
      ¬ thinReflectingPlural.IdentityUIP ∧
      thinReflectingPlural.ReflectsEndpoints) ∧
    (thinNonreflectingSubsingleton.ModeThin ∧
      thinNonreflectingSubsingleton.IdentityUIP ∧
      ¬ thinNonreflectingSubsingleton.ReflectsEndpoints) ∧
    (thinReflectingSubsingleton.ModeThin ∧
      thinReflectingSubsingleton.IdentityUIP ∧
      thinReflectingSubsingleton.ReflectsEndpoints) ∧
    (thinNonreflectingPlural.ModeThin ∧
      ¬ thinNonreflectingPlural.IdentityUIP ∧
      ¬ thinNonreflectingPlural.ReflectsEndpoints) := by
  exact
    ⟨⟨withThinOIE_modeThin _, reflectedPlural_not_uip,
        reflectedPlural_reflects⟩,
      ⟨withThinOIE_modeThin _, indiscreteSubsingleton_uip,
        indiscreteSubsingleton_not_reflects⟩,
      ⟨withThinOIE_modeThin _, liftedEquality_uip,
        liftedEquality_reflects⟩,
      ⟨withThinOIE_modeThin _, indiscretePlural_not_uip,
        indiscretePlural_not_reflects⟩⟩

/-! ## Cross-axis non-implications -/

theorem modeThin_does_not_imply_identityUIP :
    ¬ ∀ profile : Profile.{0, 0, 0},
      profile.ModeThin → profile.IdentityUIP := by
  intro purported
  exact reflectedPlural_not_uip
    (purported thinReflectingPlural (withThinOIE_modeThin _))

theorem identityUIP_does_not_imply_modeThin :
    ¬ ∀ profile : Profile.{0, 0, 0},
      profile.IdentityUIP → profile.ModeThin := by
  intro purported
  exact withThickComparison_not_modeThin liftedEquality
    (purported (withThickComparison liftedEquality)
      liftedEquality_uip)

theorem modeThin_does_not_imply_endpointReflection :
    ¬ ∀ profile : Profile.{0, 0, 0},
      profile.ModeThin → profile.ReflectsEndpoints := by
  intro purported
  exact indiscreteSubsingleton_not_reflects
    (purported thinNonreflectingSubsingleton (withThinOIE_modeThin _))

theorem endpointReflection_does_not_imply_modeThin :
    ¬ ∀ profile : Profile.{0, 0, 0},
      profile.ReflectsEndpoints → profile.ModeThin := by
  intro purported
  exact withThickComparison_not_modeThin liftedEquality
    (purported (withThickComparison liftedEquality)
      liftedEquality_reflects)

/-- Even a proof-relevant identity-route layer and a thick comparison layer
can coexist; neither feature is a substitute for the other. -/
theorem thick_mode_with_plural_identity :
    ¬ (withThickComparison reflectedPlural).ModeThin ∧
      ¬ (withThickComparison reflectedPlural).IdentityUIP ∧
      (withThickComparison reflectedPlural).ReflectsEndpoints :=
  ⟨withThickComparison_not_modeThin _,
    reflectedPlural_not_uip,
    reflectedPlural_reflects⟩

/-! ## Audited theorem crowns -/

#print axioms withThinOIE_modeThin
#print axioms withThickComparison_not_modeThin
#print axioms thin_mode_identity_four_cells
#print axioms modeThin_does_not_imply_identityUIP
#print axioms identityUIP_does_not_imply_modeThin
#print axioms modeThin_does_not_imply_endpointReflection
#print axioms endpointReflection_does_not_imply_modeThin
#print axioms thick_mode_with_plural_identity

end Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality
