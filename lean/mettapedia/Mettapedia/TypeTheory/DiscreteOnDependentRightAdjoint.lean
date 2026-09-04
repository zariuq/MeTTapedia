import Mettapedia.TypeTheory.CwfDependentRightAdjoint
import Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

/-!
# Dependent discrete embedding and the route-action boundary

The discrete context functor sends a bare extensional carrier to the route
context whose only routes are equalities.  Dependent sections over this
context contain no extra information: route naturality is forced by the
reflexivity law.  Consequently the discrete embedding lifts to a dependent
right adjoint from the ordinary set-family CwF to the route-family CwF.

The adjacent points functor has a different dependent obligation.  Pulling an
arbitrary point-indexed family back to a route context requires transport
along every route.  Such transport is extra structure and may not exist.  A
two-point codiscrete context with an inhabited fibre at one point and an empty
fibre at the other gives the minimal obstruction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DiscreteOnDependentRightAdjoint

open Mettapedia.TypeTheory.CwfDependentRightAdjoint
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.RouteFamilyCwf
open Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

universe u

/-! ## Families and sections over a discrete route context -/

/-- Read the fibres of a route family over a discrete context as an ordinary
extensional family. -/
def discreteFibres (context : ExtType.{u})
    (family : RouteFamily (discreteOn.obj context)) :
    context.carrier -> Type u :=
  family.fibre

/-- Discrete fibre readout commutes with extensional substitution. -/
theorem discreteFibres_natural {first last : ExtType.{u}}
    (family : RouteFamily (discreteOn.obj last))
    (substitution : ExtHom first last) :
    discreteFibres first
        (RouteFamily.reindex family (discreteOn.map substitution)) =
      extCwf.tySub (discreteFibres last family) substitution :=
  rfl

/-- Forget route naturality from a section over a discrete context. -/
def forgetDiscreteSection (context : ExtType.{u})
    {family : RouteFamily (discreteOn.obj context)}
    (term : RouteSection family) :
    forall point : context.carrier, family.fibre point :=
  term.value

/-- Every ordinary dependent section is route-natural over a discrete
context. -/
def restoreDiscreteSection (context : ExtType.{u})
    {family : RouteFamily (discreteOn.obj context)}
    (term : forall point : context.carrier, family.fibre point) :
    RouteSection family where
  value := term
  natural route := by
    cases route
    exact family.transport_refl _ _

/-- Route-natural and ordinary sections agree exactly over a discrete
context. -/
def discreteSectionEquiv (context : ExtType.{u})
    (family : RouteFamily (discreteOn.obj context)) :
    RouteSection family ≃
      (forall point : context.carrier, family.fibre point) where
  toFun := forgetDiscreteSection context
  invFun := restoreDiscreteSection context
  left_inv term := by
    apply RouteSection.ext
    rfl
  right_inv _ := rfl

/-- The discrete section equivalence is natural under extensional
substitution. -/
theorem forgetDiscreteSection_natural {first last : ExtType.{u}}
    (family : RouteFamily (discreteOn.obj last))
    (term : RouteSection family) (substitution : ExtHom first last) :
    HEq
      (forgetDiscreteSection first
        (RouteSection.reindex term (discreteOn.map substitution)))
      (extCwf.tmSub (forgetDiscreteSection last term) substitution) :=
  HEq.rfl

/-! ## The dependent right adjoint -/

/-- The discrete embedding lifts to a dependent right adjoint.  Its right
action simply reads the fibres, and the term equivalence proves that the
equality-only route discipline adds no term-level restriction. -/
def discreteOnDra : DependentRightAdjoint extCwf routeCwf where
  leftContext context := discreteOn.obj context
  leftSub substitution := discreteOn.map substitution
  leftSub_id context := by
    apply RouteHom.ext
    intro point
    rfl
  leftSub_comp later earlier := by
    apply RouteHom.ext
    intro point
    rfl
  rightType context family := discreteFibres context family
  rightType_natural := discreteFibres_natural
  termEquiv := discreteSectionEquiv
  termEquiv_natural := forgetDiscreteSection_natural

/-- The discrete DRA bundled over the chosen terminal CwFs. -/
def discreteOnDraWithTerminal :
    DependentRightAdjointWithTerminal extCwfWithTerminal
      routeCwfWithTerminal where
  toDra := discreteOnDra

/-! ## Points boundary: fibres alone do not supply route transport -/

/-- The additional action needed to turn a point-indexed family into a
route-indexed dependent family without changing its fibres. -/
structure RouteAction (context : RouteType.{u})
    (family : context.carrier -> Type u) where
  transport : {source target : context.carrier} ->
    context.Route source target -> family source -> family target
  transport_refl : forall (point : context.carrier) (value : family point),
    transport (context.route_refl point) value = value

namespace RouteAction

/-- Package a route action as a route family. -/
def toRouteFamily {context : RouteType.{u}}
    {family : context.carrier -> Type u}
    (action : RouteAction context family) : RouteFamily context where
  fibre := family
  transport := action.transport
  transport_refl := action.transport_refl

/-- Positive control: every constant family has the identity route action. -/
def constant (context : RouteType.{u}) (valueType : Type u) :
    RouteAction context (fun _ => valueType) where
  transport _ value := value
  transport_refl _ _ := rfl

end RouteAction

namespace PointsCanary

/-- A codiscrete two-point route context: in particular there is a route
from `false` to `true`. -/
def context : RouteType.{0} where
  carrier := Bool
  Route _ _ := True
  route_refl _ := trivial

/-- An extensional family with an inhabited fibre at `false` and an empty
fibre at `true`. -/
def family : context.carrier -> Type
  | false => PUnit
  | true => PEmpty

/-- No route action can transport the inhabitant along the route from
`false` to `true`. -/
theorem noRouteAction : ¬ Nonempty (RouteAction context family) := by
  rintro ⟨action⟩
  exact PEmpty.elim
    (action.transport (source := false) (target := true) trivial PUnit.unit)

end PointsCanary

/-- The discrete embedding has an exact dependent lift, while bare point
fibres do not universally determine transport back along routes. -/
theorem discrete_and_points_dependent_boundary :
    Nonempty (DependentRightAdjoint extCwf.{0} routeCwf.{0}) ∧
      (∃ (context : RouteType.{0})
        (family : context.carrier -> Type),
        ¬ Nonempty (RouteAction context family)) :=
  ⟨⟨discreteOnDra.{0}⟩,
    ⟨PointsCanary.context, PointsCanary.family,
      PointsCanary.noRouteAction⟩⟩

#print axioms discreteFibres_natural
#print axioms discreteSectionEquiv
#print axioms forgetDiscreteSection_natural
#print axioms discreteOnDra
#print axioms discreteOnDraWithTerminal
#print axioms RouteAction.constant
#print axioms PointsCanary.noRouteAction
#print axioms discrete_and_points_dependent_boundary

end Mettapedia.TypeTheory.DiscreteOnDependentRightAdjoint
