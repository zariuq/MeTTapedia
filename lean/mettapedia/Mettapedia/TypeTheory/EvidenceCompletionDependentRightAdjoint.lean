import Mettapedia.TypeTheory.CwfDependentRightAdjoint
import Mettapedia.TypeTheory.OperationalFamilyCwf
import Mettapedia.TypeTheory.RouteFamilyCwf

/-!
# Dependent evidence completion and its reflexivity boundary

The context functor `evidenceCompletion` adds only reflexive routes to an
authored operational step relation.  Its dependent action is therefore exact:
an intensional family over the completed context restricts to primitive
steps, and a primitive-step-natural section extends uniquely across the new
reflexive routes.  This yields a genuine dependent right adjoint between the
operational-family and route-family CwFs.

The reverse direction has an explicit boundary.  An arbitrary operational
family over a route context may assign nonidentity transport to the selected
reflexive route.  Such a family cannot be reused unchanged as a route family.
The obstruction is exactly `ReflexivityCoherent`, not a failure of the context
adjunction itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.EvidenceCompletionDependentRightAdjoint

open Relation
open Mettapedia.TypeTheory.CwfDependentRightAdjoint
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.OperationalFamilyCwf
open Mettapedia.TypeTheory.RouteFamilyCwf

universe u

/-! ## Restriction along primitive routes -/

/-- Forget the newly adjoined reflexive routes in an intensional dependent
family, retaining transport along every authored operational step. -/
def restrictFamily (context : DynSys.{u})
    (family : RouteFamily (evidenceCompletion.obj context)) :
    DynFamily context where
  fibre point := family.fibre point
  transport step value := family.transport (.single step) value

@[simp]
theorem restrictFamily_fibre (context : DynSys.{u})
    (family : RouteFamily (evidenceCompletion.obj context))
    (point : context.carrier) :
    (restrictFamily context family).fibre point = family.fibre point :=
  rfl

@[simp]
theorem restrictFamily_transport (context : DynSys.{u})
    (family : RouteFamily (evidenceCompletion.obj context))
    {source target : context.carrier} (step : context.Step source target)
    (value : family.fibre source) :
    (restrictFamily context family).transport step value =
      family.transport (.single step) value :=
  rfl

/-- Restriction of dependent families commutes with operational
substitution. -/
theorem restrictFamily_natural {first last : DynSys.{u}}
    (family : RouteFamily (evidenceCompletion.obj last))
    (substitution : DynHom first last) :
    restrictFamily first
        (RouteFamily.reindex family (evidenceCompletion.map substitution)) =
      DynFamily.reindex (restrictFamily last family) substitution :=
  rfl

/-! ## Sections across evidence completion -/

/-- Restrict a route-natural section to primitive operational steps. -/
def restrictSection (context : DynSys.{u})
    {family : RouteFamily (evidenceCompletion.obj context)}
    (term : RouteSection family) :
    DynSection (restrictFamily context family) where
  value point := term.value point
  natural step := term.natural (.single step)

/-- Extend a primitive-step-natural section across the freely adjoined
reflexive routes. -/
def extendSection (context : DynSys.{u})
    {family : RouteFamily (evidenceCompletion.obj context)}
    (term : DynSection (restrictFamily context family)) :
    RouteSection family where
  value point := term.value point
  natural route := by
    cases route with
    | refl => exact family.transport_refl _ _
    | single step => exact term.natural step

/-- Restriction and extension give an exact equivalence of dependent
sections. -/
def sectionEquiv (context : DynSys.{u})
    (family : RouteFamily (evidenceCompletion.obj context)) :
    RouteSection family ≃ DynSection (restrictFamily context family) where
  toFun := restrictSection context
  invFun := extendSection context
  left_inv term := by
    apply RouteSection.ext
    rfl
  right_inv term := by
    apply DynSection.ext
    rfl

/-- The section equivalence is natural under operational substitution. -/
theorem restrictSection_natural {first last : DynSys.{u}}
    (family : RouteFamily (evidenceCompletion.obj last))
    (term : RouteSection family) (substitution : DynHom first last) :
    HEq
      (restrictSection first
        (RouteSection.reindex term (evidenceCompletion.map substitution)))
      (DynSection.reindex (restrictSection last term) substitution) :=
  HEq.rfl

/-! ## The dependent right adjoint -/

/-- Free reflexive evidence completion lifts from contexts to a dependent
right adjoint.  The right action forgets only the adjoined reflexive routes;
the term equivalence proves that no section information is lost. -/
def evidenceCompletionDra :
    DependentRightAdjoint dynCwf routeCwf where
  leftContext context := evidenceCompletion.obj context
  leftSub substitution := evidenceCompletion.map substitution
  leftSub_id context := by
    apply RouteHom.ext
    intro point
    rfl
  leftSub_comp later earlier := by
    apply RouteHom.ext
    intro point
    rfl
  rightType context family := restrictFamily context family
  rightType_natural := restrictFamily_natural
  termEquiv := sectionEquiv
  termEquiv_natural := restrictSection_natural

/-- The evidence-completion DRA over the selected terminal CwFs.  As usual
for a DRA, its context functor is not required to preserve the chosen terminal
context on the nose. -/
def evidenceCompletionDraWithTerminal :
    DependentRightAdjointWithTerminal dynCwfWithTerminal
      routeCwfWithTerminal where
  toDra := evidenceCompletionDra

/-! ## Reverse boundary: operational transport need not respect reflexivity -/

/-- The exact extra law required to reuse an operational family over the
forgotten route dynamics as an intensional route family with the same fibres
and transport. -/
def ReflexivityCoherent {context : RouteType.{u}}
    (family : DynFamily (forgetReflexivity.obj context)) : Prop :=
  forall (point : context.carrier) (value : family.fibre point),
    family.transport (context.route_refl point) value = value

/-- A reflexivity-coherent operational family can be reused as a route
family without changing either its fibres or its transport operation. -/
def liftReflexivityCoherent {context : RouteType.{u}}
    (family : DynFamily (forgetReflexivity.obj context))
    (coherent : ReflexivityCoherent family) : RouteFamily context where
  fibre := family.fibre
  transport := family.transport
  transport_refl := coherent

@[simp]
theorem liftReflexivityCoherent_fibre {context : RouteType.{u}}
    (family : DynFamily (forgetReflexivity.obj context))
    (coherent : ReflexivityCoherent family) (point : context.carrier) :
    (liftReflexivityCoherent family coherent).fibre point =
      family.fibre point :=
  rfl

@[simp]
theorem liftReflexivityCoherent_transport {context : RouteType.{u}}
    (family : DynFamily (forgetReflexivity.obj context))
    (coherent : ReflexivityCoherent family)
    {source target : context.carrier} (route : context.Route source target)
    (value : family.fibre source) :
    (liftReflexivityCoherent family coherent).transport route value =
      family.transport route value :=
  rfl

/-- Forget only the route family's reflexivity proof, retaining its fibre and
transport data definitionally. -/
def forgetRouteFamily {context : RouteType.{u}}
    (family : RouteFamily context) :
    DynFamily (forgetReflexivity.obj context) where
  fibre := family.fibre
  transport := family.transport

/-- A route-family lift that reuses an operational family exactly after
forgetting only the route-family law.  The computational data may not be
repaired or restricted. -/
structure UnchangedRouteLift {context : RouteType.{u}}
    (family : DynFamily (forgetReflexivity.obj context)) where
  routeFamily : RouteFamily context
  forget_eq : forgetRouteFamily routeFamily = family

/-- Reflexivity coherence is necessary and sufficient for an unchanged
route-family lift. -/
theorem nonempty_unchangedRouteLift_iff {context : RouteType.{u}}
    (family : DynFamily (forgetReflexivity.obj context)) :
    Nonempty (UnchangedRouteLift family) ↔ ReflexivityCoherent family := by
  constructor
  · rintro ⟨⟨routeFamily, forget_eq⟩⟩
    subst family
    exact routeFamily.transport_refl
  · intro coherent
    exact
      ⟨{ routeFamily := liftReflexivityCoherent family coherent
         forget_eq := rfl }⟩

/-- Positive control: constant operational transport satisfies the required
reflexivity law and lifts unchanged. -/
theorem constant_reflexivityCoherent (context : RouteType.{u})
    (valueType : Type u) :
    ReflexivityCoherent
      (DynFamily.constant (forgetReflexivity.obj context) valueType) := by
  intro point value
  rfl

namespace ReflexivityCanary

/-- A one-point intensional context with its selected reflexive route. -/
def point : RouteType.{0} where
  carrier := PUnit
  Route _ _ := True
  route_refl _ := trivial

/-- This is a valid operational family after forgetting reflexivity as a
law, but its transport flips Boolean values even on the selected reflexive
route. -/
def flipOnReflexivity : DynFamily (forgetReflexivity.obj point) where
  fibre _ := Bool
  transport _ value := !value

/-- The operational family cannot be reused unchanged as an intensional
route family: its reflexive transport is observably nonidentity. -/
theorem flipOnReflexivity_not_coherent :
    ¬ ReflexivityCoherent flipOnReflexivity := by
  intro coherent
  have contradiction := coherent PUnit.unit false
  change true = false at contradiction
  exact Bool.noConfusion contradiction

/-- Equivalently, the flipping operational family has no unchanged
route-family lift. -/
theorem flipOnReflexivity_no_unchanged_lift :
    ¬ Nonempty (UnchangedRouteLift flipOnReflexivity) := by
  rw [nonempty_unchangedRouteLift_iff]
  exact flipOnReflexivity_not_coherent

end ReflexivityCanary

/-- The two directions of the context adjunction have genuinely asymmetric
dependent obligations: evidence completion always supports the DRA above,
whereas unchanged reverse reuse requires an additional law and can fail. -/
theorem dependent_evidence_boundary :
    Nonempty
        (DependentRightAdjoint dynCwf.{0} routeCwf.{0}) ∧
      (∃ (context : RouteType.{0}) (family : DynFamily
          (forgetReflexivity.obj context)),
        ¬ Nonempty (UnchangedRouteLift family)) :=
  ⟨⟨evidenceCompletionDra.{0}⟩,
    ⟨ReflexivityCanary.point, ReflexivityCanary.flipOnReflexivity,
      ReflexivityCanary.flipOnReflexivity_no_unchanged_lift⟩⟩

#print axioms restrictFamily_natural
#print axioms sectionEquiv
#print axioms restrictSection_natural
#print axioms evidenceCompletionDra
#print axioms evidenceCompletionDraWithTerminal
#print axioms constant_reflexivityCoherent
#print axioms nonempty_unchangedRouteLift_iff
#print axioms ReflexivityCanary.flipOnReflexivity_not_coherent
#print axioms ReflexivityCanary.flipOnReflexivity_no_unchanged_lift
#print axioms dependent_evidence_boundary

end Mettapedia.TypeTheory.EvidenceCompletionDependentRightAdjoint
