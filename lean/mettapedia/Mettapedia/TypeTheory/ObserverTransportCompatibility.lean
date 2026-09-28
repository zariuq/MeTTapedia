import Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
import Mettapedia.TypeTheory.UnivalentUniverseTransport

/-!
# Erasure and dependent transport

An erasure into the extensional mode sends an object to its readout, a route to
the equation between the readouts of its ends, and a value to an observation
over the readout of its object.  Transport in the extensional mode runs along
equations (`transportE`).  For a family with transport along routes, the
compatibility law of a fibre observer `E` is

`E_B (transport p a) = transport_E (E p) (E_A a)`  (`TransportCompatible`).

**The naive law is false.**  The erasure of a loop is an equation of a readout
with itself, along which extensional transport is the identity.  So the law
requires the observer to be blind to transport along loops, and an observer
that keeps the value fails it as soon as a loop moves a point
(`not_transportCompatible_of_loop_moves`).  In the universe of finite types,
whose identity of types is equivalence, transport along the negation path of
`Bool` moves `true`, and the value observer is not compatible with transport
(`FiniteUniverse.value_not_transportCompatible`).

**The corrected law.**  A fibre observer is compatible with transport exactly
when, read on the total space of the family, it factors through the extensional
readout of the total space (`transportCompatible_iff_factors`): these are the
observers that factor through the extensional mode.  The readout of the total
space is compatible itself (`totalReadout_transportCompatible`), and so is every
observer computed from it (`transportCompatible_of_readout`).

The transport of the impredicative value model is an instance, with the
relation of the target type's pack as the relation between the two sides
(`ValueSide.TransportReadout`).
-/

set_option autoImplicit false

universe uBase uFamily uObject uRoute uFiber uObserved

namespace Mettapedia.TypeTheory.ObserverTransportCompatibility

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.RouteTransportDiscriminator
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

/-! ## Transport in the extensional mode -/

section Extensional

variable {Base : Type uBase} (Family : Base → Type uFamily)

/-- Transport in the extensional mode: along an equation of readouts. -/
def transportE {first second : Base} (equation : first = second) (value : Family first) :
    Family second :=
  equation ▸ value

@[simp] theorem transportE_rfl {base : Base} (value : Family base) :
    transportE Family rfl value = value :=
  rfl

/-- Along an equation of a readout with itself, extensional transport is the
identity. -/
theorem transportE_self {base : Base} (equation : base = base) (value : Family base) :
    transportE Family equation value = value :=
  rfl

/-- In a constant family, extensional transport is the identity. -/
theorem transportE_const {Value : Type uFamily} {first second : Base}
    (equation : first = second) (value : Value) :
    transportE (fun _ => Value) equation value = value := by
  subst equation
  rfl

/-- A square closed by extensional transport is an equation of points of the
total space. -/
theorem eq_transportE_iff {first second : Base} (equation : first = second)
    (value : Family first) (value' : Family second) :
    value' = transportE Family equation value ↔
      (⟨second, value'⟩ : Σ base, Family base) = ⟨first, value⟩ := by
  subst equation
  constructor
  · intro same
    rw [same]
    rfl
  · intro same
    exact eq_of_heq (Sigma.mk.inj same).2

end Extensional

/-! ## The compatibility law for a transport family -/

section Family

variable {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
variable {groupoid : RouteGroupoid layer}
variable (family : TransportFamily.{uObject, uRoute, uFiber} layer groupoid)

variable (layer) in
/-- The base as an intensional route type: an object is routed to another when
some route joins them. -/
def baseRoutes : RouteType.{uObject} where
  carrier := Object
  Route source target := Nonempty (layer.Route source target)
  route_refl object := ⟨layer.refl object⟩

variable (layer) in
/-- The extensional readout of the base. -/
abbrev Readout : Type uObject :=
  (routeQuotient.obj (baseRoutes layer)).carrier

variable (layer) in
/-- The erasure of an object: its readout. -/
def erase (object : Object) : Readout layer :=
  Quot.mk _ object

/-- The erasure of a route: the equation between the readouts of its ends.
Parallel routes have one erasure, and a loop's is an equation of a readout with
itself. -/
theorem erasePath {source target : Object} (route : layer.Route source target) :
    erase layer source = erase layer target :=
  Quot.sound ⟨route⟩

/-- The comprehension of the family as an intensional route type: a point of the
total space is routed to its transport along any route. -/
def totalRoutes : RouteType.{max uObject uFiber} where
  carrier := Σ object, family.Fibre object
  Route first second :=
    ∃ route : layer.Route first.1 second.1, family.transport route first.2 = second.2
  route_refl point := ⟨layer.refl point.1, family.transport_refl point.1 point.2⟩

/-- The extensional readout of the total space. -/
def totalReadout (point : Σ object, family.Fibre object) :
    (routeQuotient.obj (totalRoutes family)).carrier :=
  Quot.mk _ point

/-- A value and its transport have one readout of the total space. -/
theorem totalReadout_transport {source target : Object} (route : layer.Route source target)
    (value : family.Fibre source) :
    totalReadout family ⟨target, family.transport route value⟩ =
      totalReadout family ⟨source, value⟩ :=
  (Quot.sound ⟨route, rfl⟩).symm

variable {Observed : Readout layer → Type uObserved}

/-- **The compatibility law** `E_B (transport p a) = transport_E (E p) (E_A a)`
for a fibre observer `E`, whose observation of a value lies over the readout of
its object. -/
def TransportCompatible (observe : ∀ object, family.Fibre object → Observed (erase layer object)) :
    Prop :=
  ∀ ⦃source target : Object⦄ (route : layer.Route source target) (value : family.Fibre source),
    observe target (family.transport route value) =
      transportE Observed (erasePath route) (observe source value)

/-- A fibre observer read on the total space, over the readout of the base. -/
def totalObservation (observe : ∀ object, family.Fibre object → Observed (erase layer object))
    (point : Σ object, family.Fibre object) : Σ readout, Observed readout :=
  ⟨erase layer point.1, observe point.1 point.2⟩

/-- **The corrected law.**  A fibre observer commutes with transport exactly when,
read on the total space, it factors through the extensional readout of the
total space. -/
theorem transportCompatible_iff_factors
    (observe : ∀ object, family.Fibre object → Observed (erase layer object)) :
    TransportCompatible family observe ↔
      Factors (totalReadout family) (totalObservation family observe) := by
  constructor
  · intro compatible
    refine ⟨Quot.lift (totalObservation family observe) ?_, fun _ => rfl⟩
    rintro ⟨source, value⟩ ⟨target, image⟩ ⟨route, transported⟩
    change layer.Route source target at route
    change family.transport route value = image at transported
    subst transported
    exact ((eq_transportE_iff Observed (erasePath route) _ _).1 (compatible route value)).symm
  · intro factors source target route value
    exact (eq_transportE_iff Observed (erasePath route) _ _).2
      (factors.constantOnFibers _ _ (totalReadout_transport family route value))

/-- The readout of the total space commutes with transport. -/
theorem totalReadout_transportCompatible :
    TransportCompatible (Observed := fun _ => (routeQuotient.obj (totalRoutes family)).carrier)
      family (fun object value => totalReadout family ⟨object, value⟩) := by
  intro source target route value
  rw [transportE_const]
  exact totalReadout_transport family route value

/-- Every observer computed from the readout of the total space commutes with
transport. -/
theorem transportCompatible_of_readout {Value : Type uObserved}
    (read : (routeQuotient.obj (totalRoutes family)).carrier → Value) :
    TransportCompatible (Observed := fun _ => Value) family
      (fun object value => read (totalReadout family ⟨object, value⟩)) := by
  intro source target route value
  rw [transportE_const]
  exact congrArg read (totalReadout_transport family route value)

/-- **The naive law fails** for an observer that keeps the value at an object
where a loop moves a point: the erasure of the loop is an equation of a readout
with itself, whose extensional transport is the identity. -/
theorem not_transportCompatible_of_loop_moves {object : Object}
    (loop : layer.Route object object) {value : family.Fibre object}
    (moves : family.transport loop value ≠ value)
    (observe : ∀ object, family.Fibre object → Observed (erase layer object))
    (keeps : Function.Injective (observe object)) :
    ¬ TransportCompatible family observe := fun compatible =>
  moves (keeps ((compatible loop value).trans (transportE_self Observed _ _)))

end Family

/-! ## The universe of finite types -/

namespace FiniteUniverse

open UnivalentUniverseTransport
open UnivalentUniverseTransport.FiniteUniverse

/-- The value observer of the universe of finite types: a decoded value with its
code. -/
def valueObserver (code : Code) (value : El code) : Σ code, El code :=
  ⟨code, value⟩

/-- The observations of the value observer, the same over every readout. -/
abbrev Values (_ : Readout (pathLayer El)) : Type := Σ code, El code

/-- The value observer keeps the value. -/
theorem valueObserver_injective (code : Code) : Function.Injective (valueObserver code) :=
  fun _ _ same => eq_of_heq (Sigma.mk.inj same).2

/-- Transport along the negation path moves `true`. -/
theorem notPath_moves_true : (decoding El).transport notPath true ≠ true := by
  rw [transport_notPath_true]
  exact Bool.false_ne_true

/-- **The naive law is false**: the value observer does not commute with
transport in the universe of finite types. -/
theorem value_not_transportCompatible :
    ¬ TransportCompatible (Observed := Values) (decoding El) valueObserver :=
  not_transportCompatible_of_loop_moves (Observed := Values) (decoding El) notPath
    notPath_moves_true valueObserver (valueObserver_injective .bool)

/-- Equivalently, the value observer does not factor through the extensional
readout of the total space. -/
theorem value_not_factors :
    ¬ Factors (totalReadout (decoding El))
      (totalObservation (Observed := Values) (decoding El) valueObserver) :=
  fun factors => value_not_transportCompatible
    ((transportCompatible_iff_factors (Observed := Values) (decoding El) valueObserver).2 factors)

/-- **Positive twin**: the readout of the total space of the decoding family
commutes with transport. -/
theorem totalReadout_compatible :
    TransportCompatible (Observed := fun _ => (routeQuotient.obj (totalRoutes (decoding El))).carrier)
      (decoding El) (fun code value => totalReadout (decoding El) ⟨code, value⟩) :=
  totalReadout_transportCompatible (decoding El)

end FiniteUniverse

end Mettapedia.TypeTheory.ObserverTransportCompatibility
