import Mettapedia.TypeTheory.DependencyExtensionalityReadoutSquare

/-!
# Application-extensional collapse of a dependent function space

A beta function carrier may retain distinctions that no application can
observe.  Its application-extensional collapse is the quotient by pointwise
application equality.  The construction works uniformly for constant and
genuinely varying result families.

The quotient has the expected universal property: precisely the observers
constant on pointwise-application classes descend through it.  It is
equivalent to the carrier of extensional sections, while the original-to-
quotient map is injective exactly when the original function carrier was
already application-extensional.

This is a local extensional reflection of one function space.  It does not
globally quotient syntax, proof routes, code, occurrences, provenance, or
cost, and it does not select an equality discipline for an entire language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ApplicationExtensionalCollapse

open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality
open Mettapedia.TypeTheory.DependencyExtensionalityReadoutSquare

universe uDomain uCodomain uFunction uObservation

variable {Domain : Type uDomain} {Codomain : Domain → Type uCodomain}
variable (space : DependentFunctionSpace.{uDomain, uCodomain, uFunction}
  Domain Codomain)

/-- Pointwise application equality on a retained function carrier. -/
def applicationSetoid : Setoid space.Function where
  r := fun left right =>
    ∀ argument, space.application left argument =
      space.application right argument
  iseqv := by
    constructor
    · intro function argument
      rfl
    · intro left right related argument
      exact (related argument).symm
    · intro first second third firstSecond secondThird argument
      exact (firstSecond argument).trans (secondThird argument)

/-- The application-extensional reflection of a beta function space. -/
def collapse : DependentFunctionSpace.{uDomain, uCodomain, uFunction}
    Domain Codomain where
  Function := Quotient (applicationSetoid space)
  abstraction := fun body =>
    Quotient.mk (applicationSetoid space) (space.abstraction body)
  application := fun function argument =>
    Quotient.liftOn function
      (fun retained => space.application retained argument)
      (by
        intro left right related
        exact related argument)
  beta := by
    intro body argument
    exact space.beta body argument

/-- The canonical map into the extensional collapse. -/
def collapseMap : space.Function → (collapse space).Function :=
  Quotient.mk (applicationSetoid space)

@[simp] theorem collapse_application_collapseMap
    (function : space.Function) (argument : Domain) :
    (collapse space).application (collapseMap space function) argument =
      space.application function argument :=
  rfl

/-- Every quotient class has an original representative. -/
theorem collapseMap_surjective : Function.Surjective (collapseMap space) := by
  intro functionClass
  refine Quotient.inductionOn functionClass ?_
  intro function
  exact ⟨function, rfl⟩

/-- The quotient function carrier is application-extensional by
construction. -/
theorem collapse_applicationExtensional :
    (collapse space).ApplicationExtensional := by
  intro left right pointwise
  revert pointwise
  refine Quotient.inductionOn₂ left right ?_
  intro retainedLeft retainedRight pointwise
  apply Quotient.sound
  intro argument
  exact pointwise argument

/-- The canonical collapse map is injective exactly when the original
carrier was already application-extensional. -/
theorem collapseMap_injective_iff :
    Function.Injective (collapseMap space) ↔
      space.ApplicationExtensional := by
  constructor
  · intro injective left right pointwise
    apply injective
    apply Quotient.sound
    exact pointwise
  · intro extensional left right sameClass
    apply extensional left right
    have related : (applicationSetoid space).r left right :=
      Quotient.exact sameClass
    exact related

/-- Since the collapse map is always surjective, it is bijective exactly for
an already application-extensional carrier. -/
theorem collapseMap_bijective_iff :
    Function.Bijective (collapseMap space) ↔
      space.ApplicationExtensional := by
  constructor
  · intro bijective
    exact (collapseMap_injective_iff space).1 bijective.1
  · intro extensional
    exact ⟨(collapseMap_injective_iff space).2 extensional,
      collapseMap_surjective space⟩

/-- An observer is insensitive to the distinctions collapsed by application
when it is constant on pointwise-equal functions. -/
def ApplicationInvariant {Observation : Type uObservation}
    (observer : space.Function → Observation) : Prop :=
  ∀ left right,
    (∀ argument, space.application left argument =
      space.application right argument) →
    observer left = observer right

/-- Descend an application-invariant observer to the quotient. -/
def descendObserver {Observation : Type uObservation}
    (observer : space.Function → Observation)
    (invariant : ApplicationInvariant space observer) :
    (collapse space).Function → Observation :=
  fun functionClass =>
    Quotient.liftOn functionClass observer
      (by
        intro left right related
        exact invariant left right related)

@[simp] theorem descendObserver_collapseMap
    {Observation : Type uObservation}
    (observer : space.Function → Observation)
    (invariant : ApplicationInvariant space observer)
    (function : space.Function) :
    descendObserver space observer invariant (collapseMap space function) =
      observer function :=
  rfl

/-- Any function out of the quotient induces an application-invariant
observer on the original carrier. -/
theorem applicationInvariant_of_descended
    {Observation : Type uObservation}
    (observer : (collapse space).Function → Observation) :
    ApplicationInvariant space (fun function =>
      observer (collapseMap space function)) := by
  intro left right pointwise
  exact congrArg observer (Quotient.sound pointwise)

/-- The descended observer is uniquely determined by its values on original
functions. -/
theorem descendObserver_unique
    {Observation : Type uObservation}
    (observer : space.Function → Observation)
    (invariant : ApplicationInvariant space observer)
    (candidate : (collapse space).Function → Observation)
    (agrees : ∀ function,
      candidate (collapseMap space function) = observer function) :
    candidate = descendObserver space observer invariant := by
  funext functionClass
  refine Quotient.inductionOn functionClass ?_
  intro function
  exact agrees function

/-- Application on the quotient is an exact readout to extensional
sections. -/
theorem collapse_functionReadout_exact :
    (functionReadout (collapse space)).Exact :=
  (functionReadout_exact_iff_applicationExtensional (collapse space)).2
    (collapse_applicationExtensional space)

/-- The quotient carrier is therefore canonically equivalent to the type of
extensional dependent sections. -/
def collapseSectionEquiv :
    (collapse space).Function ≃ ((argument : Domain) → Codomain argument) where
  toFun := (collapse space).application
  invFun := (collapse space).abstraction
  left_inv := by
    intro function
    apply collapse_applicationExtensional space
    intro argument
    exact (collapse space).beta ((collapse space).application function) argument
  right_inv := by
    intro body
    funext argument
    exact (collapse space).beta body argument

/-! ## Constant-family and genuinely dependent controls -/

namespace Canary

/-- The extensional simple carrier is unchanged up to bijection. -/
theorem simpleExtensional_collapse_bijective :
    Function.Bijective (collapseMap simpleExtensional.{0}) :=
  (collapseMap_bijective_iff simpleExtensional.{0}).2
    simpleExtensional_applicationExtensional

/-- The route-sensitive simple carrier is genuinely collapsed. -/
theorem simpleRoute_collapse_not_injective :
    ¬ Function.Injective (collapseMap simpleRouteSensitive.{0}) := by
  rw [collapseMap_injective_iff simpleRouteSensitive.{0}]
  exact simpleRouteSensitive_not_applicationExtensional

theorem simpleRoute_pair_collapses :
    collapseMap simpleRouteSensitive.{0} (false, false) =
      collapseMap simpleRouteSensitive.{0} (false, true) := by
  apply Quotient.sound
  intro argument
  cases argument
  rfl

/-- The extensional genuinely dependent carrier is unchanged up to
bijection. -/
theorem dependentExtensional_collapse_bijective :
    Function.Bijective (collapseMap dependentExtensional) :=
  (collapseMap_bijective_iff dependentExtensional).2
    dependentExtensional_applicationExtensional

/-- The same route erasure occurs for a genuinely varying result family. -/
theorem dependentRoute_collapse_not_injective :
    ¬ Function.Injective (collapseMap dependentRouteSensitive) := by
  rw [collapseMap_injective_iff dependentRouteSensitive]
  exact dependentRouteSensitive_not_applicationExtensional

theorem dependentRoute_pair_collapses :
    collapseMap dependentRouteSensitive (false, false) =
      collapseMap dependentRouteSensitive (false, true) := by
  apply Quotient.sound
  intro argument
  cases argument <;> rfl

/-- Extensional collapse is independent of whether result types are constant
or genuinely dependent. -/
theorem dependency_extensional_collapse_boundary :
    Function.Bijective (collapseMap simpleExtensional.{0}) ∧
      ¬ Function.Injective (collapseMap simpleRouteSensitive.{0}) ∧
      Function.Bijective (collapseMap dependentExtensional) ∧
      ¬ Function.Injective (collapseMap dependentRouteSensitive) ∧
      (¬ ∃ Constant : Type,
        ∀ argument, Nonempty (varyingBoolFamily argument ≃ Constant)) :=
  ⟨simpleExtensional_collapse_bijective,
    simpleRoute_collapse_not_injective,
    dependentExtensional_collapse_bijective,
    dependentRoute_collapse_not_injective,
    varyingBoolFamily_not_constant⟩

end Canary

#print axioms applicationSetoid
#print axioms collapse_applicationExtensional
#print axioms collapseMap_injective_iff
#print axioms collapseMap_bijective_iff
#print axioms descendObserver_unique
#print axioms collapse_functionReadout_exact
#print axioms collapseSectionEquiv
#print axioms Canary.dependency_extensional_collapse_boundary

end Mettapedia.TypeTheory.ApplicationExtensionalCollapse
