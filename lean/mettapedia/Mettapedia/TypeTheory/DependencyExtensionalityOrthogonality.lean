import Mathlib.Logic.Equiv.Basic

/-!
# Dependency and function extensionality are independent

Simple versus dependent typing and intensional versus extensional function
equality are different design axes.  This module isolates the distinction at
one dependent function space, without choosing a syntax, universe hierarchy,
evaluation strategy, or proof theory.

`DependentFunctionSpace` asks only for abstraction, application, and beta.
`ApplicationExtensional` is an additional property: functions which agree at
every argument are equal.  The four concrete models below show that both a
constant result family and a genuinely varying result family admit either an
extensional or a route-sensitive function carrier.

The route-sensitive carriers retain a Boolean tag which application does not
observe.  Their final theorem shows that the tag cannot be reconstructed from
extensional behavior.  Thus an extensional readout may be useful and sound
without being a faithful account of proof routes, occurrences, provenance, or
cost receipts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

universe u v w

/-- A dependent function space with beta, but no built-in eta or function
extensionality principle. -/
structure DependentFunctionSpace (Domain : Type u)
    (Codomain : Domain → Type v) where
  Function : Type w
  abstraction : ((argument : Domain) → Codomain argument) → Function
  application : Function → (argument : Domain) → Codomain argument
  beta : ∀ (body : (argument : Domain) → Codomain argument)
    (argument : Domain), application (abstraction body) argument = body argument

namespace DependentFunctionSpace

variable {Domain : Type u} {Codomain : Domain → Type v}

/-- Extensional equality for one dependent function space.  This is an
additional capability, not part of beta reduction. -/
def ApplicationExtensional
    (space : DependentFunctionSpace.{u, v, w} Domain Codomain) : Prop :=
  ∀ left right : space.Function,
    (∀ argument, space.application left argument =
      space.application right argument) →
    left = right

/-- Two distinct functions which application cannot distinguish. -/
def HasApplicationIndistinguishablePair
    (space : DependentFunctionSpace.{u, v, w} Domain Codomain) : Prop :=
  ∃ left right : space.Function,
    left ≠ right ∧
      ∀ argument, space.application left argument =
        space.application right argument

/-- Application extensionality rules out hidden distinctions in the function
carrier. -/
theorem applicationExtensional_excludes_indistinguishablePair
    (space : DependentFunctionSpace.{u, v, w} Domain Codomain)
    (extensional : space.ApplicationExtensional) :
    ¬ space.HasApplicationIndistinguishablePair := by
  rintro ⟨left, right, distinct, sameApplications⟩
  exact distinct (extensional left right sameApplications)

end DependentFunctionSpace

/-! ## Constant and genuinely varying result families -/

/-- A simple function type is the constant-family special case. -/
def constantFamily (Codomain : Type v) : PUnit → Type v :=
  fun _ => Codomain

/-- A small genuinely dependent family: the false fibre is a singleton and
the true fibre has two elements. -/
def varyingBoolFamily : Bool → Type
  | false => PUnit
  | true => Bool

/-- The two fibres of `varyingBoolFamily` are not equivalent. -/
theorem false_true_fibres_not_equivalent :
    ¬ Nonempty ((varyingBoolFamily false) ≃ (varyingBoolFamily true)) := by
  rintro ⟨equivalence⟩
  obtain ⟨falsePreimage, falseImage⟩ := equivalence.surjective false
  obtain ⟨truePreimage, trueImage⟩ := equivalence.surjective true
  have preimagesEqual : falsePreimage = truePreimage := by
    cases falsePreimage
    cases truePreimage
    rfl
  have imagesEqual : equivalence falsePreimage = equivalence truePreimage :=
    congrArg equivalence preimagesEqual
  have falseEqualsTrue : false = true :=
    falseImage.symm.trans (imagesEqual.trans trueImage)
  exact Bool.false_ne_true falseEqualsTrue

/-- No one type is equivalent to every fibre of `varyingBoolFamily`; the
dependency is semantic rather than a change of spelling. -/
theorem varyingBoolFamily_not_constant :
    ¬ ∃ Constant : Type,
      ∀ argument, Nonempty ((varyingBoolFamily argument) ≃ Constant) := by
  rintro ⟨Constant, allFibres⟩
  obtain ⟨falseEquivalence⟩ := allFibres false
  obtain ⟨trueEquivalence⟩ := allFibres true
  apply false_true_fibres_not_equivalent
  exact ⟨falseEquivalence.trans trueEquivalence.symm⟩

/-! ## Simple, extensional beta function space -/

/-- Ordinary Booleans represent functions from the singleton domain to
Booleans. -/
def simpleExtensional :
    DependentFunctionSpace PUnit (constantFamily Bool) where
  Function := Bool
  abstraction := fun body => body PUnit.unit
  application := fun function _ => function
  beta := by
    intro body argument
    cases argument
    rfl

theorem simpleExtensional_applicationExtensional :
    simpleExtensional.ApplicationExtensional := by
  intro left right sameApplications
  exact sameApplications PUnit.unit

/-! ## Simple, route-sensitive beta function space -/

/-- The first Boolean is extensional behavior; the second is a retained route
tag which application deliberately does not erase from the carrier. -/
def simpleRouteSensitive :
    DependentFunctionSpace PUnit (constantFamily Bool) where
  Function := Bool × Bool
  abstraction := fun body => (body PUnit.unit, false)
  application := fun function _ => function.1
  beta := by
    intro body argument
    cases argument
    rfl

theorem simpleRouteSensitive_hasIndistinguishablePair :
    simpleRouteSensitive.HasApplicationIndistinguishablePair := by
  refine ⟨(false, false), (false, true), ?_, ?_⟩
  · intro equality
    have tagsEqual := congrArg Prod.snd equality
    exact Bool.false_ne_true tagsEqual
  · intro argument
    cases argument
    rfl

theorem simpleRouteSensitive_not_applicationExtensional :
    ¬ simpleRouteSensitive.ApplicationExtensional :=
  fun extensional =>
    simpleRouteSensitive.applicationExtensional_excludes_indistinguishablePair
      extensional simpleRouteSensitive_hasIndistinguishablePair

/-! ## Genuinely dependent, extensional beta function space -/

/-- A section of `varyingBoolFamily` is determined by its Boolean value in the
true fibre; its false-fibre component is uniquely `PUnit.unit`. -/
def dependentExtensional :
    DependentFunctionSpace Bool varyingBoolFamily where
  Function := Bool
  abstraction := fun body => body true
  application := fun function argument =>
    match argument with
    | false => PUnit.unit
    | true => function
  beta := by
    intro body argument
    cases argument with
    | false =>
        change PUnit.unit = body false
        exact Subsingleton.elim _ _
    | true => rfl

theorem dependentExtensional_applicationExtensional :
    dependentExtensional.ApplicationExtensional := by
  intro left right sameApplications
  exact sameApplications true

/-! ## Genuinely dependent, route-sensitive beta function space -/

/-- The same dependent sections may retain a route tag independently of
their pointwise values. -/
def dependentRouteSensitive :
    DependentFunctionSpace Bool varyingBoolFamily where
  Function := Bool × Bool
  abstraction := fun body => (body true, false)
  application := fun function argument =>
    match argument with
    | false => PUnit.unit
    | true => function.1
  beta := by
    intro body argument
    cases argument with
    | false =>
        change PUnit.unit = body false
        exact Subsingleton.elim _ _
    | true => rfl

theorem dependentRouteSensitive_hasIndistinguishablePair :
    dependentRouteSensitive.HasApplicationIndistinguishablePair := by
  refine ⟨(false, false), (false, true), ?_, ?_⟩
  · intro equality
    have tagsEqual := congrArg Prod.snd equality
    exact Bool.false_ne_true tagsEqual
  · intro argument
    cases argument <;> rfl

theorem dependentRouteSensitive_not_applicationExtensional :
    ¬ dependentRouteSensitive.ApplicationExtensional :=
  fun extensional =>
    dependentRouteSensitive.applicationExtensional_excludes_indistinguishablePair
      extensional dependentRouteSensitive_hasIndistinguishablePair

/-! ## Orthogonality and observer nonfactorization -/

/-- The four constructive witnesses establish the independence relevant to
type-theory architecture: dependency does not imply intensionality, and
simplicity does not imply extensionality. -/
theorem dependency_extensionality_orthogonal :
    simpleExtensional.ApplicationExtensional ∧
      simpleRouteSensitive.HasApplicationIndistinguishablePair ∧
      (¬ ∃ Constant : Type,
        ∀ argument, Nonempty ((varyingBoolFamily argument) ≃ Constant)) ∧
      dependentExtensional.ApplicationExtensional ∧
      dependentRouteSensitive.HasApplicationIndistinguishablePair :=
  ⟨simpleExtensional_applicationExtensional,
    simpleRouteSensitive_hasIndistinguishablePair,
    varyingBoolFamily_not_constant,
    dependentExtensional_applicationExtensional,
    dependentRouteSensitive_hasIndistinguishablePair⟩

/-- Extensional behavior of the simple route-sensitive carrier. -/
def simpleBehavior : simpleRouteSensitive.Function → Bool :=
  Prod.fst

/-- A proof-route, occurrence, provenance, or cost-like observation retained
in the simple route-sensitive carrier. -/
def simpleRouteTag : simpleRouteSensitive.Function → Bool :=
  Prod.snd

/-- The canonical route-free representative of one extensional behavior. -/
def canonicalSimpleFunction : Bool → simpleRouteSensitive.Function :=
  fun behavior => (behavior, false)

/-- Extensional behavior has a section: every visible Boolean behavior has a
canonical route-free representative. -/
@[simp] theorem simpleBehavior_canonicalSimpleFunction (behavior : Bool) :
    simpleBehavior (canonicalSimpleFunction behavior) = behavior :=
  rfl

/-- The extensional readout is therefore surjective. -/
theorem simpleBehavior_surjective : Function.Surjective simpleBehavior := by
  intro behavior
  exact ⟨canonicalSimpleFunction behavior, rfl⟩

/-- No reconstruction from extensional behavior can be a left inverse on all
route-bearing functions.  A canonical section does not turn a lossy readout
into an equivalence. -/
theorem extensionalBehavior_has_no_global_reconstruction :
    ¬ ∃ reconstruct : Bool → simpleRouteSensitive.Function,
      ∀ function : simpleRouteSensitive.Function,
        reconstruct (simpleBehavior function) = function := by
  rintro ⟨reconstruct, recovers⟩
  have first := recovers (false, false)
  have second := recovers (false, true)
  have functionsEqual : (false, false) = (false, true) :=
    first.symm.trans second
  exact Bool.false_ne_true (congrArg Prod.snd functionsEqual)

/-- No function of extensional behavior alone can recover the retained route
tag for every function. -/
theorem routeTag_does_not_factor_through_extensionalBehavior :
    ¬ ∃ summarize : Bool → Bool,
      ∀ function : simpleRouteSensitive.Function,
        summarize (simpleBehavior function) = simpleRouteTag function := by
  rintro ⟨summarize, factors⟩
  have first := factors (false, false)
  have second := factors (false, true)
  change summarize false = false at first
  change summarize false = true at second
  exact Bool.false_ne_true (first.symm.trans second)

#print axioms
  DependentFunctionSpace.applicationExtensional_excludes_indistinguishablePair
#print axioms false_true_fibres_not_equivalent
#print axioms varyingBoolFamily_not_constant
#print axioms simpleRouteSensitive_not_applicationExtensional
#print axioms dependentRouteSensitive_not_applicationExtensional
#print axioms dependency_extensionality_orthogonal
#print axioms simpleBehavior_surjective
#print axioms extensionalBehavior_has_no_global_reconstruction
#print axioms routeTag_does_not_factor_through_extensionalBehavior

end Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality
