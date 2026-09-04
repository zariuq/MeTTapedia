import Mettapedia.Computability.ComputationalTrinity
import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-!
# Dependent functions as a contextual three-face comparison

A dependent function space has two potentially different carriers:

* its retained function objects, which may contain routes, occurrences, or
  other intensional evidence; and
* its extensional sections, obtained by applying a function at every
  argument.

Beta makes application onto sections a split epimorphism: abstraction is a
section of application.  Application extensionality is exactly the missing
injectivity which promotes this canonical comparison to an isomorphism.

This module places that fact in the contextual computational-trinity
interface.  The program face is the retained function carrier, while the
logic and space faces are the dependent sections.  The comparison always
commutes and always represents every section.  It is exact precisely when
application is extensional.  Thus dependency, extensionality, and retained
operational evidence remain independent design choices.

The examples include both a constant family and a genuinely varying family,
each with an exact and a route-sensitive comparison.  No syntax, universe
hierarchy, evaluation strategy, or product calculus is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentFunctionComparison

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

universe u v

variable {Domain : Type u} {Codomain : Domain → Type v}

/-- The extensional behavior of a dependent function is a section of its
result family. -/
abbrev Section (Domain : Type u) (Codomain : Domain → Type v) :=
  (argument : Domain) → Codomain argument

/-- A one-object context category is sufficient to expose the distinction
between retained function objects and their extensional sections. -/
abbrev Context := Discrete PUnit

private def here : Contextᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- The retained function carrier, viewed contextually. -/
def functionFace
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    Face.{0, 0, max u v} Context :=
  (Functor.const Contextᵒᵖ).obj space.Function

/-- The dependent-section carrier, viewed contextually. -/
def sectionFace
    (_space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    Face.{0, 0, max u v} Context :=
  (Functor.const Contextᵒᵖ).obj (Section Domain Codomain)

/-- Pointwise application is the canonical map from retained functions to
their extensional behavior. -/
def applicationTransformation
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    functionFace space ⟶ sectionFace space :=
  (Functor.const Contextᵒᵖ).map (TypeCat.ofHom space.application)

/-- The canonical three-face comparison.  Logic and space use the same
section carrier here so that the only question under test is whether the
retained program/function face contains distinctions beyond application. -/
def comparison
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    Comparison.{0, 0, max u v} Context where
  program := functionFace space
  logic := sectionFace space
  space := sectionFace space
  programToLogic := applicationTransformation space
  logicToSpace := 𝟙 (sectionFace space)
  programToSpace := applicationTransformation space
  coherence := by
    ext context function
    rfl

/-! ## Beta gives complete extensional behavior -/

/-- Abstraction is a right inverse of application. -/
theorem application_abstraction
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain)
    (body : Section Domain Codomain) :
    space.application (space.abstraction body) = body := by
  funext argument
  exact space.beta body argument

/-- Every dependent section is represented by a retained function object.
This is the precise completeness supplied by beta; it says nothing about
faithfulness. -/
theorem application_surjective
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    Function.Surjective space.application := by
  intro body
  exact ⟨space.abstraction body, application_abstraction space body⟩

/-- Application extensionality is exactly injectivity of the application
map. -/
theorem application_injective_iff_extensional
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    Function.Injective space.application ↔
      space.ApplicationExtensional := by
  constructor
  · intro injective left right pointwise
    apply injective
    funext argument
    exact pointwise argument
  · intro extensional left right sameApplication
    apply extensional left right
    intro argument
    exact congrFun sameApplication argument

/-- Beta plus application extensionality identifies retained functions with
dependent sections. -/
def applicationEquiv
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain)
    (extensional : space.ApplicationExtensional) :
    space.Function ≃ Section Domain Codomain where
  toFun := space.application
  invFun := space.abstraction
  left_inv := by
    intro function
    apply extensional
    intro argument
    exact space.beta (space.application function) argument
  right_inv := application_abstraction space

/-! ## Exactness of the canonical contextual comparison -/

/-- The canonical application comparison is exact when its displayed
program-to-logic map is the forward map of a natural isomorphism.  Requiring
agreement with `applicationTransformation` prevents an unrelated isomorphism
between equally sized carriers from witnessing the property. -/
def CanonicallyExact
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) : Prop :=
  ∃ exactMap : functionFace space ≅ sectionFace space,
    exactMap.hom = applicationTransformation space

/-- Function extensionality constructs the canonical contextual
isomorphism. -/
def canonicalIso
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain)
    (extensional : space.ApplicationExtensional) :
    functionFace space ≅ sectionFace space :=
  (Functor.const Contextᵒᵖ).mapIso
    (applicationEquiv space extensional).toIso

@[simp] theorem canonicalIso_hom
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain)
    (extensional : space.ApplicationExtensional) :
    (canonicalIso space extensional).hom =
      applicationTransformation space := by
  rfl

/-- The canonical comparison is exact exactly when application is
extensional.  Beta already supplies the surjective half; this theorem
identifies the remaining design choice. -/
theorem canonicallyExact_iff_applicationExtensional
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    CanonicallyExact space ↔ space.ApplicationExtensional := by
  constructor
  · rintro ⟨exactMap, agrees⟩
    rw [← application_injective_iff_extensional space]
    intro left right sameApplication
    have componentAgreement :=
      congrArg (fun transformation => transformation.app here) agrees
    apply (exactMap.app here).toEquiv.injective
    change exactMap.hom.app here left = exactMap.hom.app here right
    rw [componentAgreement]
    exact sameApplication
  · intro extensional
    exact ⟨canonicalIso space extensional,
      canonicalIso_hom space extensional⟩

/-- When application is extensional, the program, logic, and space faces form
an exact computational trinity. -/
def exactTrinity
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain)
    (extensional : space.ApplicationExtensional) :
    Exact.{0, 0, max u v} Context where
  program := functionFace space
  logic := sectionFace space
  space := sectionFace space
  programLogic := canonicalIso space extensional
  logicSpace := Iso.refl (sectionFace space)

/-! ## Information loss is exactly application-indistinguishability -/

/-- The canonical comparison loses retained program information exactly when
two distinct function objects have the same applications. -/
theorem comparison_losesProgramInformation_iff
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain) :
    (comparison space).LosesProgramInformation ↔
      space.HasApplicationIndistinguishablePair := by
  constructor
  · rintro ⟨context, left, right, distinct, sameImage⟩
    change space.application left = space.application right at sameImage
    refine ⟨left, right, distinct, ?_⟩
    intro argument
    exact congrFun sameImage argument
  · rintro ⟨left, right, distinct, sameApplications⟩
    refine ⟨here, left, right, distinct, ?_⟩
    change space.application left = space.application right
    funext argument
    exact sameApplications argument

/-- A hidden application-indistinguishable pair rules out canonical
exactness. -/
theorem not_canonicallyExact_of_indistinguishablePair
    (space : DependentFunctionSpace.{u, v, max u v} Domain Codomain)
    (hidden : space.HasApplicationIndistinguishablePair) :
    ¬ CanonicallyExact space := by
  rw [canonicallyExact_iff_applicationExtensional]
  exact fun extensional =>
    space.applicationExtensional_excludes_indistinguishablePair
      extensional hidden

/-! ## Four cross-axis controls -/

/-- A simple constant-family function space can have an exact canonical
trinity. -/
theorem simple_extensional_comparison_exact :
    CanonicallyExact simpleExtensional :=
  (canonicallyExact_iff_applicationExtensional simpleExtensional).2
    simpleExtensional_applicationExtensional

/-- A simple constant-family function space can instead retain information
which its extensional section does not see. -/
theorem simple_route_comparison_lossy :
    (comparison simpleRouteSensitive).LosesProgramInformation ∧
      ¬ CanonicallyExact simpleRouteSensitive :=
  ⟨(comparison_losesProgramInformation_iff simpleRouteSensitive).2
      simpleRouteSensitive_hasIndistinguishablePair,
    not_canonicallyExact_of_indistinguishablePair simpleRouteSensitive
      simpleRouteSensitive_hasIndistinguishablePair⟩

/-- A genuinely varying dependent family also admits an exact canonical
trinity.  Exactness is therefore not a privilege of simple types. -/
theorem dependent_extensional_comparison_exact :
    (¬ ∃ Constant : Type,
        ∀ argument,
          Nonempty ((varyingBoolFamily argument) ≃ Constant)) ∧
      CanonicallyExact dependentExtensional :=
  ⟨varyingBoolFamily_not_constant,
    (canonicallyExact_iff_applicationExtensional dependentExtensional).2
      dependentExtensional_applicationExtensional⟩

/-- Genuine dependency also coexists with a route-sensitive, non-exact
comparison. -/
theorem dependent_route_comparison_lossy :
    (¬ ∃ Constant : Type,
        ∀ argument,
          Nonempty ((varyingBoolFamily argument) ≃ Constant)) ∧
      (comparison dependentRouteSensitive).LosesProgramInformation ∧
      ¬ CanonicallyExact dependentRouteSensitive :=
  ⟨varyingBoolFamily_not_constant,
    (comparison_losesProgramInformation_iff dependentRouteSensitive).2
      dependentRouteSensitive_hasIndistinguishablePair,
    not_canonicallyExact_of_indistinguishablePair dependentRouteSensitive
      dependentRouteSensitive_hasIndistinguishablePair⟩

/-- The complete matrix is constructive: constant versus varying result
families and exact versus route-sensitive trinity comparisons are orthogonal
axes. -/
theorem dependency_and_canonical_exactness_orthogonal :
    CanonicallyExact simpleExtensional ∧
      (comparison simpleRouteSensitive).LosesProgramInformation ∧
      (¬ ∃ Constant : Type,
        ∀ argument,
          Nonempty ((varyingBoolFamily argument) ≃ Constant)) ∧
      CanonicallyExact dependentExtensional ∧
      (comparison dependentRouteSensitive).LosesProgramInformation :=
  ⟨simple_extensional_comparison_exact,
    simple_route_comparison_lossy.1,
    varyingBoolFamily_not_constant,
    dependent_extensional_comparison_exact.2,
    dependent_route_comparison_lossy.2.1⟩

#print axioms application_abstraction
#print axioms application_surjective
#print axioms application_injective_iff_extensional
#print axioms canonicallyExact_iff_applicationExtensional
#print axioms comparison_losesProgramInformation_iff
#print axioms simple_route_comparison_lossy
#print axioms dependent_extensional_comparison_exact
#print axioms dependent_route_comparison_lossy
#print axioms dependency_and_canonical_exactness_orthogonal

end Mettapedia.TypeTheory.DependentFunctionComparison
