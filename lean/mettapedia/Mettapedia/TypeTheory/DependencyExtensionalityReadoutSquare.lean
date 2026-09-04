import Mettapedia.TypeTheory.DependentFunctionComparison
import Mettapedia.TypeTheory.FibrewiseFullyFaithfulCwfMorphism
import Mettapedia.TypeTheory.SplitReadoutMorphism

/-!
# Simple-to-dependent squares for extensional readouts

The constant-family fragment of a dependent theory and the choice of an
extensional equality discipline are independent.  This module makes that
claim functorial rather than merely comparing four isolated examples.

Every beta function space has a split readout from retained function objects
to extensional sections.  For the canonical simple and genuinely dependent
Boolean examples, the ordinary extensional carriers form one commuting
simple-to-dependent square and the route-retaining carriers form another.
Both squares have bijective maps on their retained and visible carriers.
Nevertheless, the first readouts are exact while the second readouts are not.

Together with the proper fibrewise fully faithful constant-family inclusion,
this supplies a positive and a negative control for the architectural seam:
a well-behaved simple fragment inside a dependent theory neither selects
function extensionality nor licenses erasure of retained routes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependencyExtensionalityReadoutSquare

open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality
open Mettapedia.TypeTheory.DependentFunctionComparison
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.FibrewiseFullyFaithfulCwfMorphism
open Mettapedia.TypeTheory.SplitReadoutMorphism

universe u v w

variable {Domain : Type u} {Codomain : Domain → Type v}

/-- Application and abstraction form the canonical split readout of any beta
function space. -/
def functionReadout
    (space : DependentFunctionSpace.{u, v, w} Domain Codomain) :
    SplitReadout space.Function (Section Domain Codomain) where
  observe := space.application
  representative := space.abstraction
  observe_representative := by
    intro body
    funext argument
    exact space.beta body argument

/-- Faithfulness of the application readout is precisely application
extensionality. -/
theorem functionReadout_faithful_iff_applicationExtensional
    (space : DependentFunctionSpace.{u, v, w} Domain Codomain) :
    (functionReadout space).Faithful ↔ space.ApplicationExtensional := by
  constructor
  · intro injective left right pointwise
    apply injective
    funext argument
    exact pointwise argument
  · intro extensional left right sameApplication
    apply extensional left right
    intro argument
    exact congrFun sameApplication argument

/-- Since beta already supplies every visible section, exactness of the
application readout is also precisely application extensionality. -/
theorem functionReadout_exact_iff_applicationExtensional
    (space : DependentFunctionSpace.{u, v, w} Domain Codomain) :
    (functionReadout space).Exact ↔ space.ApplicationExtensional := by
  rw [(functionReadout space).exact_iff_faithful]
  exact functionReadout_faithful_iff_applicationExtensional space

/-! ## The visible simple-to-dependent section equivalence -/

/-- Extend a simple Boolean section to the genuinely varying Boolean family.
The singleton false fibre has no information; the true fibre carries the
original Boolean result. -/
def embedSection :
    Section PUnit (constantFamily Bool) →
      Section Bool varyingBoolFamily :=
  fun body argument =>
    match argument with
    | false => PUnit.unit
    | true => body PUnit.unit

/-- Restrict a dependent section to its only informative fibre. -/
def projectSection :
    Section Bool varyingBoolFamily →
      Section PUnit (constantFamily Bool) :=
  fun body _ => body true

@[simp] theorem projectSection_embedSection
    (body : Section PUnit (constantFamily Bool)) :
    projectSection (embedSection body) = body := by
  funext argument
  cases argument
  rfl

@[simp] theorem embedSection_projectSection
    (body : Section Bool varyingBoolFamily) :
    embedSection (projectSection body) = body := by
  funext argument
  cases argument with
  | false =>
      change PUnit.unit = body false
      exact Subsingleton.elim _ _
  | true => rfl

/-- The visible section carriers are equivalent even though the dependent
family itself is not constant. -/
def sectionEquiv :
    Section PUnit (constantFamily Bool) ≃
      Section Bool varyingBoolFamily where
  toFun := embedSection
  invFun := projectSection
  left_inv := projectSection_embedSection
  right_inv := embedSection_projectSection

/-! ## Bundled readout objects and natural squares -/

def simpleExtensionalObject : Object where
  Source := simpleExtensional.Function
  Target := Section PUnit (constantFamily Bool)
  readout := functionReadout simpleExtensional

def dependentExtensionalObject : Object where
  Source := dependentExtensional.Function
  Target := Section Bool varyingBoolFamily
  readout := functionReadout dependentExtensional

def simpleRouteObject : Object where
  Source := simpleRouteSensitive.Function
  Target := Section PUnit (constantFamily Bool)
  readout := functionReadout simpleRouteSensitive

def dependentRouteObject : Object where
  Source := dependentRouteSensitive.Function
  Target := Section Bool varyingBoolFamily
  readout := functionReadout dependentRouteSensitive

/-- The simple and dependent extensional carriers commute with application
and with the selected abstractions. -/
def extensionalSquare :
    simpleExtensionalObject.Hom dependentExtensionalObject where
  sourceMap := id
  targetMap := embedSection
  observe_natural := by
    intro function
    change dependentExtensional.application function =
      embedSection (simpleExtensional.application function)
    funext argument
    cases argument <;> rfl
  representative_natural := by
    intro body
    change simpleExtensional.abstraction body =
      dependentExtensional.abstraction (embedSection body)
    rfl

/-- The same square exists for route-retaining function objects.  Its source
map is the identity on both the visible behavior and the hidden route. -/
def routeSquare : simpleRouteObject.Hom dependentRouteObject where
  sourceMap := id
  targetMap := embedSection
  observe_natural := by
    intro function
    change dependentRouteSensitive.application function =
      embedSection (simpleRouteSensitive.application function)
    funext argument
    cases argument <;> rfl
  representative_natural := by
    intro body
    change simpleRouteSensitive.abstraction body =
      dependentRouteSensitive.abstraction (embedSection body)
    rfl

theorem extensionalSquare_source_bijective :
    Function.Bijective extensionalSquare.sourceMap :=
  by
    change Function.Bijective (id : Bool → Bool)
    exact Function.bijective_id

theorem extensionalSquare_target_bijective :
    Function.Bijective extensionalSquare.targetMap :=
  by
    change Function.Bijective embedSection
    exact sectionEquiv.bijective

theorem routeSquare_source_bijective :
    Function.Bijective routeSquare.sourceMap :=
  by
    change Function.Bijective (id : Bool × Bool → Bool × Bool)
    exact Function.bijective_id

theorem routeSquare_target_bijective :
    Function.Bijective routeSquare.targetMap :=
  by
    change Function.Bijective embedSection
    exact sectionEquiv.bijective

/-! ## Positive and negative exactness controls -/

/-- Exactness transports across the extensional square from the simple
function space to the genuinely dependent one. -/
theorem dependentExtensional_exact_via_square :
    dependentExtensionalObject.readout.Exact := by
  apply extensionalSquare.target_exact_of_source_exact
    extensionalSquare_source_bijective.2
    extensionalSquare_target_bijective.1
  exact (functionReadout_exact_iff_applicationExtensional
    simpleExtensional).2 simpleExtensional_applicationExtensional

/-- The route-sensitive source is not exact despite having the same visible
section comparison and bijective square maps. -/
theorem simpleRoute_not_exact : ¬ simpleRouteObject.readout.Exact := by
  change ¬ (functionReadout simpleRouteSensitive).Exact
  rw [functionReadout_exact_iff_applicationExtensional]
  exact simpleRouteSensitive_not_applicationExtensional

/-- If the dependent route-sensitive readout were exact, reflection along
the square would make the simple route-sensitive readout exact. -/
theorem dependentRoute_not_exact : ¬ dependentRouteObject.readout.Exact := by
  intro targetExact
  exact simpleRoute_not_exact
    (routeSquare.source_exact_of_target_exact
      routeSquare_source_bijective.1 targetExact)

/-- A commuting square with bijective carrier maps does not by itself imply
that either readout is exact.  The retained route is preserved rather than
silently quotiented away. -/
theorem bijective_route_square_does_not_force_exactness :
    Function.Bijective routeSquare.sourceMap ∧
      Function.Bijective routeSquare.targetMap ∧
      ¬ simpleRouteObject.readout.Exact ∧
      ¬ dependentRouteObject.readout.Exact :=
  ⟨routeSquare_source_bijective,
    routeSquare_target_bijective,
    simpleRoute_not_exact,
    dependentRoute_not_exact⟩

/-- The complete compatibility result: constant families form a proper fully
faithful fragment of dependent families; a natural exact readout square and
a natural route-retaining non-exact square coexist over that relationship.
Consequently the simple-to-dependent inclusion does not select an equality
discipline. -/
theorem proper_dependency_does_not_select_extensionality :
    setFamilyConstantEmbedding.{0}.Proper ∧
      Function.Bijective extensionalSquare.sourceMap ∧
      Function.Bijective extensionalSquare.targetMap ∧
      simpleExtensionalObject.readout.Exact ∧
      dependentExtensionalObject.readout.Exact ∧
      Function.Bijective routeSquare.sourceMap ∧
      Function.Bijective routeSquare.targetMap ∧
      ¬ simpleRouteObject.readout.Exact ∧
      ¬ dependentRouteObject.readout.Exact :=
  ⟨setFamilyConstantEmbedding_proper,
    extensionalSquare_source_bijective,
    extensionalSquare_target_bijective,
    (functionReadout_exact_iff_applicationExtensional
      simpleExtensional).2 simpleExtensional_applicationExtensional,
    dependentExtensional_exact_via_square,
    routeSquare_source_bijective,
    routeSquare_target_bijective,
    simpleRoute_not_exact,
    dependentRoute_not_exact⟩

#print axioms functionReadout_exact_iff_applicationExtensional
#print axioms sectionEquiv
#print axioms dependentExtensional_exact_via_square
#print axioms bijective_route_square_does_not_force_exactness
#print axioms proper_dependency_does_not_select_extensionality

end Mettapedia.TypeTheory.DependencyExtensionalityReadoutSquare
