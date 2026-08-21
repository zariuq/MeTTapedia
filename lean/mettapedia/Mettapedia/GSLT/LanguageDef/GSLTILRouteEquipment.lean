import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.GSLT.Core.OperationalPathFibration
import Mettapedia.GSLT.LanguageDef.GSLTILStructuralComparison

/-!
# The layered route semantics of GSLT-IL

Authored GSLT-IL routes are proof-relevant loose arrows.  They remain usable
as relations even when they are partial, nondeterministic, or retain several
distinct occurrences with the same visible output.  A route may additionally
earn a `Representation` on a typed source fibre.  That evidence compiles the
loose arrow to one direct function and is exactly the boundary at which the
existing indexed operational path fibration applies.

This is the gradual route discipline:

* loose execution is the ambient semantics and needs no license;
* representability is additional evidence, never an authoring assertion;
* a represented operational route induces the established path functor;
* composition retains its intermediate loose witness while its admitted map
  executes as ordinary function composition.

The typed fibre is essential.  A finite authored route is normally partial
on the type of all raw patterns.  Native types select the domain on which
coverage and proof-relevant determinism can actually be established.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Occurrence-retaining authored routes -/

/-- One exact authored reason why a route maps a source to a target. -/
structure RouteWitness (program : Program) (route : RouteDecl)
    (source target : Pattern) where
  routeMember : route ∈ program.routes
  rule : RouteRule
  ruleMember : rule ∈ program.routeRules
  nameEq : rule.name = route.name
  sourceEq : rule.source = source
  targetEq : rule.target = target

/-- The proof-relevant loose meaning of an authored route occurrence. -/
def routeLoose (program : Program) (route : RouteDecl) :
    Loose Pattern Pattern :=
  RouteWitness program route

theorem nonempty_routeWitness_iff (program : Program) (route : RouteDecl)
    (source target : Pattern) :
    Nonempty (RouteWitness program route source target) ↔
      RouteMaps program route source target := by
  constructor
  · rintro ⟨witness⟩
    exact ⟨witness.routeMember, witness.rule, witness.ruleMember,
      witness.nameEq, witness.sourceEq, witness.targetEq⟩
  · rintro ⟨routeMember, rule, ruleMember, nameEq, sourceEq, targetEq⟩
    exact ⟨⟨routeMember, rule, ruleMember, nameEq, sourceEq, targetEq⟩⟩

/-- A representation of the proof-relevant route implies ordinary
functionality, but the converse is intentionally not claimed. -/
theorem functional_of_representation (program : Program) (route : RouteDecl)
    (representation : Representation (routeLoose program route)) :
    StructuralComparison.Functional program route := by
  intro source firstTarget secondTarget firstMap secondMap
  obtain ⟨firstWitness⟩ :=
    (nonempty_routeWitness_iff program route source firstTarget).2 firstMap
  obtain ⟨secondWitness⟩ :=
    (nonempty_routeWitness_iff program route source secondTarget).2 secondMap
  have firstEq :=
    (representation.exact source firstTarget firstWitness).down.down
  have secondEq :=
    (representation.exact source secondTarget secondWitness).down.down
  exact firstEq.symm.trans secondEq

theorem not_representable_of_not_functional
    (program : Program) (route : RouteDecl)
    (notFunctional : ¬ StructuralComparison.Functional program route) :
    ¬ Nonempty (Representation (routeLoose program route)) := by
  rintro ⟨representation⟩
  exact notFunctional (functional_of_representation program route representation)

/-! ## Native typed fibres -/

/-- A native type selects the authored source and target fibres on which a
route may be admitted.  The source text remains unchanged. -/
structure TypedRouteProfile (program : Program) (route : RouteDecl) where
  Source : Type
  Target : Type
  sourcePattern : Source → Pattern
  targetPattern : Target → Pattern

namespace TypedRouteProfile

/-- The authored route restricted to its native typed endpoints. -/
def related {program : Program} {route : RouteDecl}
    (profile : TypedRouteProfile program route) :
    Loose profile.Source profile.Target :=
  fun source target =>
    RouteWitness program route (profile.sourcePattern source)
      (profile.targetPattern target)

/-- Admission on a typed fibre is exact representability of its retained
route witnesses. -/
abbrev License {program : Program} {route : RouteDecl}
    (profile : TypedRouteProfile program route) :=
  Representation profile.related

theorem license_iff_total_and_deterministic
    {program : Program} {route : RouteDecl}
    (profile : TypedRouteProfile program route) :
    Nonempty profile.License ↔
      Total profile.related ∧ Deterministic profile.related :=
  Representation.nonempty_iff_total_and_deterministic

/-- A license exposes the direct map selected once by admission. -/
def compile {program : Program} {route : RouteDecl}
    {profile : TypedRouteProfile program route}
    (license : profile.License) : profile.Source → profile.Target :=
  license.map

/-- The compiled map neither adds nor drops a route result on the licensed
fibre.  This is the strongest extensional reflection available after
proof-relevant witnesses are deliberately hidden from the hot path. -/
theorem related_iff_compiled_eq
    {program : Program} {route : RouteDecl}
    {profile : TypedRouteProfile program route}
    (license : profile.License) (source : profile.Source)
    (target : profile.Target) :
    Nonempty (profile.related source target) ↔
      profile.compile license source = target := by
  constructor
  · rintro ⟨witness⟩
    exact (license.exact source target witness).down.down
  · intro equal
    exact ⟨(license.exact source target).symm ⟨⟨equal⟩⟩⟩

end TypedRouteProfile

/-! ## Represented operational routes recover the functional fibration -/

/-- A loose route between two GSLTs together with the exact evidence that its
direct map preserves equations and steps. -/
structure RepresentedOperationalRoute
    (source : GSLT) (target : GSLT) where
  related : Loose source.Term target.Term
  representation : Representation related
  mapEquiv : ∀ {left right}, source.Equiv left right →
    target.Equiv (representation.map left) (representation.map right)
  mapStep : ∀ {left right}, source.Step left right →
    target.Step (representation.map left) (representation.map right)

namespace RepresentedOperationalRoute

/-- The identity route is already represented. -/
def id (system : GSLT) : RepresentedOperationalRoute system system where
  related := companion _root_.id
  representation := Representation.companionSelf _root_.id
  mapEquiv := fun equivalent => equivalent
  mapStep := fun step => step

/-- Represented operational routes compose both loosely and tightly.  The
loose composite retains the middle term and both witnesses; the compiled map
is ordinary function composition. -/
def comp {first middle last : GSLT}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last) :
    RepresentedOperationalRoute first last where
  related := LooseRelationEquipment.comp earlier.related later.related
  representation :=
    Representation.horizontalComp earlier.representation later.representation
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  mapStep := fun step => later.mapStep (earlier.mapStep step)

/-- Forget the loose witnesses only after admission, obtaining the existing
functional operational translation. -/
def toOperationalTranslation {source target : GSLT}
    (route : RepresentedOperationalRoute source target) :
    OperationalTranslation source target where
  mapTerm := route.representation.map
  mapEquiv := route.mapEquiv
  mapStep := route.mapStep

@[simp] theorem toOperationalTranslation_mapTerm
    {source target : GSLT}
    (route : RepresentedOperationalRoute source target) :
    route.toOperationalTranslation.mapTerm = route.representation.map :=
  rfl

@[simp] theorem toOperationalTranslation_id (system : GSLT) :
    (id system).toOperationalTranslation = OperationalTranslation.id system := by
  ext
  rfl

@[simp] theorem toOperationalTranslation_comp
    {first middle last : GSLT}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last) :
    (comp earlier later).toOperationalTranslation =
      OperationalTranslation.comp earlier.toOperationalTranslation
        later.toOperationalTranslation := by
  ext
  rfl

/-- Consequently every admitted operational route acts on complete retained
execution paths through the established indexed path functor. -/
def pathFunctor {source target : GSLT}
    (route : RepresentedOperationalRoute source target) :=
  route.toOperationalTranslation.pathFunctor

end RepresentedOperationalRoute

/-! ## Proof-relevant negative control -/

namespace DuplicateOccurrenceCanary

private def atom (name : String) : Pattern := .apply name []
private def sourceSpace := atom "source-space"
private def targetSpace := atom "target-space"
private def input := atom "input"
private def output := atom "output"

private def route : RouteDecl :=
  { occurrence := atom "route-occurrence"
    name := "duplicate"
    sourceSpace := sourceSpace
    targetSpace := targetSpace }

private def firstRule : RouteRule :=
  { occurrence := atom "first-occurrence"
    name := "duplicate"
    source := input
    target := output }

private def secondRule : RouteRule :=
  { occurrence := atom "second-occurrence"
    name := "duplicate"
    source := input
    target := output }

private def program : Program :=
  { spaceRules := []
    routes := [route]
    routeRules := [firstRule, secondRule] }

private def profile : TypedRouteProfile program route where
  Source := Unit
  Target := Unit
  sourcePattern _ := input
  targetPattern _ := output

private def firstWitness : profile.related () () where
  routeMember := by simp [program]
  rule := firstRule
  ruleMember := by simp [program]
  nameEq := by simp [firstRule, route]
  sourceEq := by simp [profile, firstRule]
  targetEq := by simp [profile, firstRule]

private def secondWitness : profile.related () () where
  routeMember := by simp [program]
  rule := secondRule
  ruleMember := by simp [program]
  nameEq := by simp [secondRule, route]
  sourceEq := by simp [profile, secondRule]
  targetEq := by simp [profile, secondRule]

private theorem witnesses_distinct : firstWitness ≠ secondWitness := by
  intro same
  have rulesEqual : firstRule = secondRule :=
    congrArg RouteWitness.rule same
  simp [firstRule, secondRule, atom] at rulesEqual

/-- The typed route is covered: its only source has an authored result. -/
theorem typed_total : Total profile.related := by
  intro source
  cases source
  exact ⟨⟨(), firstWitness⟩⟩

/-- Two distinct authored occurrences remain distinct even when their visible
source and target coincide. -/
theorem typed_not_deterministic : ¬ Deterministic profile.related := by
  intro deterministic
  have pairEq := (deterministic ()).allEq
    (⟨(), firstWitness⟩ : Sigma fun target => profile.related () target)
    ⟨(), secondWitness⟩
  exact witnesses_distinct (eq_of_heq (Sigma.mk.inj pairEq).2)

/-- Visible single-valuedness and coverage do not license compilation when
occurrence provenance remains ambiguous. -/
theorem typed_not_representable : ¬ Nonempty profile.License := by
  intro represented
  exact typed_not_deterministic
    ((profile.license_iff_total_and_deterministic).mp represented).2

end DuplicateOccurrenceCanary

#print axioms functional_of_representation
#print axioms TypedRouteProfile.license_iff_total_and_deterministic
#print axioms TypedRouteProfile.related_iff_compiled_eq
#print axioms RepresentedOperationalRoute.toOperationalTranslation_comp
#print axioms DuplicateOccurrenceCanary.typed_not_representable

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
