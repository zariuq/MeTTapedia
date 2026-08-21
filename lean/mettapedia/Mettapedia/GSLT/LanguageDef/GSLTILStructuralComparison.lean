import Mettapedia.GSLT.Core.OperationalPathFibration
import Mettapedia.GSLT.LanguageDef.GSLTILSyntax

/-!
# Structural comparison obligations for GSLT-IL

The functional indexed candidate is now concrete: operational translations
induce functors on execution-path categories and hence a Grothendieck total
category.  Its naturality squares are supplied by `IndexedOperational`.

The finite authored language is deliberately more general, however: one
route declaration may denote a relation rather than a function.  The
counterexample below proves that this fragment cannot be represented by the
functional indexed candidate without an additional admission condition or a
relational completion.  This module records that boundary without choosing a
particular equipment or double-categorical package.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.StructuralComparison

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Functional routes and their derived naturality cells -/

/-- Functionality is an admission property of an authored route, not a
property granted merely by its route declaration. -/
def Functional (program : Program) (route : RouteDecl) : Prop :=
  ∀ {source firstTarget secondTarget},
    RouteMaps program route source firstTarget ->
    RouteMaps program route source secondTarget ->
    firstTarget = secondTarget

/-- The double-cell obligation for a functional operational translation is
already a consequence of step preservation: compute-then-transport and
transport-then-compute form a filled naturality diamond. -/
def functionalNaturalityDiamond
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :=
  Command.naturalityDiamond diagram route step

/-! ## Negative control: authored routes need not be functional -/

namespace RelationalCanary

private def atom (name : String) : Pattern := .apply name []

private def sourceSpace := atom "source-space"
private def targetSpace := atom "target-space"
private def input := atom "input"
private def firstOutput := atom "first-output"
private def secondOutput := atom "second-output"

private def route : RouteDecl :=
  { occurrence := atom "route-occurrence"
    name := "choose"
    sourceSpace := sourceSpace
    targetSpace := targetSpace }

private def firstRule : RouteRule :=
  { occurrence := atom "first-occurrence"
    name := "choose"
    source := input
    target := firstOutput }

private def secondRule : RouteRule :=
  { occurrence := atom "second-occurrence"
    name := "choose"
    source := input
    target := secondOutput }

private def program : Program :=
  { spaceRules := []
    routes := [route]
    routeRules := [firstRule, secondRule] }

private theorem maps_first :
    RouteMaps program route input firstOutput := by
  refine ⟨by simp [program], firstRule, by simp [program], ?_⟩
  simp [firstRule, route]

private theorem maps_second :
    RouteMaps program route input secondOutput := by
  refine ⟨by simp [program], secondRule, by simp [program], ?_⟩
  simp [secondRule, route]

private theorem outputs_distinct : firstOutput ≠ secondOutput := by
  simp [firstOutput, secondOutput, atom]

/-- A single declared route may retain two distinct outputs for one input. -/
theorem authored_route_not_functional : ¬ Functional program route := by
  intro functional
  exact outputs_distinct (functional maps_first maps_second)

/-- Consequently no single term function represents the route relation
exactly.  A functional interpretation needs a proved functionality license;
otherwise the semantic package must retain relational nondeterminism. -/
theorem no_function_represents_authored_route :
    ¬ ∃ translate : Pattern -> Pattern,
      ∀ source target,
        RouteMaps program route source target ↔ translate source = target := by
  rintro ⟨translate, represents⟩
  have firstEquation : translate input = firstOutput :=
    (represents input firstOutput).mp maps_first
  have secondEquation : translate input = secondOutput :=
    (represents input secondOutput).mp maps_second
  exact outputs_distinct (firstEquation.symm.trans secondEquation)

end RelationalCanary

end Mettapedia.GSLT.LanguageDef.GSLTIL.StructuralComparison
