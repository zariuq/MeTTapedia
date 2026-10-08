import Mettapedia.GSLT.Core.OperationalPathFibration
import Mettapedia.GSLT.LanguageDef.GSLTILSyntax
import Mettapedia.GSLT.LanguageDef.GSLTILFibreExecution
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Structural comparison obligations for GSLT-ML

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

/-! ## Declaration maps and behavioral transport

Even a map between validated, equation-free LangDefs need not preserve
bisimilarity: the target can add a rewrite that separates source states.
The covered-translation interface in `GSLTILFibreExecution` proves the
additional local behavioral obligations explicitly.
-/

namespace DeclarationBoundary

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis

private def ready : Pattern := .apply "Ready" []
private def done : Pattern := .apply "Done" []

private def advance : RewriteRule :=
  { name := "advance", typeContext := [], premises := [], left := ready, right := done }

private def active : LanguageDef :=
  { name := "Active", types := ["State"],
    terms := [{ label := "Ready", category := "State", params := [], syntaxPattern := [] },
      { label := "Done", category := "State", params := [], syntaxPattern := [] }],
    equations := [], rewrites := [advance] }

private def idle : LanguageDef := { active with name := "Idle", rewrites := [] }

private theorem active_validates : active.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  intro rule member
  simp only [active, List.mem_cons, List.not_mem_nil, or_false] at member
  subst rule
  simp [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    LanguageDef.validatePatternConstructors,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    LanguageDef.typeNames, advance, active, ready, done]

private theorem idle_validates : idle.validate = [] := by decide +kernel

private def activeObject : ValidatedLanguageDef := ⟨active, active_validates⟩
private def idleObject : ValidatedLanguageDef := ⟨idle, idle_validates⟩

/-- A declaration-preserving inclusion may add a target rewrite. -/
def inclusion : StructuralMorphism idleObject activeObject where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration member
    rw [mapTypeDecl_id]
    exact member
  mapsTerms := by
    intro grammar member
    rw [mapGrammarRule_id]
    exact member
  mapsEquations := by
    intro equation member
    change List.Mem equation [] at member
    cases member
  mapsRewrites := by
    intro rewrite member
    change List.Mem rewrite [] at member
    cases member

private theorem active_nonrecursive :
    ∀ rule ∈ active.rewrites, NoncontextualPremises rule.premises := by
  intro rule member
  simp only [active, List.mem_cons, List.not_mem_nil, or_false] at member
  subst rule
  exact .nil

private theorem idle_nonrecursive :
    ∀ rule ∈ idle.rewrites, NoncontextualPremises rule.premises := by
  intro rule member
  simp [idle] at member

private theorem idle_no_step (source target : Pattern) :
    ¬ (langGSLT idle).Step source target := by
  intro step
  have member := (mem_rootFrontier_iff_langGSLTUsing_step RelationEnv.empty idle
    (by decide +kernel) idle_nonrecursive source target).mpr step
  simp [rewriteStepWithPremisesUsing, idle] at member

/-- The two declared states are bisimilar before any rewrite is added. -/
theorem idle_states_bisimilar : (langGSLT idle).Bisimilar ready done := by
  refine ⟨fun left right => left = ready ∧ right = done, ⟨?_, ?_⟩, rfl, rfl⟩
  · intro left right _ next step
    exact (idle_no_step left next step).elim
  · intro left right _ next step
    exact (idle_no_step right next step).elim

private theorem ready_step : (langGSLT active).Step ready done :=
  (mem_rootFrontier_iff_langGSLTUsing_step RelationEnv.empty active
    (by decide +kernel) active_nonrecursive ready done).mp (by decide +kernel)

private theorem done_no_step (target : Pattern) :
    ¬ (langGSLT active).Step done target := by
  intro step
  have member := (mem_rootFrontier_iff_langGSLTUsing_step RelationEnv.empty active
    (by decide +kernel) active_nonrecursive done target).mpr step
  have noAnswers : rewriteStepWithPremisesUsing RelationEnv.empty active done = [] :=
    by decide +kernel
  rw [noAnswers] at member
  exact List.not_mem_nil member

/-- Adding `Ready -> Done` separates the same two states behaviorally. -/
theorem active_states_not_bisimilar : ¬ (langGSLT active).Bisimilar ready done := by
  rintro ⟨relation, ⟨forward, _⟩, related⟩
  obtain ⟨next, step, _⟩ := forward related ready_step
  exact done_no_step next step

/-- The structural inclusion's own term map cannot be a behavioral GSLT
morphism. Declaration preservation alone therefore cannot supply this
behavioral transport interface. -/
theorem structural_map_not_behavioral :
    ¬ ∃ morphism : GSLT.Morphism (langGSLT idle) (langGSLT active),
      morphism.toFun = mapPattern inclusion.symbols := by
  rintro ⟨morphism, sameMap⟩
  have preserved := morphism.preserves_bisim idle_states_bisimilar
  rw [sameMap] at preserved
  exact active_states_not_bisimilar
    (by simpa only [inclusion, mapPattern_id] using preserved)

end DeclarationBoundary

end Mettapedia.GSLT.LanguageDef.GSLTIL.StructuralComparison
