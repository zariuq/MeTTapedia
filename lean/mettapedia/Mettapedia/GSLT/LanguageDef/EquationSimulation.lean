import Mettapedia.GSLT.LanguageDef.SymbolMapSimulation
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.LanguageDef.CollectionAlgebraTransport

/-!
# The static equivalence along a structural presentation morphism

`SymbolMapSimulation` carries one-step reduction along a structural
presentation morphism.  This module carries the static equivalence: every
generator of the equation theory of the source is sent to a generator of the
equation theory of the target, so equivalent patterns have equivalent images.

There are two kinds of generator.

* An instance of an authored equation.  The morphism sends the equation to an
  equation of the target, matching is carried by every map of symbols, and
  the premises are transported with the same evidence that transports the
  premises of a rewrite.
* A law derived from a collection declaration.  The complete declaration
  action transports its algebra metadata, including the unit constructor
  reference.  Permutation, deduplication, flattening, singleton and both unit
  laws therefore transport without a fixed-unit or injectivity assumption.

The evaluator with no external relation still requires preservation of its
built-in `"eq"` relation.  Fixed-unit specializations remain available for
consumers that compare an algebra before and after transport literally.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.EquationSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
open Mettapedia.GSLT.LanguageDef.StructuralSimulation
open Mettapedia.GSLT.LanguageDef.SymbolMapSimulation
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism

/-! ## Instances of authored equations -/

/-- A bounded instance of an authored equation maps to a bounded instance of
the image equation, in the same orientation and at the same depth. -/
theorem equationInstanceAt_map_of_rewrites
    {symbols : LanguageDefSymbolMap} {base base' : BasePremiseEvaluator}
    {source target : LanguageDef}
    (mapsEquations : ∀ equation, List.Mem equation source.equations →
      List.Mem (mapEquation symbols equation) target.equations)
    (mapsRules : ∀ rule, List.Mem rule source.rewrites →
      List.Mem (mapRewriteRule symbols rule) target.rewrites)
    (mapsBaseResults : MapsBasePremiseResultsAt symbols base base' source target)
    {fuel : Nat} {left right : Pattern}
    (evidence : EquationInstanceAt base source fuel left right) :
    EquationInstanceAt base' target fuel
      (mapPattern symbols left) (mapPattern symbols right) := by
  cases evidence with
  | forward member matched premises built =>
      rename_i equation initial final
      refine EquationInstanceAt.forward
        (equation := mapEquation symbols equation)
        (initialBindings := mapBindings symbols initial)
        (finalBindings := mapBindings symbols final)
        (mapsEquations equation member) ?_ ?_ ?_
      · exact mem_matchPattern_mapPattern symbols matched
      · exact premisesAt_map_of_rewrites mapsRules mapsBaseResults premises
      · show applyBindings (mapBindings symbols final)
          (mapPattern symbols equation.right) = _
        rw [applyBindings_mapPattern, built]
  | reverse member matched premises built =>
      rename_i equation initial final
      refine EquationInstanceAt.reverse
        (equation := mapEquation symbols equation)
        (initialBindings := mapBindings symbols initial)
        (finalBindings := mapBindings symbols final)
        (mapsEquations equation member) ?_ ?_ ?_
      · exact mem_matchPattern_mapPattern symbols matched
      · exact premisesAt_map_of_rewrites mapsRules mapsBaseResults premises
      · show applyBindings (mapBindings symbols final)
          (mapPattern symbols equation.left) = _
        rw [applyBindings_mapPattern, built]

/-- Bounded authored equation instances map along a structural morphism.
The premises use the same direct transport as rewrite premises. -/
theorem equationInstanceAt_map_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {fuel : Nat} {left right : Pattern}
    (evidence : EquationInstanceAt base source.language fuel left right) :
    EquationInstanceAt base' target.language fuel
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) :=
  equationInstanceAt_map_of_rewrites morphism.mapsEquations morphism.mapsRewrites
    (mapsBaseResults.toTarget source.language target.language baseMono) evidence

/-- An instance of an authored equation maps to an instance of the image
equation. -/
theorem equationInstance_map_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {left right : Pattern}
    (evidence : EquationInstance base source.language left right) :
    EquationInstance base' target.language
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) := by
  obtain ⟨fuel, bounded⟩ := evidence
  exact ⟨fuel, equationInstanceAt_map_of_structuralMorphism morphism mapsBaseResults baseMono
    bounded⟩

/-! ## Laws derived from collection declarations -/

/-- Sorting at a category maps to sorting at the image category. -/
theorem sortedAt_map_of_structuralMorphism {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {pattern : Pattern} {category : String}
    (sorted : SortedAt source.language pattern category) :
    SortedAt target.language (mapPattern morphism.symbols pattern)
      (morphism.symbols.sort category) := by
  obtain ⟨free, bound, typed⟩ := sorted
  exact ⟨free.map morphism.symbols, bound.map (mapTypeExpr morphism.symbols),
    typed.map morphism⟩

/-- A declared collection carrier maps to a declared collection carrier of the
same kind. -/
theorem collectionCarrierRule_map_of_structuralMorphism
    {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    {rule : GrammarRule} {kind : CollType}
    (declaration : CollectionCarrierRule source.language rule kind) :
    CollectionCarrierRule target.language (mapGrammarRule morphism.symbols rule) kind where
  authored := morphism.mapsTerms rule declaration.authored
  selfSorted := by
    obtain ⟨parameterName, elementType, parameters⟩ := declaration.selfSorted
    exact ⟨parameterName, mapTypeExpr morphism.symbols elementType, by
      simp [mapGrammarRule, parameters, mapTermParam, mapTypeExpr]⟩

/-- The constructor map fixes every unit that a collection algebra of the
language declares. -/
def FixesDeclaredUnits (symbols : LanguageDefSymbolMap) (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.terms, ∀ algebra, rule.algebra? = some algebra →
    ∀ unit, algebra.unit = some unit → symbols.constructor unit = unit

/-- A language whose constructors declare no collection algebra has no
declared unit to fix. -/
theorem fixesDeclaredUnits_of_no_algebra (symbols : LanguageDefSymbolMap)
    {language : LanguageDef} (none : language.hasAlgebraDeclarations = false) :
    FixesDeclaredUnits symbols language := by
  intro rule membership algebra declared
  have absent := List.any_eq_false.mp none rule membership
  rw [declared] at absent
  simp at absent

/-- A constructor map that is the identity fixes every declared unit. -/
theorem fixesDeclaredUnits_of_constructor_id (symbols : LanguageDefSymbolMap)
    (language : LanguageDef) (fixed : ∀ label, symbols.constructor label = label) :
    FixesDeclaredUnits symbols language :=
  fun _ _ _ _ unit _ => fixed unit

/-- A declaration map transports the complete algebra, including its unit.
No injectivity or fixed-unit condition is needed for this renamed law. -/
theorem algebraRule_transport_of_structuralMorphism
    {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (declaration : AlgebraRule source.language rule kind algebra) :
    AlgebraRule target.language (mapGrammarRule morphism.symbols rule) kind
      (mapCollectionAlgebra morphism.symbols.constructor algebra) where
  authored := morphism.mapsTerms rule declaration.authored
  declared := by simp only [mapGrammarRule, declaration.declared, Option.map_some]
  selfSorted := by
    obtain ⟨parameterName, parameters⟩ := declaration.selfSorted
    exact ⟨parameterName, by simp [mapGrammarRule, parameters, mapTermParam, mapTypeExpr]⟩
  unitAuthored := by
    intro targetUnit mapped
    cases original : algebra.unit with
    | none => simp [mapCollectionAlgebra, original] at mapped
    | some unit =>
        have equal : morphism.symbols.constructor unit = targetUnit := by
          simpa only [mapCollectionAlgebra, original, Option.map_some, Option.some.injEq]
            using mapped
        obtain ⟨unitRule, unitMember, unitLabel, unitCategory, unitParameters⟩ :=
          declaration.unitAuthored unit original
        refine ⟨mapGrammarRule morphism.symbols unitRule,
          morphism.mapsTerms unitRule unitMember, ?_, ?_, ?_⟩
        · show morphism.symbols.constructor unitRule.label = targetUnit
          exact (congrArg morphism.symbols.constructor unitLabel).trans equal
        · show morphism.symbols.sort unitRule.category = morphism.symbols.sort rule.category
          exact congrArg morphism.symbols.sort unitCategory
        · show unitRule.params.map (mapTermParam morphism.symbols) = []
          simp only [unitParameters, List.map_nil]

/-- A declared collection algebra maps to a declared collection algebra with
the same laws, when the declared units are fixed. -/
theorem algebraRule_map_of_structuralMorphism
    {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    (units : FixesDeclaredUnits morphism.symbols source.language)
    {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (declaration : AlgebraRule source.language rule kind algebra) :
    AlgebraRule target.language (mapGrammarRule morphism.symbols rule) kind algebra where
  authored := morphism.mapsTerms rule declaration.authored
  declared := by
    have fixed : mapCollectionAlgebra morphism.symbols.constructor algebra = algebra :=
      mapCollectionAlgebra_eq_self _ _
        (units rule declaration.authored algebra declaration.declared)
    simp only [mapGrammarRule, declaration.declared, Option.map_some, fixed]
  selfSorted := by
    obtain ⟨parameterName, parameters⟩ := declaration.selfSorted
    exact ⟨parameterName, by simp [mapGrammarRule, parameters, mapTermParam, mapTypeExpr]⟩
  unitAuthored := by
    intro unit declared
    obtain ⟨unitRule, unitMember, unitLabel, unitCategory, unitParameters⟩ :=
      declaration.unitAuthored unit declared
    refine ⟨mapGrammarRule morphism.symbols unitRule,
      morphism.mapsTerms unitRule unitMember, ?_, ?_, ?_⟩
    · show morphism.symbols.constructor unitRule.label = unit
      rw [unitLabel]
      exact units rule declaration.authored algebra declaration.declared unit declared
    · show morphism.symbols.sort unitRule.category = morphism.symbols.sort rule.category
      rw [unitCategory]
    · show unitRule.params.map (mapTermParam morphism.symbols) = []
      rw [unitParameters]
      rfl

/-- All declaration-derived laws survive complete signature transport,
including a renamed unit. Constructor injectivity is unnecessary. -/
theorem derivedInstance_transport_of_structuralMorphism
    {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    {left right : Pattern} (derived : DerivedInstance source.language left right) :
    DerivedInstance target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) := by
  cases derived with
  | bagPerm carrier sorted permuted =>
      simp only [mapPattern, mapPatternList_eq_map]
      exact .bagPerm (collectionCarrierRule_map_of_structuralMorphism morphism carrier)
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted) (permuted.map _)
  | setPerm carrier sorted permuted =>
      simp only [mapPattern, mapPatternList_eq_map]
      exact .setPerm (collectionCarrierRule_map_of_structuralMorphism morphism carrier)
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted) (permuted.map _)
  | setDedup carrier sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_cons]
      exact .setDedup (collectionCarrierRule_map_of_structuralMorphism morphism carrier)
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | flatten declaration flattens sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_append, List.map_cons]
      exact .flatten (algebraRule_transport_of_structuralMorphism morphism declaration)
        flattens (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | singleton declaration flattens sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_cons, List.map_nil]
      exact .singleton (algebraRule_transport_of_structuralMorphism morphism declaration)
        flattens (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | unitElim declaration declared sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_append, List.map_cons, List.map_nil]
      exact .unitElim (algebraRule_transport_of_structuralMorphism morphism declaration)
        (by simp only [mapCollectionAlgebra_unit, declared, Option.map_some])
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | emptyUnit declaration declared sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_nil]
      exact .emptyUnit (algebraRule_transport_of_structuralMorphism morphism declaration)
        (by simp only [mapCollectionAlgebra_unit, declared, Option.map_some])
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)

/-- **Every law derived from a collection declaration maps to the same law of
the image declaration**, when the declared units are fixed. -/
theorem derivedInstance_map_of_structuralMorphism
    {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    (units : FixesDeclaredUnits morphism.symbols source.language)
    {left right : Pattern} (derived : DerivedInstance source.language left right) :
    DerivedInstance target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) := by
  cases derived with
  | bagPerm carrier sorted permuted =>
      simp only [mapPattern, mapPatternList_eq_map]
      exact .bagPerm (collectionCarrierRule_map_of_structuralMorphism morphism carrier)
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
        (permuted.map _)
  | setPerm carrier sorted permuted =>
      simp only [mapPattern, mapPatternList_eq_map]
      exact .setPerm (collectionCarrierRule_map_of_structuralMorphism morphism carrier)
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
        (permuted.map _)
  | setDedup carrier sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_cons]
      exact .setDedup (collectionCarrierRule_map_of_structuralMorphism morphism carrier)
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | flatten declaration flattens sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_append, List.map_cons]
      exact .flatten (algebraRule_map_of_structuralMorphism morphism units declaration)
        flattens
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | singleton declaration flattens sorted =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_cons, List.map_nil]
      exact .singleton (algebraRule_map_of_structuralMorphism morphism units declaration)
        flattens
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | unitElim declaration declared sorted =>
      rename_i rule kind algebra unit pre post
      have fixed : morphism.symbols.constructor unit = unit :=
        units rule declaration.authored algebra declaration.declared unit declared
      simp only [mapPattern, mapPatternList_eq_map, List.map_append, List.map_cons,
        List.map_nil, fixed]
      exact .unitElim (algebraRule_map_of_structuralMorphism morphism units declaration)
        declared
        (by simpa [mapPattern, mapGrammarRule, fixed] using
          sortedAt_map_of_structuralMorphism morphism sorted)
  | emptyUnit declaration declared sorted =>
      rename_i rule kind algebra unit
      have fixed : morphism.symbols.constructor unit = unit :=
        units rule declaration.authored algebra declaration.declared unit declared
      simp only [mapPattern, mapPatternList_eq_map, List.map_nil, fixed]
      exact .emptyUnit (algebraRule_map_of_structuralMorphism morphism units declaration)
        declared
        (by simpa [mapPattern, mapGrammarRule] using
          sortedAt_map_of_structuralMorphism morphism sorted)

/-! ## The static equivalence -/

/-- **One equation step maps to one equation step.** -/
theorem equationContextStep_map_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (units : FixesDeclaredUnits morphism.symbols source.language)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {left right : Pattern}
    (step : EquationContextStep base source.language left right) :
    EquationContextStep base' target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) := by
  cases step with
  | inContext context generator =>
      rw [← CIGSLT.mapOneHoleContext_fill, ← CIGSLT.mapOneHoleContext_fill]
      refine EquationContextStep.inContext _ ?_
      rcases generator with authored | derived
      · exact Or.inl (equationInstance_map_of_structuralMorphism morphism mapsBaseResults
          baseMono authored)
      · exact Or.inr (derivedInstance_map_of_structuralMorphism morphism units derived)

/-- A map preserving contextual equation generators preserves their least
equivalence closure.  The target equivalence pulls back to an equivalence on
the source, so Mathlib's closure elimination discharges the common law. -/
theorem equationEquiv_map_of_contextSteps {base base' : BasePremiseEvaluator}
    {source target : LanguageDef} (mapping : Pattern → Pattern)
    (maps : ∀ {left right : Pattern}, EquationContextStep base source left right →
      EquationContextStep base' target (mapping left) (mapping right))
    {left right : Pattern} (equivalent : EquationEquiv base source left right) :
    EquationEquiv base' target (mapping left) (mapping right) :=
  Relation.EqvGen.eqvGen_le
    (r' := Function.onFun (Relation.EqvGen (EquationContextStep base' target)) mapping)
    (fun _ _ step => Relation.EqvGen.rel _ _ (maps step)) _ _ equivalent

/-- Forward transport of both contextual equations and primitive reduction
preserves a step modulo equations.  This law does not assume that the map is
injective, or that every target step has a source preimage. -/
theorem stepModuloEquations_map_of_contextSteps {base base' : BasePremiseEvaluator}
    {source target : LanguageDef} (mapping : Pattern → Pattern)
    (mapsEquations : ∀ {left right : Pattern}, EquationContextStep base source left right →
      EquationContextStep base' target (mapping left) (mapping right))
    (mapsSteps : ∀ {left right : Pattern}, Step base source left right →
      Step base' target (mapping left) (mapping right))
    {left right : Pattern} (step : StepModuloEquations base source left right) :
    StepModuloEquations base' target (mapping left) (mapping right) := by
  obtain ⟨redex, contractum, before, primitive, after⟩ := step
  exact ⟨mapping redex, mapping contractum,
    equationEquiv_map_of_contextSteps mapping mapsEquations before,
    mapsSteps primitive, equationEquiv_map_of_contextSteps mapping mapsEquations after⟩

/-- **The static equivalence maps along a structural presentation morphism**
that fixes the declared units. -/
theorem equationEquiv_map_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (units : FixesDeclaredUnits morphism.symbols source.language)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {left right : Pattern}
    (equivalent : EquationEquiv base source.language left right) :
    EquationEquiv base' target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) :=
  equationEquiv_map_of_contextSteps (mapPattern morphism.symbols)
    (equationContextStep_map_of_structuralMorphism morphism units mapsBaseResults baseMono)
    equivalent

/-- **Reduction modulo the equations maps along a structural presentation
morphism.** -/
theorem stepModuloEquations_map_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (units : FixesDeclaredUnits morphism.symbols source.language)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {left right : Pattern}
    (step : StepModuloEquations base source.language left right) :
    StepModuloEquations base' target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) :=
  stepModuloEquations_map_of_contextSteps (mapPattern morphism.symbols)
    (equationContextStep_map_of_structuralMorphism morphism units mapsBaseResults baseMono)
    (SymbolMapSimulation.step_map_of_structuralMorphism morphism mapsBaseResults baseMono) step

/-! ## The evaluator with no external relation -/

/-- **One equation step maps to one equation step, for the evaluator with no
external relation.**  The evaluator hypotheses reduce to one condition on
names: the relation map fixes the built-in relation `"eq"`. -/
theorem equationContextStep_map_default {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    (units : FixesDeclaredUnits morphism.symbols source.language)
    {left right : Pattern}
    (step : EquationContextStep (engineBasePremises RelationEnv.empty) source.language
      left right) :
    EquationContextStep (engineBasePremises RelationEnv.empty) target.language
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) :=
  equationContextStep_map_of_structuralMorphism morphism units
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols
      relationFixesEq)
    (engineBasePremises_empty_mono _ _) step

/-- The static equivalence maps, for the evaluator with no external
relation. -/
theorem equationEquiv_map_default {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    (units : FixesDeclaredUnits morphism.symbols source.language)
    {left right : Pattern}
    (equivalent : EquationEquiv (engineBasePremises RelationEnv.empty) source.language
      left right) :
    EquationEquiv (engineBasePremises RelationEnv.empty) target.language
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) :=
  equationEquiv_map_of_structuralMorphism morphism units
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols
      relationFixesEq)
    (engineBasePremises_empty_mono _ _) equivalent

/-- Reduction modulo the equations maps, for the evaluator with no external
relation. -/
theorem stepModuloEquations_map_default {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    (units : FixesDeclaredUnits morphism.symbols source.language)
    {left right : Pattern}
    (step : StepModuloEquations (engineBasePremises RelationEnv.empty) source.language
      left right) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) target.language
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) :=
  stepModuloEquations_map_of_structuralMorphism morphism units
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols
      relationFixesEq)
    (engineBasePremises_empty_mono _ _) step

/-! ## Complete algebra transport -/

/-- Contextual equation generators transport with the whole declaration,
including renamed unit references. -/
theorem equationContextStep_transport_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {left right : Pattern}
    (step : EquationContextStep base source.language left right) :
    EquationContextStep base' target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) := by
  cases step with
  | inContext context generator =>
      rw [← CIGSLT.mapOneHoleContext_fill, ← CIGSLT.mapOneHoleContext_fill]
      refine EquationContextStep.inContext _ ?_
      rcases generator with authored | derived
      · exact Or.inl (equationInstance_map_of_structuralMorphism morphism mapsBaseResults
          baseMono authored)
      · exact Or.inr (derivedInstance_transport_of_structuralMorphism morphism derived)

/-- Static equivalence transports along a complete declaration map. -/
theorem equationEquiv_transport_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {left right : Pattern}
    (equivalent : EquationEquiv base source.language left right) :
    EquationEquiv base' target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) :=
  equationEquiv_map_of_contextSteps (mapPattern morphism.symbols)
    (equationContextStep_transport_of_structuralMorphism morphism mapsBaseResults baseMono)
    equivalent

/-- Reduction modulo equations transports with renamed collection units. -/
theorem stepModuloEquations_transport_of_structuralMorphism
    {base base' : BasePremiseEvaluator} {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {left right : Pattern}
    (step : StepModuloEquations base source.language left right) :
    StepModuloEquations base' target.language (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) :=
  stepModuloEquations_map_of_contextSteps (mapPattern morphism.symbols)
    (equationContextStep_transport_of_structuralMorphism morphism mapsBaseResults baseMono)
    (SymbolMapSimulation.step_map_of_structuralMorphism morphism mapsBaseResults baseMono) step

/-- With no external relation, contextual equations transport whenever the
built-in equality relation keeps its name. -/
theorem equationContextStep_transport_default {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    {left right : Pattern}
    (step : EquationContextStep (engineBasePremises RelationEnv.empty) source.language
      left right) :
    EquationContextStep (engineBasePremises RelationEnv.empty) target.language
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) :=
  equationContextStep_transport_of_structuralMorphism morphism
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols relationFixesEq)
    (engineBasePremises_empty_mono _ _) step

/-- Complete declaration transport preserves static equivalence for the
empty external-relation evaluator. -/
theorem equationEquiv_transport_default {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    {left right : Pattern}
    (equivalent : EquationEquiv (engineBasePremises RelationEnv.empty) source.language
      left right) :
    EquationEquiv (engineBasePremises RelationEnv.empty) target.language
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) :=
  equationEquiv_transport_of_structuralMorphism morphism
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols relationFixesEq)
    (engineBasePremises_empty_mono _ _) equivalent

/-- Complete declaration transport preserves reduction modulo equations
for the empty external-relation evaluator. -/
theorem stepModuloEquations_transport_default {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    {left right : Pattern}
    (step : StepModuloEquations (engineBasePremises RelationEnv.empty) source.language
      left right) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) target.language
      (mapPattern morphism.symbols left) (mapPattern morphism.symbols right) :=
  stepModuloEquations_transport_of_structuralMorphism morphism
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols relationFixesEq)
    (engineBasePremises_empty_mono _ _) step

end Mettapedia.GSLT.LanguageDef.EquationSimulation
