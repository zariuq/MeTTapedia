import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.StructuralCategory
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationRequest
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationValidation

/-!
# Functorial sparse native-type GSLT generation

The selected native-type construction is a literal syntax-emitting functor.
Its output objects are single flat `CalculusLanguageDef` values admitted by
the ordinary checker.  An input arrow first reindexes its typed demand along
an injective structural map and then appends an exact residual demand.

Generated carrier names are positional private names. Injective reindexing
preserves those positions, while append-only refinement preserves the rows
already emitted. The induced calculus-language action is therefore identity
on private names even though carrier expressions, typing evidence, and
source-language structure move nontrivially.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CategoryTheory

namespace SelectedNativeTypeFoundation

/-- The validated flat calculus generated from one request. -/
def generated (request : FoundationRequest) :
    ValidatedCalculusLanguageDef :=
  validated request.demand

/-- Injective source reindexing preserves the stable private carrier slots. -/
theorem stableCarrierTypes_reindex
    (request : FoundationRequest)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    stableCarrierTypes request.demand =
      stableCarrierTypes (request.demand.map structural) := by
  exact (Demand.stableCarrierTypes_map structural sortInjective
    request.demand).symm

theorem stableCarrierNames_reindex
    (request : FoundationRequest)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    stableCarrierNames request.demand =
      stableCarrierNames (request.demand.map structural) := by
  exact (Demand.stableCarrierNames_map structural sortInjective
    request.demand).symm

/-- Structural map induced by the horizontal, exact-reindexing part of a
request transformation. -/
noncomputable def mapReindex
    (request : FoundationRequest)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    CalculusStructuralMorphism
      (generated request)
      (validated (request.demand.map structural)) where
  symbols := CalculusLanguageSymbols.id
  mapsTypes declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapTypeDecl_id]
    change List.Mem declaration
      (definition (request.demand.map structural)).types
    change List.Mem declaration (definition request.demand).types at membership
    rw [definition_types] at membership ⊢
    rw [stableCarrierTypes_reindex request structural sortInjective]
      at membership
    exact membership
  mapsTerms declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapGrammarRule_id]
    change List.Mem declaration
      (definition (request.demand.map structural)).terms
    change List.Mem declaration (definition request.demand).terms at membership
    rw [definition_terms] at membership ⊢
    rw [stableCarrierNames_reindex request structural sortInjective]
      at membership
    exact membership
  mapsEquations declaration membership := by
    change List.Mem declaration (definition request.demand).equations at membership
    rw [definition_equations] at membership
    exact False.elim (List.not_mem_nil membership)
  mapsRewrites declaration membership := by
    change List.Mem declaration (definition request.demand).rewrites at membership
    rw [definition_rewrites] at membership
    exact False.elim (List.not_mem_nil membership)
  mapsJudgments declaration membership := by
    change List.Mem declaration (definition request.demand).judgments at membership
    change List.Mem (mapJudgmentDecl CalculusLanguageSymbols.id declaration)
      (definition (request.demand.map structural)).judgments
    rw [mapJudgmentDecl_id, definition_judgments]
    rw [definition_judgments] at membership
    rw [stableCarrierNames_reindex request structural sortInjective]
      at membership
    exact membership
  mapsRules declaration membership := by
    change List.Mem declaration (definition request.demand).rules at membership
    change List.Mem (mapRuleSchema CalculusLanguageSymbols.id declaration)
      (definition (request.demand.map structural)).rules
    rw [mapRuleSchema_id, definition_rules]
    rw [definition_rules] at membership
    rw [stableCarrierNames_reindex request structural sortInjective]
      at membership
    exact membership
  mapsConversion declaration equality := by
    change (definition request.demand).conversion = some declaration at equality
    rw [definition_conversion] at equality
    cases equality

/-- Structural inclusion induced by the vertical, append-only residual part
of a request transformation. -/
noncomputable def mapResidual
    {source target : FoundationRequest}
    (morphism : FoundationMorphism source target) :
    CalculusStructuralMorphism
      (validated (source.demand.map morphism.structural))
      (generated target) := by
  apply CalculusStructuralMorphism.ofAppendOnly
  have appendOnly := definition_appendOnly
    (source.demand.map morphism.structural) morphism.residual
  rw [morphism.target_eq] at appendOnly
  exact appendOnly

/-- Complete generated-calculus map for a mixed request transformation. -/
noncomputable def mapGenerated
    {source target : FoundationRequest}
    (morphism : FoundationMorphism source target) :
    CalculusStructuralMorphism (generated source) (generated target) :=
  CalculusStructuralMorphism.comp
    (mapReindex source morphism.structural morphism.sortInjective)
    (mapResidual morphism)

/-- Sparse OSLF syntax generation is an honest functor from generation
requests and their exact transformations to validated flat calculus GSLTs. -/
noncomputable def functor :
    CategoryTheory.Functor FoundationRequest
      ValidatedCalculusLanguageDef where
  obj := generated
  map := mapGenerated
  map_id request := by
    apply CalculusStructuralMorphism.ext
    rfl
  map_comp earlier later := by
    apply CalculusStructuralMorphism.ext
    rfl

/-- The generated map respects the canonical horizontal-then-vertical
factorization of every request transformation. -/
theorem map_horizontal_vertical_factorization
    {source target : FoundationRequest}
    (morphism : source ⟶ target) :
    functor.map morphism =
      functor.map morphism.horizontalPart ≫
        functor.map morphism.verticalPart := by
  rw [← functor.map_comp]
  exact congrArg functor.map morphism.horizontal_vertical_factorization

/-- Generated calculus maps satisfy the same reindexing/refinement square as
their source requests.  Thus sparse generation respects the elementary
horizontal/vertical interchange law. -/
theorem generated_reindex_append_square
    (request : FoundationRequest)
    (residual : Demand request.language)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    functor.map
        (FoundationMorphism.reindex request structural sortInjective) ≫
      functor.map
        (FoundationMorphism.ofDemandRefinement
          { residual := residual.map structural
            target_eq := (Demand.map_append structural
              request.demand residual).symm }) =
    functor.map
        (FoundationMorphism.ofDemandRefinement
          (appendRefinement request.demand residual)) ≫
      functor.map
        (FoundationMorphism.reindex (request.append residual)
          structural sortInjective) := by
  rw [← functor.map_comp, ← functor.map_comp]
  exact congrArg functor.map
    (reindex_append_square request residual structural sortInjective)

/-! ## Positive and negative controls -/

namespace FunctorCanary

/-- Every admitted request transformation yields a structural map of the
whole generated calculus, including judgment and inference-rule rows. -/
theorem request_transformation_maps_complete_calculus
    {source target : FoundationRequest} (morphism : source ⟶ target) :
    Nonempty (generated source ⟶ generated target) :=
  ⟨functor.map morphism⟩

/-- Every exact residual demand maps the already generated calculus into its
complete append-only extension. -/
theorem appended_demand_maps_complete_calculus
    {source : ValidatedLanguageDef} (earlier residual : Demand source) :
    Nonempty
      (generated ⟨source, earlier⟩ ⟶
        generated ⟨source, earlier.append residual⟩) :=
  ⟨functor.map
    (FoundationMorphism.ofDemandRefinement
      (appendRefinement earlier residual))⟩

/-- A non-injective structural map cannot underlie a generator-domain arrow;
generated carrier slots are therefore never silently coalesced. -/
theorem noninjective_structural_map_remains_rejected
    {source target : FoundationRequest}
    (structural : StructuralMorphism source.language target.language)
    (noninjective : ¬ Function.Injective structural.symbols.sort) :
    ¬ ∃ morphism : source ⟶ target,
      morphism.structural = structural := by
  rintro ⟨morphism, equality⟩
  apply noninjective
  intro first second namesEqual
  apply morphism.sortInjective
  rw [equality]
  exact namesEqual

end FunctorCanary

#print axioms stableCarrierNames_reindex
#print axioms stableCarrierTypes_reindex
#print axioms mapReindex
#print axioms mapResidual
#print axioms mapGenerated
#print axioms functor
#print axioms map_horizontal_vertical_factorization
#print axioms generated_reindex_append_square
#print axioms FunctorCanary.request_transformation_maps_complete_calculus
#print axioms FunctorCanary.appended_demand_maps_complete_calculus
#print axioms FunctorCanary.noninjective_structural_map_remains_rejected

end SelectedNativeTypeFoundation

end Mettapedia.OSLF.Framework
