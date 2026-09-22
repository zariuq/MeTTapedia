import Mettapedia.OSLF.Framework.ContextualModalSignatureCompiler
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationTransport

/-!
# Transport of the contextual modal signature compiler

Structural language maps act on retained occurrence typings and their ordered
carrier support. Contextual modal declarations commute with this action when
the supplied carrier resolvers agree on that finite support. For injective
sort maps, the actual sparse carrier compiler supplies this compatibility:
source expressions move while their certified private slots stay fixed.

Authored language names reindex explicitly; equality of the emitted semantic
rows does not identify those names or the source carrier expressions.

These are transport laws for the existing compiler, not a free generated
typing construction or an adjunction. No local modal profile is selected.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

private def mapExtensionName (f : String → String)
    (extension : CalculusLanguageExtension) : CalculusLanguageExtension :=
  { extension with rename := extension.rename.map f }

private theorem mapExtensionName_comp (f : String → String)
    (first second : CalculusLanguageExtension) :
    (mapExtensionName f first).comp (mapExtensionName f second) =
      mapExtensionName f (first.comp second) := by
  cases firstName : first.rename <;> cases secondName : second.rename <;>
    simp [mapExtensionName, CalculusLanguageExtension.comp, firstName, secondName]

private theorem mapExtensionName_apply (name : String)
    (extension : CalculusLanguageExtension) (base : CalculusLanguageDef) :
    (mapExtensionName (fun _ => name) extension).apply { base with name := name } =
      { extension.apply base with name := name } := by
  cases rename : extension.rename <;>
    simp [mapExtensionName, CalculusLanguageExtension.apply, rename]

namespace ContextualModalSignature

/-- Reindexing the carrier coordinate of an ordered parameter row is the
same as pulling back its resolver. Names and dependency order do not move. -/
theorem parametersFor_map (symbols : LanguageDefSymbolMap)
    (resolve : TypeExpr → String) (bindings : List (String × TypeExpr))
    (result : TypeExpr) :
    parametersFor resolve
        (bindings.map fun binding => (binding.1, mapTypeExpr symbols binding.2))
        (mapTypeExpr symbols result) =
      parametersFor (fun object => resolve (mapTypeExpr symbols object))
        bindings result := by
  simp [parametersFor, relyParametersFor, resolvedCarrier, List.map_map,
    Function.comp_def]

/-- The same contextual modal declaration travels with its retained typing.
Compatibility is required only on carriers the declaration actually uses. -/
theorem modalRule_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sourceResolve targetResolve : TypeExpr → String) (slot : Nat)
    (typing : DisplayedRewriteTyping source)
    (compatible : ∀ object ∈ carrierSupport typing,
      targetResolve (mapTypeExpr morphism.symbols object) = sourceResolve object) :
    modalRule targetResolve slot (typing.map morphism) =
      modalRule sourceResolve slot typing := by
  have pulled : modalRule targetResolve slot (typing.map morphism) =
      modalRule (fun object => targetResolve (mapTypeExpr morphism.symbols object))
        slot typing := by
    unfold modalRule parameters relyBindings
    rw [DisplayedContextProfile.bindings_map]
    dsimp only [DisplayedRewriteTyping.map]
    rw [parametersFor_map]
  exact pulled.trans (modalRule_congr _ _ slot typing compatible)

end ContextualModalSignature

namespace ContextualModalExtension

private theorem idxOf_map_injective {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : α → β) (injective : Function.Injective f)
    (items : List α) (item : α) :
    (items.map f).idxOf (f item) = items.idxOf item := by
  induction items with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.idxOf_cons, cond_eq_ite, beq_iff_eq,
        injective.eq_iff, inductionHypothesis]

/-- Exact injective reindexing preserves the certified slot of a retained
carrier. This is a lookup theorem, not equality of carrier expressions. -/
theorem compiledCarrierName_map_of_mem {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeFoundation.Demand source) {object : TypeExpr}
    (retained : object ∈ demand.carrierObjects.objects) :
    compiledCarrierName (demand.map morphism)
        (mapTypeExpr morphism.symbols object) =
      compiledCarrierName demand object := by
  have mappedRetained := SelectedNativeTypeFoundation.Demand.mappedCarrier_mem
    morphism demand retained
  rw [compiledCarrierName_of_mem _ mappedRetained,
    compiledCarrierName_of_mem _ retained]
  change CarrierObjectLanguageDef.Naming.indexedNameAt
      ((demand.map morphism).carrierObjects.objects.idxOf
        (mapTypeExpr morphism.symbols object)) =
    CarrierObjectLanguageDef.Naming.indexedNameAt
      (demand.carrierObjects.objects.idxOf object)
  rw [SelectedNativeTypeFoundation.Demand.carrierInventory_map
    morphism sortInjective demand]
  rw [idxOf_map_injective _
    (StructuralRenamingSemantics.mapTypeExpr_injective
      morphism.symbols sortInjective)]

end ContextualModalExtension

namespace SelectedNativeTypeFoundation

/-- Exact source reindexing changes the slot denotations, but no emitted
private carrier row. The equality follows from inventory transport. -/
theorem definition_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : Demand source) :
    definition (demand.map morphism) =
      { definition demand with name := (definition (Demand.empty target)).name } := by
  apply CalculusLanguageDef.ext
  · rfl
  all_goals simp [Demand.stableCarrierTypes_map morphism sortInjective,
    Demand.stableCarrierNames_map morphism sortInjective]

private theorem residual_eq_of_endpoints
    {firstSource firstTarget secondSource secondTarget : CalculusLanguageDef}
    (first : CalculusLanguageExtension.AppendOnlyCalculusRefinement
      firstSource firstTarget)
    (second : CalculusLanguageExtension.AppendOnlyCalculusRefinement
      secondSource secondTarget)
    (name : String)
    (sources : firstSource = { secondSource with name := name })
    (targets : firstTarget = { secondTarget with name := name }) :
    first.residual = { second.residual with rename := some name } := by
  subst sources
  subst targets
  rfl

/-- The actual allocated suffix is invariant under injective reindexing of
both the existing demand and its residual. -/
theorem appendExtension_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (compiled residual : Demand source) :
    appendExtension (compiled.map morphism) (residual.map morphism) =
      { appendExtension compiled residual with
        rename := some (definition (Demand.empty target)).name } := by
  unfold appendExtension CarrierObjectLanguageDef.indexedAppendExtension
  apply residual_eq_of_endpoints
  · exact definition_map morphism sortInjective compiled
  · rw [← Demand.carrierObjects_append, ← Demand.carrierObjects_append,
      ← Demand.map_append]
    exact definition_map morphism sortInjective (compiled.append residual)

end SelectedNativeTypeFoundation

namespace GroundedRewriteOccurrence

/-- Singleton demand formation commutes with transport of the actual atom. -/
theorem singletonDemand_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (occurrence : GroundedRewriteOccurrence source) :
    (occurrence.map morphism).singletonDemand =
      occurrence.singletonDemand.map morphism := by
  apply SelectedNativeTypeFoundation.Demand.ext
  rfl

/-- Ordered atom streams map to the same mapped batch demand. -/
theorem demandOfList_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (occurrences : List (GroundedRewriteOccurrence source)) :
    demandOfList (occurrences.map (map morphism)) =
      (demandOfList occurrences).map morphism := by
  apply SelectedNativeTypeFoundation.Demand.ext
  simp [demandOfList, SelectedNativeTypeFoundation.Demand.map,
    List.map_map, Function.comp_def]

end GroundedRewriteOccurrence

namespace SelectedNativeTypeFoundation.Demand

/-- Transport preserves the complete chronological occurrence stream,
including distinct occurrences with equal typing projections. -/
theorem groundedOccurrences_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) (demand :
      SelectedNativeTypeFoundation.Demand source) :
    (demand.map morphism).groundedOccurrences =
      demand.groundedOccurrences.map (GroundedRewriteOccurrence.map morphism) := by
  apply GroundedRewriteOccurrence.list_ext
  rw [groundedOccurrences_typings, map_typings]
  have typed := congrArg (List.map (DisplayedRewriteTyping.map morphism))
    (groundedOccurrences_typings demand)
  simpa only [List.map_map, Function.comp_def,
    GroundedRewriteOccurrence.map_typing] using typed.symm

end SelectedNativeTypeFoundation.Demand

namespace ContextualModalSignatureCompiler

/-- The emitted contextual row is invariant under exact source reindexing,
including its global occurrence slot and complete dependent parameter row. -/
theorem modalTerm_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) :
    modalTerm (compiled.map morphism) (occurrence.map morphism) =
      modalTerm compiled occurrence := by
  unfold modalTerm singleton
  rw [GroundedRewriteOccurrence.singletonDemand_map,
    ← SelectedNativeTypeFoundation.Demand.map_append]
  simp only [SelectedNativeTypeFoundation.Demand.map_typings, List.length_map,
    GroundedRewriteOccurrence.map_typing]
  apply ContextualModalSignature.modalRule_map
  intro object membership
  apply ContextualModalExtension.compiledCarrierName_map_of_mem
    morphism sortInjective
  apply SelectedNativeTypeFoundation.Demand.requiredCarrier_mem_objects
    (compiled.append occurrence.singletonDemand) (typing := occurrence.typing)
  · simp [SelectedNativeTypeFoundation.Demand.append,
      GroundedRewriteOccurrence.singletonDemand]
  · exact ContextualModalExtension.carrierSupport_mem_requiredCarrierRoots
      occurrence.typing membership

/-- The chronological compiler's real carrier/modal delta transports
without regrouping or restarting the prefix. -/
theorem stepExtension_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) :
    stepExtension (compiled.map morphism) (occurrence.map morphism) =
      mapExtensionName
        (fun _ => (SelectedNativeTypeFoundation.definition
          (SelectedNativeTypeFoundation.Demand.empty target)).name)
        (stepExtension compiled occurrence) := by
  unfold stepExtension singleton
  simp only [GroundedRewriteOccurrence.singletonDemand_map]
  rw [SelectedNativeTypeFoundation.appendExtension_map morphism sortInjective,
    modalTerm_map morphism sortInjective]
  rfl

/-- The existing writer-state compiler emits the same ordered extension
after transporting its retained state and atom stream. -/
theorem runFrom_extension_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrences : List (GroundedRewriteOccurrence source)) :
    ((generator target).runFrom (compiled.map morphism)
        (occurrences.map (GroundedRewriteOccurrence.map morphism))).2 =
      mapExtensionName
        (fun _ => (SelectedNativeTypeFoundation.definition
          (SelectedNativeTypeFoundation.Demand.empty target)).name)
        (((generator source).runFrom compiled occurrences).2) := by
  induction occurrences generalizing compiled with
  | nil => rfl
  | cons occurrence occurrences inductionHypothesis =>
      simp only [List.map_cons, IncrementalCalculusGenerator.runFrom_cons]
      change
        (stepExtension (compiled.map morphism) (occurrence.map morphism)).comp
          (((generator target).runFrom
            ((compiled.map morphism).append (singleton (occurrence.map morphism)))
            (occurrences.map (GroundedRewriteOccurrence.map morphism))).2) = _
      rw [stepExtension_map morphism sortInjective]
      unfold singleton
      rw [GroundedRewriteOccurrence.singletonDemand_map,
        ← SelectedNativeTypeFoundation.Demand.map_append,
        inductionHypothesis]
      exact mapExtensionName_comp _ _ _

/-- Full chronological compilation commutes with injective source
reindexing. This covers every emitted row, not merely declaration counts. -/
theorem definition_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeFoundation.Demand source) :
    definition (demand.map morphism) =
      { definition demand with name := (base target).name } := by
  unfold definition IncrementalCalculusGenerator.compileFrom
  rw [SelectedNativeTypeFoundation.Demand.groundedOccurrences_map]
  have emptyMap : (SelectedNativeTypeFoundation.Demand.empty source).map morphism =
      SelectedNativeTypeFoundation.Demand.empty target := by
    apply SelectedNativeTypeFoundation.Demand.ext
    rfl
  rw [← emptyMap, runFrom_extension_map morphism sortInjective]
  have baseMap : base target = { base source with name := (base target).name } := by
    unfold base
    rw [← emptyMap, SelectedNativeTypeFoundation.definition_map morphism sortInjective]
  rw [baseMap]
  exact mapExtensionName_apply _ _ _

/-- The already compiled prefix and its exact residual extension travel
together. Reindexing does not invent a second continuation semantics. -/
theorem continuationExtension_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    continuationExtension (compiled.map morphism) (residual.map morphism) =
      mapExtensionName
        (fun _ => (base target).name)
        (continuationExtension compiled residual) := by
  unfold continuationExtension
  rw [SelectedNativeTypeFoundation.Demand.groundedOccurrences_map,
    runFrom_extension_map morphism sortInjective]
  rfl

end ContextualModalSignatureCompiler

/-! ## Non-identity transport and rejected row changes -/

namespace ContextualModalTransportCanary

open ContextualModalSignature

private def symbols : LanguageDefSymbolMap where
  sort := fun name => "transported:" ++ name
  constructor := fun name => "transported:" ++ name
  relation := fun name => "transported:" ++ name
  equation := fun name => "transported:" ++ name
  rewrite := fun name => "transported:" ++ name

private def targetLanguage : LanguageDef :=
  StructuralCoproduct.renameLanguage "contextual-modal-transport-target"
    symbols Canary.sourceLanguage

private theorem target_valid : targetLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide +kernel
  case hconstructors => decide +kernel
  case hrewrites => decide +kernel
  case hcategory => decide +kernel
  case hparams => decide +kernel
  case hsyntax => decide +kernel
  case hrewriteValid =>
    intro rewrite membership
    have selected : rewrite = mapRewriteRule symbols Canary.contextualRewrite := by
      simpa [targetLanguage, StructuralCoproduct.renameLanguage,
        Canary.sourceLanguage] using membership
    subst rewrite
    simp [LanguageDef.validateRewrite, targetLanguage,
      StructuralCoproduct.renameLanguage, Canary.sourceLanguage,
      mapRewriteRule, mapTypeContext, mapPattern, mapPatternList,
      mapTypeDecl, mapGrammarRule, mapTermParam, mapTypeExpr, symbols,
      Canary.contextualRewrite, Canary.ternaryTerm, Canary.termType,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name membership
    simpa [TypeExpr.baseNames] using membership

private def target : ValidatedLanguageDef := ⟨targetLanguage, target_valid⟩

private def morphism : StructuralMorphism Canary.source target where
  symbols := symbols
  mapsTypes _ membership := List.mem_map_of_mem membership
  mapsTerms _ membership := List.mem_map_of_mem membership
  mapsEquations _ membership := List.mem_map_of_mem membership
  mapsRewrites _ membership := List.mem_map_of_mem membership

private theorem sortInjective : Function.Injective morphism.symbols.sort := by
  intro first second same
  exact (String.append_right_inj "transported:").mp same

private def occurrence : GroundedRewriteOccurrence Canary.source where
  typing := Canary.middleTyping
  grounded := by
    intro object membership name nameMembership
    simp [SelectedNativeTypeFoundation.requiredCarrierRoots,
      DisplayedContextProfile.carrierTypes,
      Canary.middle_occurrence_dependencies_exact] at membership
    dsimp only [Canary.middleTyping] at membership
    simp only [List.not_mem_nil] at membership
    have objectEqual : object = .base Canary.termType.name := by
      rcases membership with same | same | impossible | same
      · exact same
      · exact same
      · exact impossible.elim
      · exact same
    subst object
    simpa [TypeExpr.baseNames, Canary.source, Canary.sourceLanguage,
      LanguageDef.typeNames] using nameMembership

/-- Source reindexing is nontrivial even though generated private rows align. -/
theorem source_carrier_really_changes :
    mapTypeExpr morphism.symbols occurrence.typing.focusType ≠
      occurrence.typing.focusType := by
  decide +kernel

/-- Both fixed-context dependencies survive the transported middle
occurrence; the focus-local variable is not promoted to a rely argument. -/
theorem contextual_row_still_has_three_parameters (resolve : TypeExpr → String) :
    (modalRule resolve 7 (occurrence.typing.map morphism)).params.length = 3 := by
  rw [modalRule_parameter_count, DisplayedContextProfile.bindings_map]
  simp [occurrence, Canary.middle_occurrence_dependencies_exact]

/-- The complete actual compiler artifact transports, with the changed
authored-language name accounted for instead of silently equated. -/
theorem chronological_rows_transport :
    ContextualModalSignatureCompiler.definition
        (occurrence.singletonDemand.map morphism) =
      { ContextualModalSignatureCompiler.definition occurrence.singletonDemand with
        name := (ContextualModalSignatureCompiler.base target).name } :=
  ContextualModalSignatureCompiler.definition_map morphism sortInjective _

/-- Named dependency order remains observable even when every carrier is
the same. Permuting relies is not the established transport action. -/
theorem reversed_dependencies_change_row (resolve : TypeExpr → String)
    (carrier : TypeExpr) :
    parametersFor resolve [("left", carrier), ("right", carrier)] carrier ≠
      parametersFor resolve [("right", carrier), ("left", carrier)] carrier := by
  intro same
  have heads := congrArg (fun parameters : List TermParam => parameters.head?) same
  simp [parametersFor, relyParametersFor, TermParam.simple.injEq] at heads

/-- Removing a fixed-context dependency changes the arity of the generated
row; a unary approximation cannot pass the contextual transport law. -/
theorem dropped_dependency_changes_row (resolve : TypeExpr → String)
    (carrier : TypeExpr) :
    parametersFor resolve [("left", carrier), ("right", carrier)] carrier ≠
      parametersFor resolve [("left", carrier)] carrier := by
  intro same
  have lengths := congrArg List.length same
  simp at lengths

end ContextualModalTransportCanary

#print axioms ContextualModalSignature.parametersFor_map
#print axioms ContextualModalSignature.modalRule_map
#print axioms ContextualModalExtension.compiledCarrierName_map_of_mem
#print axioms ContextualModalSignatureCompiler.modalTerm_map
#print axioms SelectedNativeTypeFoundation.definition_map
#print axioms SelectedNativeTypeFoundation.appendExtension_map
#print axioms ContextualModalSignatureCompiler.runFrom_extension_map
#print axioms ContextualModalSignatureCompiler.definition_map
#print axioms ContextualModalSignatureCompiler.continuationExtension_map
#print axioms ContextualModalTransportCanary.source_carrier_really_changes
#print axioms ContextualModalTransportCanary.chronological_rows_transport
#print axioms ContextualModalTransportCanary.reversed_dependencies_change_row
#print axioms ContextualModalTransportCanary.dropped_dependency_changes_row

end Mettapedia.OSLF.Framework
