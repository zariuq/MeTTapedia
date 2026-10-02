import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationValidation
import Mettapedia.GSLT.LanguageDef.CostFunctor

/-!
# Transport of finite continuation decorations

Continuation positions are transported through the actual declaration map.
Their parameter indices, schema variables and binder metadata are retained.
This supplies the finite-bundle action over existing continued theory maps;
it does not assert operational preservation for a generated cost language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism WellSorted

theorem continuationResult?_mapTermParam (symbols : LanguageDefSymbolMap)
    (parameter : TermParam) :
    continuationResult? (mapTermParam symbols parameter) =
      (continuationResult? parameter).map (mapTypeExpr symbols) := by
  unfold continuationResult?
  rw [parameterType?_mapTermParam]
  cases parameterType? parameter with
  | none => rfl
  | some type => cases type <;> rfl

namespace ContinuationSchemaVariable

def map {pattern : Pattern} (symbols : LanguageDefSymbolMap)
    (witness : ContinuationSchemaVariable pattern) :
    ContinuationSchemaVariable (mapPattern symbols pattern) := by
  cases witness with
  | plain name => exact .plain name
  | abstraction binder name => exact .abstraction binder name
  | multiAbstraction arity binders name => exact .multiAbstraction arity binders name

@[simp] theorem map_name {pattern : Pattern} (symbols : LanguageDefSymbolMap)
    (witness : ContinuationSchemaVariable pattern) :
    (witness.map symbols).name = witness.name := by
  cases witness <;> rfl

instance {pattern : Pattern} : Subsingleton (ContinuationSchemaVariable pattern) where
  allEq left right := by cases left <;> cases right <;> rfl

end ContinuationSchemaVariable

namespace ContinuationPosition

def map {source target : InteractivePresentation}
    {sourceConstructor : DeclaredConstructor source.presentation}
    {targetConstructor : DeclaredConstructor target.presentation}
    (symbols : LanguageDefSymbolMap)
    (constructorMap : mapGrammarRule symbols sourceConstructor.1 = targetConstructor.1)
    (sortMap : symbols.sort source.interactingSort.1.name = target.interactingSort.1.name)
    (position : ContinuationPosition source sourceConstructor) :
    ContinuationPosition target targetConstructor where
  index := position.index
  inBounds := by
    rw [← constructorMap]
    simpa [mapGrammarRule] using position.inBounds
  hasInteractingResult := by
    have parameterMap :
        targetConstructor.1.params[position.index]'(by
          rw [← constructorMap]
          simpa [mapGrammarRule] using position.inBounds) =
        mapTermParam symbols position.toConstructorParameter.parameter := by
      simp [← constructorMap, mapGrammarRule, ConstructorParameter.parameter]
    dsimp only [ConstructorParameter.parameter]
    rw [parameterMap, continuationResult?_mapTermParam, position.hasInteractingResult]
    simp [mapTypeExpr, sortMap]

@[simp] theorem map_index {source target : InteractivePresentation}
    {sourceConstructor : DeclaredConstructor source.presentation}
    {targetConstructor : DeclaredConstructor target.presentation}
    (symbols : LanguageDefSymbolMap)
    (constructorMap : mapGrammarRule symbols sourceConstructor.1 = targetConstructor.1)
    (sortMap : symbols.sort source.interactingSort.1.name = target.interactingSort.1.name)
    (position : ContinuationPosition source sourceConstructor) :
    (position.map symbols constructorMap sortMap).index = position.index := rfl

end ContinuationPosition

theorem RepresentedBy.map {constructor : GrammarRule} {pattern : Pattern}
    (represented : RepresentedBy constructor pattern) (symbols : LanguageDefSymbolMap) :
    RepresentedBy (mapGrammarRule symbols constructor) (mapPattern symbols pattern) := by
  cases pattern <;> simp only [RepresentedBy] at represented
  case apply label arguments =>
    obtain ⟨ordinary, labelEq, arityEq⟩ := represented
    refine ⟨fun bare => ordinary ((usesBareCollection_mapGrammarRule_iff _ _).mp bare), ?_, ?_⟩
    · exact congrArg symbols.constructor labelEq
    · simpa [mapPatternList_eq_map, mapGrammarRule] using arityEq
  case collection tag elements rest =>
    obtain ⟨name, type, parameters⟩ := represented
    exact ⟨name, mapTypeExpr symbols type, by simp [mapGrammarRule, parameters, mapTermParam,
      mapTypeExpr]⟩

namespace InteractionOperandForm

def map {source target : InteractivePresentation}
    {sourceConstructor : DeclaredConstructor source.presentation}
    {targetConstructor : DeclaredConstructor target.presentation}
    {position : ContinuationPosition source sourceConstructor}
    {schema pattern : Pattern}
    (form : InteractionOperandForm sourceConstructor position schema pattern)
    (symbols : LanguageDefSymbolMap)
    (constructorMap : mapGrammarRule symbols sourceConstructor.1 = targetConstructor.1)
    (sortMap : symbols.sort source.interactingSort.1.name = target.interactingSort.1.name) :
    InteractionOperandForm targetConstructor (position.map symbols constructorMap sortMap)
      (mapPattern symbols schema) (mapPattern symbols pattern) := by
  cases form with
  | direct same => exact .direct (congrArg (mapPattern symbols) same)
  | introduced represented selected =>
    refine .introduced (by simpa only [constructorMap] using represented.map symbols) ?_
    cases schema <;> simp only at selected
    simpa only [mapPattern, mapPatternList_eq_map, List.getElem?_map,
      ContinuationPosition.map_index, Option.map_some] using
      congrArg (Option.map (mapPattern symbols)) selected

end InteractionOperandForm

namespace ContinuationDecorationSlot

def map {source target : InteractivePresentation}
    {sourceOperand : InteractionOperandProfile source}
    {targetOperand : InteractionOperandProfile target}
    (symbols : LanguageDefSymbolMap)
    (constructorMap : mapGrammarRule symbols sourceOperand.constructor.1 = targetOperand.constructor.1)
    (sortMap : symbols.sort source.interactingSort.1.name = target.interactingSort.1.name)
    (schemaMap : mapPattern symbols sourceOperand.schemaTerm = targetOperand.schemaTerm)
    (slot : ContinuationDecorationSlot sourceOperand) : ContinuationDecorationSlot targetOperand where
  position := slot.position.map symbols constructorMap sortMap
  pattern := mapPattern symbols slot.pattern
  schemaVariable := slot.schemaVariable.map symbols
  form := by
    rw [← schemaMap]
    exact slot.form.map symbols constructorMap sortMap

@[simp] theorem map_index {source target : InteractivePresentation}
    {sourceOperand : InteractionOperandProfile source}
    {targetOperand : InteractionOperandProfile target}
    (symbols : LanguageDefSymbolMap)
    (constructorMap : mapGrammarRule symbols sourceOperand.constructor.1 = targetOperand.constructor.1)
    (sortMap : symbols.sort source.interactingSort.1.name = target.interactingSort.1.name)
    (schemaMap : mapPattern symbols sourceOperand.schemaTerm = targetOperand.schemaTerm)
    (slot : ContinuationDecorationSlot sourceOperand) :
    (slot.map symbols constructorMap sortMap schemaMap).position.index = slot.position.index := rfl

@[simp] theorem map_name {source target : InteractivePresentation}
    {sourceOperand : InteractionOperandProfile source}
    {targetOperand : InteractionOperandProfile target}
    (symbols : LanguageDefSymbolMap)
    (constructorMap : mapGrammarRule symbols sourceOperand.constructor.1 = targetOperand.constructor.1)
    (sortMap : symbols.sort source.interactingSort.1.name = target.interactingSort.1.name)
    (schemaMap : mapPattern symbols sourceOperand.schemaTerm = targetOperand.schemaTerm)
    (slot : ContinuationDecorationSlot sourceOperand) :
    (slot.map symbols constructorMap sortMap schemaMap).schemaVariable.name =
      slot.schemaVariable.name := ContinuationSchemaVariable.map_name _ _

/-- A slot's data are its position and schema pattern; the remaining fields
certify their occurrence in the fixed operand. -/
@[ext] theorem ext {presentation : InteractivePresentation}
    {operand : InteractionOperandProfile presentation}
    (left right : ContinuationDecorationSlot operand)
    (indexEq : left.position.index = right.position.index)
    (patternEq : left.pattern = right.pattern) : left = right := by
  have formUnique {position : ContinuationPosition presentation operand.constructor}
      {pattern : Pattern} (witness : ContinuationSchemaVariable pattern)
      (a b : InteractionOperandForm operand.constructor position operand.schemaTerm pattern) : a = b := by
    cases a with
    | direct same =>
        cases b with
        | direct other => rfl
        | introduced represented selected =>
            have impossible : RepresentedBy operand.constructor.1 pattern := same ▸ represented
            cases witness <;> exact False.elim impossible
    | introduced represented selected =>
        cases b with
        | introduced other selectedOther => rfl
        | direct same =>
            have impossible : RepresentedBy operand.constructor.1 pattern := same ▸ represented
            cases witness <;> exact False.elim impossible
  cases left with
  | mk leftPosition leftPattern leftVariable leftForm =>
      cases right with
      | mk rightPosition rightPattern rightVariable rightForm =>
          dsimp only at indexEq patternEq
          have positions : leftPosition = rightPosition := by
            cases leftPosition with
            | mk leftParameter leftResult =>
                cases rightPosition with
                | mk rightParameter rightResult =>
                    cases leftParameter
                    cases rightParameter
                    cases indexEq
                    rfl
          cases positions
          cases patternEq
          have witnesses : leftVariable = rightVariable := Subsingleton.elim _ _
          cases witnesses
          rw [formUnique leftVariable leftForm rightForm]

end ContinuationDecorationSlot

namespace ContinuationDecorationProfile

/-- Reindex the finite decoration along an existing interactive declaration
map that carries the two authored operand occurrences. Canonicalization and
bisimilarity are not needed to transport this syntactic data. -/
def mapAlong {source target : IGSLT}
    {sourceCut : InteractionCutPresentation source} {targetCut : InteractionCutPresentation target}
    (morphism : InteractiveMorphism source.presentation target.presentation)
    (programConstructor : morphism.structural.mapConstructor sourceCut.program.constructor =
      targetCut.program.constructor)
    (environmentConstructor : morphism.structural.mapConstructor sourceCut.environment.constructor =
      targetCut.environment.constructor)
    (programSchema : mapPattern morphism.structural.symbols sourceCut.program.schemaTerm =
      targetCut.program.schemaTerm)
    (environmentSchema : mapPattern morphism.structural.symbols sourceCut.environment.schemaTerm =
      targetCut.environment.schemaTerm)
    (profile : ContinuationDecorationProfile sourceCut) : ContinuationDecorationProfile targetCut where
  programAdditional := profile.programAdditional.map (ContinuationDecorationSlot.map
    morphism.structural.symbols (congrArg Subtype.val programConstructor)
    (congrArg (fun sort => sort.1.name) morphism.mapsInteractingSort) programSchema)
  environmentAdditional := profile.environmentAdditional.map (ContinuationDecorationSlot.map
    morphism.structural.symbols (congrArg Subtype.val environmentConstructor)
    (congrArg (fun sort => sort.1.name) morphism.mapsInteractingSort) environmentSchema)
  constructorClosure := profile.constructorClosure.map morphism.structural.mapConstructor

@[simp] theorem mapAlong_id {source : IGSLT} {cut : InteractionCutPresentation source}
    (profile : ContinuationDecorationProfile cut) :
    profile.mapAlong (InteractiveMorphism.id source.presentation)
      (StructuralMorphism.mapConstructor_id _ _) (StructuralMorphism.mapConstructor_id _ _)
      (mapPattern_id _) (mapPattern_id _) = profile := by
  cases profile with
  | mk program environment closure =>
      simp only [mapAlong]
      congr 1
      · conv_rhs => rw [← List.map_id program]
        apply List.map_congr_left
        intro slot _
        apply ContinuationDecorationSlot.ext
        · rfl
        · exact mapPattern_id _
      · conv_rhs => rw [← List.map_id environment]
        apply List.map_congr_left
        intro slot _
        apply ContinuationDecorationSlot.ext
        · rfl
        · exact mapPattern_id _
      · conv_rhs => rw [← List.map_id closure]
        apply List.map_congr_left
        intro constructor _
        exact StructuralMorphism.mapConstructor_id _ _

theorem mapAlong_comp {source middle target : IGSLT}
    {sourceCut : InteractionCutPresentation source} {middleCut : InteractionCutPresentation middle}
    {targetCut : InteractionCutPresentation target}
    (first : InteractiveMorphism source.presentation middle.presentation)
    (second : InteractiveMorphism middle.presentation target.presentation)
    (programFirst : first.structural.mapConstructor sourceCut.program.constructor = middleCut.program.constructor)
    (environmentFirst : first.structural.mapConstructor sourceCut.environment.constructor = middleCut.environment.constructor)
    (schemaProgramFirst : mapPattern first.structural.symbols sourceCut.program.schemaTerm = middleCut.program.schemaTerm)
    (schemaEnvironmentFirst : mapPattern first.structural.symbols sourceCut.environment.schemaTerm = middleCut.environment.schemaTerm)
    (programSecond : second.structural.mapConstructor middleCut.program.constructor = targetCut.program.constructor)
    (environmentSecond : second.structural.mapConstructor middleCut.environment.constructor = targetCut.environment.constructor)
    (schemaProgramSecond : mapPattern second.structural.symbols middleCut.program.schemaTerm = targetCut.program.schemaTerm)
    (schemaEnvironmentSecond : mapPattern second.structural.symbols middleCut.environment.schemaTerm = targetCut.environment.schemaTerm)
    (profile : ContinuationDecorationProfile sourceCut) :
    profile.mapAlong (InteractiveMorphism.comp first second)
      (by change (StructuralMorphism.comp first.structural second.structural).mapConstructor _ = _
          rw [StructuralMorphism.mapConstructor_comp, programFirst, programSecond])
      (by change (StructuralMorphism.comp first.structural second.structural).mapConstructor _ = _
          rw [StructuralMorphism.mapConstructor_comp, environmentFirst, environmentSecond])
      (by change mapPattern (first.structural.symbols.comp second.structural.symbols) _ = _
          rw [mapPattern_comp, schemaProgramFirst, schemaProgramSecond])
      (by change mapPattern (first.structural.symbols.comp second.structural.symbols) _ = _
          rw [mapPattern_comp, schemaEnvironmentFirst, schemaEnvironmentSecond]) =
      (profile.mapAlong first programFirst environmentFirst schemaProgramFirst schemaEnvironmentFirst).mapAlong
        second programSecond environmentSecond schemaProgramSecond schemaEnvironmentSecond := by
  cases profile with
  | mk program environment closure =>
      simp only [mapAlong, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro slot _
        apply ContinuationDecorationSlot.ext
        · rfl
        · exact mapPattern_comp _ _ _
      · apply List.map_congr_left
        intro slot _
        apply ContinuationDecorationSlot.ext
        · rfl
        · exact mapPattern_comp _ _ _
      · apply List.map_congr_left
        intro constructor _
        exact StructuralMorphism.mapConstructor_comp _ _ _

variable {source target : CIGSLT}

/-- Continued maps use the same operand transport. No new contraction rule or
continuation slot is selected by the stronger categorical interface. -/
def map (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut) : ContinuationDecorationProfile target.cut :=
  profile.mapAlong morphism.underlying.structural
    morphism.mapsProgramConstructor morphism.mapsEnvironmentConstructor
    morphism.mapsProgramSchema morphism.mapsEnvironmentSchema

@[simp] theorem map_selectedParameter (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut) (constructor : GrammarRule) (index : Nat) :
    (profile.map morphism).selectedParameter
        (mapGrammarRule morphism.underlying.structural.structural.symbols constructor) index =
      profile.selectedParameter constructor index := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedParameter, map, mapAlong, List.any_map, Function.comp_def,
    ContinuationDecorationSlot.map, ContinuationPosition.map, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq, morphism.isSelectedContinuation_map,
    morphism.mapConstructor_eq_program_iff, morphism.mapConstructor_eq_environment_iff]

@[simp] theorem map_selectedVariable (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut) (name : String) :
    (profile.map morphism).selectedVariable name = profile.selectedVariable name := by
  simp only [selectedVariable, map, mapAlong, List.any_map, Function.comp_def,
    ContinuationDecorationSlot.map, ContinuationSchemaVariable.map_name, ← morphism.mapsProgramContinuationVariableName,
    ← morphism.mapsEnvironmentContinuationVariableName]

@[simp] theorem map_id (profile : ContinuationDecorationProfile source.cut) :
    profile.map (CIGSLT.Morphism.id source) = profile :=
  profile.mapAlong_id

@[simp] theorem map_comp {third : CIGSLT}
    (first : source.Morphism target) (second : target.Morphism third)
    (profile : ContinuationDecorationProfile source.cut) :
    profile.map (CIGSLT.Morphism.comp first second) = (profile.map first).map second :=
  profile.mapAlong_comp first.underlying.structural second.underlying.structural
    first.mapsProgramConstructor first.mapsEnvironmentConstructor
    first.mapsProgramSchema first.mapsEnvironmentSchema
    second.mapsProgramConstructor second.mapsEnvironmentConstructor
    second.mapsProgramSchema second.mapsEnvironmentSchema

theorem map_baseParameter (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut) (constructor : GrammarRule)
    (entry : TermParam × Nat) :
    mapTermParam (costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols)
        (profile.baseParameter constructor entry) =
      (profile.map morphism).baseParameter
        (mapGrammarRule morphism.underlying.structural.structural.symbols constructor)
        (mapTermParam morphism.underlying.structural.structural.symbols entry.1, entry.2) := by
  unfold baseParameter
  rw [map_selectedParameter]
  split
  · exact mapTermParam_costWrapped _ _ _ morphism.mapsInteractingSortName
      morphism.reflectsInteractingSort entry.1
  · exact mapTermParam_costBase _ entry.1

/-- Decorating declarations commutes with their actual structural translation. -/
theorem map_baseConstructor (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut) (constructor : GrammarRule) :
    mapGrammarRule (costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols)
        (profile.baseConstructor constructor) =
      (profile.map morphism).baseConstructor
        (mapGrammarRule morphism.underlying.structural.structural.symbols constructor) := by
  have parameters :
      (constructor.params.zipIdx.map (profile.baseParameter constructor)).map
          (mapTermParam (costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols)) =
        (mapGrammarRule morphism.underlying.structural.structural.symbols constructor).params.zipIdx.map
          ((profile.map morphism).baseParameter
            (mapGrammarRule morphism.underlying.structural.structural.symbols constructor)) := by
    simp only [mapGrammarRule]
    rw [List.zipIdx_map]
    simp only [List.map_map]
    apply List.map_congr_left
    intro entry _
    exact profile.map_baseParameter morphism constructor entry
  cases constructor
  simp only [baseConstructor, mapGrammarRule] at parameters ⊢
  congr 1 <;> simp_all [mapCollectionAlgebra, Option.map_map, Function.comp_def]

/-- The actual declaration action induces a structural map of finite generated
signatures. Duplicate-free images are required explicitly: arbitrary structural
maps need not be injective on constructor declarations. -/
def generatedStructural (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut)
    (sourceUnique : profile.constructorClosure.Nodup)
    (imageUnique : (profile.map morphism).constructorClosure.Nodup) :
    StructuralMorphism (profile.generatedPresentation sourceUnique)
      ((profile.map morphism).generatedPresentation imageUnique) where
  symbols := costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols
  mapsTypes declaration member := by
    dsimp only [generatedPresentation, generatedLanguage] at member ⊢
    rcases List.mem_append.mp member with base | wrapped
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp base
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨mapTypeDecl morphism.underlying.structural.structural.symbols original,
        morphism.underlying.structural.structural.mapsTypes original originalMember, ?_⟩
      exact (CIGSLT.Morphism.mapTypeDecl_costBase _ _).symm
    · obtain rfl := List.mem_singleton.mp wrapped
      apply List.mem_append_right
      simp [mapTypeDecl, TypeDecl.plain]
  mapsTerms constructor member := by
    dsimp only [generatedPresentation, generatedLanguage] at member ⊢
    rcases List.mem_append.mp member with base | wrapped
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp base
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨mapGrammarRule morphism.underlying.structural.structural.symbols original,
        morphism.underlying.structural.structural.mapsTerms original originalMember,
        (profile.map_baseConstructor morphism original).symm⟩
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp wrapped
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨morphism.underlying.structural.structural.mapConstructor original,
        List.mem_map.mpr ⟨original, originalMember, rfl⟩, ?_⟩
      exact (morphism.mapGrammarRule_costWrappedConstructor original.1).symm
  mapsEquations _ member := False.elim (List.not_mem_nil member)
  mapsRewrites _ member := False.elim (List.not_mem_nil member)

/-- Transport preserves typing in arbitrary free and binder-local contexts. -/
theorem map_hasType (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut)
    (sourceUnique : profile.constructorClosure.Nodup)
    (imageUnique : (profile.map morphism).constructorClosure.Nodup)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType profile.generatedLanguage free bound pattern type) :
    HasType (profile.map morphism).generatedLanguage
      (free.map (costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols))
      (bound.map (mapTypeExpr (costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols)))
      (mapPattern (costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols) pattern)
      (mapTypeExpr (costLanguageDefSymbolMap morphism.underlying.structural.structural.symbols) type) :=
  typed.map (profile.generatedStructural morphism sourceUnique imageUnique)

theorem map_closure_nodup (morphism : source.Morphism target)
    (profile : ContinuationDecorationProfile source.cut)
    (unique : profile.constructorClosure.Nodup)
    (injective : Function.Injective morphism.underlying.structural.structural.mapConstructor) :
    (profile.map morphism).constructorClosure.Nodup := unique.map injective

end ContinuationDecorationProfile

end Mettapedia.GSLT.LanguageDef
