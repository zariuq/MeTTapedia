import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Structural maps of flat calculus language definitions

`CalculusLanguageDef` is one flat language object.  Its structural maps carry
all of that object together: ordinary sorts and operational declarations,
judgment forms, inference rules, and the optional conversion root.

The outer head of a judgment is a different namespace from the constructors
inside its arguments.  `CalculusLanguageSymbols` records that distinction,
and `mapJudgmentPattern` applies it structurally.  This makes the category a
usable codomain for syntax-generating operations: transporting only the five
ordinary `LanguageDef` rows is not enough to transport a generated type
theory.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Symbol actions for every namespace of a flat calculus language. -/
@[ext]
structure CalculusLanguageSymbols extends LanguageDefSymbolMap where
  /-- Outer heads of judgments. -/
  judgment : String → String
  /-- Stable identifiers of inference rules. -/
  rule : String → String

namespace CalculusLanguageSymbols

/-- Identity action on every calculus-language namespace. -/
def id : CalculusLanguageSymbols where
  toLanguageDefSymbolMap := LanguageDefSymbolMap.id
  judgment := _root_.id
  rule := _root_.id

@[simp] theorem id_language :
    id.toLanguageDefSymbolMap = LanguageDefSymbolMap.id :=
  rfl

/-- Consecutive symbol actions. -/
def comp (first second : CalculusLanguageSymbols) :
    CalculusLanguageSymbols where
  toLanguageDefSymbolMap := first.toLanguageDefSymbolMap.comp
    second.toLanguageDefSymbolMap
  judgment := second.judgment ∘ first.judgment
  rule := second.rule ∘ first.rule

@[simp] theorem comp_language (first second : CalculusLanguageSymbols) :
    (first.comp second).toLanguageDefSymbolMap =
      first.toLanguageDefSymbolMap.comp second.toLanguageDefSymbolMap :=
  rfl

@[simp] theorem id_comp (symbols : CalculusLanguageSymbols) :
    id.comp symbols = symbols := by
  ext name <;> rfl

@[simp] theorem comp_id (symbols : CalculusLanguageSymbols) :
    symbols.comp id = symbols := by
  ext name <;> rfl

theorem comp_assoc (first second third : CalculusLanguageSymbols) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  ext name <;> rfl

end CalculusLanguageSymbols

/-- Map a declared judgment form. -/
def mapJudgmentDecl (symbols : CalculusLanguageSymbols)
    (declaration : JudgmentDecl) : JudgmentDecl :=
  { head := symbols.judgment declaration.head
    arity := declaration.arity }

/-- Map one judgment expression.  Its outer head belongs to the judgment
namespace; constructor occurrences in its arguments belong to the ordinary
language namespace.  Ill-shaped non-application inputs are still mapped
structurally, so this operation is total before validation. -/
def mapJudgmentPattern (symbols : CalculusLanguageSymbols) : Pattern → Pattern
  | .apply head arguments =>
      .apply (symbols.judgment head)
        (arguments.map (mapPattern symbols.toLanguageDefSymbolMap))
  | pattern => mapPattern symbols.toLanguageDefSymbolMap pattern

/-- Map an inference-rule schema without changing its local metavariable or
side-condition coordinates. -/
def mapRuleSchema (symbols : CalculusLanguageSymbols)
    (rule : RuleSchema) : RuleSchema :=
  { id := ⟨symbols.rule rule.id.value⟩
    metavariables := rule.metavariables
    premises := rule.premises.map (mapJudgmentPattern symbols)
    conclusion := mapJudgmentPattern symbols rule.conclusion
    sideConditions := rule.sideConditions }

/-- Map the rooted conversion judgment while preserving its protocol
version.  A version change is a semantic revision, not a symbol renaming. -/
def mapConversionDecl (symbols : CalculusLanguageSymbols)
    (declaration : ConversionDecl) : ConversionDecl :=
  { judgmentHead := symbols.judgment declaration.judgmentHead
    version := declaration.version }

@[simp] theorem mapJudgmentDecl_id (declaration : JudgmentDecl) :
    mapJudgmentDecl CalculusLanguageSymbols.id declaration = declaration := by
  cases declaration
  rfl

theorem mapJudgmentDecl_comp (first second : CalculusLanguageSymbols)
    (declaration : JudgmentDecl) :
    mapJudgmentDecl (first.comp second) declaration =
      mapJudgmentDecl second (mapJudgmentDecl first declaration) := by
  cases declaration
  rfl

@[simp] theorem mapJudgmentPattern_id (judgment : Pattern) :
    mapJudgmentPattern CalculusLanguageSymbols.id judgment = judgment := by
  cases judgment <;>
    simp [mapJudgmentPattern, CalculusLanguageSymbols.id, mapPattern_id]

theorem mapJudgmentPattern_comp (first second : CalculusLanguageSymbols)
    (judgment : Pattern) :
    mapJudgmentPattern (first.comp second) judgment =
      mapJudgmentPattern second (mapJudgmentPattern first judgment) := by
  cases judgment <;>
    simp [mapJudgmentPattern, CalculusLanguageSymbols.comp, mapPattern,
      mapPattern_comp, List.map_map, Function.comp_def]

@[simp] theorem mapRuleSchema_id (rule : RuleSchema) :
    mapRuleSchema CalculusLanguageSymbols.id rule = rule := by
  cases rule with
  | mk ruleId metavariables premises conclusion sideConditions =>
      simp only [mapRuleSchema, RuleSchema.mk.injEq,
        CalculusLanguageSymbols.id, true_and, and_true]
      constructor
      · rfl
      · constructor
        · calc
            List.map (mapJudgmentPattern CalculusLanguageSymbols.id) premises =
                List.map _root_.id premises := by
              apply List.map_congr_left
              intro judgment _
              exact mapJudgmentPattern_id judgment
            _ = premises := by simp
        · exact mapJudgmentPattern_id conclusion

theorem mapRuleSchema_comp (first second : CalculusLanguageSymbols)
    (rule : RuleSchema) :
    mapRuleSchema (first.comp second) rule =
      mapRuleSchema second (mapRuleSchema first rule) := by
  cases rule with
  | mk ruleId metavariables premises conclusion sideConditions =>
      simp only [mapRuleSchema, RuleSchema.mk.injEq,
        CalculusLanguageSymbols.comp,
        Function.comp_apply, List.map_map, true_and, and_true]
      constructor
      · apply List.map_congr_left
        intro judgment _
        exact mapJudgmentPattern_comp first second judgment
      · exact mapJudgmentPattern_comp first second conclusion

@[simp] theorem mapConversionDecl_id (declaration : ConversionDecl) :
    mapConversionDecl CalculusLanguageSymbols.id declaration = declaration := by
  cases declaration
  rfl

theorem mapConversionDecl_comp (first second : CalculusLanguageSymbols)
    (declaration : ConversionDecl) :
    mapConversionDecl (first.comp second) declaration =
      mapConversionDecl second (mapConversionDecl first declaration) := by
  cases declaration
  rfl

namespace ValidatedCalculusLanguageDef

/-- Forget only the inference rows of a validated flat calculus language.
The ordinary language remains validated because its validation is a conjunct
of calculus-language admission. -/
def toValidatedLanguageDef (definition : ValidatedCalculusLanguageDef) :
    ValidatedLanguageDef :=
  ⟨definition.1.toLanguageDef, by
    have valid := definition.2
    unfold CalculusLanguageDef.isValid at valid
    simp only [Bool.and_eq_true] at valid
    have localValid := valid.1.1.1
    unfold CalculusLanguageDef.hasValidLocalRules at localValid
    simp only [Bool.and_eq_true] at localValid
    simpa using localValid.1.1⟩

@[simp] theorem toValidatedLanguageDef_language
    (definition : ValidatedCalculusLanguageDef) :
    definition.toValidatedLanguageDef.language =
      definition.1.toLanguageDef :=
  rfl

end ValidatedCalculusLanguageDef

/-- A structural map of complete flat calculus languages.  The target may
contain additional declarations, but every mapped source row must occur
there. -/
structure CalculusStructuralMorphism
    (source target : ValidatedCalculusLanguageDef) where
  symbols : CalculusLanguageSymbols
  mapsTypes : ∀ declaration,
    List.Mem declaration source.1.types →
      List.Mem (mapTypeDecl symbols.toLanguageDefSymbolMap declaration)
        target.1.types
  mapsTerms : ∀ declaration,
    List.Mem declaration source.1.terms →
      List.Mem (mapGrammarRule symbols.toLanguageDefSymbolMap declaration)
        target.1.terms
  mapsEquations : ∀ declaration,
    List.Mem declaration source.1.equations →
      List.Mem (mapEquation symbols.toLanguageDefSymbolMap declaration)
        target.1.equations
  mapsRewrites : ∀ declaration,
    List.Mem declaration source.1.rewrites →
      List.Mem (mapRewriteRule symbols.toLanguageDefSymbolMap declaration)
        target.1.rewrites
  mapsJudgments : ∀ declaration,
    List.Mem declaration source.1.judgments →
      List.Mem (mapJudgmentDecl symbols declaration) target.1.judgments
  mapsRules : ∀ declaration,
    List.Mem declaration source.1.rules →
      List.Mem (mapRuleSchema symbols declaration) target.1.rules
  mapsConversion : ∀ declaration,
    source.1.conversion = some declaration →
      target.1.conversion = some (mapConversionDecl symbols declaration)

namespace CalculusStructuralMorphism

/-- Forget inference declarations and retain the structural map of the
ordinary language rows. -/
def toLanguageDefMorphism
    {source target : ValidatedCalculusLanguageDef}
    (morphism : CalculusStructuralMorphism source target) :
    StructuralMorphism source.toValidatedLanguageDef
      target.toValidatedLanguageDef where
  symbols := morphism.symbols.toLanguageDefSymbolMap
  mapsTypes := morphism.mapsTypes
  mapsTerms := morphism.mapsTerms
  mapsEquations := morphism.mapsEquations
  mapsRewrites := morphism.mapsRewrites

/-- Calculus-language structural maps contain no proof-relevant hidden
choice: their action on symbol namespaces determines them. -/
@[ext]
theorem ext {source target : ValidatedCalculusLanguageDef}
    {first second : CalculusStructuralMorphism source target}
    (symbols : first.symbols = second.symbols) : first = second := by
  cases first
  cases second
  cases symbols
  rfl

/-- Identity structural map. -/
def id (definition : ValidatedCalculusLanguageDef) :
    CalculusStructuralMorphism definition definition where
  symbols := CalculusLanguageSymbols.id
  mapsTypes declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapTypeDecl_id]
    exact membership
  mapsTerms declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapGrammarRule_id]
    exact membership
  mapsEquations declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapEquation_id]
    exact membership
  mapsRewrites declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapRewriteRule_id]
    exact membership
  mapsJudgments declaration membership := by
    simpa using membership
  mapsRules declaration membership := by
    simpa using membership
  mapsConversion declaration equality := by
    simpa using equality

/-- Composition of structural calculus-language maps. -/
def comp {first second third : ValidatedCalculusLanguageDef}
    (earlier : CalculusStructuralMorphism first second)
    (later : CalculusStructuralMorphism second third) :
    CalculusStructuralMorphism first third where
  symbols := earlier.symbols.comp later.symbols
  mapsTypes declaration membership := by
    change List.Mem
      (mapTypeDecl
        (earlier.symbols.toLanguageDefSymbolMap.comp
          later.symbols.toLanguageDefSymbolMap) declaration) third.1.types
    rw [mapTypeDecl_comp]
    exact later.mapsTypes _ (earlier.mapsTypes declaration membership)
  mapsTerms declaration membership := by
    change List.Mem
      (mapGrammarRule
        (earlier.symbols.toLanguageDefSymbolMap.comp
          later.symbols.toLanguageDefSymbolMap) declaration) third.1.terms
    rw [mapGrammarRule_comp]
    exact later.mapsTerms _ (earlier.mapsTerms declaration membership)
  mapsEquations declaration membership := by
    change List.Mem
      (mapEquation
        (earlier.symbols.toLanguageDefSymbolMap.comp
          later.symbols.toLanguageDefSymbolMap) declaration) third.1.equations
    rw [mapEquation_comp]
    exact later.mapsEquations _ (earlier.mapsEquations declaration membership)
  mapsRewrites declaration membership := by
    change List.Mem
      (mapRewriteRule
        (earlier.symbols.toLanguageDefSymbolMap.comp
          later.symbols.toLanguageDefSymbolMap) declaration) third.1.rewrites
    rw [mapRewriteRule_comp]
    exact later.mapsRewrites _ (earlier.mapsRewrites declaration membership)
  mapsJudgments declaration membership := by
    rw [mapJudgmentDecl_comp]
    exact later.mapsJudgments _ (earlier.mapsJudgments declaration membership)
  mapsRules declaration membership := by
    rw [mapRuleSchema_comp]
    exact later.mapsRules _ (earlier.mapsRules declaration membership)
  mapsConversion declaration equality := by
    have firstMapped := earlier.mapsConversion declaration equality
    have secondMapped := later.mapsConversion
      (mapConversionDecl earlier.symbols declaration) firstMapped
    simpa [mapConversionDecl_comp] using secondMapped

/-- Every append-only refinement induces the canonical identity-on-symbols
structural inclusion of complete flat calculus languages. -/
def ofAppendOnly
    {source target : ValidatedCalculusLanguageDef}
    (refinement :
      CalculusLanguageExtension.AppendOnlyCalculusRefinement source.1 target.1) :
    CalculusStructuralMorphism source target where
  symbols := CalculusLanguageSymbols.id
  mapsTypes declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapTypeDecl_id]
    exact List.IsPrefix.mem membership refinement.types
  mapsTerms declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapGrammarRule_id]
    exact List.IsPrefix.mem membership refinement.terms
  mapsEquations declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapEquation_id]
    exact List.IsPrefix.mem membership refinement.equations
  mapsRewrites declaration membership := by
    rw [CalculusLanguageSymbols.id_language, mapRewriteRule_id]
    exact List.IsPrefix.mem membership refinement.rewrites
  mapsJudgments declaration membership := by
    rw [mapJudgmentDecl_id]
    exact List.IsPrefix.mem membership refinement.judgments
  mapsRules declaration membership := by
    rw [mapRuleSchema_id]
    exact List.IsPrefix.mem membership refinement.rules
  mapsConversion declaration equality := by
    rw [refinement.conversion, equality, mapConversionDecl_id]

@[simp] theorem toLanguageDefMorphism_id
    (definition : ValidatedCalculusLanguageDef) :
    (id definition).toLanguageDefMorphism =
      StructuralMorphism.id definition.toValidatedLanguageDef := by
  apply StructuralMorphism.ext
  rfl

theorem toLanguageDefMorphism_comp
    {first second third : ValidatedCalculusLanguageDef}
    (earlier : CalculusStructuralMorphism first second)
    (later : CalculusStructuralMorphism second third) :
    (comp earlier later).toLanguageDefMorphism =
      StructuralMorphism.comp earlier.toLanguageDefMorphism
        later.toLanguageDefMorphism := by
  apply StructuralMorphism.ext
  rfl

end CalculusStructuralMorphism

/-- Validated flat calculus languages and their complete structural maps form
a category. -/
instance : CategoryTheory.Category ValidatedCalculusLanguageDef where
  Hom := CalculusStructuralMorphism
  id := CalculusStructuralMorphism.id
  comp := CalculusStructuralMorphism.comp
  id_comp morphism := by
    apply CalculusStructuralMorphism.ext
    exact CalculusLanguageSymbols.id_comp morphism.symbols
  comp_id morphism := by
    apply CalculusStructuralMorphism.ext
    exact CalculusLanguageSymbols.comp_id morphism.symbols
  assoc first second third := by
    apply CalculusStructuralMorphism.ext
    exact CalculusLanguageSymbols.comp_assoc
      first.symbols second.symbols third.symbols

/-! ## Positive and negative controls -/

namespace CalculusStructuralMorphismCanary

private def judgment : JudgmentDecl :=
  { head := "calculus-structural-map:judgment", arity := 0 }

private def sourceDefinition : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "calculus-structural-map:source"
    judgments := [judgment] }

private def emptyDefinition : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "calculus-structural-map:empty" }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem source_valid : sourceDefinition.isValid = true := by
  have validate : sourceDefinition.toLanguageDef.validate = [] := by
    exact emptyLanguage_validate _
  have uniqueHead :
      ["calculus-structural-map:judgment"].eraseDups.length = 1 := by
    decide
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [sourceDefinition, judgment,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.ruleIds, uniqueHead,
    LanguageDef.empty, Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]

private theorem empty_valid : emptyDefinition.isValid = true := by
  have validate : emptyDefinition.toLanguageDef.validate = [] := by
    exact emptyLanguage_validate _
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [emptyDefinition,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.ruleIds]

private def source : ValidatedCalculusLanguageDef :=
  ⟨sourceDefinition, source_valid⟩

private def empty : ValidatedCalculusLanguageDef :=
  ⟨emptyDefinition, empty_valid⟩

/-- Every admitted flat calculus language has its full structural identity. -/
theorem identity_exists : Nonempty (source ⟶ source) :=
  ⟨CalculusStructuralMorphism.id source⟩

/-- Forgetting all judgment rows cannot be a structural calculus-language
map, even though both ordinary five-field languages are empty. -/
theorem judgment_cannot_be_erased : IsEmpty (source ⟶ empty) := by
  constructor
  intro morphism
  have sourceMembership : List.Mem judgment source.1.judgments := by
    change List.Mem judgment [judgment]
    exact List.Mem.head _
  have mapped := morphism.mapsJudgments judgment sourceMembership
  change List.Mem (mapJudgmentDecl morphism.symbols judgment) [] at mapped
  exact List.not_mem_nil mapped

end CalculusStructuralMorphismCanary

#print axioms mapJudgmentPattern_comp
#print axioms mapRuleSchema_comp
#print axioms ValidatedCalculusLanguageDef.toValidatedLanguageDef
#print axioms CalculusStructuralMorphism.comp
#print axioms CalculusStructuralMorphism.ofAppendOnly
#print axioms CalculusStructuralMorphismCanary.identity_exists
#print axioms CalculusStructuralMorphismCanary.judgment_cannot_be_erased

end Mettapedia.GSLT.LanguageDef
