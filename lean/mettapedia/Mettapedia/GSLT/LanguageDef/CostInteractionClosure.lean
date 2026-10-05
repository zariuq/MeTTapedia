import Mettapedia.GSLT.LanguageDef.CostInteraction

/-!
# Sorting and validation closure for the generic Cost interaction

The whole-redex Cost rule is admitted by the same `LanguageDef.validate`
boundary as every authored calculus.  Its sorting derivation is transported
from the selected continued interaction; the funding apparatus contributes
only ordinary constructor applications in disjoint schema namespaces.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open StructuralMorphism
open ReflectionExtension
open WellSorted
open ContinuationRetypingPlan

theorem lookupTypeContext_map_injective
    (context : List (String × TypeExpr)) (mapName : String → String)
    (mapType : String → TypeExpr → TypeExpr)
    (injective : Function.Injective mapName) (name : String) :
    lookupTypeContext
        (context.map fun entry =>
          (mapName entry.1, mapType entry.1 entry.2))
        (mapName name) =
      (lookupTypeContext context name).map (mapType name) := by
  induction context with
  | nil => simp [lookupTypeContext]
  | cons entry context inductionHypothesis =>
      rcases entry with ⟨entryName, entryType⟩
      by_cases equality : entryName = name
      · subst entryName
        simp [lookupTypeContext]
      · have mappedInequality : mapName entryName ≠ mapName name :=
          fun mappedEquality => equality (injective mappedEquality)
        simp [lookupTypeContext, equality, mappedInequality,
          inductionHypothesis]

theorem lookupTypeContext_map_outside
    (context : List (String × TypeExpr)) (mapName : String → String)
    (mapType : String → TypeExpr → TypeExpr) (sought : String)
    (outside : ∀ name, mapName name ≠ sought) :
    lookupTypeContext
        (context.map fun entry =>
          (mapName entry.1, mapType entry.1 entry.2)) sought = none := by
  induction context with
  | nil => simp [lookupTypeContext]
  | cons entry context inductionHypothesis =>
      rcases entry with ⟨entryName, entryType⟩
      simp [lookupTypeContext, outside entryName, inductionHypothesis]

@[simp]
theorem lookupTypeContext_append (left right : List (String × TypeExpr))
    (name : String) :
    lookupTypeContext (left ++ right) name =
      match lookupTypeContext left name with
      | some type => some type
      | none => lookupTypeContext right name := by
  induction left with
  | nil => simp [lookupTypeContext]
  | cons entry left inductionHypothesis =>
      rcases entry with ⟨entryName, entryType⟩
      by_cases equality : entryName = name <;>
        simp [lookupTypeContext, equality, inductionHypothesis]

/-- Every rewrite selected from a validated language passes the exact
per-rewrite component of that validation. -/
theorem validateRewrite_eq_nil_of_validate_eq_nil
    (language : LanguageDef) (valid : language.validate = [])
    (rewrite : RewriteRule) (membership : rewrite ∈ language.rewrites) :
    language.validateRewrite rewrite = [] := by
  have rewriteErrors :
      language.rewrites.flatMap (language.validateRewrite ·) = [] := by
    unfold LanguageDef.validate at valid
    simp only [List.append_eq_nil_iff] at valid
    aesop
  exact (List.flatMap_eq_nil_iff.mp rewriteErrors) rewrite membership

/-- The wildcard/scope component is a necessary part of per-rewrite
validation. -/
theorem validateRulePatterns_eq_nil_of_validateRewrite_eq_nil
    (language : LanguageDef) (rewrite : RewriteRule)
    (clean : language.validateRewrite rewrite = []) :
    LanguageDef.validateRulePatterns s!"rewrite {rewrite.name}"
      (language.terms.map (·.label)) rewrite.typeContext rewrite.premises
      rewrite.left rewrite.right = [] := by
  unfold LanguageDef.validateRewrite at clean
  simp only [List.append_eq_nil_iff] at clean
  aesop

/-- Every type-context entry of an accepted rewrite mentions only declared
sorts of the same authored language. -/
theorem rewriteTypeContext_baseName_mem_of_validate_eq_nil
    (language : LanguageDef) (valid : language.validate = [])
    (rewrite : RewriteRule) (rewriteMembership : rewrite ∈ language.rewrites)
    (entry : String × TypeExpr) (entryMembership : entry ∈ rewrite.typeContext)
    (name : String) (nameMembership : name ∈ entry.2.baseNames) :
    name ∈ language.typeNames := by
  have rewriteClean := validateRewrite_eq_nil_of_validate_eq_nil
    language valid rewrite rewriteMembership
  unfold LanguageDef.validateRewrite at rewriteClean
  simp only [List.append_eq_nil_iff] at rewriteClean
  apply LanguageDef.baseName_mem_of_validateTypeExpr_eq_nil
    language.typeNames s!"rewrite {rewrite.name}" entry.2 ?_ nameMembership
  aesop

/-- A premise-free rule passes the generic wildcard/scope validator once its
five independent obligations are discharged.  Keeping this decomposition
explicit lets generated languages prove hygiene from their construction
rather than by evaluation of an opaque validator. -/
theorem validateRulePatterns_noPremises_eq_nil
    (context : String) (knownConstructors : List String)
    (typeContext : List (String × TypeExpr)) (left right : Pattern)
    (leftScoped : left.isWellScoped = true)
    (rightScoped : right.isWellScoped = true)
    (fvarsAvoidConstructors :
      ∀ name ∈
        ((LanguageDef.patternFvarNames [] left ++
          LanguageDef.patternFvarNames [] right).eraseDups),
        name ∉ knownConstructors)
    (bindersAvoidConstructors :
      ∀ name ∈
        ((LanguageDef.patternBinderNames left ++
          LanguageDef.patternBinderNames right).eraseDups),
        name ∉ knownConstructors)
    (contextAvoidsConstructors :
      ∀ entry ∈ typeContext,
        entry.1 ∉ knownConstructors)
    (rightBoundByLeft :
      ∀ name ∈ (LanguageDef.patternFvarNames [] right).eraseDups,
        name ∈ LanguageDef.patternFvarNames [] left) :
    LanguageDef.validateRulePatterns context knownConstructors typeContext []
      left right = [] := by
  unfold LanguageDef.validateRulePatterns
  simp only [List.flatMap_nil, List.append_nil,
    List.all_nil, Bool.and_true, leftScoped, rightScoped, if_true,
    List.nil_append, List.append_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [fvarsAvoidConstructors name membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [bindersAvoidConstructors name membership]
  · apply List.filterMap_eq_nil_iff.mpr
    intro entry membership
    rcases entry with ⟨name, type⟩
    simp [contextAvoidsConstructors (name, type) membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [rightBoundByLeft name membership]

@[simp]
theorem patternFvarNames_nil (pattern : Pattern) :
    LanguageDef.patternFvarNames [] pattern = pattern.freeFvarNames := by
  simp [LanguageDef.patternFvarNames]

/-- In a validated premise-free schema, every right-hand metavariable is
already supplied by the left.  The constructor-name escape hatch in the
dangling check cannot apply because the same validator independently rejects
constructor/metavariable collisions. -/
theorem rightFvar_mem_left_of_validateRulePatterns_noPremises_eq_nil
    (context : String) (knownConstructors : List String)
    (typeContext : List (String × TypeExpr)) (left right : Pattern)
    (clean : LanguageDef.validateRulePatterns context knownConstructors
      typeContext [] left right = [])
    (name : String)
    (rightMembership :
      name ∈ LanguageDef.patternFvarNames [] right) :
    name ∈ LanguageDef.patternFvarNames [] left := by
  have rightEraseMembership :
      name ∈ (LanguageDef.patternFvarNames [] right).eraseDups := by
    simpa using rightMembership
  have bothEraseMembership :
      name ∈
        ((LanguageDef.patternFvarNames [] left ++
          LanguageDef.patternFvarNames [] right).eraseDups) := by
    simpa using (show name ∈
      LanguageDef.patternFvarNames [] left ++
        LanguageDef.patternFvarNames [] right from
          List.mem_append.mpr (Or.inr rightMembership))
  unfold LanguageDef.validateRulePatterns at clean
  simp only [List.flatMap_nil, List.append_nil,
    List.append_eq_nil_iff] at clean
  rcases clean with
    ⟨⟨⟨⟨_scopeClean, labelCollisionsClean⟩, _binderCollisionsClean⟩,
      _contextCollisionsClean⟩, danglingClean⟩
  have labelComponent :=
    (List.flatMap_eq_nil_iff.mp labelCollisionsClean)
      name bothEraseMembership
  have notConstructor : name ∉ knownConstructors := by
    intro constructorMembership
    simp [constructorMembership] at labelComponent
  have danglingComponent :=
    (List.flatMap_eq_nil_iff.mp danglingClean) name rightEraseMembership
  by_contra missingLeft
  simp [notConstructor] at danglingComponent
  exact missingLeft (by simpa using danglingComponent)

/-- In a validated premise-free rewrite, every right-hand metavariable is
supplied by its authored redex. -/
theorem rightFvar_mem_left_of_validatedRewrite_noPremises
    (language : LanguageDef) (valid : language.validate = [])
    (rewrite : RewriteRule) (membership : rewrite ∈ language.rewrites)
    (premisesEmpty : rewrite.premises = []) (name : String)
    (rightMembership : name ∈ LanguageDef.patternFvarNames [] rewrite.right) :
    name ∈ LanguageDef.patternFvarNames [] rewrite.left := by
  have rewriteClean := validateRewrite_eq_nil_of_validate_eq_nil
    language valid rewrite membership
  have patternClean := validateRulePatterns_eq_nil_of_validateRewrite_eq_nil
    language rewrite rewriteClean
  rw [premisesEmpty] at patternClean
  exact rightFvar_mem_left_of_validateRulePatterns_noPremises_eq_nil
    s!"rewrite {rewrite.name}" (language.terms.map (·.label))
    rewrite.typeContext rewrite.left rewrite.right patternClean name rightMembership

/-- Variable coverage of the selected contraction follows from source
validation before any generated Cost language is constructed. -/
theorem InteractionCutPresentation.rightFvar_mem_left {theory : IGSLT}
    (cut : InteractionCutPresentation theory) (name : String)
    (membership : name ∈ theory.presentation.interactionRewrite.1.right.freeFvarNames) :
    name ∈ theory.presentation.interactionRewrite.1.left.freeFvarNames := by
  simpa only [patternFvarNames_nil] using
    rightFvar_mem_left_of_validatedRewrite_noPremises
      theory.presentation.presentation.language theory.presentation.presentation.valid
      theory.presentation.interactionRewrite.1 cut.interactionRewrite_mem
      cut.interactionPremisesEmpty name
      (by simpa only [patternFvarNames_nil] using membership)

/-- In a validated premise-free equation, every right-hand metavariable is
supplied by the left-hand pattern. -/
theorem rightFvar_mem_left_of_validatedEquation_noPremises
    (language : LanguageDef) (valid : language.validate = [])
    (equation : Equation) (membership : equation ∈ language.equations)
    (premisesEmpty : equation.premises = []) (name : String)
    (rightMembership :
      name ∈ LanguageDef.patternFvarNames [] equation.right) :
    name ∈ LanguageDef.patternFvarNames [] equation.left := by
  have equationClean := validateEquation_eq_nil_of_validate_eq_nil
    language valid equation membership
  unfold LanguageDef.validateEquation at equationClean
  simp only [List.append_eq_nil_iff] at equationClean
  have patternsClean :
      LanguageDef.validateRulePatterns s!"equation {equation.name}"
        (language.terms.map (·.label)) equation.typeContext
        equation.premises equation.left equation.right = [] := by
    aesop
  rw [premisesEmpty] at patternsClean
  exact rightFvar_mem_left_of_validateRulePatterns_noPremises_eq_nil
    s!"equation {equation.name}" (language.terms.map (·.label))
    equation.typeContext equation.left equation.right patternsClean
    name rightMembership

namespace StructuralMorphism

/-- Structural presentation maps preserve rule-local metavariable names. -/
@[simp]
theorem mapPattern_freeFvarNames (symbols : LanguageDefSymbolMap)
    (pattern : Pattern) :
    (mapPattern symbols pattern).freeFvarNames = pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        Pattern.freeFvarNames, List.flatMap_map]
      exact List.flatMap_congr inductionHypothesis
  | hlambda => simp_all [mapPattern, Pattern.freeFvarNames]
  | hmultiLambda => simp_all [mapPattern, Pattern.freeFvarNames]
  | hsubst => simp_all [mapPattern, Pattern.freeFvarNames]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        Pattern.freeFvarNames, List.flatMap_map]
      rw [List.flatMap_congr inductionHypothesis]

/-- Structural presentation maps preserve binder metadata. -/
@[simp]
theorem mapPattern_patternBinderNames (symbols : LanguageDefSymbolMap)
    (pattern : Pattern) :
    LanguageDef.patternBinderNames (mapPattern symbols pattern) =
      LanguageDef.patternBinderNames pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        LanguageDef.patternBinderNames]
      rw [Mettapedia.GSLT.LanguageDef.attach_flatMap_value,
        Mettapedia.GSLT.LanguageDef.attach_flatMap_value, List.flatMap_map]
      exact List.flatMap_congr inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      cases binder <;>
        simp only [mapPattern, LanguageDef.patternBinderNames.eq_4,
          LanguageDef.patternBinderNames.eq_5, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      rw [mapPattern, LanguageDef.patternBinderNames.eq_6,
        LanguageDef.patternBinderNames.eq_6, inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      rw [mapPattern, LanguageDef.patternBinderNames.eq_7,
        LanguageDef.patternBinderNames.eq_7,
        bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      rw [mapPattern, mapPatternList_eq_map,
        LanguageDef.patternBinderNames.eq_8,
        LanguageDef.patternBinderNames.eq_8]
      rw [Mettapedia.GSLT.LanguageDef.attach_flatMap_value,
        Mettapedia.GSLT.LanguageDef.attach_flatMap_value, List.flatMap_map]
      exact List.flatMap_congr inductionHypothesis

end StructuralMorphism

namespace ContinuationRetypingPlan

/-- Contractum retyping changes constructor and sort copies, never the
authored rule's metavariable names. -/
@[simp]
theorem mapContractum_freeFvarNames
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (pattern : Pattern) :
    (plan.mapContractum pattern).freeFvarNames = pattern.freeFvarNames :=
  StructuralMorphism.mapPattern_freeFvarNames _ pattern

/-- Contractum retyping also preserves binder metadata exactly. -/
@[simp]
theorem mapContractum_patternBinderNames
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (pattern : Pattern) :
    LanguageDef.patternBinderNames (plan.mapContractum pattern) =
      LanguageDef.patternBinderNames pattern :=
  StructuralMorphism.mapPattern_patternBinderNames _ pattern

end ContinuationRetypingPlan

namespace WellSorted

/-- A constructor reference resolves to one authored declaration with the
recorded arity.  Uniqueness is supplied separately by language validation. -/
def ConstructorReferenceDeclared (language : LanguageDef)
    (reference : String × Nat) : Prop :=
  ∃ rule ∈ language.terms,
    rule.label = reference.1 ∧ rule.params.length = reference.2

mutual
  theorem HasType.constructorReferencesDeclared
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      ∀ reference ∈ pattern.constructorRefs,
        ConstructorReferenceDeclared language reference := by
    cases typed with
    | @bvar bound index type lookup =>
        simp [Pattern.constructorRefs]
    | @fvar bound name type lookup =>
        simp [Pattern.constructorRefs]
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        intro reference referenceMembership
        simp only [Pattern.constructorRefs] at referenceMembership
        split at referenceMembership
        next =>
          exact (ArgumentsHaveTypes.constructorReferencesListDeclared
            argumentsTyped).2 reference referenceMembership
        next =>
          exact (ArgumentsHaveTypes.constructorReferencesListDeclared
            argumentsTyped).2 reference referenceMembership
        next =>
          exact (ArgumentsHaveTypes.constructorReferencesListDeclared
            argumentsTyped).2 reference referenceMembership
        next =>
          simp only [List.mem_cons] at referenceMembership
          rcases referenceMembership with root | nested
          · subst reference
            exact ⟨rule, membership, rfl,
              (ArgumentsHaveTypes.constructorReferencesListDeclared
                argumentsTyped).1.symm⟩
          · exact (ArgumentsHaveTypes.constructorReferencesListDeclared
              argumentsTyped).2 reference nested
    | @lambda bound binder body domain codomain bodyTyped =>
        simpa [Pattern.constructorRefs] using fun reference membership =>
          HasType.constructorReferencesDeclared bodyTyped reference membership
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        simpa [Pattern.constructorRefs] using fun reference membership =>
          HasType.constructorReferencesDeclared bodyTyped reference membership
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        intro reference referenceMembership
        simp only [Pattern.constructorRefs, List.mem_append] at referenceMembership
        rcases referenceMembership with bodyMembership | replacementMembership
        · exact HasType.constructorReferencesDeclared
            bodyTyped reference bodyMembership
        · exact HasType.constructorReferencesDeclared
            replacementTyped reference replacementMembership
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simpa [Pattern.constructorRefs] using fun reference membership =>
          ElementsHaveType.constructorReferencesListDeclared
            elementsTyped reference membership
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simpa [Pattern.constructorRefs] using fun reference membership =>
          ElementsHaveType.constructorReferencesListDeclared
            elementsTyped reference membership

  theorem ArgumentsHaveTypes.constructorReferencesListDeclared
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      arguments.length = parameters.length ∧
        ∀ reference ∈ Pattern.constructorRefsList arguments,
          ConstructorReferenceDeclared language reference := by
    cases typed with
    | nil =>
        exact ⟨rfl, by simp [Pattern.constructorRefsList]⟩
    | cons representation parameterType argumentTyped argumentsTyped =>
        have tailEvidence :=
          ArgumentsHaveTypes.constructorReferencesListDeclared argumentsTyped
        constructor
        · simp [tailEvidence.1]
        · intro reference referenceMembership
          simp only [Pattern.constructorRefsList, List.mem_append]
            at referenceMembership
          rcases referenceMembership with
            argumentMembership | argumentsMembership
          · exact HasType.constructorReferencesDeclared
              argumentTyped reference argumentMembership
          · exact tailEvidence.2 reference argumentsMembership

  theorem ElementsHaveType.constructorReferencesListDeclared
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType) :
      ∀ reference ∈ Pattern.constructorRefsList elements,
        ConstructorReferenceDeclared language reference := by
    cases typed with
    | nil => simp [Pattern.constructorRefsList]
    | cons elementTyped elementsTyped =>
        intro reference referenceMembership
        simp only [Pattern.constructorRefsList, List.mem_append]
          at referenceMembership
        rcases referenceMembership with elementMembership | elementsMembership
        · exact HasType.constructorReferencesDeclared
            elementTyped reference elementMembership
        · exact ElementsHaveType.constructorReferencesListDeclared
            elementsTyped reference elementsMembership
end

private theorem filter_constructor_label_eq_nil_of_not_mem
    (constructors : List GrammarRule) (label : String)
    (absent : label ∉ constructors.map (·.label)) :
    constructors.filter (fun declaration => declaration.label == label) = [] := by
  induction constructors with
  | nil => rfl
  | cons constructor constructors inductionHypothesis =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      have headInequality : constructor.label ≠ label :=
        fun equality => absent.1 equality.symm
      simp [headInequality, inductionHypothesis absent.2]

private theorem filter_constructor_label_eq_singleton
    (constructors : List GrammarRule)
    (labelsNodup : (constructors.map (·.label)).Nodup)
    (rule : GrammarRule) (membership : rule ∈ constructors) :
    constructors.filter (fun declaration => declaration.label == rule.label) =
      [rule] := by
  induction constructors with
  | nil => simp at membership
  | cons constructor constructors inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at labelsNodup
      rcases labelsNodup with ⟨headAbsent, tailNodup⟩
      simp only [List.mem_cons] at membership
      rcases membership with equality | tailMembership
      · subst constructor
        simp [filter_constructor_label_eq_nil_of_not_mem
          constructors rule.label headAbsent]
      · have headInequality : constructor.label ≠ rule.label := by
          intro labelEquality
          exact headAbsent (List.mem_map.mpr
            ⟨rule, tailMembership, labelEquality.symm⟩)
        simp [headInequality,
          inductionHypothesis tailNodup tailMembership]

/-- A typed pattern passes constructor-reference validation in any language
whose constructor labels are unique. -/
theorem HasType.validatePatternConstructors_eq_nil
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    (labelsNodup : (language.terms.map (·.label)).Nodup)
    (context : String) :
    LanguageDef.validatePatternConstructors context language.terms pattern =
      [] := by
  unfold LanguageDef.validatePatternConstructors
  apply List.flatMap_eq_nil_iff.mpr
  intro reference referenceMembership
  rcases typed.constructorReferencesDeclared reference referenceMembership with
    ⟨rule, ruleMembership, labelEquality, arityEquality⟩
  rcases reference with ⟨label, arity⟩
  simp only at labelEquality arityEquality
  subst label
  dsimp only
  rw [filter_constructor_label_eq_singleton language.terms labelsNodup
    rule ruleMembership]
  simp [arityEquality]

end WellSorted

namespace SchemaSidesWellSorted

/-- A sorted schema remains sorted after extending the constructor signature
and applying one injective renaming to all schema-local names. -/
theorem mapSchemaNames_weakenTerms
    {sourceLanguage targetLanguage : LanguageDef}
    (includes : ∀ rule, rule ∈ sourceLanguage.terms →
      rule ∈ targetLanguage.terms)
    (mapName : String → String) (injective : Function.Injective mapName)
    {typeContext : List (String × TypeExpr)} {left right : Pattern}
    (sorted : SchemaSidesWellSorted sourceLanguage typeContext left right) :
    SchemaSidesWellSorted targetLanguage
      (mapTypeContextSchemaNames mapName typeContext)
      (mapPatternSchemaNames mapName left)
      (mapPatternSchemaNames mapName right) := by
  rcases sorted with ⟨type, leftTyped, rightTyped⟩
  refine ⟨type, ?_, ?_⟩
  · apply (leftTyped.weakenTerms includes).mapSchemaNames mapName
    intro name nameType lookup
    rw [FreeTypeContext.ofList_mapTypeContextSchemaNames mapName injective]
    exact lookup
  · apply (rightTyped.weakenTerms includes).mapSchemaNames mapName
    intro name nameType lookup
    rw [FreeTypeContext.ofList_mapTypeContextSchemaNames mapName injective]
    exact lookup

end SchemaSidesWellSorted

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Free-variable assignment induced by the generated rule's exact declared
type context. -/
def costWholeRedexFreeContext (profile : ContinuationDecorationProfile cut) :
    FreeTypeContext :=
  lookupTypeContext profile.costWholeRedexTypeContext

/-- The complete Cost language adds the static equations and exactly the
funded whole-redex rule to the validated Cost signature. -/
def costWholeLanguage (profile : ContinuationDecorationProfile cut) : LanguageDef :=
  { profile.costCoreLanguage with
    name := "$cost:interaction:" ++ theory.presentation.presentation.language.name
    equations := profile.costStaticEquations
    rewrites := [profile.costWholeRedexRewrite] }

/-- The reflective interpretation generated for the Cost language from a
reflection profile of the source.  It is an extension over the five-field
core, never a field of that core. -/
def costWholeReflectionProfile (profile : ContinuationDecorationProfile cut)
    (reflection : ReflectionProfile) : ReflectionProfile :=
  { presentations := profile.costStaticReflectivePresentations reflection
    rules := profile.costInteractionReflectiveRules reflection }

end ContinuationDecorationProfile

namespace WrappableIGSLT

open ContinuationDecorationProfile (ofRetypingPlan)

/-- The complete generic Cost language adds exactly the funded whole-redex
rule to the already validated Cost signature. -/
def costWholeLanguage (source : WrappableIGSLT) : LanguageDef :=
  (ofRetypingPlan source.continuationRetyping).costWholeLanguage

theorem costWholeLanguage_def (source : WrappableIGSLT) :
    source.costWholeLanguage =
      { source.costCoreLanguage with
        name := "$cost:interaction:" ++
          source.theory.presentation.presentation.language.name
        equations := source.costStaticEquations
        rewrites := [source.costWholeRedexRewrite] } :=
  rfl

/-- The reflective interpretation generated for the Cost language.  It is an
extension over the five-field core, never a field of that core. -/
def costWholeReflectionProfile (source : WrappableIGSLT) : ReflectionProfile :=
  (ofRetypingPlan source.continuationRetyping).costWholeReflectionProfile
    source.reflection.1

theorem costWholeReflectionProfile_def (source : WrappableIGSLT) :
    source.costWholeReflectionProfile =
      { presentations := source.costStaticReflectivePresentations
        rules := source.costInteractionReflectiveRules } :=
  rfl

@[simp]
theorem costWholeLanguage_terms (source : WrappableIGSLT) :
    source.costWholeLanguage.terms = source.costCoreLanguage.terms := rfl

@[simp]
theorem costWholeLanguage_typeNames (source : WrappableIGSLT) :
    source.costWholeLanguage.typeNames = source.costCoreLanguage.typeNames := rfl

@[simp]
theorem costWholeLanguage_rewrites (source : WrappableIGSLT) :
    source.costWholeLanguage.rewrites = [source.costWholeRedexRewrite] := rfl

@[simp]
theorem costWholeLanguage_equations (source : WrappableIGSLT) :
    source.costWholeLanguage.equations = source.costStaticEquations := rfl

@[simp]
theorem costWholeReflectionProfile_presentations (source : WrappableIGSLT) :
    source.costWholeReflectionProfile.presentations =
      source.costStaticReflectivePresentations := rfl

@[simp]
theorem costWholeReflectionProfile_rules (source : WrappableIGSLT) :
    source.costWholeReflectionProfile.rules =
      source.costInteractionReflectiveRules := rfl

/-- Every authored constructor has its declaration-derived base copy in the
complete Cost language. -/
theorem costBaseConstructor_mem_costWhole (source : WrappableIGSLT)
    (constructor : GrammarRule)
    (membership : constructor ∈
      source.theory.presentation.presentation.language.terms) :
    costBaseConstructor source.cut constructor ∈
      source.costWholeLanguage.terms :=
  List.mem_append_left _
    (source.continuationRetyping.costBaseConstructor_mem_generated
      constructor membership)

/-- Every constructor in the cut-derived non-principal fragment has its
uniform wrapped copy in the complete Cost language. -/
theorem costWrappedConstructor_mem_costWhole (source : WrappableIGSLT)
    (constructor : DeclaredConstructor
      source.theory.presentation.presentation)
    (membership : constructor ∈
      source.continuationRetyping.wrappedConstructors) :
    costWrappedConstructor (theory := source.theory) constructor.1 ∈
      source.costWholeLanguage.terms :=
  List.mem_append_left _
    (source.continuationRetyping.costWrappedConstructor_mem_generated
      constructor membership)

/-- The final collision-free base equation image is sorted in the complete
Cost signature. -/
theorem costBaseEquationDecl_wellSorted (source : WrappableIGSLT)
    (equation : Equation)
    (membership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    EquationWellSorted source.costWholeLanguage
      (costBaseEquationDecl equation) := by
  have raw :=
    (source.equationsRetypable equation membership).baseWellSorted
  exact raw.mapSchemaNames_weakenTerms
    (fun _ membership => List.mem_append_left _ membership) costSourceSchemaName
      costSourceSchemaName_injective

/-- The final collision-free wrapped equation image is sorted in the complete
Cost signature. -/
theorem costWrappedEquationDecl_wellSorted (source : WrappableIGSLT)
    (equation : Equation)
    (membership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    EquationWellSorted source.costWholeLanguage
      (costWrappedEquationDecl source.theory equation) := by
  have raw :=
    (source.equationsRetypable equation membership).wrappedWellSorted
  exact raw.mapSchemaNames_weakenTerms
    (fun _ membership => List.mem_append_left _ membership) costSourceSchemaName
      costSourceSchemaName_injective

theorem costSourceSchemaName_ne_costPrefix (name suffix : String) :
    costSourceSchemaName name ≠ "$cost:" ++ suffix := by
  intro equality
  have characters := congrArg String.toList equality
  simp [costSourceSchemaName, costSourceSchemaTag] at characters

theorem costAdministrativeSchemaName_ne_costPrefix (name suffix : String) :
    costAdministrativeSchemaName name ≠ "$cost:" ++ suffix := by
  intro equality
  have characters := congrArg String.toList equality
  simp [costAdministrativeSchemaName, costAdministrativeSchemaTag]
    at characters

/-- Free-variable assignment induced by the generated rule's exact declared
type context. -/
def costWholeRedexFreeContext (source : WrappableIGSLT) : FreeTypeContext :=
  (ofRetypingPlan source.continuationRetyping).costWholeRedexFreeContext

theorem costWholeRedexFreeContext_def (source : WrappableIGSLT) :
    source.costWholeRedexFreeContext =
      lookupTypeContext source.costWholeRedexTypeContext :=
  rfl

theorem costBaseSortName_mem_costWhole (source : WrappableIGSLT) (name : String)
    (membership : name ∈
      source.theory.presentation.presentation.language.typeNames) :
    costBaseSortName name ∈ source.costWholeLanguage.typeNames := by
  rw [costWholeLanguage_typeNames, costCoreLanguage_typeNames,
    generatedLanguage_typeNames]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨name, membership, rfl⟩))

theorem costWrappedSortName_mem_costWhole (source : WrappableIGSLT) :
    costWrappedSortName ∈ source.costWholeLanguage.typeNames := by
  rw [costWholeLanguage_typeNames, costCoreLanguage_typeNames,
    generatedLanguage_typeNames]
  exact List.mem_append_left _ (List.mem_append_right _ (by simp))

end WrappableIGSLT

namespace ContinuationDecorationProfile

/-- The profile of a continued theory has that theory's whole language. -/
theorem ofRetypingPlan_costWholeLanguage (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeLanguage =
      source.costWholeLanguage :=
  rfl

/-- The profile of a continued theory has that theory's funded rule. -/
theorem ofRetypingPlan_costWholeRedexRewrite (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeRedexRewrite =
      source.costWholeRedexRewrite :=
  rfl

end ContinuationDecorationProfile

end Mettapedia.GSLT.LanguageDef
