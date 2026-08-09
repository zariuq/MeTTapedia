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
  simp only [List.flatMap_nil, List.append_nil, List.all_cons,
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
theorem mapPattern_freeFvarNames (symbols : PresentationSymbols)
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
theorem mapPattern_patternBinderNames (symbols : PresentationSymbols)
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

mutual
  /-- Contractum retyping changes constructor and sort copies, never the
  authored rule's metavariable names. -/
  @[simp]
  theorem mapContractum_freeFvarNames
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut) (pattern : Pattern) :
      (plan.mapContractum pattern).freeFvarNames = pattern.freeFvarNames := by
    cases pattern with
    | bvar index => simp [mapContractum, Pattern.freeFvarNames]
    | fvar name => simp [mapContractum, Pattern.freeFvarNames]
    | apply constructor arguments =>
        simpa [mapContractum, Pattern.freeFvarNames] using
          mapContractumList_freeFvarNames plan arguments
    | lambda binder body =>
        simpa [mapContractum, Pattern.freeFvarNames] using
          mapContractum_freeFvarNames plan body
    | multiLambda arity binders body =>
        simpa [mapContractum, Pattern.freeFvarNames] using
          mapContractum_freeFvarNames plan body
    | subst body replacement =>
        simp [mapContractum, Pattern.freeFvarNames,
          mapContractum_freeFvarNames plan body,
          mapContractum_freeFvarNames plan replacement]
    | collection collectionType elements rest =>
        simpa [mapContractum, Pattern.freeFvarNames] using
          mapContractumList_freeFvarNames plan elements

  @[simp]
  theorem mapContractumList_freeFvarNames
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut) (patterns : List Pattern) :
      (plan.mapContractumList patterns).flatMap Pattern.freeFvarNames =
        patterns.flatMap Pattern.freeFvarNames := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp only [mapContractumList, List.flatMap_cons,
          mapContractum_freeFvarNames plan pattern,
          mapContractumList_freeFvarNames plan patterns]
end

mutual
  /-- Contractum retyping also preserves binder metadata exactly. -/
  @[simp]
  theorem mapContractum_patternBinderNames
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut) (pattern : Pattern) :
      LanguageDef.patternBinderNames (plan.mapContractum pattern) =
        LanguageDef.patternBinderNames pattern := by
    cases pattern with
    | bvar index => simp [mapContractum, LanguageDef.patternBinderNames]
    | fvar name => simp [mapContractum, LanguageDef.patternBinderNames]
    | apply constructor arguments =>
        simpa [mapContractum, LanguageDef.patternBinderNames] using
          mapContractumList_patternBinderNames plan arguments
    | lambda binder body =>
        cases binder <;>
          simp [mapContractum, LanguageDef.patternBinderNames,
            mapContractum_patternBinderNames plan body]
    | multiLambda arity binders body =>
        simp [mapContractum, LanguageDef.patternBinderNames,
          mapContractum_patternBinderNames plan body]
    | subst body replacement =>
        simp [mapContractum, LanguageDef.patternBinderNames,
          mapContractum_patternBinderNames plan body,
          mapContractum_patternBinderNames plan replacement]
    | collection collectionType elements rest =>
        simpa [mapContractum, LanguageDef.patternBinderNames] using
          mapContractumList_patternBinderNames plan elements

  @[simp]
  theorem mapContractumList_patternBinderNames
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut) (patterns : List Pattern) :
      (plan.mapContractumList patterns).attach.flatMap
          (fun entry => LanguageDef.patternBinderNames entry.1) =
        patterns.attach.flatMap
          (fun entry => LanguageDef.patternBinderNames entry.1) := by
    rw [Mettapedia.GSLT.LanguageDef.attach_flatMap_value,
      Mettapedia.GSLT.LanguageDef.attach_flatMap_value]
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        have tailEquality :=
          mapContractumList_patternBinderNames plan patterns
        rw [Mettapedia.GSLT.LanguageDef.attach_flatMap_value,
          Mettapedia.GSLT.LanguageDef.attach_flatMap_value] at tailEquality
        simp only [mapContractumList, List.flatMap_cons,
          mapContractum_patternBinderNames plan pattern, tailEquality]
end

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

namespace CIGSLT

/-- The complete generic Cost language adds exactly the funded whole-redex
rule to the already validated Cost signature. -/
def costWholeLanguage (source : CIGSLT) : LanguageDef :=
  { source.costCoreLanguage with
    name := "$cost:interaction:" ++
      source.theory.presentation.presentation.language.name
    equations := source.costStaticEquations
    rewrites := [source.costWholeRedexRewrite] }

/-- The reflective interpretation generated for the Cost language.  It is an
extension over the five-field core, never a field of that core. -/
def costWholeReflectionProfile (source : CIGSLT) : ReflectionProfile :=
  { presentations := source.costStaticReflectivePresentations
    rules := source.costInteractionReflectiveRules }

@[simp]
theorem costWholeLanguage_terms (source : CIGSLT) :
    source.costWholeLanguage.terms = source.costCoreLanguage.terms := rfl

@[simp]
theorem costWholeLanguage_typeNames (source : CIGSLT) :
    source.costWholeLanguage.typeNames = source.costCoreLanguage.typeNames := rfl

@[simp]
theorem costWholeLanguage_rewrites (source : CIGSLT) :
    source.costWholeLanguage.rewrites = [source.costWholeRedexRewrite] := rfl

@[simp]
theorem costWholeLanguage_equations (source : CIGSLT) :
    source.costWholeLanguage.equations = source.costStaticEquations := rfl

@[simp]
theorem costWholeReflectionProfile_presentations (source : CIGSLT) :
    source.costWholeReflectionProfile.presentations =
      source.costStaticReflectivePresentations := rfl

@[simp]
theorem costWholeReflectionProfile_rules (source : CIGSLT) :
    source.costWholeReflectionProfile.rules =
      source.costInteractionReflectiveRules := rfl

private theorem generatedTerms_mem_costWhole (source : CIGSLT)
    (rule : GrammarRule)
    (membership : rule ∈ source.continuationRetyping.generatedLanguage.terms) :
    rule ∈ source.costWholeLanguage.terms := by
  change rule ∈ source.costCoreLanguage.terms
  exact List.mem_append_left _ membership

private theorem generatedTypeNames_mem_costWhole (source : CIGSLT)
    (name : String)
    (membership :
      name ∈ source.continuationRetyping.generatedLanguage.typeNames) :
    name ∈ source.costWholeLanguage.typeNames := by
  change name ∈ source.costCoreLanguage.typeNames
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_left _ membership

/-- Every authored constructor has its declaration-derived base copy in the
complete Cost language. -/
theorem costBaseConstructor_mem_costWhole (source : CIGSLT)
    (constructor : GrammarRule)
    (membership : constructor ∈
      source.theory.presentation.presentation.language.terms) :
    costBaseConstructor source.cut constructor ∈
      source.costWholeLanguage.terms :=
  source.generatedTerms_mem_costWhole _
    (source.continuationRetyping.costBaseConstructor_mem_generated
      constructor membership)

/-- Every constructor in the cut-derived non-principal fragment has its
uniform wrapped copy in the complete Cost language. -/
theorem costWrappedConstructor_mem_costWhole (source : CIGSLT)
    (constructor : AuthoredConstructor
      source.theory.presentation.presentation)
    (membership : constructor ∈
      source.continuationRetyping.wrappedConstructors) :
    costWrappedConstructor (theory := source.theory) constructor.1 ∈
      source.costWholeLanguage.terms :=
  source.generatedTerms_mem_costWhole _
    (source.continuationRetyping.costWrappedConstructor_mem_generated
      constructor membership)

/-- The two generated equation namespaces are individually injective and
mutually disjoint, so the static Cost theory inherits duplicate freedom from
the authored source equations. -/
theorem costStaticEquationNames_nodup (source : CIGSLT) :
    (source.costStaticEquations.map (·.name)).Nodup := by
  rw [costStaticEquations, List.map_append, List.map_map, List.map_map,
    List.nodup_append]
  have sourceNodup := LanguageDef.equationNames_nodup_of_validate_eq_nil
    source.theory.presentation.presentation.language
    source.theory.presentation.presentation.valid
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def] using
      sourceNodup.map costBaseEquationName_injective
  · simpa [Function.comp_def] using
      sourceNodup.map costWrappedEquationName_injective
  · intro baseName baseMembership wrappedName wrappedMembership equality
    rcases List.mem_map.mp baseMembership with
      ⟨baseEquation, _baseEquationMembership, rfl⟩
    rcases List.mem_map.mp wrappedMembership with
      ⟨wrappedEquation, _wrappedEquationMembership, rfl⟩
    exact costBaseEquationName_ne_wrapped _ _ equality

/-- The two tagged copies of the authored reflective presentations retain
unique names, and the reserved tags keep the copies disjoint. -/
theorem costStaticReflectivePresentationNames_nodup (source : CIGSLT) :
    (source.costStaticReflectivePresentations.map (·.name)).Nodup := by
  rw [costStaticReflectivePresentations, List.map_append, List.map_map,
    List.map_map, List.nodup_append]
  have sourceNodup :=
    presentationNames_nodup_of_validate_eq_nil source.reflection.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def, costBaseReflectivePresentationDecl,
      costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
      mapReflectivePresentation] using
      sourceNodup.map costBaseReflectiveName_injective
  · simpa [Function.comp_def, costWrappedReflectivePresentationDecl,
      costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols,
      mapReflectivePresentation] using
      sourceNodup.map costWrappedReflectiveName_injective
  · intro baseName baseMembership wrappedName wrappedMembership equality
    rcases List.mem_map.mp baseMembership with
      ⟨basePresentation, _basePresentationMembership, rfl⟩
    rcases List.mem_map.mp wrappedMembership with
      ⟨wrappedPresentation, _wrappedPresentationMembership, rfl⟩
    exact costBaseReflectiveName_ne_wrapped _ _ equality

private theorem reflectiveRuleName_filter_nodup
    (rules : List ReflectiveRuleDecl) (predicate : ReflectiveRuleDecl → Bool)
    (namesNodup : (rules.map (·.name)).Nodup) :
    ((rules.filter predicate).map (·.name)).Nodup := by
  induction rules with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at namesNodup
      rcases namesNodup with ⟨headFresh, tailNodup⟩
      by_cases selected : predicate head
      · simp only [List.filter_cons, selected, if_true, List.map_cons,
          List.nodup_cons]
        refine ⟨?_, inductionHypothesis tailNodup⟩
        intro filteredMembership
        apply headFresh
        rcases List.mem_map.mp filteredMembership with
          ⟨declaration, declarationMembership, nameEquality⟩
        exact List.mem_map.mpr ⟨declaration,
          (List.mem_filter.mp declarationMembership).1, nameEquality⟩
      · simp [selected, inductionHypothesis tailNodup]

/-- Selecting a sublist of authored reflective rules and applying the
injective base tag preserves duplicate freedom. -/
theorem costInteractionReflectiveRuleNames_nodup (source : CIGSLT) :
    (source.costInteractionReflectiveRules.map (·.name)).Nodup := by
  rw [costInteractionReflectiveRules, List.map_map]
  have sourceNodup :=
    ruleNames_nodup_of_validate_eq_nil source.reflection.2
  have filteredNodup :
      ((source.reflection.1.rules.filter
          fun declaration => declaration.rewriteRule ==
            source.theory.presentation.interactionRewrite.1.name).map
        (·.name)).Nodup := by
    exact reflectiveRuleName_filter_nodup _ _ sourceNodup
  simpa [Function.comp_def, costInteractionReflectiveRuleDecl] using
    filteredNodup.map costBaseReflectiveRuleName_injective

/-- Schema-local alpha-renaming carries every equation of the intermediate
reflective retyping language into the final collision-free static theory. -/
private theorem mapEquationSchemaNames_mem_costStaticEquations
    (source : CIGSLT) (equation : Equation)
    (membership : equation ∈
      (reflectiveRetypingLanguage source.continuationRetyping).equations) :
    mapEquationSchemaNames costSourceSchemaName equation ∈
      source.costStaticEquations := by
  rw [reflectiveRetypingLanguage] at membership
  rw [costStaticEquations]
  rcases List.mem_append.mp membership with
      baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourceEquation, sourceMembership, rfl⟩
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨sourceEquation, sourceMembership, rfl⟩)
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourceEquation, sourceMembership, rfl⟩
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨sourceEquation, sourceMembership, rfl⟩)

/-- A reflective presentation validated in the exact continuation-retyped
signature remains valid after adjoining the Cost apparatus and applying the
collision-free alpha-renaming to its selected equation. -/
private theorem validateReflectivePresentation_of_retyping
    (source : CIGSLT) (declaration : ReflectivePresentationDecl)
    (valid :
      (reflectiveRetypingLanguage source.continuationRetyping).validateReflectivePresentation
        declaration = []) :
    source.costWholeLanguage.validateReflectivePresentation declaration = [] := by
  rcases LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      (reflectiveRetypingLanguage source.continuationRetyping)
      declaration valid with ⟨witness⟩
  have labelsNodup :
      (source.costWholeLanguage.terms.map (·.label)).Nodup := by
    rw [costWholeLanguage_terms]
    exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      source.costCoreLanguage source.costCoreLanguage_validate
  have equationNamesNodup :
      (source.costWholeLanguage.equations.map (·.name)).Nodup := by
    simpa only [costWholeLanguage_equations] using
      source.costStaticEquationNames_nodup
  have quoteFiltered : witness.quote ∈
      (reflectiveRetypingLanguage source.continuationRetyping).terms.filter
        (fun term => term.label == declaration.quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have quoteMembership := (List.mem_filter.mp quoteFiltered).1
  have quoteLabel : witness.quote.label = declaration.quoteConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2
  change witness.quote ∈
      source.continuationRetyping.generatedLanguage.terms at quoteMembership
  have dropFiltered : witness.drop ∈
      (reflectiveRetypingLanguage source.continuationRetyping).terms.filter
        (fun term => term.label == declaration.dropConstructor) := by
    rw [witness.dropUnique]
    simp
  have dropMembership := (List.mem_filter.mp dropFiltered).1
  have dropLabel : witness.drop.label = declaration.dropConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp dropFiltered).2
  change witness.drop ∈
      source.continuationRetyping.generatedLanguage.terms at dropMembership
  have unitFiltered : witness.unit ∈
      (reflectiveRetypingLanguage source.continuationRetyping).terms.filter
        (fun term => term.label == declaration.parallelUnitConstructor) := by
    rw [witness.unitUnique]
    simp
  have unitMembership := (List.mem_filter.mp unitFiltered).1
  have unitLabel :
      witness.unit.label = declaration.parallelUnitConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp unitFiltered).2
  change witness.unit ∈
      source.continuationRetyping.generatedLanguage.terms at unitMembership
  have equationFiltered : witness.equation ∈
      (reflectiveRetypingLanguage source.continuationRetyping).equations.filter
        (fun candidate => candidate.name == declaration.quoteDropEquation) := by
    rw [witness.equationUnique]
    simp
  have equationMembership := (List.mem_filter.mp equationFiltered).1
  have equationName :
      witness.equation.name = declaration.quoteDropEquation :=
    beq_iff_eq.mp (List.mem_filter.mp equationFiltered).2
  have mappedEquationMembership :=
    source.mapEquationSchemaNames_mem_costStaticEquations witness.equation
      equationMembership
  have quoteUnique :
      source.costWholeLanguage.terms.filter
          (fun term => term.label == declaration.quoteConstructor) =
        [witness.quote] := by
    simpa [quoteLabel] using
      LanguageDef.filter_terms_by_label_eq_singleton
        source.costWholeLanguage.terms witness.quote labelsNodup
        (source.generatedTerms_mem_costWhole witness.quote quoteMembership)
  have dropUnique :
      source.costWholeLanguage.terms.filter
          (fun term => term.label == declaration.dropConstructor) =
        [witness.drop] := by
    simpa [dropLabel] using
      LanguageDef.filter_terms_by_label_eq_singleton
        source.costWholeLanguage.terms witness.drop labelsNodup
        (source.generatedTerms_mem_costWhole witness.drop dropMembership)
  have unitUnique :
      source.costWholeLanguage.terms.filter
          (fun term => term.label == declaration.parallelUnitConstructor) =
        [witness.unit] := by
    simpa [unitLabel] using
      LanguageDef.filter_terms_by_label_eq_singleton
        source.costWholeLanguage.terms witness.unit labelsNodup
        (source.generatedTerms_mem_costWhole witness.unit unitMembership)
  have equationUnique :
      source.costWholeLanguage.equations.filter
          (fun candidate => candidate.name == declaration.quoteDropEquation) =
        [mapEquationSchemaNames costSourceSchemaName witness.equation] := by
    simpa [mapEquationSchemaNames, equationName] using
      LanguageDef.filter_equations_by_name_eq_singleton
        source.costWholeLanguage.equations
        (mapEquationSchemaNames costSourceSchemaName witness.equation)
        equationNamesNodup mappedEquationMembership
  apply (LanguageDef.ReflectivePresentationWitness.validate
    ({ quote := witness.quote
       drop := witness.drop
       unit := witness.unit
       equation := mapEquationSchemaNames costSourceSchemaName witness.equation
       quoteParameter := witness.quoteParameter
       dropParameter := witness.dropParameter
       processSort := source.generatedTypeNames_mem_costWhole
         declaration.processSort witness.processSort
       nameSort := source.generatedTypeNames_mem_costWhole
         declaration.nameSort witness.nameSort
       sortsDistinct := witness.sortsDistinct
       quoteUnique := quoteUnique
       quoteCategory := witness.quoteCategory
       quoteParameters := witness.quoteParameters
       dropUnique := dropUnique
       dropCategory := witness.dropCategory
       dropParameters := witness.dropParameters
       unitUnique := unitUnique
       unitCategory := witness.unitCategory
       unitParameters := witness.unitParameters
       equationUnique := equationUnique
       equationShape := quoteDropShape_mapEquationSchemaNames
         costSourceSchemaName declaration witness.equation
           witness.equationShape } :
      LanguageDef.ReflectivePresentationWitness
        source.costWholeLanguage declaration))

/-- Every tagged base or wrapped presentation in the generated static theory
passes the final language's exact reflective validator. -/
theorem costStaticReflectivePresentation_validate (source : CIGSLT)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈ source.costStaticReflectivePresentations) :
    source.costWholeLanguage.validateReflectivePresentation declaration = [] := by
  rw [costStaticReflectivePresentations, List.mem_append] at membership
  rcases membership with baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourceDeclaration, sourceMembership, rfl⟩
    exact source.validateReflectivePresentation_of_retyping
      (costBaseReflectivePresentationDecl sourceDeclaration)
      (source.reflectivePresentationsRetypable sourceDeclaration
        sourceMembership).1
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourceDeclaration, sourceMembership, rfl⟩
    exact source.validateReflectivePresentation_of_retyping
      (costWrappedReflectivePresentationDecl source.theory sourceDeclaration)
      (source.reflectivePresentationsRetypable sourceDeclaration
        sourceMembership).2

/-- Each selected source rule-local reflective interpretation is transported
to the generated whole-redex rule, matching in the base presentation and
substituting in the wrapped presentation. -/
theorem costInteractionReflectiveRule_validate (source : CIGSLT)
    (declaration : ReflectiveRuleDecl)
    (membership : declaration ∈ source.costInteractionReflectiveRules) :
    source.costWholeLanguage.validateReflectiveRule
      source.costStaticReflectivePresentations declaration = [] := by
  rw [costInteractionReflectiveRules] at membership
  rcases List.mem_map.mp membership with
    ⟨sourceDeclaration, selectedMembership, rfl⟩
  have sourceMembership := (List.mem_filter.mp selectedMembership).1
  have sourceValid := rule_validate_eq_nil_of_validate_eq_nil
    source.reflection.2 sourceMembership
  rcases LanguageDef.reflectiveRuleWitness_of_validate_eq_nil
      source.theory.presentation.presentation.language
      source.reflection.1.presentations sourceDeclaration
      sourceValid with ⟨witness⟩
  have matchingFiltered : witness.matchingPresentation ∈
      source.reflection.1.presentations.filter
        (fun candidate =>
          candidate.name == sourceDeclaration.matchingPresentation) := by
    rw [witness.matchingUnique]
    simp
  have matchingMembership := (List.mem_filter.mp matchingFiltered).1
  have matchingName : witness.matchingPresentation.name =
      sourceDeclaration.matchingPresentation :=
    beq_iff_eq.mp (List.mem_filter.mp matchingFiltered).2
  have substitutionFiltered : witness.substitutionPresentation ∈
      source.reflection.1.presentations.filter
        (fun candidate =>
          candidate.name == sourceDeclaration.substitutionPresentation) := by
    rw [witness.substitutionUnique]
    simp
  have substitutionMembership :=
    (List.mem_filter.mp substitutionFiltered).1
  have substitutionName : witness.substitutionPresentation.name =
      sourceDeclaration.substitutionPresentation :=
    beq_iff_eq.mp (List.mem_filter.mp substitutionFiltered).2
  let basePresentation :=
    costBaseReflectivePresentationDecl witness.matchingPresentation
  let wrappedPresentation :=
    costWrappedReflectivePresentationDecl source.theory
      witness.substitutionPresentation
  have baseMembership :
      basePresentation ∈ source.costStaticReflectivePresentations := by
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨witness.matchingPresentation,
      matchingMembership, rfl⟩
  have wrappedMembership :
      wrappedPresentation ∈ source.costStaticReflectivePresentations := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨witness.substitutionPresentation,
      substitutionMembership, rfl⟩
  have presentationNamesNodup :
      (source.costWholeReflectionProfile.presentations.map (·.name)).Nodup := by
    simpa only [costWholeReflectionProfile_presentations] using
      source.costStaticReflectivePresentationNames_nodup
  have matchingUnique :
      source.costWholeReflectionProfile.presentations.filter
          (fun candidate => candidate.name == costBaseReflectiveName
            sourceDeclaration.matchingPresentation) =
        [basePresentation] := by
    have unique := LanguageDef.filter_by_string_key_eq_singleton
      (fun candidate : ReflectivePresentationDecl => candidate.name)
      source.costWholeReflectionProfile.presentations basePresentation
      presentationNamesNodup
      (by simpa only [costWholeReflectionProfile_presentations] using
        baseMembership)
    simpa [basePresentation, costInteractionReflectiveRuleDecl,
      costBaseReflectivePresentationDecl, mapReflectivePresentation,
      costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
      matchingName] using unique
  have substitutionUnique :
      source.costWholeReflectionProfile.presentations.filter
          (fun candidate => candidate.name == costWrappedReflectiveName
            sourceDeclaration.substitutionPresentation) =
        [wrappedPresentation] := by
    have unique := LanguageDef.filter_by_string_key_eq_singleton
      (fun candidate : ReflectivePresentationDecl => candidate.name)
      source.costWholeReflectionProfile.presentations wrappedPresentation
      presentationNamesNodup
      (by simpa only [costWholeReflectionProfile_presentations] using
        wrappedMembership)
    simpa [wrappedPresentation, costInteractionReflectiveRuleDecl,
      costWrappedReflectivePresentationDecl, mapReflectivePresentation,
      costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols,
      substitutionName] using unique
  have rewriteUnique :
      source.costWholeLanguage.rewrites.filter
          (fun candidate => candidate.name == costWholeRedexRewriteName) =
        [source.costWholeRedexRewrite] := by
    simp [costWholeLanguage_rewrites, costWholeRedexRewrite,
      costWholeRedexRewriteName]
  exact (LanguageDef.ReflectiveRuleWitness.validate
    ({ rewrite := source.costWholeRedexRewrite
       matchingPresentation := basePresentation
       substitutionPresentation := wrappedPresentation
       rewriteUnique := rewriteUnique
       matchingUnique := matchingUnique
       substitutionUnique := substitutionUnique } :
      LanguageDef.ReflectiveRuleWitness source.costWholeLanguage
        source.costStaticReflectivePresentations
        (costInteractionReflectiveRuleDecl sourceDeclaration)))

/-- The final collision-free base equation image is sorted in the complete
Cost signature. -/
theorem costBaseEquationDecl_wellSorted (source : CIGSLT)
    (equation : Equation)
    (membership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    EquationWellSorted source.costWholeLanguage
      (costBaseEquationDecl equation) := by
  have raw :=
    (source.equationsRetypable equation membership).baseWellSorted
  exact raw.mapSchemaNames_weakenTerms
    (source.generatedTerms_mem_costWhole) costSourceSchemaName
      costSourceSchemaName_injective

/-- The final collision-free wrapped equation image is sorted in the complete
Cost signature. -/
theorem costWrappedEquationDecl_wellSorted (source : CIGSLT)
    (equation : Equation)
    (membership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    EquationWellSorted source.costWholeLanguage
      (costWrappedEquationDecl source.theory equation) := by
  have raw :=
    (source.equationsRetypable equation membership).wrappedWellSorted
  exact raw.mapSchemaNames_weakenTerms
    (source.generatedTerms_mem_costWhole) costSourceSchemaName
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

/-- Every constructor in the generated Cost signature occupies the reserved
`$cost:` namespace. -/
theorem costCoreTerm_label_has_costPrefix (source : CIGSLT)
    (term : GrammarRule) (membership : term ∈ source.costCoreLanguage.terms) :
    ∃ suffix, term.label = "$cost:" ++ suffix := by
  have labelMembership :
      term.label ∈ source.costCoreLanguage.terms.map (·.label) :=
    List.mem_map.mpr ⟨term, membership, rfl⟩
  rw [source.costCoreConstructorLabels,
    source.continuationRetyping.generatedLanguage_constructorLabels]
      at labelMembership
  rcases List.mem_append.mp labelMembership with
    generatedMembership | apparatusMembership
  · rcases List.mem_append.mp generatedMembership with
      baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with
        ⟨sourceLabel, _, equality⟩
      refine ⟨"base-constructor:" ++ sourceLabel, ?_⟩
      rw [← equality]
      unfold costBaseConstructorName
      unfold costBaseConstructorTag
      calc
        "$cost:base-constructor:" ++ sourceLabel =
            ("$cost:" ++ "base-constructor:") ++ sourceLabel := by
              rw [show "$cost:base-constructor:" =
                "$cost:" ++ "base-constructor:" by decide]
        _ = "$cost:" ++ ("base-constructor:" ++ sourceLabel) := by
          exact String.append_assoc
    · rcases List.mem_map.mp wrappedMembership with
        ⟨sourceLabel, _, equality⟩
      refine ⟨"wrapped-constructor:" ++ sourceLabel, ?_⟩
      rw [← equality]
      unfold costWrappedConstructorName
      unfold costWrappedConstructorTag
      calc
        "$cost:wrapped-constructor:" ++ sourceLabel =
            ("$cost:" ++ "wrapped-constructor:") ++ sourceLabel := by
              rw [show "$cost:wrapped-constructor:" =
                "$cost:" ++ "wrapped-constructor:" by decide]
        _ = "$cost:" ++ ("wrapped-constructor:" ++ sourceLabel) := by
          exact String.append_assoc
  · rcases List.mem_map.mp apparatusMembership with
      ⟨suffix, _, equality⟩
    refine ⟨"apparatus-constructor:" ++ suffix, ?_⟩
    rw [← equality]
    unfold costApparatusConstructorName
    rw [show "$cost:apparatus-constructor:" =
      "$cost:" ++ "apparatus-constructor:" by decide, String.append_assoc]

theorem costSourceSchemaName_ne_costCoreTermLabel (source : CIGSLT)
    (name : String) (term : GrammarRule)
    (membership : term ∈ source.costCoreLanguage.terms) :
    costSourceSchemaName name ≠ term.label := by
  rcases source.costCoreTerm_label_has_costPrefix term membership with
    ⟨suffix, equality⟩
  rw [equality]
  exact costSourceSchemaName_ne_costPrefix name suffix

theorem costAdministrativeSchemaName_ne_costCoreTermLabel (source : CIGSLT)
    (name : String) (term : GrammarRule)
    (membership : term ∈ source.costCoreLanguage.terms) :
    costAdministrativeSchemaName name ≠ term.label := by
  rcases source.costCoreTerm_label_has_costPrefix term membership with
    ⟨suffix, equality⟩
  rw [equality]
  exact costAdministrativeSchemaName_ne_costPrefix name suffix

theorem generatedSchemaName_not_mem_costCoreLabels (source : CIGSLT)
    (name : String)
    (generated :
      (∃ sourceName, name = costSourceSchemaName sourceName) ∨
        ∃ administrativeName,
          name = costAdministrativeSchemaName administrativeName) :
    name ∉ source.costCoreLanguage.terms.map (·.label) := by
  intro membership
  rcases List.mem_map.mp membership with ⟨term, termMembership, equality⟩
  rcases generated with ⟨sourceName, rfl⟩ | ⟨administrativeName, rfl⟩
  · exact source.costSourceSchemaName_ne_costCoreTermLabel
      sourceName term termMembership equality.symm
  · exact source.costAdministrativeSchemaName_ne_costCoreTermLabel
      administrativeName term termMembership equality.symm

/-- A collision-free image of a premise-free authored equation passes the
wildcard/scope component of validation.  The proof uses the source equation's
validated binding flow; generated constructor names play no role in deciding
which metavariables are bound. -/
theorem costMappedEquation_validateRulePatterns
    (source : CIGSLT) (symbols : PresentationSymbols)
    (equation : Equation)
    (equationMembership : equation ∈
      source.theory.presentation.presentation.language.equations)
    (premisesEmpty : equation.premises = [])
    (sorted : EquationWellSorted source.costWholeLanguage
      (mapEquationSchemaNames costSourceSchemaName
        (mapEquation symbols equation))) :
    LanguageDef.validateRulePatterns
      s!"equation {(mapEquation symbols equation).name}"
      (source.costWholeLanguage.terms.map (·.label))
      (mapTypeContextSchemaNames costSourceSchemaName
        (mapTypeContext symbols equation.typeContext)) []
      (mapPatternSchemaNames costSourceSchemaName
        (mapPattern symbols equation.left))
      (mapPatternSchemaNames costSourceSchemaName
        (mapPattern symbols equation.right)) = [] := by
  rcases sorted with ⟨type, leftTyped, rightTyped⟩
  change HasType source.costWholeLanguage
      (FreeTypeContext.ofList
        (mapTypeContextSchemaNames costSourceSchemaName
          (mapTypeContext symbols equation.typeContext))) []
      (mapPatternSchemaNames costSourceSchemaName
        (mapPattern symbols equation.left)) type at leftTyped
  change HasType source.costWholeLanguage
      (FreeTypeContext.ofList
        (mapTypeContextSchemaNames costSourceSchemaName
          (mapTypeContext symbols equation.typeContext))) []
      (mapPatternSchemaNames costSourceSchemaName
        (mapPattern symbols equation.right)) type at rightTyped
  apply validateRulePatterns_noPremises_eq_nil
  · simpa [Pattern.isWellScoped] using leftTyped.isWellScopedAt
  · simpa [Pattern.isWellScoped] using rightTyped.isWellScopedAt
  · intro name membership
    have combined := List.mem_eraseDups.mp membership
    rw [patternFvarNames_nil, patternFvarNames_nil,
      mapPatternSchemaNames_freeFvarNames,
      mapPatternSchemaNames_freeFvarNames,
      StructuralMorphism.mapPattern_freeFvarNames,
      StructuralMorphism.mapPattern_freeFvarNames,
      ← List.map_append] at combined
    rcases List.mem_map.mp combined with ⟨sourceName, _sourceMembership,
      equality⟩
    rw [costWholeLanguage_terms]
    exact source.generatedSchemaName_not_mem_costCoreLabels name
      (Or.inl ⟨sourceName, equality.symm⟩)
  · intro name membership
    have combined := List.mem_eraseDups.mp membership
    rw [mapPatternSchemaNames_patternBinderNames,
      mapPatternSchemaNames_patternBinderNames,
      StructuralMorphism.mapPattern_patternBinderNames,
      StructuralMorphism.mapPattern_patternBinderNames,
      ← List.map_append] at combined
    rcases List.mem_map.mp combined with ⟨sourceName, _sourceMembership,
      equality⟩
    rw [costWholeLanguage_terms]
    exact source.generatedSchemaName_not_mem_costCoreLabels name
      (Or.inl ⟨sourceName, equality.symm⟩)
  · intro entry membership
    simp only [mapTypeContextSchemaNames, mapTypeContext, List.map_map,
      List.mem_map] at membership
    rcases membership with ⟨sourceEntry, _sourceMembership, rfl⟩
    rw [costWholeLanguage_terms]
    exact source.generatedSchemaName_not_mem_costCoreLabels
      (costSourceSchemaName sourceEntry.1)
      (Or.inl ⟨sourceEntry.1, rfl⟩)
  · intro name rightMembership
    have rightMembershipRaw := List.mem_eraseDups.mp rightMembership
    rw [patternFvarNames_nil,
      mapPatternSchemaNames_freeFvarNames,
      StructuralMorphism.mapPattern_freeFvarNames] at rightMembershipRaw
    rcases List.mem_map.mp rightMembershipRaw with
      ⟨sourceName, sourceRightMembership, equality⟩
    have sourceLeftMembership :=
      rightFvar_mem_left_of_validatedEquation_noPremises
        source.theory.presentation.presentation.language
        source.theory.presentation.presentation.valid equation
        equationMembership premisesEmpty sourceName
        (by simpa [patternFvarNames_nil] using sourceRightMembership)
    rw [patternFvarNames_nil,
      mapPatternSchemaNames_freeFvarNames,
      StructuralMorphism.mapPattern_freeFvarNames]
    exact List.mem_map.mpr
      ⟨sourceName, by simpa [patternFvarNames_nil] using sourceLeftMembership,
        equality⟩

/-- Free-variable assignment induced by the generated rule's exact declared
type context. -/
def costWholeRedexFreeContext (source : CIGSLT) : FreeTypeContext :=
  lookupTypeContext source.costWholeRedexTypeContext

theorem lookup_costRetypedSourceContext (source : CIGSLT) (name : String) :
    lookupTypeContext source.costRetypedSourceContext
        (costSourceSchemaName name) =
      source.continuationRetyping.generatedFreeContext name := by
  unfold costRetypedSourceContext ContinuationRetypingPlan.generatedFreeContext
  simpa using
    (lookupTypeContext_map_injective
      source.theory.presentation.interactionRewrite.1.typeContext
      costSourceSchemaName
      (fun schemaName type =>
        if schemaName = source.cut.program.continuationVariable.name ∨
            schemaName = source.cut.environment.continuationVariable.name then
          costWrappedTypeExpr
            source.theory.presentation.interactingSort.1.name type
        else
          costBaseTypeExpr type)
      costSourceSchemaName_injective name)

theorem costWholeRedexFreeContext_source (source : CIGSLT)
    (name : String) (type : TypeExpr)
    (lookup : source.continuationRetyping.generatedFreeContext name =
      some type) :
    source.costWholeRedexFreeContext (costSourceSchemaName name) =
      some type := by
  rw [costWholeRedexFreeContext, costWholeRedexTypeContext,
    lookupTypeContext_append, lookup_costRetypedSourceContext, lookup]

private theorem lookup_costRetypedSourceContext_signature_none
    (source : CIGSLT) :
    lookupTypeContext source.costRetypedSourceContext
        source.costSignatureVariable = none := by
  unfold costRetypedSourceContext
  exact lookupTypeContext_map_outside
    source.theory.presentation.interactionRewrite.1.typeContext
    costSourceSchemaName
    (fun schemaName type =>
      if schemaName = source.cut.program.continuationVariable.name ∨
          schemaName = source.cut.environment.continuationVariable.name then
        costWrappedTypeExpr
          source.theory.presentation.interactingSort.1.name type
      else
        costBaseTypeExpr type)
    source.costSignatureVariable
    (fun name => source.costSourceSchemaName_ne_signature name)

private theorem lookup_costRetypedSourceContext_stackTail_none
    (source : CIGSLT) :
    lookupTypeContext source.costRetypedSourceContext
        source.costStackTailVariable = none := by
  unfold costRetypedSourceContext
  exact lookupTypeContext_map_outside
    source.theory.presentation.interactionRewrite.1.typeContext
    costSourceSchemaName
    (fun schemaName type =>
      if schemaName = source.cut.program.continuationVariable.name ∨
          schemaName = source.cut.environment.continuationVariable.name then
        costWrappedTypeExpr
          source.theory.presentation.interactingSort.1.name type
      else
        costBaseTypeExpr type)
    source.costStackTailVariable
    (fun name => source.costSourceSchemaName_ne_stackTail name)

@[simp]
theorem costWholeRedexFreeContext_signature (source : CIGSLT) :
    source.costWholeRedexFreeContext source.costSignatureVariable =
      some (.base costSignatureSortName) := by
  rw [costWholeRedexFreeContext, costWholeRedexTypeContext,
    lookupTypeContext_append,
    lookup_costRetypedSourceContext_signature_none]
  simp [lookupTypeContext]

@[simp]
theorem costWholeRedexFreeContext_stackTail (source : CIGSLT) :
    source.costWholeRedexFreeContext source.costStackTailVariable =
      some (.base costTokenStackSortName) := by
  rw [costWholeRedexFreeContext, costWholeRedexTypeContext,
    lookupTypeContext_append,
    lookup_costRetypedSourceContext_stackTail_none]
  simp [lookupTypeContext, source.costSignatureVariable_ne_stackTail]

private theorem generatedTerms_mem_costCore (source : CIGSLT)
    (rule : GrammarRule)
    (membership :
      rule ∈ source.continuationRetyping.generatedLanguage.terms) :
    rule ∈ source.costCoreLanguage.terms := by
  exact List.mem_append_left _ membership

theorem costMappedRedex_hasType (source : CIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      (mapPatternSchemaNames costSourceSchemaName
        (mapPattern costBasePresentationSymbols
          source.theory.presentation.interactionRewrite.1.left))
      (costBaseSortName
        source.theory.presentation.interactingSort.1.name) := by
  exact (source.redexRetypable.weakenTerms
      (generatedTerms_mem_costCore source)).mapSchemaNames
        costSourceSchemaName (source.costWholeRedexFreeContext_source)

theorem costMappedContractum_hasType (source : CIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      source.costMappedContractum costWrappedSortName := by
  exact (source.wrappable.weakenTerms
      (generatedTerms_mem_costCore source)).mapSchemaNames
        costSourceSchemaName (source.costWholeRedexFreeContext_source)

private theorem costSignedConstructor_mem (source : CIGSLT) :
    costSignedConstructor
        source.theory.presentation.interactingSort.1.name ∈
      source.costCoreLanguage.terms := by
  apply List.mem_append_right
  simp [costCoreConstructors]

private theorem costTokenStackConsConstructor_mem (source : CIGSLT) :
    costTokenStackConsConstructor ∈ source.costCoreLanguage.terms := by
  apply List.mem_append_right
  simp [costCoreConstructors]

private theorem costFundingConstructor_mem (source : CIGSLT) :
    costFundingConstructor ∈ source.costCoreLanguage.terms := by
  apply List.mem_append_right
  simp [costCoreConstructors]

private theorem costContactConstructor_mem (source : CIGSLT) :
    costContactConstructor ∈ source.costCoreLanguage.terms := by
  apply List.mem_append_right
  simp [costCoreConstructors]

theorem costSignatureVariable_hasType (source : CIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      (.fvar source.costSignatureVariable) costSignatureSortName := by
  exact .fvar (source.costWholeRedexFreeContext_signature)

theorem costStackTailVariable_hasType (source : CIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      (.fvar source.costStackTailVariable) costTokenStackSortName := by
  exact .fvar (source.costWholeRedexFreeContext_stackTail)

theorem costSigned_hasType (source : CIGSLT) {body : Pattern}
    (bodyTyped :
      HasSort source.costCoreLanguage source.costWholeRedexFreeContext [] body
        (costBaseSortName
          source.theory.presentation.interactingSort.1.name)) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      (.apply costSignedConstructorName
        [body, .fvar source.costSignatureVariable]) costWrappedSortName := by
  apply HasType.constructor (costSignedConstructor_mem source)
  · simp [UsesBareCollection, costSignedConstructor]
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · exact bodyTyped
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · exact source.costSignatureVariable_hasType
      · exact .nil

theorem costTokenStackCons_hasType (source : CIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      (.apply costTokenStackConsConstructorName
        [.fvar source.costSignatureVariable,
          .fvar source.costStackTailVariable]) costTokenStackSortName := by
  apply HasType.constructor (costTokenStackConsConstructor_mem source)
  · simp [UsesBareCollection, costTokenStackConsConstructor]
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · exact source.costSignatureVariable_hasType
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · exact source.costStackTailVariable_hasType
      · exact .nil

theorem costFunding_hasType (source : CIGSLT) {stack : Pattern}
    (stackTyped :
      HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
        stack costTokenStackSortName) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      (.apply costFundingConstructorName [stack]) costWrappedSortName := by
  apply HasType.constructor (costFundingConstructor_mem source)
  · simp [UsesBareCollection, costFundingConstructor]
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · exact stackTyped
    · exact .nil

theorem costContact_hasType (source : CIGSLT) {left right : Pattern}
    (leftTyped :
      HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
        left costWrappedSortName)
    (rightTyped :
      HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
        right costWrappedSortName) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      (.apply costContactConstructorName [left, right]) costWrappedSortName := by
  apply HasType.constructor (costContactConstructor_mem source)
  · simp [UsesBareCollection, costContactConstructor]
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · exact leftTyped
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · exact rightTyped
      · exact .nil

theorem costWholeRedexSource_hasType (source : CIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      source.costWholeRedexSource costWrappedSortName := by
  rw [source.costWholeRedexSource_eq]
  exact source.costContact_hasType
    (source.costSigned_hasType source.costMappedRedex_hasType)
    (source.costFunding_hasType source.costTokenStackCons_hasType)

theorem costWholeRedexTarget_hasType (source : CIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      source.costWholeRedexTarget costWrappedSortName := by
  unfold costWholeRedexTarget
  exact source.costContact_hasType source.costMappedContractum_hasType
    (source.costFunding_hasType source.costStackTailVariable_hasType)

@[simp]
theorem costWholeRedexSource_freeFvarNames (source : CIGSLT) :
    source.costWholeRedexSource.freeFvarNames =
      source.theory.presentation.interactionRewrite.1.left.freeFvarNames.map
          costSourceSchemaName ++
        [source.costSignatureVariable, source.costSignatureVariable,
          source.costStackTailVariable] := by
  rw [source.costWholeRedexSource_eq]
  simp [Pattern.freeFvarNames]

@[simp]
theorem costWholeRedexTarget_freeFvarNames (source : CIGSLT) :
    source.costWholeRedexTarget.freeFvarNames =
      source.theory.presentation.interactionRewrite.1.right.freeFvarNames.map
          costSourceSchemaName ++
        [source.costStackTailVariable] := by
  simp [costWholeRedexTarget, costMappedContractum,
    Pattern.freeFvarNames]

@[simp]
theorem costWholeRedexSource_patternBinderNames (source : CIGSLT) :
    LanguageDef.patternBinderNames source.costWholeRedexSource =
      (LanguageDef.patternBinderNames
        source.theory.presentation.interactionRewrite.1.left).map
          costSourceSchemaName := by
  rw [source.costWholeRedexSource_eq]
  simp [LanguageDef.patternBinderNames]

@[simp]
theorem costWholeRedexTarget_patternBinderNames (source : CIGSLT) :
    LanguageDef.patternBinderNames source.costWholeRedexTarget =
      (LanguageDef.patternBinderNames
        source.theory.presentation.interactionRewrite.1.right).map
          costSourceSchemaName := by
  simp [costWholeRedexTarget, costMappedContractum,
    LanguageDef.patternBinderNames]

theorem costWholeRedex_fvar_generated (source : CIGSLT) (name : String)
    (membership : name ∈
      (LanguageDef.patternFvarNames [] source.costWholeRedexSource ++
        LanguageDef.patternFvarNames [] source.costWholeRedexTarget).eraseDups) :
    (∃ sourceName, name = costSourceSchemaName sourceName) ∨
      ∃ administrativeName,
        name = costAdministrativeSchemaName administrativeName := by
  have combined := List.mem_eraseDups.mp membership
  rw [patternFvarNames_nil, patternFvarNames_nil,
    source.costWholeRedexSource_freeFvarNames,
    source.costWholeRedexTarget_freeFvarNames] at combined
  simp only [List.mem_append, List.mem_map, List.mem_cons] at combined
  rcases combined with
    (⟨sourceName, _, equality⟩ | equality | equality | equality) |
      ⟨sourceName, _, equality⟩ | equality
  · exact Or.inl ⟨sourceName, equality.symm⟩
  · exact Or.inr ⟨"signature", by
      simpa [costSignatureVariable] using equality⟩
  · exact Or.inr ⟨"signature", by
      simpa [costSignatureVariable] using equality⟩
  · exact Or.inr ⟨"stack-tail", by
      simpa [costStackTailVariable] using equality⟩
  · exact Or.inl ⟨sourceName, equality.symm⟩
  · exact Or.inr ⟨"stack-tail", by
      simpa [costStackTailVariable] using equality⟩

theorem costWholeRedex_binder_generated (source : CIGSLT) (name : String)
    (membership : name ∈
      (LanguageDef.patternBinderNames source.costWholeRedexSource ++
        LanguageDef.patternBinderNames source.costWholeRedexTarget).eraseDups) :
    ∃ sourceName, name = costSourceSchemaName sourceName := by
  have combined := List.mem_eraseDups.mp membership
  rw [source.costWholeRedexSource_patternBinderNames,
    source.costWholeRedexTarget_patternBinderNames] at combined
  simp only [List.mem_append, List.mem_map] at combined
  rcases combined with
    ⟨sourceName, _, equality⟩ | ⟨sourceName, _, equality⟩
  · exact ⟨sourceName, equality.symm⟩
  · exact ⟨sourceName, equality.symm⟩

theorem costWholeRedex_contextName_generated (source : CIGSLT)
    (entry : String × TypeExpr)
    (membership : entry ∈ source.costWholeRedexTypeContext) :
    (∃ sourceName, entry.1 = costSourceSchemaName sourceName) ∨
      ∃ administrativeName,
        entry.1 = costAdministrativeSchemaName administrativeName := by
  simp only [costWholeRedexTypeContext, List.mem_append] at membership
  rcases membership with sourceEntry | administrativeEntry
  · simp only [costRetypedSourceContext, List.mem_map] at sourceEntry
    rcases sourceEntry with ⟨originalEntry, _, rfl⟩
    exact Or.inl ⟨originalEntry.1, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
      at administrativeEntry
    rcases administrativeEntry with equality | equality
    · subst entry
      exact Or.inr ⟨"signature", rfl⟩
    · subst entry
      exact Or.inr ⟨"stack-tail", rfl⟩

theorem costWholeRedex_fvars_avoid_constructorLabels (source : CIGSLT)
    (name : String)
    (membership : name ∈
      (LanguageDef.patternFvarNames [] source.costWholeRedexSource ++
        LanguageDef.patternFvarNames [] source.costWholeRedexTarget).eraseDups) :
    name ∉ source.costWholeLanguage.terms.map (·.label) := by
  rw [costWholeLanguage_terms]
  exact source.generatedSchemaName_not_mem_costCoreLabels name
    (source.costWholeRedex_fvar_generated name membership)

theorem costWholeRedex_binders_avoid_constructorLabels (source : CIGSLT)
    (name : String)
    (membership : name ∈
      (LanguageDef.patternBinderNames source.costWholeRedexSource ++
        LanguageDef.patternBinderNames source.costWholeRedexTarget).eraseDups) :
    name ∉ source.costWholeLanguage.terms.map (·.label) := by
  rw [costWholeLanguage_terms]
  rcases source.costWholeRedex_binder_generated name membership with
    ⟨sourceName, equality⟩
  exact source.generatedSchemaName_not_mem_costCoreLabels name
    (Or.inl ⟨sourceName, equality⟩)

theorem costWholeRedex_context_avoids_constructorLabels (source : CIGSLT)
    (entry : String × TypeExpr)
    (membership : entry ∈ source.costWholeRedexTypeContext) :
    entry.1 ∉ source.costWholeLanguage.terms.map (·.label) := by
  rw [costWholeLanguage_terms]
  exact source.generatedSchemaName_not_mem_costCoreLabels entry.1
    (source.costWholeRedex_contextName_generated entry membership)

set_option maxHeartbeats 1000000 in
theorem costWholeRedex_rightFvar_mem_left (source : CIGSLT)
    (name : String)
    (membership :
      name ∈ LanguageDef.patternFvarNames [] source.costWholeRedexTarget) :
    name ∈ LanguageDef.patternFvarNames [] source.costWholeRedexSource := by
  rw [patternFvarNames_nil, source.costWholeRedexTarget_freeFvarNames]
      at membership
  simp only [List.mem_append, List.mem_map, List.mem_cons] at membership
  rcases membership with ⟨sourceName, sourceRightMembership, equality⟩ |
      equality
  · have selectedRewriteClean := validateRewrite_eq_nil_of_validate_eq_nil
      source.theory.presentation.presentation.language
      source.theory.presentation.presentation.valid
      source.theory.presentation.interactionRewrite.1
      source.cut.interactionRewrite_mem
    have selectedPatternsClean :=
      validateRulePatterns_eq_nil_of_validateRewrite_eq_nil
        source.theory.presentation.presentation.language
        source.theory.presentation.interactionRewrite.1
        selectedRewriteClean
    rw [source.cut.interactionPremisesEmpty] at selectedPatternsClean
    have sourceLeftMembership :=
      rightFvar_mem_left_of_validateRulePatterns_noPremises_eq_nil
        s!"rewrite {source.theory.presentation.interactionRewrite.1.name}"
        (source.theory.presentation.presentation.language.terms.map
          (·.label))
        source.theory.presentation.interactionRewrite.1.typeContext
        source.theory.presentation.interactionRewrite.1.left
        source.theory.presentation.interactionRewrite.1.right
        selectedPatternsClean sourceName (by simpa using sourceRightMembership)
    rw [patternFvarNames_nil, source.costWholeRedexSource_freeFvarNames]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨sourceName, by simpa using sourceLeftMembership,
      equality⟩
  · rw [patternFvarNames_nil, source.costWholeRedexSource_freeFvarNames]
    apply List.mem_append_right
    simp only [List.not_mem_nil, or_false] at equality
    exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inl equality)))))

theorem costWholeRedexSource_isWellScoped (source : CIGSLT) :
    source.costWholeRedexSource.isWellScoped = true := by
  simpa [Pattern.isWellScoped] using
    source.costWholeRedexSource_hasType.isWellScopedAt

theorem costWholeRedexTarget_isWellScoped (source : CIGSLT) :
    source.costWholeRedexTarget.isWellScoped = true := by
  simpa [Pattern.isWellScoped] using
    source.costWholeRedexTarget_hasType.isWellScopedAt

theorem costWholeRedex_validateRulePatterns (source : CIGSLT) :
    LanguageDef.validateRulePatterns
      s!"rewrite {source.costWholeRedexRewrite.name}"
      (source.costWholeLanguage.terms.map (·.label))
      source.costWholeRedexTypeContext [] source.costWholeRedexSource
      source.costWholeRedexTarget = [] := by
  apply validateRulePatterns_noPremises_eq_nil
  · exact source.costWholeRedexSource_isWellScoped
  · exact source.costWholeRedexTarget_isWellScoped
  · exact source.costWholeRedex_fvars_avoid_constructorLabels
  · exact source.costWholeRedex_binders_avoid_constructorLabels
  · exact source.costWholeRedex_context_avoids_constructorLabels
  · intro name membership
    exact source.costWholeRedex_rightFvar_mem_left name
      (List.mem_eraseDups.mp membership)

theorem costBaseSortName_mem_costWhole (source : CIGSLT) (name : String)
    (membership : name ∈
      source.theory.presentation.presentation.language.typeNames) :
    costBaseSortName name ∈ source.costWholeLanguage.typeNames := by
  rw [costWholeLanguage_typeNames, costCoreLanguage_typeNames,
    generatedLanguage_typeNames]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨name, membership, rfl⟩))

theorem costWrappedSortName_mem_costWhole (source : CIGSLT) :
    costWrappedSortName ∈ source.costWholeLanguage.typeNames := by
  rw [costWholeLanguage_typeNames, costCoreLanguage_typeNames,
    generatedLanguage_typeNames]
  exact List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem costSignatureSortName_mem_costWhole (source : CIGSLT) :
    costSignatureSortName ∈ source.costWholeLanguage.typeNames := by
  rw [costWholeLanguage_typeNames, costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by
    simp [costCoreSortSuffixes, costSignatureSortName])

theorem costTokenStackSortName_mem_costWhole (source : CIGSLT) :
    costTokenStackSortName ∈ source.costWholeLanguage.typeNames := by
  rw [costWholeLanguage_typeNames, costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by
    simp [costCoreSortSuffixes, costTokenStackSortName])

theorem costBaseTypeExpr_baseName_mem_costWhole (source : CIGSLT)
    (type : TypeExpr)
    (sourceKnown : ∀ name ∈ type.baseNames,
      name ∈ source.theory.presentation.presentation.language.typeNames)
    (name : String) (membership : name ∈ (costBaseTypeExpr type).baseNames) :
    name ∈ source.costWholeLanguage.typeNames := by
  rw [costBaseTypeExpr_baseNames] at membership
  rcases List.mem_map.mp membership with ⟨sourceName, sourceMembership, rfl⟩
  exact source.costBaseSortName_mem_costWhole sourceName
    (sourceKnown sourceName sourceMembership)

theorem costWrappedTypeExpr_baseName_mem_costWhole (source : CIGSLT)
    (type : TypeExpr)
    (sourceKnown : ∀ name ∈ type.baseNames,
      name ∈ source.theory.presentation.presentation.language.typeNames)
    (name : String)
    (membership : name ∈
      (costWrappedTypeExpr
        source.theory.presentation.interactingSort.1.name type).baseNames) :
    name ∈ source.costWholeLanguage.typeNames := by
  rw [costWrappedTypeExpr_baseNames] at membership
  rcases List.mem_map.mp membership with ⟨sourceName, sourceMembership, rfl⟩
  by_cases interacting :
      sourceName = source.theory.presentation.interactingSort.1.name
  · rw [if_pos interacting]
    exact source.costWrappedSortName_mem_costWhole
  · rw [if_neg interacting]
    exact source.costBaseSortName_mem_costWhole sourceName
      (sourceKnown sourceName sourceMembership)

/-- Every sort annotation in a base-fiber equation context names a sort of
the complete Cost language. -/
theorem costBaseEquationDecl_typeContext_baseName_mem (source : CIGSLT)
    (equation : Equation)
    (equationMembership : equation ∈
      source.theory.presentation.presentation.language.equations)
    (entry : String × TypeExpr)
    (entryMembership : entry ∈ (costBaseEquationDecl equation).typeContext)
    (name : String) (nameMembership : name ∈ entry.2.baseNames) :
    name ∈ source.costWholeLanguage.typeNames := by
  simp only [costBaseEquationDecl, mapEquationSchemaNames,
    mapTypeContextSchemaNames, costBaseEquation, mapEquation,
    mapTypeContext, List.map_map, List.mem_map] at entryMembership
  rcases entryMembership with ⟨sourceEntry, sourceEntryMembership, rfl⟩
  change name ∈
    (mapTypeExpr costBaseStaticSymbols sourceEntry.2).baseNames
      at nameMembership
  rw [mapTypeExpr_costBaseStaticSymbols] at nameMembership
  apply source.costBaseTypeExpr_baseName_mem_costWhole sourceEntry.2
  · intro sourceName sourceNameMembership
    exact equationTypeContext_baseName_mem_of_validate_eq_nil
      source.theory.presentation.presentation.language
      source.theory.presentation.presentation.valid equation
      equationMembership sourceEntry sourceEntryMembership sourceName
      sourceNameMembership
  · exact nameMembership

/-- Every sort annotation in a wrapped-fiber equation context names a sort
of the complete Cost language. -/
theorem costWrappedEquationDecl_typeContext_baseName_mem (source : CIGSLT)
    (equation : Equation)
    (equationMembership : equation ∈
      source.theory.presentation.presentation.language.equations)
    (entry : String × TypeExpr)
    (entryMembership : entry ∈
      (costWrappedEquationDecl source.theory equation).typeContext)
    (name : String) (nameMembership : name ∈ entry.2.baseNames) :
    name ∈ source.costWholeLanguage.typeNames := by
  simp only [costWrappedEquationDecl, mapEquationSchemaNames,
    mapTypeContextSchemaNames, costWrappedEquation, mapEquation,
    mapTypeContext, List.map_map, List.mem_map] at entryMembership
  rcases entryMembership with ⟨sourceEntry, sourceEntryMembership, rfl⟩
  change name ∈
    (mapTypeExpr (costWrappedStaticSymbols source.theory)
      sourceEntry.2).baseNames at nameMembership
  rw [mapTypeExpr_costWrappedStaticSymbols] at nameMembership
  apply source.costWrappedTypeExpr_baseName_mem_costWhole sourceEntry.2
  · intro sourceName sourceNameMembership
    exact equationTypeContext_baseName_mem_of_validate_eq_nil
      source.theory.presentation.presentation.language
      source.theory.presentation.presentation.valid equation
      equationMembership sourceEntry sourceEntryMembership sourceName
      sourceNameMembership
  · exact nameMembership

/-- Every base-fiber image of an authored equation passes the exact
per-equation validator of the generated Cost language. -/
theorem costBaseEquationDecl_validate (source : CIGSLT)
    (equation : Equation)
    (equationMembership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    source.costWholeLanguage.validateEquation
      (costBaseEquationDecl equation) = [] := by
  have premisesEmpty :=
    (source.equationsRetypable equation equationMembership).premiseFree
  have sorted :=
    source.costBaseEquationDecl_wellSorted equation equationMembership
  have wildcardClean := source.costMappedEquation_validateRulePatterns
    costBaseStaticSymbols equation equationMembership premisesEmpty sorted
  rcases sorted with ⟨type, leftTyped, rightTyped⟩
  have labelsNodup :
      (source.costWholeLanguage.terms.map (·.label)).Nodup := by
    rw [costWholeLanguage_terms]
    exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      source.costCoreLanguage source.costCoreLanguage_validate
  unfold LanguageDef.validateEquation
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro entry entryMembership
    exact LanguageDef.validateTypeExpr_eq_nil_of_baseNames
      source.costWholeLanguage.typeNames
      s!"equation {(costBaseEquationDecl equation).name}" entry.2
      (source.costBaseEquationDecl_typeContext_baseName_mem equation
        equationMembership entry entryMembership)
  · exact leftTyped.validatePatternConstructors_eq_nil labelsNodup
      (s!"equation {(costBaseEquationDecl equation).name}" ++ " lhs")
  · exact rightTyped.validatePatternConstructors_eq_nil labelsNodup
      (s!"equation {(costBaseEquationDecl equation).name}" ++ " rhs")
  · simp [costBaseEquationDecl_premises, premisesEmpty]
  · simpa [costBaseEquationDecl, mapEquationSchemaNames, costBaseEquation,
      mapEquation, premisesEmpty] using wildcardClean

/-- Every hereditary wrapped-fiber image of an authored equation passes the
exact per-equation validator of the generated Cost language. -/
theorem costWrappedEquationDecl_validate (source : CIGSLT)
    (equation : Equation)
    (equationMembership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    source.costWholeLanguage.validateEquation
      (costWrappedEquationDecl source.theory equation) = [] := by
  have premisesEmpty :=
    (source.equationsRetypable equation equationMembership).premiseFree
  have sorted :=
    source.costWrappedEquationDecl_wellSorted equation equationMembership
  have wildcardClean := source.costMappedEquation_validateRulePatterns
    (costWrappedStaticSymbols source.theory) equation equationMembership
      premisesEmpty sorted
  rcases sorted with ⟨type, leftTyped, rightTyped⟩
  have labelsNodup :
      (source.costWholeLanguage.terms.map (·.label)).Nodup := by
    rw [costWholeLanguage_terms]
    exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      source.costCoreLanguage source.costCoreLanguage_validate
  unfold LanguageDef.validateEquation
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro entry entryMembership
    exact LanguageDef.validateTypeExpr_eq_nil_of_baseNames
      source.costWholeLanguage.typeNames
      s!"equation {(costWrappedEquationDecl source.theory equation).name}"
      entry.2
      (source.costWrappedEquationDecl_typeContext_baseName_mem equation
        equationMembership entry entryMembership)
  · exact leftTyped.validatePatternConstructors_eq_nil labelsNodup
      (s!"equation {(costWrappedEquationDecl source.theory equation).name}" ++
        " lhs")
  · exact rightTyped.validatePatternConstructors_eq_nil labelsNodup
      (s!"equation {(costWrappedEquationDecl source.theory equation).name}" ++
        " rhs")
  · simp [costWrappedEquationDecl_premises, premisesEmpty]
  · simpa [costWrappedEquationDecl, mapEquationSchemaNames,
      costWrappedEquation, mapEquation, premisesEmpty] using wildcardClean

/-- Every equation selected from the generated static Cost theory is one of
the two validated images of an authored equation. -/
theorem costStaticEquation_validate (source : CIGSLT)
    (equation : Equation) (membership : equation ∈ source.costStaticEquations) :
    source.costWholeLanguage.validateEquation equation = [] := by
  rw [costStaticEquations, List.mem_append] at membership
  rcases membership with baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourceEquation, sourceMembership, rfl⟩
    exact source.costBaseEquationDecl_validate sourceEquation sourceMembership
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourceEquation, sourceMembership, rfl⟩
    exact source.costWrappedEquationDecl_validate sourceEquation
      sourceMembership

theorem costWholeRedexTypeContext_baseName_mem (source : CIGSLT)
    (entry : String × TypeExpr)
    (entryMembership : entry ∈ source.costWholeRedexTypeContext)
    (name : String) (nameMembership : name ∈ entry.2.baseNames) :
    name ∈ source.costWholeLanguage.typeNames := by
  simp only [costWholeRedexTypeContext, List.mem_append] at entryMembership
  rcases entryMembership with sourceEntry | administrativeEntry
  · simp only [costRetypedSourceContext, List.mem_map] at sourceEntry
    rcases sourceEntry with ⟨originalEntry, originalMembership, rfl⟩
    have sourceKnown : ∀ sourceName ∈ originalEntry.2.baseNames,
        sourceName ∈
          source.theory.presentation.presentation.language.typeNames := by
      intro sourceName sourceNameMembership
      exact rewriteTypeContext_baseName_mem_of_validate_eq_nil
        source.theory.presentation.presentation.language
        source.theory.presentation.presentation.valid
        source.theory.presentation.interactionRewrite.1
        source.cut.interactionRewrite_mem originalEntry originalMembership
        sourceName sourceNameMembership
    by_cases selected :
        originalEntry.1 = source.cut.program.continuationVariable.name ∨
          originalEntry.1 = source.cut.environment.continuationVariable.name
    · simp only [selected, ↓reduceIte] at nameMembership
      exact source.costWrappedTypeExpr_baseName_mem_costWhole
        originalEntry.2 sourceKnown name nameMembership
    · simp only [selected, ↓reduceIte] at nameMembership
      exact source.costBaseTypeExpr_baseName_mem_costWhole
        originalEntry.2 sourceKnown name nameMembership
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
      at administrativeEntry
    rcases administrativeEntry with equality | equality
    · subst entry
      simp only [TypeExpr.baseNames, List.mem_singleton] at nameMembership
      subst name
      exact source.costSignatureSortName_mem_costWhole
    · subst entry
      simp only [TypeExpr.baseNames, List.mem_singleton] at nameMembership
      subst name
      exact source.costTokenStackSortName_mem_costWhole

set_option maxHeartbeats 1000000 in
theorem costWholeRedexRewrite_validate (source : CIGSLT) :
    source.costWholeLanguage.validateRewrite
      source.costWholeRedexRewrite = [] := by
  have labelsNodup :
      (source.costWholeLanguage.terms.map (·.label)).Nodup := by
    rw [costWholeLanguage_terms]
    exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      source.costCoreLanguage source.costCoreLanguage_validate
  unfold LanguageDef.validateRewrite
  simp only [costWholeRedexRewrite, List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro entry membership
    exact LanguageDef.validateTypeExpr_eq_nil_of_baseNames
      source.costWholeLanguage.typeNames
      s!"rewrite {source.costWholeRedexRewrite.name}" entry.2
      (source.costWholeRedexTypeContext_baseName_mem entry membership)
  · simpa [costWholeLanguage_terms, costWholeRedexRewriteName] using
      source.costWholeRedexSource_hasType.validatePatternConstructors_eq_nil
        labelsNodup
        (toString "rewrite " ++ toString "$cost:rewrite:whole-redex" ++ " lhs")
  · simpa [costWholeLanguage_terms, costWholeRedexRewriteName] using
      source.costWholeRedexTarget_hasType.validatePatternConstructors_eq_nil
        labelsNodup
        (toString "rewrite " ++ toString "$cost:rewrite:whole-redex" ++ " rhs")
  · rfl
  · exact source.costWholeRedex_validateRulePatterns

/-- The generic Cost interaction is an ordinary validated language
presentation: its only reduction authority is the generated whole-redex
rewrite over the already validated Cost signature. -/
theorem costWholeLanguage_validate (source : CIGSLT) :
    source.costWholeLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  · simpa only [costWholeLanguage_typeNames] using
      LanguageDef.typeNames_nodup_of_validate_eq_nil
        source.costCoreLanguage source.costCoreLanguage_validate
  · simpa only [costWholeLanguage_terms] using
      LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        source.costCoreLanguage source.costCoreLanguage_validate
  · exact source.costStaticEquationNames_nodup
  · simp only [costWholeLanguage_rewrites, List.map_singleton,
      List.nodup_singleton]
  · intro term membership
    exact LanguageDef.termCategory_mem_of_validate_eq_nil
      source.costCoreLanguage source.costCoreLanguage_validate term
      (by simpa only [costWholeLanguage_terms] using membership)
  · intro term termMembership parameter parameterMembership name
      nameMembership
    exact LanguageDef.termParam_baseName_mem_of_validate_eq_nil
      source.costCoreLanguage source.costCoreLanguage_validate term
      (by simpa only [costWholeLanguage_terms] using termMembership)
      parameter parameterMembership name nameMembership
  · intro term membership
    exact Or.inl (costCoreTerm_syntaxPattern_eq_nil source term
      (by simpa only [costWholeLanguage_terms] using membership))
  · intro equation membership
    exact source.costStaticEquation_validate equation
      (by simpa only [costWholeLanguage_equations] using membership)
  · intro rewrite membership
    simp only [costWholeLanguage_rewrites, List.mem_singleton] at membership
    subst rewrite
    exact source.costWholeRedexRewrite_validate

/-- The generated reflective interpretation validates independently against
the generated five-field Cost language. -/
theorem costWholeReflectionProfile_validate (source : CIGSLT) :
    Mettapedia.OSLF.MeTTaIL.Reflection.validate source.costWholeLanguage
      source.costWholeReflectionProfile = [] := by
  unfold Mettapedia.OSLF.MeTTaIL.Reflection.validate
  simp only [costWholeReflectionProfile,
    source.costStaticReflectivePresentationNames_nodup,
    source.costInteractionReflectiveRuleNames_nodup, if_true,
    List.nil_append, List.append_eq_nil_iff]
  constructor
  · apply List.flatMap_eq_nil_iff.mpr
    intro declaration membership
    exact source.costStaticReflectivePresentation_validate declaration
      (by simpa only [costWholeReflectionProfile_presentations] using
        membership)
  · apply List.flatMap_eq_nil_iff.mpr
    intro declaration membership
    exact source.costInteractionReflectiveRule_validate declaration
      (by simpa only [costWholeReflectionProfile_rules] using membership)

/-- The admitted reflection fibre over the generated Cost core. -/
def costWholeAdmittedReflection (source : CIGSLT) :
    ReflectionExtension.AdmittedProfile source.costWholeLanguage :=
  ⟨source.costWholeReflectionProfile,
    source.costWholeReflectionProfile_validate⟩

/-- The validated structural output of the generic Cost interaction layer. -/
def costWholePresentation (source : CIGSLT) : ValidatedLanguageDef where
  language := source.costWholeLanguage
  valid := source.costWholeLanguage_validate

namespace Morphism

/-- A continued-theory morphism carries the complete generated Cost
presentation structurally: inherited and apparatus declarations follow the
Cost-core map, static equations follow the authored source equations, and the
single funded interaction follows the selected continuation cut. -/
def costWholeStructural {source target : CIGSLT}
    (morphism : source.Morphism target) :
    StructuralMorphism source.costWholePresentation
      target.costWholePresentation where
  symbols := costPresentationSymbols
    morphism.underlying.structural.structural.symbols
  mapsTypes declaration membership := by
    change List.Mem declaration source.costCoreLanguage.types at membership
    change List.Mem (mapTypeDecl
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        declaration) target.costCoreLanguage.types
    exact morphism.costCoreStructural.mapsTypes declaration membership
  mapsTerms constructor membership := by
    change List.Mem constructor source.costCoreLanguage.terms at membership
    change List.Mem (mapGrammarRule
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        constructor) target.costCoreLanguage.terms
    exact morphism.costCoreStructural.mapsTerms constructor membership
  mapsEquations equation membership := by
    change List.Mem equation source.costStaticEquations at membership
    change List.Mem (mapEquation
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        equation) target.costStaticEquations
    exact morphism.mapsCostStaticEquations equation membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [source.costWholeRedexRewrite] at membership
    change List.Mem (mapRewriteRule
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        rewrite) [target.costWholeRedexRewrite]
    cases membership with
    | head =>
        rw [morphism.map_costWholeRedexRewrite]
        exact List.Mem.head _
    | tail _ impossible => cases impossible

end Morphism

/-- The complete declaration-derived Cost presentation is functorial on
continued interactive theories. -/
def costWholeFunctor : CategoryTheory.Functor CIGSLT ValidatedLanguageDef where
  obj source := source.costWholePresentation
  map morphism := morphism.costWholeStructural
  map_id source := by
    apply StructuralMorphism.ext
    exact costPresentationSymbols_id
  map_comp first second := by
    apply StructuralMorphism.ext
    exact costPresentationSymbols_comp
      first.underlying.structural.structural.symbols
      second.underlying.structural.structural.symbols

end CIGSLT

end Mettapedia.GSLT.LanguageDef
