import Mettapedia.GSLT.LanguageDef.InteractionCut

/-!
# Declaration-derived continuation retyping

Wrappability is a sorting statement, not a callback or policy flag.  This
module constructs the exact intermediate signature used to ask that
statement.  Source declarations are placed in a tagged base namespace;
selected interaction continuations are re-sorted to a fresh wrapped sort;
and the cut-derived hereditary closure gives every non-principal constructor
a wrapped copy.  The authored interaction rule remains the source of the
contractum.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism
open WellSorted

/-! ## Collision-free generated namespaces -/

def costBaseSortTag : String := "$cost:base-sort:"
def costBaseConstructorTag : String := "$cost:base-constructor:"
def costWrappedConstructorTag : String := "$cost:wrapped-constructor:"

def costBaseSortName (name : String) : String := costBaseSortTag ++ name
def costBaseConstructorName (name : String) : String :=
  costBaseConstructorTag ++ name
def costWrappedConstructorName (name : String) : String :=
  costWrappedConstructorTag ++ name
def costWrappedSortName : String := "$cost:wrapped-term"

/-- Embed source sorts and constructors into their reserved base namespaces.
Rule-local metavariable names remain unchanged. -/
def costBasePresentationSymbols : PresentationSymbols where
  sort := costBaseSortName
  constructor := costBaseConstructorName
  relation := id
  equation := id
  rewrite := id
  reflective := id
  reflectiveRule := id

theorem costBaseSortName_injective : Function.Injective costBaseSortName := by
  intro left right equality
  exact (String.append_right_inj "$cost:base-sort:").mp equality

theorem costBaseConstructorName_injective :
    Function.Injective costBaseConstructorName := by
  intro left right equality
  exact (String.append_right_inj "$cost:base-constructor:").mp equality

theorem costWrappedConstructorName_injective :
    Function.Injective costWrappedConstructorName := by
  intro left right equality
  exact (String.append_right_inj "$cost:wrapped-constructor:").mp equality

theorem costBaseSortName_ne_wrapped (name : String) :
    costBaseSortName name ≠ costWrappedSortName := by
  intro equality
  change ("$cost:" ++ "base-sort:") ++ name =
    "$cost:" ++ "wrapped-term" at equality
  rw [String.append_assoc] at equality
  have stripped : "base-sort:" ++ name = "wrapped-term" :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

theorem costBaseConstructorName_ne_wrapped (base wrapped : String) :
    costBaseConstructorName base ≠ costWrappedConstructorName wrapped := by
  intro equality
  change ("$cost:" ++ "base-constructor:") ++ base =
    ("$cost:" ++ "wrapped-constructor:") ++ wrapped at equality
  rw [String.append_assoc, String.append_assoc] at equality
  have stripped : "base-constructor:" ++ base =
      "wrapped-constructor:" ++ wrapped :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

/-- Embed every source type in the tagged base namespace. -/
def costBaseTypeExpr : TypeExpr → TypeExpr
  | .base sort => .base (costBaseSortName sort)
  | .arrow domain codomain =>
      .arrow (costBaseTypeExpr domain) (costBaseTypeExpr codomain)
  | .multiBinder body => .multiBinder (costBaseTypeExpr body)
  | .collection collectionType element =>
      .collection collectionType (costBaseTypeExpr element)

@[simp]
theorem costBaseTypeExpr_baseNames (type : TypeExpr) :
    (costBaseTypeExpr type).baseNames =
      type.baseNames.map costBaseSortName := by
  induction type <;>
    simp_all [costBaseTypeExpr, TypeExpr.baseNames, List.map_append]

/-- Retype occurrences of the interacting sort to the wrapped-term sort,
while embedding every other source sort in the tagged base namespace. -/
def costWrappedTypeExpr (interactingSort : String) : TypeExpr → TypeExpr
  | .base sort =>
      if sort = interactingSort then .base costWrappedSortName
      else .base (costBaseSortName sort)
  | .arrow domain codomain =>
      .arrow (costWrappedTypeExpr interactingSort domain)
        (costWrappedTypeExpr interactingSort codomain)
  | .multiBinder body =>
      .multiBinder (costWrappedTypeExpr interactingSort body)
  | .collection collectionType element =>
      .collection collectionType
        (costWrappedTypeExpr interactingSort element)

@[simp]
theorem costWrappedTypeExpr_baseNames (interactingSort : String)
    (type : TypeExpr) :
    (costWrappedTypeExpr interactingSort type).baseNames =
      type.baseNames.map fun sort =>
        if sort = interactingSort then costWrappedSortName
        else costBaseSortName sort := by
  induction type with
  | base sort =>
      by_cases equality : sort = interactingSort <;>
        simp [costWrappedTypeExpr, TypeExpr.baseNames, equality]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [costWrappedTypeExpr, TypeExpr.baseNames, domainHypothesis,
        codomainHypothesis, List.map_append]
  | multiBinder body inductionHypothesis =>
      simp [costWrappedTypeExpr, TypeExpr.baseNames, inductionHypothesis]
  | collection collectionType body inductionHypothesis =>
      simp [costWrappedTypeExpr, TypeExpr.baseNames, inductionHypothesis]

/-- Map only the type annotation of one constructor parameter. -/
def mapParameterType (mapType : TypeExpr → TypeExpr) : TermParam → TermParam
  | .simple name type => .simple name (mapType type)
  | .abstractionNamed binder name type =>
      .abstractionNamed binder name (mapType type)
  | .multiAbstractionNamed binders name type =>
      .multiAbstractionNamed binders name (mapType type)

@[simp]
theorem mapParameterType_typeExpr (mapType : TypeExpr → TypeExpr)
    (parameter : TermParam) :
    TermParam.typeExpr (mapParameterType mapType parameter) =
      mapType (TermParam.typeExpr parameter) := by
  cases parameter <;> rfl

/-- Retyping a selected continuation sends its interacting result to the
fresh wrapped carrier, independently of whether the parameter is plain,
single-binding, or multi-binding. -/
theorem continuationResult?_mapParameterType_costWrapped
    (interactingSort : String) (parameter : TermParam)
    (selected : continuationResult? parameter =
      some (.base interactingSort)) :
    continuationResult?
        (mapParameterType (costWrappedTypeExpr interactingSort) parameter) =
      some (.base costWrappedSortName) := by
  cases parameter with
  | simple name type =>
      cases type <;>
        simp_all [mapParameterType, continuationResult?, WellSorted.parameterType?,
          costWrappedTypeExpr]
  | abstractionNamed binder name type =>
      cases type <;>
        simp_all [mapParameterType, continuationResult?, WellSorted.parameterType?,
          costWrappedTypeExpr]
  | multiAbstractionNamed binders name type =>
      cases type <;>
        simp_all [mapParameterType, continuationResult?, WellSorted.parameterType?,
          costWrappedTypeExpr]
      case arrow domain codomain =>
        cases domain <;>
          simp_all [costWrappedTypeExpr]

/-- Retype one indexed parameter of a base constructor.  Naming this action
makes explicit that selection is positional declaration data, not a traversal
policy hidden in the generated grammar. -/
def costBaseParameter {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) (entry : TermParam × Nat) : TermParam :=
  if isSelectedContinuation cut constructor entry.2 then
    mapParameterType
      (costWrappedTypeExpr theory.presentation.interactingSort.1.name) entry.1
  else
    mapParameterType costBaseTypeExpr entry.1

/-- The base copy of a source constructor.  Exactly the selected continuation
positions are re-sorted; every other parameter remains in the base copy. -/
def costBaseConstructor {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) : GrammarRule :=
  { constructor with
    label := costBaseConstructorName constructor.label
    category := costBaseSortName constructor.category
    params := constructor.params.zipIdx.map (costBaseParameter cut constructor)
    syntaxPattern := []
    evalPolicy? := none }

@[simp]
theorem costBaseConstructor_label {theory : IGSLT}
    (cut : InteractionCutPresentation theory) (constructor : GrammarRule) :
    (costBaseConstructor cut constructor).label =
      costBaseConstructorName constructor.label :=
  rfl

@[simp]
theorem costBaseConstructor_params_length {theory : IGSLT}
    (cut : InteractionCutPresentation theory) (constructor : GrammarRule) :
    (costBaseConstructor cut constructor).params.length =
      constructor.params.length := by
  simp [costBaseConstructor]

theorem costBaseConstructor_parameter {theory : IGSLT}
    (cut : InteractionCutPresentation theory) (constructor : GrammarRule)
    (index : Nat) (inBounds : index < constructor.params.length) :
    (costBaseConstructor cut constructor).params[index]'(by
        simpa using inBounds) =
      costBaseParameter cut constructor (constructor.params[index], index) := by
  simp [costBaseConstructor, List.getElem_map, List.getElem_zipIdx]

/-- Continuation retyping changes sort annotations but not whether a
constructor uses the bare single-collection representation. -/
theorem usesBareCollection_costBaseConstructor_iff {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) :
    UsesBareCollection (costBaseConstructor cut constructor) ↔
      UsesBareCollection constructor := by
  cases constructor with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases parameters with
      | nil => simp [UsesBareCollection, costBaseConstructor]
      | cons parameter parameters =>
          cases parameters with
          | nil =>
              cases parameter with
              | simple name type =>
                  simp only [UsesBareCollection, costBaseConstructor,
                    costBaseParameter, List.zipIdx_cons, List.map_cons,
                    List.singleton_inj, TermParam.simple.injEq]
                  split <;> cases type <;>
                    simp [mapParameterType, costWrappedTypeExpr,
                      costBaseTypeExpr] ;
                    split <;> simp
              | abstractionNamed binder name type =>
                  simp only [UsesBareCollection, costBaseConstructor,
                    costBaseParameter, List.zipIdx_cons, List.map_cons]
                  split <;> simp [mapParameterType]
              | multiAbstractionNamed binders name type =>
                  simp only [UsesBareCollection, costBaseConstructor,
                    costBaseParameter, List.zipIdx_cons, List.map_cons]
                  split <;> simp [mapParameterType]
          | cons second rest =>
              simp [UsesBareCollection, costBaseConstructor]

/-- A wrapped contractum copy of a source constructor.  Every occurrence of
the interacting sort in its profile is re-sorted uniformly. -/
def costWrappedConstructor {theory : IGSLT}
    (constructor : GrammarRule) : GrammarRule :=
  { constructor with
    label := costWrappedConstructorName constructor.label
    category :=
      if constructor.category = theory.presentation.interactingSort.1.name then
        costWrappedSortName
      else
        costBaseSortName constructor.category
    params := constructor.params.map
      (mapParameterType
        (costWrappedTypeExpr theory.presentation.interactingSort.1.name))
    syntaxPattern := []
    evalPolicy? := none }

@[simp]
theorem costWrappedConstructor_label {theory : IGSLT}
    (constructor : GrammarRule) :
    (costWrappedConstructor (theory := theory) constructor).label =
      costWrappedConstructorName constructor.label :=
  rfl

/-- Uniform hereditary retyping preserves whether a constructor is represented
by a bare single collection parameter. -/
theorem usesBareCollection_costWrappedConstructor_iff {theory : IGSLT}
    (constructor : GrammarRule) :
    UsesBareCollection (costWrappedConstructor (theory := theory) constructor) ↔
      UsesBareCollection constructor := by
  constructor
  · rintro ⟨parameterName, collectionType, elementType, mappedShape⟩
    cases constructor with
    | mk label category parameters syntaxPattern evalPolicy =>
      simp only [costWrappedConstructor] at mappedShape
      cases parameters with
      | nil => simp at mappedShape
      | cons parameter parameters =>
          cases parameters with
          | nil =>
              cases parameter with
              | simple originalName originalType =>
                  cases originalType with
                  | base sort =>
                      by_cases selected :
                          sort = theory.presentation.interactingSort.1.name <;>
                        simp_all [mapParameterType, costWrappedTypeExpr]
                  | arrow domain codomain =>
                      simp_all [mapParameterType, costWrappedTypeExpr]
                  | multiBinder body =>
                      simp_all [mapParameterType, costWrappedTypeExpr]
                  | collection originalCollection originalElement =>
                      simp_all [mapParameterType, costWrappedTypeExpr,
                        UsesBareCollection]
              | abstractionNamed binder body type =>
                  simp [mapParameterType] at mappedShape
              | multiAbstractionNamed binders body type =>
                  simp [mapParameterType] at mappedShape
          | cons next rest => simp at mappedShape
  · rintro ⟨parameterName, collectionType, elementType, shape⟩
    refine ⟨parameterName, collectionType,
      costWrappedTypeExpr theory.presentation.interactingSort.1.name
        elementType, ?_⟩
    simp [costWrappedConstructor, shape, mapParameterType,
      costWrappedTypeExpr]

/-! ## Wrappability plan and compiled sorting problem -/

/-- Finite declaration data needed to retype the exact authored contractum.
Principal interaction constructors are excluded from the wrapped closure:
otherwise the transformed contractum could expose a fresh unguarded redex. -/
def ResidualCovered {theory : IGSLT}
    (wrappedConstructors :
      List (AuthoredConstructor theory.presentation.presentation))
    {contractum : Pattern} :
    ResidualRepresentation
      (presentation := theory.presentation.presentation) contractum → Prop
  | .constructor residual _ => residual ∈ wrappedConstructors
  | .substitution _ _ => True

/-- The hereditary continuation closure is determined by the ordered cut:
every authored constructor except its two introductions receives a wrapped
copy.  It is declaration-derived data, not a configurable traversal policy. -/
def continuationConstructors {theory : IGSLT}
    (cut : InteractionCutPresentation theory) :
    List (AuthoredConstructor theory.presentation.presentation) :=
  theory.presentation.presentation.language.terms.attach.filter fun constructor =>
    decide (constructor ≠ cut.program.constructor ∧
      constructor ≠ cut.environment.constructor)

/-- A continuation plan carries only the substantive closure obligation: the
authored contractum is represented by the hereditary signature induced by the
cut. -/
structure ContinuationRetypingPlan {theory : IGSLT}
    (cut : InteractionCutPresentation theory) where
  residualCovered : ResidualCovered (continuationConstructors cut) cut.residual

namespace ContinuationRetypingPlan

@[simp]
theorem mem_continuationConstructors_iff {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : AuthoredConstructor theory.presentation.presentation) :
    constructor ∈ continuationConstructors cut ↔
      constructor ≠ cut.program.constructor ∧
        constructor ≠ cut.environment.constructor := by
  constructor
  · intro membership
    exact of_decide_eq_true
      (List.mem_filter.mp membership).2
  · intro inequalities
    apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ constructor, ?_⟩
    exact decide_eq_true inequalities

/-- The exact hereditary constructor closure induced by this plan's cut. -/
def wrappedConstructors {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (_plan : ContinuationRetypingPlan cut) :
    List (AuthoredConstructor theory.presentation.presentation) :=
  continuationConstructors cut

@[simp]
theorem mem_wrappedConstructors_iff {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (constructor : AuthoredConstructor theory.presentation.presentation) :
    constructor ∈ plan.wrappedConstructors ↔
      constructor ≠ cut.program.constructor ∧
        constructor ≠ cut.environment.constructor := by
  exact mem_continuationConstructors_iff cut constructor

/-- Validation makes the declaration-derived hereditary closure
duplicate-free. -/
theorem noDuplicates {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    plan.wrappedConstructors.Nodup := by
  unfold wrappedConstructors continuationConstructors
  apply List.Nodup.filter
  apply List.nodup_attach.mpr
  exact List.Nodup.of_map (fun constructor => constructor.label)
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      theory.presentation.presentation.language
      theory.presentation.presentation.valid)

theorem programNotWrapped {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    cut.program.constructor ∉ plan.wrappedConstructors := by
  rw [plan.mem_wrappedConstructors_iff]
  exact fun inequalities => inequalities.1 rfl

theorem environmentNotWrapped {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    cut.environment.constructor ∉ plan.wrappedConstructors := by
  rw [plan.mem_wrappedConstructors_iff]
  exact fun inequalities => inequalities.2 rfl

/-- Labels of the exact source constructors receiving wrapped copies. -/
def wrappedLabels {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : List String :=
  plan.wrappedConstructors.map (·.1.label)

/-- Source types embedded in the base namespace, followed by the one new
wrapped-term sort. -/
def generatedTypes {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (_plan : ContinuationRetypingPlan cut) : List TypeDecl :=
  (theory.presentation.presentation.language.types.map fun declaration =>
    { declaration with name := costBaseSortName declaration.name }) ++
  [TypeDecl.plain costWrappedSortName]

/-- The declaration-level signature in which wrappability is checked. -/
def generatedLanguage {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : LanguageDef :=
  { name := "$cost:continuation-signature:" ++
      theory.presentation.presentation.language.name
    types := plan.generatedTypes
    terms :=
      theory.presentation.presentation.language.terms.map
          (costBaseConstructor cut) ++
        plan.wrappedConstructors.map
          (fun constructor =>
            costWrappedConstructor (theory := theory) constructor.1)
    equations := []
    rewrites := [] }

/-- The authored envelope around the interaction core remains a signature
context after the exact continuation retyping.  This is the structural
closure condition needed to reconstruct the generated interaction cut; it
does not grant the envelope any reduction authority. -/
def SourceEnvelopeRetypable {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : Prop :=
  SignatureContext plan.generatedLanguage
    (costBaseSortName cut.coreContact.sort.1.name)
    (costBaseSortName theory.presentation.interactingSort.1.name)
    (CIGSLT.mapOneHoleContext costBasePresentationSymbols
      cut.sourceShape.envelope)

@[simp]
theorem generatedLanguage_typeNames {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.typeNames =
      theory.presentation.presentation.language.typeNames.map
          costBaseSortName ++
        [costWrappedSortName] := by
  simp [generatedLanguage, generatedTypes, LanguageDef.typeNames,
    TypeDecl.plain, List.map_map]

/-- The tagged source sorts and the wrapped sort form a duplicate-free
generated namespace. -/
theorem generatedTypeNames_nodup {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.typeNames.Nodup := by
  rw [generatedLanguage_typeNames, List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · exact (LanguageDef.typeNames_nodup_of_validate_eq_nil
      theory.presentation.presentation.language
      theory.presentation.presentation.valid).map
        costBaseSortName_injective
  · intro generated generatedMembership reserved reservedMembership
    simp only [List.mem_singleton] at reservedMembership
    subst reserved
    simp only [List.mem_map] at generatedMembership
    rcases generatedMembership with ⟨sourceName, _, rfl⟩
    exact costBaseSortName_ne_wrapped sourceName

theorem authoredConstructorLabel_injective
    (presentation : ValidatedLanguageDef) :
    Function.Injective
      (fun constructor : AuthoredConstructor presentation =>
        constructor.1.label) := by
  intro left right equality
  apply Subtype.ext
  exact List.inj_on_of_nodup_map
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      presentation.language presentation.valid)
    left.2 right.2 equality

/-- Membership in the label projection is equivalent to membership of the
exact authored constructor.  Validation makes constructor labels unique, so
this projection loses no identity information. -/
theorem mem_wrappedLabels_iff {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (constructor : AuthoredConstructor theory.presentation.presentation) :
    constructor.1.label ∈ plan.wrappedLabels ↔
      constructor ∈ plan.wrappedConstructors := by
  constructor
  · intro labelMembership
    rcases List.mem_map.mp labelMembership with
      ⟨wrapped, wrappedMembership, labelEquality⟩
    have constructorEquality : wrapped = constructor :=
      authoredConstructorLabel_injective
        theory.presentation.presentation labelEquality
    simpa [constructorEquality] using wrappedMembership
  · intro constructorMembership
    exact List.mem_map.mpr ⟨constructor, constructorMembership, rfl⟩

theorem generatedLanguage_constructorLabels {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.terms.map (·.label) =
      (theory.presentation.presentation.language.terms.map (·.label)).map
          costBaseConstructorName ++
        plan.wrappedLabels.map costWrappedConstructorName := by
  simp only [generatedLanguage, List.map_append]
  congr 1
  · simp only [List.map_map]
    apply List.map_congr_left
    intro constructor _membership
    rfl
  · simp only [wrappedLabels, List.map_map]
    apply List.map_congr_left
    intro constructor _membership
    rfl

/-- Base and wrapped constructor copies remain duplicate-free and occupy
disjoint generated namespaces. -/
theorem generatedConstructorLabels_nodup {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    (plan.generatedLanguage.terms.map (·.label)).Nodup := by
  rw [generatedLanguage_constructorLabels, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      theory.presentation.presentation.language
      theory.presentation.presentation.valid).map
        costBaseConstructorName_injective
  · exact (plan.noDuplicates.map
      (authoredConstructorLabel_injective
        theory.presentation.presentation)).map
          costWrappedConstructorName_injective
  · intro base baseMembership wrapped wrappedMembership
    simp only [List.mem_map] at baseMembership wrappedMembership
    rcases baseMembership with ⟨sourceBase, _, rfl⟩
    rcases wrappedMembership with ⟨sourceWrapped, _, rfl⟩
    exact costBaseConstructorName_ne_wrapped sourceBase sourceWrapped

/-- Every generated constructor returns one of the generated sorts. -/
theorem generatedTerm_category_mem {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (term : GrammarRule)
    (membership : term ∈ plan.generatedLanguage.terms) :
    term.category ∈ plan.generatedLanguage.typeNames := by
  rw [generatedLanguage_typeNames]
  simp only [generatedLanguage, List.mem_append] at membership
  rcases membership with baseMembership | wrappedMembership
  · simp only [List.mem_map] at baseMembership
    rcases baseMembership with ⟨source, sourceMembership, rfl⟩
    change costBaseSortName source.category ∈ _ ++ _
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨source.category, ?_, rfl⟩
    exact LanguageDef.termCategory_mem_of_validate_eq_nil
      theory.presentation.presentation.language
      theory.presentation.presentation.valid source sourceMembership
  · simp only [List.mem_map] at wrappedMembership
    rcases wrappedMembership with ⟨source, sourceMembership, rfl⟩
    change (if source.1.category =
        theory.presentation.interactingSort.1.name then
          costWrappedSortName else costBaseSortName source.1.category) ∈ _ ++ _
    split
    · exact List.mem_append_right _ (by simp)
    · apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨source.1.category, ?_, rfl⟩
      exact LanguageDef.termCategory_mem_of_validate_eq_nil
        theory.presentation.presentation.language
        theory.presentation.presentation.valid source.1 source.2

private theorem costBaseConstructor_parameter_baseName_mem
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (source : GrammarRule)
    (sourceMembership :
      source ∈ theory.presentation.presentation.language.terms)
    (parameter : TermParam)
    (parameterMembership : parameter ∈ (costBaseConstructor cut source).params)
    (name : String)
    (nameMembership : name ∈ (TermParam.typeExpr parameter).baseNames) :
    name ∈ plan.generatedLanguage.typeNames := by
  rw [generatedLanguage_typeNames]
  simp only [costBaseConstructor] at parameterMembership
  rcases List.mem_map.mp parameterMembership with
    ⟨sourceEntry, sourceEntryMembership, rfl⟩
  have sourceParameterMembership : sourceEntry.1 ∈ source.params :=
    List.fst_mem_of_mem_zipIdx sourceEntryMembership
  simp only [costBaseParameter] at nameMembership
  split at nameMembership
  · rw [mapParameterType_typeExpr, costWrappedTypeExpr_baseNames]
      at nameMembership
    rcases List.mem_map.mp nameMembership with
      ⟨sourceName, sourceNameMembership, rfl⟩
    split
    · exact List.mem_append_right _ (by simp)
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨sourceName,
        LanguageDef.termParam_baseName_mem_of_validate_eq_nil
          theory.presentation.presentation.language
          theory.presentation.presentation.valid source sourceMembership
          sourceEntry.1 sourceParameterMembership sourceName
          sourceNameMembership, rfl⟩
  · rw [mapParameterType_typeExpr, costBaseTypeExpr_baseNames]
      at nameMembership
    rcases List.mem_map.mp nameMembership with
      ⟨sourceName, sourceNameMembership, rfl⟩
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨sourceName,
      LanguageDef.termParam_baseName_mem_of_validate_eq_nil
        theory.presentation.presentation.language
        theory.presentation.presentation.valid source sourceMembership
        sourceEntry.1 sourceParameterMembership sourceName
        sourceNameMembership, rfl⟩

private theorem costWrappedConstructor_parameter_baseName_mem
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (source : AuthoredConstructor theory.presentation.presentation)
    (parameter : TermParam)
    (parameterMembership : parameter ∈
      (costWrappedConstructor (theory := theory) source.1).params)
    (name : String)
    (nameMembership : name ∈ (TermParam.typeExpr parameter).baseNames) :
    name ∈ plan.generatedLanguage.typeNames := by
  rw [generatedLanguage_typeNames]
  simp only [costWrappedConstructor, List.mem_map] at parameterMembership
  rcases parameterMembership with
    ⟨sourceParameter, sourceParameterMembership, rfl⟩
  rw [mapParameterType_typeExpr, costWrappedTypeExpr_baseNames]
    at nameMembership
  rcases List.mem_map.mp nameMembership with
    ⟨sourceName, sourceNameMembership, rfl⟩
  split
  · exact List.mem_append_right _ (by simp)
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨sourceName,
      LanguageDef.termParam_baseName_mem_of_validate_eq_nil
        theory.presentation.presentation.language
        theory.presentation.presentation.valid source.1 source.2
        sourceParameter sourceParameterMembership sourceName
        sourceNameMembership, rfl⟩

/-- Every sort referenced by a generated constructor parameter is declared
by the generated signature. -/
theorem generatedTerm_parameter_baseName_mem {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (term : GrammarRule)
    (termMembership : term ∈ plan.generatedLanguage.terms)
    (parameter : TermParam) (parameterMembership : parameter ∈ term.params)
    (name : String)
    (nameMembership : name ∈ (TermParam.typeExpr parameter).baseNames) :
    name ∈ plan.generatedLanguage.typeNames := by
  simp only [generatedLanguage, List.mem_append] at termMembership
  rcases termMembership with baseMembership | wrappedMembership
  · simp only [List.mem_map] at baseMembership
    rcases baseMembership with ⟨source, sourceMembership, rfl⟩
    exact costBaseConstructor_parameter_baseName_mem plan source
      sourceMembership parameter parameterMembership name nameMembership
  · simp only [List.mem_map] at wrappedMembership
    rcases wrappedMembership with ⟨source, sourceMembership, rfl⟩
    exact costWrappedConstructor_parameter_baseName_mem plan source
      parameter parameterMembership name nameMembership

/-- Generated typing constructors intentionally carry no parser notation or
host evaluator policy.  They are the internal signature derived from the
authored presentation, not a second surface language. -/
theorem generatedTerm_syntaxPattern_eq_nil {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (term : GrammarRule)
    (termMembership : term ∈ plan.generatedLanguage.terms) :
    term.syntaxPattern = [] := by
  simp only [generatedLanguage, List.mem_append] at termMembership
  rcases termMembership with baseMembership | wrappedMembership
  · simp only [List.mem_map] at baseMembership
    rcases baseMembership with ⟨source, _sourceMembership, rfl⟩
    rfl
  · simp only [List.mem_map] at wrappedMembership
    rcases wrappedMembership with ⟨source, _sourceMembership, rfl⟩
    rfl

/-- The declaration-derived continuation signature passes the same
`LanguageDef.validate` gate as every authored language definition. -/
theorem generatedLanguage_validate {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact generatedTypeNames_nodup plan
  · exact generatedConstructorLabels_nodup plan
  · exact generatedTerm_category_mem plan
  · exact generatedTerm_parameter_baseName_mem plan
  · intro term termMembership
    exact Or.inl (generatedTerm_syntaxPattern_eq_nil plan term termMembership)

/-- The validated generated signature retains its derivation from the exact
source `LanguageDef`; it is not independently authored data. -/
def generatedPresentation {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : ValidatedLanguageDef where
  language := plan.generatedLanguage
  valid := generatedLanguage_validate plan

/-- Every authored source constructor has its retyped base copy in the
generated continuation signature. -/
theorem costBaseConstructor_mem_generated {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (constructor : GrammarRule)
    (membership :
      constructor ∈ theory.presentation.presentation.language.terms) :
    costBaseConstructor cut constructor ∈ plan.generatedLanguage.terms :=
  List.mem_append_left _ (List.mem_map.mpr ⟨constructor, membership, rfl⟩)

/-- Every constructor selected for wrapped residual closure has its wrapped
copy in the generated continuation signature. -/
theorem costWrappedConstructor_mem_generated {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (constructor : AuthoredConstructor theory.presentation.presentation)
    (membership : constructor ∈ plan.wrappedConstructors) :
    costWrappedConstructor (theory := theory) constructor.1 ∈
      plan.generatedLanguage.terms :=
  List.mem_append_right _
    (List.mem_map.mpr ⟨constructor, membership, rfl⟩)

/-- Every authored source sort has its tagged base copy in the generated
continuation signature. -/
theorem costBaseSortName_mem_generated {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (sort : String)
    (membership :
      sort ∈ theory.presentation.presentation.language.typeNames) :
    costBaseSortName sort ∈ plan.generatedLanguage.typeNames := by
  rw [generatedLanguage_typeNames]
  exact List.mem_append_left _
    (List.mem_map.mpr ⟨sort, membership, rfl⟩)

/-- The distinguished wrapped sort belongs to every generated continuation
signature. -/
theorem costWrappedSortName_mem_generated {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    costWrappedSortName ∈ plan.generatedLanguage.typeNames := by
  rw [generatedLanguage_typeNames]
  simp

/-- A source constructor's tagged base label resolves uniquely in the
generated continuation signature. -/
theorem costBaseConstructor_filter_generated {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (constructor : GrammarRule)
    (membership :
      constructor ∈ theory.presentation.presentation.language.terms) :
    plan.generatedLanguage.terms.filter
        (fun candidate =>
          candidate.label == (costBaseConstructor cut constructor).label) =
      [costBaseConstructor cut constructor] := by
  exact LanguageDef.filter_terms_by_label_eq_singleton
    plan.generatedLanguage.terms (costBaseConstructor cut constructor)
    (generatedConstructorLabels_nodup plan)
    (plan.costBaseConstructor_mem_generated constructor membership)

/-- A selected residual constructor's wrapped label resolves uniquely in the
generated continuation signature. -/
theorem costWrappedConstructor_filter_generated {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (constructor : AuthoredConstructor theory.presentation.presentation)
    (membership : constructor ∈ plan.wrappedConstructors) :
    plan.generatedLanguage.terms.filter
        (fun candidate => candidate.label ==
          (costWrappedConstructor (theory := theory) constructor.1).label) =
      [costWrappedConstructor (theory := theory) constructor.1] := by
  exact LanguageDef.filter_terms_by_label_eq_singleton
    plan.generatedLanguage.terms
    (costWrappedConstructor (theory := theory) constructor.1)
    (generatedConstructorLabels_nodup plan)
    (plan.costWrappedConstructor_mem_generated constructor membership)

end ContinuationRetypingPlan

namespace ContinuationStableContext

private theorem take_getElem_drop {α : Type*} (elements : List α)
    (index : Nat) (inBounds : index < elements.length) :
    elements.take index ++ elements[index] :: elements.drop (index + 1) =
      elements := by
  rw [List.getElem_cons_drop inBounds]
  exact List.take_append_drop index elements

/-- A context whose hole path avoids the two selected continuation slots
survives declaration-derived continuation retyping entirely in the tagged
base fiber. -/
theorem retype {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    {source target : String} {context : OneHoleContext}
    (stable : ContinuationStableContext cut source target context) :
    SignatureContext plan.generatedLanguage
      (costBaseSortName source) (costBaseSortName target)
      (CIGSLT.mapOneHoleContext costBasePresentationSymbols context) := by
  induction stable with
  | hole => exact .hole _
  | @simpleArg parameter rule parameterName beforeParams afterParams
      before after inner ruleMembership parameters beforeLength afterLength
      notSelected innerStable inductionHypothesis =>
      have sourceInBounds : beforeParams.length < rule.params.length := by
        rw [parameters]
        simp
      have sourceAt :
          rule.params[beforeParams.length]'sourceInBounds =
            .simple parameterName (.base parameter) := by
        have sourceAtOption :
            rule.params[beforeParams.length]? =
              some (.simple parameterName (.base parameter)) := by
          rw [parameters]
          simp
        exact (List.getElem?_eq_some_iff.mp sourceAtOption).2
      have targetAt :
          (costBaseConstructor cut rule).params[beforeParams.length]'(by
            simpa using sourceInBounds) =
            .simple parameterName (.base (costBaseSortName parameter)) := by
        rw [costBaseConstructor_parameter cut rule beforeParams.length
          sourceInBounds, sourceAt]
        simp [costBaseParameter, notSelected, mapParameterType,
          costBaseTypeExpr]
      have targetParameters :
          (costBaseConstructor cut rule).params =
            (costBaseConstructor cut rule).params.take beforeParams.length ++
              .simple parameterName (.base (costBaseSortName parameter)) ::
                (costBaseConstructor cut rule).params.drop
                  (beforeParams.length + 1) := by
        rw [← targetAt]
        exact (take_getElem_drop (costBaseConstructor cut rule).params
          beforeParams.length (by simpa using sourceInBounds)).symm
      apply SignatureContext.simpleArg
          (rule := costBaseConstructor cut rule)
          (beforeParams :=
            (costBaseConstructor cut rule).params.take beforeParams.length)
          (afterParams :=
            (costBaseConstructor cut rule).params.drop
              (beforeParams.length + 1))
      · exact plan.costBaseConstructor_mem_generated rule ruleMembership
      · exact targetParameters
      · simp [beforeLength, Nat.min_eq_left (Nat.le_of_lt sourceInBounds)]
      · rw [List.length_map, afterLength, List.length_drop,
          costBaseConstructor_params_length, parameters]
        simp only [List.length_append, List.length_cons]
        omega
      · simpa [CIGSLT.mapOneHoleContext, costBasePresentationSymbols] using
          inductionHypothesis
  | @abstractionArg binderSort bodySort rule declaredBinderName
      actualBinderName bodyName beforeParams afterParams before after inner
      ruleMembership parameters beforeLength afterLength notSelected
      innerStable inductionHypothesis =>
      have sourceInBounds : beforeParams.length < rule.params.length := by
        rw [parameters]
        simp
      have sourceAt :
          rule.params[beforeParams.length]'sourceInBounds =
            .abstractionNamed declaredBinderName bodyName
              (.arrow (.base binderSort) (.base bodySort)) := by
        have sourceAtOption :
            rule.params[beforeParams.length]? =
              some (.abstractionNamed declaredBinderName bodyName
                (.arrow (.base binderSort) (.base bodySort))) := by
          rw [parameters]
          simp
        exact (List.getElem?_eq_some_iff.mp sourceAtOption).2
      have targetAt :
          (costBaseConstructor cut rule).params[beforeParams.length]'(by
            simpa using sourceInBounds) =
            .abstractionNamed declaredBinderName bodyName
              (.arrow (.base (costBaseSortName binderSort))
                (.base (costBaseSortName bodySort))) := by
        rw [costBaseConstructor_parameter cut rule beforeParams.length
          sourceInBounds, sourceAt]
        simp [costBaseParameter, notSelected, mapParameterType,
          costBaseTypeExpr]
      have targetParameters :
          (costBaseConstructor cut rule).params =
            (costBaseConstructor cut rule).params.take beforeParams.length ++
              .abstractionNamed declaredBinderName bodyName
                (.arrow (.base (costBaseSortName binderSort))
                  (.base (costBaseSortName bodySort))) ::
                (costBaseConstructor cut rule).params.drop
                  (beforeParams.length + 1) := by
        rw [← targetAt]
        exact (take_getElem_drop (costBaseConstructor cut rule).params
          beforeParams.length (by simpa using sourceInBounds)).symm
      apply SignatureContext.abstractionArg
          (rule := costBaseConstructor cut rule)
          (beforeParams :=
            (costBaseConstructor cut rule).params.take beforeParams.length)
          (afterParams :=
            (costBaseConstructor cut rule).params.drop
              (beforeParams.length + 1))
      · exact plan.costBaseConstructor_mem_generated rule ruleMembership
      · exact targetParameters
      · simp [beforeLength, Nat.min_eq_left (Nat.le_of_lt sourceInBounds)]
      · rw [List.length_map, afterLength, List.length_drop,
          costBaseConstructor_params_length, parameters]
        simp only [List.length_append, List.length_cons]
        omega
      · simpa [CIGSLT.mapOneHoleContext, costBasePresentationSymbols] using
          inductionHypothesis
  | @collectionElement elementSort rule parameterName collectionType
      before after rest inner ruleMembership parameters notSelected
      innerStable inductionHypothesis =>
      apply SignatureContext.collectionElement
          (rule := costBaseConstructor cut rule)
          (parameterName := parameterName)
          (elementSort := costBaseSortName elementSort)
      · exact plan.costBaseConstructor_mem_generated rule ruleMembership
      · simp [costBaseConstructor, parameters, costBaseParameter, notSelected,
          mapParameterType, costBaseTypeExpr]
      · simpa [CIGSLT.mapOneHoleContext, costBasePresentationSymbols] using
          inductionHypothesis

/-- Transport a continuation-stable context into any target cut containing
the Cost base copies, provided the target selects exactly the transported
source continuation positions.  This is the reusable closure principle used
when Cost retains the authored cut below its generated funding envelope. -/
theorem mapCostBase {sourceTheory targetTheory : IGSLT}
    {sourceCut : InteractionCutPresentation sourceTheory}
    (targetCut : InteractionCutPresentation targetTheory)
    (includesConstructor : ∀ rule ∈
        sourceTheory.presentation.presentation.language.terms,
      costBaseConstructor sourceCut rule ∈
        targetTheory.presentation.presentation.language.terms)
    (selection : ∀ rule
        (_membership : rule ∈
          sourceTheory.presentation.presentation.language.terms)
        (index : Nat),
      isSelectedContinuation targetCut
          (costBaseConstructor sourceCut rule) index =
        isSelectedContinuation sourceCut rule index)
    {source target : String} {context : OneHoleContext}
    (stable : ContinuationStableContext sourceCut source target context) :
    ContinuationStableContext targetCut
      (costBaseSortName source) (costBaseSortName target)
      (CIGSLT.mapOneHoleContext costBasePresentationSymbols context) := by
  induction stable with
  | hole => exact .hole _
  | @simpleArg parameter rule parameterName beforeParams afterParams
      before after inner ruleMembership parameters beforeLength afterLength
      notSelected innerStable inductionHypothesis =>
      have sourceInBounds : beforeParams.length < rule.params.length := by
        rw [parameters]
        simp
      have sourceAt :
          rule.params[beforeParams.length]'sourceInBounds =
            .simple parameterName (.base parameter) := by
        have sourceAtOption :
            rule.params[beforeParams.length]? =
              some (.simple parameterName (.base parameter)) := by
          rw [parameters]
          simp
        exact (List.getElem?_eq_some_iff.mp sourceAtOption).2
      have targetAt :
          (costBaseConstructor sourceCut rule).params[beforeParams.length]'(by
            simpa using sourceInBounds) =
            .simple parameterName (.base (costBaseSortName parameter)) := by
        rw [costBaseConstructor_parameter sourceCut rule beforeParams.length
          sourceInBounds, sourceAt]
        simp [costBaseParameter, notSelected, mapParameterType,
          costBaseTypeExpr]
      have targetParameters :
          (costBaseConstructor sourceCut rule).params =
            (costBaseConstructor sourceCut rule).params.take
                beforeParams.length ++
              .simple parameterName (.base (costBaseSortName parameter)) ::
                (costBaseConstructor sourceCut rule).params.drop
                  (beforeParams.length + 1) := by
        rw [← targetAt]
        exact (take_getElem_drop (costBaseConstructor sourceCut rule).params
          beforeParams.length (by simpa using sourceInBounds)).symm
      apply ContinuationStableContext.simpleArg
          (rule := costBaseConstructor sourceCut rule)
          (beforeParams :=
            (costBaseConstructor sourceCut rule).params.take
              beforeParams.length)
          (afterParams :=
            (costBaseConstructor sourceCut rule).params.drop
              (beforeParams.length + 1))
      · exact includesConstructor rule ruleMembership
      · exact targetParameters
      · simp [beforeLength, Nat.min_eq_left (Nat.le_of_lt sourceInBounds)]
      · rw [List.length_map, afterLength, List.length_drop,
          costBaseConstructor_params_length, parameters]
        simp only [List.length_append, List.length_cons]
        omega
      · have targetBeforeLength :
            ((costBaseConstructor sourceCut rule).params.take
              beforeParams.length).length = beforeParams.length := by
          simp [Nat.min_eq_left (Nat.le_of_lt sourceInBounds)]
        rw [targetBeforeLength,
          selection rule ruleMembership beforeParams.length, notSelected]
      · simpa [CIGSLT.mapOneHoleContext, costBasePresentationSymbols] using
          inductionHypothesis
  | @abstractionArg binderSort bodySort rule declaredBinderName
      actualBinderName bodyName beforeParams afterParams before after inner
      ruleMembership parameters beforeLength afterLength notSelected
      innerStable inductionHypothesis =>
      have sourceInBounds : beforeParams.length < rule.params.length := by
        rw [parameters]
        simp
      have sourceAt :
          rule.params[beforeParams.length]'sourceInBounds =
            .abstractionNamed declaredBinderName bodyName
              (.arrow (.base binderSort) (.base bodySort)) := by
        have sourceAtOption :
            rule.params[beforeParams.length]? =
              some (.abstractionNamed declaredBinderName bodyName
                (.arrow (.base binderSort) (.base bodySort))) := by
          rw [parameters]
          simp
        exact (List.getElem?_eq_some_iff.mp sourceAtOption).2
      have targetAt :
          (costBaseConstructor sourceCut rule).params[beforeParams.length]'(by
            simpa using sourceInBounds) =
            .abstractionNamed declaredBinderName bodyName
              (.arrow (.base (costBaseSortName binderSort))
                (.base (costBaseSortName bodySort))) := by
        rw [costBaseConstructor_parameter sourceCut rule beforeParams.length
          sourceInBounds, sourceAt]
        simp [costBaseParameter, notSelected, mapParameterType,
          costBaseTypeExpr]
      have targetParameters :
          (costBaseConstructor sourceCut rule).params =
            (costBaseConstructor sourceCut rule).params.take
                beforeParams.length ++
              .abstractionNamed declaredBinderName bodyName
                (.arrow (.base (costBaseSortName binderSort))
                  (.base (costBaseSortName bodySort))) ::
                (costBaseConstructor sourceCut rule).params.drop
                  (beforeParams.length + 1) := by
        rw [← targetAt]
        exact (take_getElem_drop (costBaseConstructor sourceCut rule).params
          beforeParams.length (by simpa using sourceInBounds)).symm
      apply ContinuationStableContext.abstractionArg
          (rule := costBaseConstructor sourceCut rule)
          (beforeParams :=
            (costBaseConstructor sourceCut rule).params.take
              beforeParams.length)
          (afterParams :=
            (costBaseConstructor sourceCut rule).params.drop
              (beforeParams.length + 1))
      · exact includesConstructor rule ruleMembership
      · exact targetParameters
      · simp [beforeLength, Nat.min_eq_left (Nat.le_of_lt sourceInBounds)]
      · rw [List.length_map, afterLength, List.length_drop,
          costBaseConstructor_params_length, parameters]
        simp only [List.length_append, List.length_cons]
        omega
      · have targetBeforeLength :
            ((costBaseConstructor sourceCut rule).params.take
              beforeParams.length).length = beforeParams.length := by
          simp [Nat.min_eq_left (Nat.le_of_lt sourceInBounds)]
        rw [targetBeforeLength,
          selection rule ruleMembership beforeParams.length, notSelected]
      · simpa [CIGSLT.mapOneHoleContext, costBasePresentationSymbols] using
          inductionHypothesis
  | @collectionElement elementSort rule parameterName collectionType
      before after rest inner ruleMembership parameters notSelected
      innerStable inductionHypothesis =>
      apply ContinuationStableContext.collectionElement
          (rule := costBaseConstructor sourceCut rule)
          (parameterName := parameterName)
          (elementSort := costBaseSortName elementSort)
      · exact includesConstructor rule ruleMembership
      · simp [costBaseConstructor, parameters, costBaseParameter, notSelected,
          mapParameterType, costBaseTypeExpr]
      · rw [selection rule ruleMembership 0, notSelected]
      · simpa [CIGSLT.mapOneHoleContext, costBasePresentationSymbols] using
          inductionHypothesis

end ContinuationStableContext

namespace ContinuationRetypingPlan

mutual
  /-- Translate the contractum, selecting wrapped constructor copies exactly
  where the cut-derived hereditary closure requires them. -/
  def mapContractum {theory : IGSLT}
      {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        let mappedConstructor :=
          if constructor ∈ plan.wrappedLabels then
            costWrappedConstructorName constructor
          else
            costBaseConstructorName constructor
        .apply mappedConstructor (mapContractumList plan arguments)
    | .lambda binder body => .lambda binder (mapContractum plan body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (mapContractum plan body)
    | .subst body replacement =>
        .subst (mapContractum plan body) (mapContractum plan replacement)
    | .collection collectionType elements rest =>
        .collection collectionType (mapContractumList plan elements) rest

  def mapContractumList {theory : IGSLT}
      {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        mapContractum plan pattern :: mapContractumList plan patterns
end

/-- Contractum translation is pointwise on pattern lists. -/
@[simp]
theorem mapContractumList_eq_map {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (patterns : List Pattern) :
    plan.mapContractumList patterns = patterns.map plan.mapContractum := by
  induction patterns <;> simp_all [mapContractumList]

/-- First-match lookup for the authored rewrite metavariable context. -/
def lookupTypeContext : List (String × TypeExpr) → String → Option TypeExpr
  | [], _ => none
  | (name, type) :: context, sought =>
      if name = sought then some type else lookupTypeContext context sought

/-- Retype exactly the two selected continuation metavariables to the wrapped
fiber.  All other rewrite variables enter the tagged base copy. -/
def generatedFreeContext {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (_plan : ContinuationRetypingPlan cut) : FreeTypeContext :=
  fun name =>
    (lookupTypeContext
      theory.presentation.interactionRewrite.1.typeContext name).map fun type =>
      if name = cut.program.continuationVariable.name ∨
          name = cut.environment.continuationVariable.name then
        costWrappedTypeExpr theory.presentation.interactingSort.1.name type
      else
        costBaseTypeExpr type

/-- The precise wrappability obligation: the exact authored interaction
contractum, translated by the finite declaration plan, has the wrapped-term
sort. -/
def Wrappable {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : Prop :=
  HasSort plan.generatedLanguage plan.generatedFreeContext []
    (plan.mapContractum theory.presentation.interactionRewrite.1.right)
    costWrappedSortName

/-- The selected interaction redex remains sorted after its two continuation
positions are moved to the wrapped fiber.  This is the source-side companion
of `Wrappable`, which types the contractum. -/
def RedexRetypable {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : Prop :=
  HasSort plan.generatedLanguage plan.generatedFreeContext []
    (mapPattern costBasePresentationSymbols
      theory.presentation.interactionRewrite.1.left)
    (costBaseSortName theory.presentation.interactingSort.1.name)

end ContinuationRetypingPlan

end Mettapedia.GSLT.LanguageDef
