import Mettapedia.GSLT.LanguageDef.InteractionCut
import Mettapedia.GSLT.LanguageDef.CollectionAlgebraTransport
import Mettapedia.GSLT.LanguageDef.TypingInversion

/-!
# Continuation decoration on an interaction cut

Wrappability is a sorting statement, not a callback or policy flag.  This
module constructs the signature in which that statement is asked.  Source
declarations are copied into a tagged base namespace; the continuation slots
of the two interacting operands are re-sorted to one fresh wrapped sort; and
a chosen closure of constructors receives wrapped copies.  The authored
interaction rule remains the source of the contractum.

An operand can carry several process-valued parameters.  The primary
continuation is selected by the cut; a decoration profile may add further
slots, each with the same declaration, binder representation and
schema-variable evidence as a primary slot.  The constructor closure is
independent of those slots.

Typing a decorated contractum does not prove activation, no-leak or iteration
laws for a metered runtime.  The profile with exactly the cut's two slots and
every non-principal constructor in its closure is the one the Cost
construction iterates; `ContinuationRetyping` defines it.
-/

set_option autoImplicit false

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
def costBaseLanguageDefSymbolMap : LanguageDefSymbolMap where
  sort := costBaseSortName
  constructor := costBaseConstructorName
  relation := id
  equation := id
  rewrite := id

@[simp]
theorem costBaseLanguageDefSymbolMap_sort (name : String) :
    costBaseLanguageDefSymbolMap.sort name = costBaseSortName name := rfl

@[simp]
theorem costBaseLanguageDefSymbolMap_constructor (name : String) :
    costBaseLanguageDefSymbolMap.constructor name =
      costBaseConstructorName name := rfl

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

/-- The tagged base action retains the complete authored type structure. -/
theorem costBaseTypeExpr_injective : Function.Injective costBaseTypeExpr := by
  intro left
  induction left with
  | base leftSort =>
      intro right equality
      cases right with
      | base rightSort =>
          have names :
              costBaseSortName leftSort = costBaseSortName rightSort := by
            simpa [costBaseTypeExpr] using TypeExpr.base.inj equality
          exact congrArg TypeExpr.base (costBaseSortName_injective names)
      | arrow domain codomain =>
          simp [costBaseTypeExpr] at equality
      | multiBinder body =>
          simp [costBaseTypeExpr] at equality
      | collection collectionType body =>
          simp [costBaseTypeExpr] at equality
  | arrow leftDomain leftCodomain domainIH codomainIH =>
      intro right equality
      cases right with
      | base sort =>
          simp [costBaseTypeExpr] at equality
      | arrow rightDomain rightCodomain =>
          have parts := TypeExpr.arrow.inj equality
          exact congrArg₂ TypeExpr.arrow
            (domainIH parts.1) (codomainIH parts.2)
      | multiBinder body =>
          simp [costBaseTypeExpr] at equality
      | collection collectionType body =>
          simp [costBaseTypeExpr] at equality
  | multiBinder leftBody bodyIH =>
      intro right equality
      cases right with
      | base sort =>
          simp [costBaseTypeExpr] at equality
      | arrow domain codomain =>
          simp [costBaseTypeExpr] at equality
      | multiBinder rightBody =>
          exact congrArg TypeExpr.multiBinder
            (bodyIH (TypeExpr.multiBinder.inj equality))
      | collection collectionType body =>
          simp [costBaseTypeExpr] at equality
  | collection leftCollectionType leftBody bodyIH =>
      intro right equality
      cases right with
      | base sort =>
          simp [costBaseTypeExpr] at equality
      | arrow domain codomain =>
          simp [costBaseTypeExpr] at equality
      | multiBinder body =>
          simp [costBaseTypeExpr] at equality
      | collection rightCollectionType rightBody =>
          have parts := TypeExpr.collection.inj equality
          exact congrArg₂ TypeExpr.collection parts.1 (bodyIH parts.2)

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

/-- The base and wrapped type actions overlap exactly on types that do not
mention the interacting sort.  This characterizes the label-free static
fiber where a compact term may carry both colors without exposing a
different type. -/
theorem costWrappedTypeExpr_eq_costBaseTypeExpr_iff
    (interactingSort : String) (type : TypeExpr) :
    costWrappedTypeExpr interactingSort type = costBaseTypeExpr type ↔
      interactingSort ∉ type.baseNames := by
  induction type with
  | base sort =>
      by_cases equality : sort = interactingSort
      · subst sort
        constructor
        · intro same
          have baseEquality : TypeExpr.base costWrappedSortName =
              TypeExpr.base (costBaseSortName interactingSort) := by
            simpa [costWrappedTypeExpr, costBaseTypeExpr] using same
          injection baseEquality with nameEquality
          exact (costBaseSortName_ne_wrapped interactingSort
            nameEquality.symm).elim
        · intro avoids
          exact (avoids (by simp [TypeExpr.baseNames])).elim
      · constructor
        · intro _
          simpa [TypeExpr.baseNames] using
            (fun reverse : interactingSort = sort => equality reverse.symm)
        · intro _
          simp [costWrappedTypeExpr, costBaseTypeExpr, equality]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [costWrappedTypeExpr, costBaseTypeExpr, TypeExpr.baseNames,
        domainHypothesis, codomainHypothesis]
  | multiBinder body inductionHypothesis =>
      simp [costWrappedTypeExpr, costBaseTypeExpr, TypeExpr.baseNames,
        inductionHypothesis]
  | collection collectionType body inductionHypothesis =>
      simp [costWrappedTypeExpr, costBaseTypeExpr, TypeExpr.baseNames,
        inductionHypothesis]

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
    evalPolicy? := none
    algebra? := constructor.algebra?.map (mapCollectionAlgebra costWrappedConstructorName) }

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

/-! ## The rewrite's variable context and authored labels -/

/-- First-match lookup for the authored rewrite metavariable context. -/
def ContinuationRetypingPlan.lookupTypeContext :
    List (String × TypeExpr) → String → Option TypeExpr
  | [], _ => none
  | (name, type) :: context, sought =>
      if name = sought then some type else lookupTypeContext context sought

/-- Validation makes constructor labels unique, so an authored constructor is
determined by its label. -/
theorem ContinuationRetypingPlan.authoredConstructorLabel_injective
    (presentation : ValidatedLanguageDef) :
    Function.Injective
      (fun constructor : DeclaredConstructor presentation =>
        constructor.1.label) := by
  intro left right equality
  apply Subtype.ext
  exact List.inj_on_of_nodup_map
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      presentation.language presentation.valid)
    left.2 right.2 equality

/-! ## Decoration profiles -/

/-- One additional continuation of an actual ordered operand. Its position
and schema occurrence are connected by the same evidence as a primary slot. -/
structure ContinuationDecorationSlot {presentation : InteractivePresentation}
    (operand : InteractionOperandProfile presentation) where
  position : ContinuationPosition presentation operand.constructor
  pattern : Pattern
  schemaVariable : ContinuationSchemaVariable pattern
  form : InteractionOperandForm operand.constructor position operand.schemaTerm pattern

namespace ContinuationDecorationSlot

variable {presentation : InteractivePresentation}
  {operand : InteractionOperandProfile presentation}

/-- A decoration slot carries an opaque schema variable, never a constructor
whose internal shape the contraction could inspect at that position. -/
theorem pattern_ne_apply (slot : ContinuationDecorationSlot operand)
    (label : String) (arguments : List Pattern) :
    slot.pattern ≠ .apply label arguments := by
  intro same
  have witness := slot.schemaVariable
  rw [same] at witness
  cases witness

/-- An additional slot names a variable of the actual interaction operand;
it cannot introduce an unrelated metavariable into the decorated context. -/
theorem name_mem_operand (slot : ContinuationDecorationSlot operand) :
    slot.schemaVariable.name ∈ operand.schemaTerm.freeFvarNames := by
  have variableInPattern : ∀ {pattern : Pattern} (witness : ContinuationSchemaVariable pattern),
      witness.name ∈ pattern.freeFvarNames := by
    intro pattern witness
    cases witness <;> simp [ContinuationSchemaVariable.name, Pattern.freeFvarNames]
  have variableMember := variableInPattern slot.schemaVariable
  cases slot.form with
  | introduced represented selected =>
      generalize operand.schemaTerm = source at represented selected ⊢
      cases source
      all_goals try exact False.elim selected
      case apply label arguments =>
        simpa only [Pattern.freeFvarNames] using List.mem_flatMap.mpr
          ⟨slot.pattern, List.mem_of_getElem? selected, variableMember⟩
  | direct same => simpa only [same] using variableMember

end ContinuationDecorationSlot

/-- Finite decoration data over a cut, without a new contraction authority.
The two primary slots are included automatically. -/
structure ContinuationDecorationProfile {theory : IGSLT}
    (cut : InteractionCutPresentation theory) where
  programAdditional : List (ContinuationDecorationSlot cut.program) := []
  environmentAdditional : List (ContinuationDecorationSlot cut.environment) := []
  constructorClosure : List (DeclaredConstructor theory.presentation.presentation)

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Selection remains positional in the exact authored constructor.  The
additional slots are tested first, so a profile without additional slots
selects, by unfolding, exactly the cut's two continuation positions. -/
def selectedParameter (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule) (index : Nat) : Bool :=
  profile.programAdditional.any (fun slot =>
      constructor == cut.program.constructor.1 && index == slot.position.index) ||
    profile.environmentAdditional.any (fun slot =>
      constructor == cut.environment.constructor.1 && index == slot.position.index) ||
    isSelectedContinuation cut constructor index

/-- A free metavariable retained by an additional slot. -/
def additionalVariable (profile : ContinuationDecorationProfile cut) (name : String) : Bool :=
  profile.programAdditional.any (fun slot => name == slot.schemaVariable.name) ||
    profile.environmentAdditional.any (fun slot => name == slot.schemaVariable.name)

/-- Selection of free metavariables follows the retained schema occurrence. -/
def selectedVariable (profile : ContinuationDecorationProfile cut) (name : String) : Bool :=
  name == cut.program.continuationVariable.name ||
    name == cut.environment.continuationVariable.name ||
    profile.programAdditional.any (fun slot => name == slot.schemaVariable.name) ||
    profile.environmentAdditional.any (fun slot => name == slot.schemaVariable.name)

/-- The wrapped or the base reading of a variable, by selection.  The
additional slots are tested first, so a profile without additional slots
chooses, by unfolding, exactly as the cut's two continuation variables do. -/
def variableChoice {α : Sort*} (profile : ContinuationDecorationProfile cut) (name : String)
    (wrapped base : α) : α :=
  if profile.additionalVariable name then wrapped
  else if name = cut.program.continuationVariable.name ∨
      name = cut.environment.continuationVariable.name then wrapped
  else base

/-- The choice is the one made by `selectedVariable`. -/
theorem variableChoice_eq {α : Sort*} (profile : ContinuationDecorationProfile cut)
    (name : String) (wrapped base : α) :
    profile.variableChoice name wrapped base =
      if profile.selectedVariable name then wrapped else base := by
  unfold variableChoice selectedVariable additionalVariable
  by_cases program : name = cut.program.continuationVariable.name <;>
    by_cases environment : name = cut.environment.continuationVariable.name <;>
    cases programSlots : profile.programAdditional.any
      (fun slot => name == slot.schemaVariable.name) <;>
    cases environmentSlots : profile.environmentAdditional.any
      (fun slot => name == slot.schemaVariable.name) <;>
    simp [program, environment]

def baseParameter (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule) (entry : TermParam × Nat) : TermParam :=
  if profile.selectedParameter constructor entry.2 then
    mapParameterType (costWrappedTypeExpr theory.presentation.interactingSort.1.name) entry.1
  else
    mapParameterType costBaseTypeExpr entry.1

def baseConstructor (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule) : GrammarRule :=
  { constructor with
    label := costBaseConstructorName constructor.label
    category := costBaseSortName constructor.category
    params := constructor.params.zipIdx.map (profile.baseParameter constructor)
    syntaxPattern := []
    evalPolicy? := none
    algebra? := constructor.algebra?.map (StructuralMorphism.mapCollectionAlgebra
      costBaseConstructorName) }

@[simp]
theorem baseConstructor_label (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule) :
    (profile.baseConstructor constructor).label = costBaseConstructorName constructor.label :=
  rfl

@[simp]
theorem baseConstructor_params_length (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule) :
    (profile.baseConstructor constructor).params.length = constructor.params.length := by
  simp [baseConstructor]

theorem baseConstructor_parameter (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule) (index : Nat) (inBounds : index < constructor.params.length) :
    (profile.baseConstructor constructor).params[index]'(by
      simpa [baseConstructor] using inBounds) =
      profile.baseParameter constructor (constructor.params[index], index) := by
  simp [baseConstructor, List.getElem_map, List.getElem_zipIdx]

/-- Adding an actual program slot changes its declared result to the wrapped
sort, using both its in-bounds position and interacting-result evidence. -/
theorem programAdditional_result (profile : ContinuationDecorationProfile cut)
    (slot : ContinuationDecorationSlot cut.program)
    (included : slot ∈ profile.programAdditional) :
    continuationResult?
      ((profile.baseConstructor cut.program.constructor.1).params[slot.position.index]'(by
        simpa [baseConstructor] using slot.position.inBounds)) =
      some (.base costWrappedSortName) := by
  have selected : profile.selectedParameter cut.program.constructor.1 slot.position.index = true := by
    have additional : profile.programAdditional.any (fun chosen =>
        cut.program.constructor.1 == cut.program.constructor.1 &&
          slot.position.index == chosen.position.index) = true :=
      List.any_eq_true.mpr ⟨slot, included, by simp⟩
    simp only [selectedParameter, additional, Bool.true_or]
  rw [baseConstructor_parameter _ _ _ slot.position.inBounds]
  unfold baseParameter
  rw [selected]
  exact continuationResult?_mapParameterType_costWrapped _ _ slot.position.hasInteractingResult

/-- The same positional law applies to additional environment continuations. -/
theorem environmentAdditional_result (profile : ContinuationDecorationProfile cut)
    (slot : ContinuationDecorationSlot cut.environment)
    (included : slot ∈ profile.environmentAdditional) :
    continuationResult?
      ((profile.baseConstructor cut.environment.constructor.1).params[slot.position.index]'(by
        simpa [baseConstructor] using slot.position.inBounds)) =
      some (.base costWrappedSortName) := by
  have selected : profile.selectedParameter cut.environment.constructor.1 slot.position.index = true := by
    have additional : profile.environmentAdditional.any (fun chosen =>
        cut.environment.constructor.1 == cut.environment.constructor.1 &&
          slot.position.index == chosen.position.index) = true :=
      List.any_eq_true.mpr ⟨slot, included, by simp⟩
    simp only [selectedParameter, additional, Bool.or_true, Bool.true_or]
  rw [baseConstructor_parameter _ _ _ slot.position.inBounds]
  unfold baseParameter
  rw [selected]
  exact continuationResult?_mapParameterType_costWrapped _ _ slot.position.hasInteractingResult

/-- Continuation retyping changes sort annotations but not whether a
constructor uses the bare single-collection representation. -/
theorem usesBareCollection_baseConstructor_iff (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule) :
    UsesBareCollection (profile.baseConstructor constructor) ↔
      UsesBareCollection constructor := by
  cases constructor with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases parameters with
      | nil => simp [UsesBareCollection, baseConstructor]
      | cons parameter parameters =>
          cases parameters with
          | nil =>
              cases parameter with
              | simple name type =>
                  simp only [UsesBareCollection, baseConstructor,
                    baseParameter, List.zipIdx_cons, List.map_cons,
                    List.singleton_inj, TermParam.simple.injEq]
                  split <;> cases type <;>
                    simp [mapParameterType, costWrappedTypeExpr,
                      costBaseTypeExpr] ;
                    split <;> simp
              | abstractionNamed binder name type =>
                  simp only [UsesBareCollection, baseConstructor,
                    baseParameter, List.zipIdx_cons, List.map_cons]
                  split <;> simp [mapParameterType]
              | multiAbstractionNamed binders name type =>
                  simp only [UsesBareCollection, baseConstructor,
                    baseParameter, List.zipIdx_cons, List.map_cons]
                  split <;> simp [mapParameterType]
          | cons second rest =>
              simp [UsesBareCollection, baseConstructor]

def wrappedLabels (profile : ContinuationDecorationProfile cut) : List String :=
  profile.constructorClosure.map (·.1.label)

def generatedLanguage (profile : ContinuationDecorationProfile cut) : LanguageDef :=
  { name := "$cost:continuation-signature:" ++
      theory.presentation.presentation.language.name
    types :=
      (theory.presentation.presentation.language.types.map fun declaration =>
        { declaration with name := costBaseSortName declaration.name }) ++
      [TypeDecl.plain costWrappedSortName]
    terms :=
      theory.presentation.presentation.language.terms.map profile.baseConstructor ++
      profile.constructorClosure.map
        (fun constructor => costWrappedConstructor (theory := theory) constructor.1)
    equations := []
    rewrites := [] }

/-- Retype the selected continuation metavariables to the wrapped fibre.  All
other rewrite variables enter the tagged base copy. -/
def generatedFreeContext (profile : ContinuationDecorationProfile cut) : FreeTypeContext :=
  fun name =>
    (ContinuationRetypingPlan.lookupTypeContext
      theory.presentation.interactionRewrite.1.typeContext name).map fun type =>
      profile.variableChoice name
        (costWrappedTypeExpr theory.presentation.interactingSort.1.name type)
        (costBaseTypeExpr type)

/-- The retyped context, read through `selectedVariable`. -/
theorem generatedFreeContext_apply (profile : ContinuationDecorationProfile cut)
    (name : String) :
    profile.generatedFreeContext name =
      (ContinuationRetypingPlan.lookupTypeContext
        theory.presentation.interactionRewrite.1.typeContext name).map fun type =>
        if profile.selectedVariable name then
          costWrappedTypeExpr theory.presentation.interactingSort.1.name type
        else
          costBaseTypeExpr type := by
  simp only [generatedFreeContext, variableChoice_eq]

/-- Contractum translation reuses the existing generic pattern action. -/
def contractumSymbols (profile : ContinuationDecorationProfile cut) : LanguageDefSymbolMap where
  sort := id
  constructor := fun label =>
    if label ∈ profile.wrappedLabels then costWrappedConstructorName label
    else costBaseConstructorName label
  relation := id
  equation := id
  rewrite := id

def mapContractum (profile : ContinuationDecorationProfile cut) : Pattern → Pattern :=
  mapPattern profile.contractumSymbols

/-- Well-sorted contraction on the selected decorated continuation bundle. -/
def Wrappable (profile : ContinuationDecorationProfile cut) : Prop :=
  HasSort profile.generatedLanguage profile.generatedFreeContext []
    (profile.mapContractum theory.presentation.interactionRewrite.1.right)
    costWrappedSortName

def RedexRetypable (profile : ContinuationDecorationProfile cut) : Prop :=
  HasSort profile.generatedLanguage profile.generatedFreeContext []
    (mapPattern costBaseLanguageDefSymbolMap theory.presentation.interactionRewrite.1.left)
    (costBaseSortName theory.presentation.interactingSort.1.name)

theorem baseConstructor_mem (profile : ContinuationDecorationProfile cut)
    (constructor : GrammarRule)
    (declared : constructor ∈ theory.presentation.presentation.language.terms) :
    profile.baseConstructor constructor ∈ profile.generatedLanguage.terms :=
  List.mem_append_left _ (List.mem_map.mpr ⟨constructor, declared, rfl⟩)

theorem wrappedConstructor_mem (profile : ContinuationDecorationProfile cut)
    (constructor : DeclaredConstructor theory.presentation.presentation)
    (included : constructor ∈ profile.constructorClosure) :
    costWrappedConstructor (theory := theory) constructor.1 ∈ profile.generatedLanguage.terms :=
  List.mem_append_right _ (List.mem_map.mpr ⟨constructor, included, rfl⟩)

/-- A translated base constructor cannot return a wrapped process. Wrapped
copies have separate labels, independently of which constructors the finite
closure admits. -/
theorem baseHead_not_wrapped (profile : ContinuationDecorationProfile cut)
    {free : FreeTypeContext} {bound : List TypeExpr} (label : String)
    (arguments : List Pattern) :
    ¬ HasType profile.generatedLanguage free bound
      (.apply (costBaseConstructorName label) arguments) (.base costWrappedSortName) := by
  intro typed
  obtain ⟨rule, membership, named, result, -, -⟩ := typed.apply_inv
  obtain base | wrapped := List.mem_append.mp membership
  · obtain ⟨source, -, rfl⟩ := List.mem_map.mp base
    exact costBaseSortName_ne_wrapped source.category (TypeExpr.base.inj result).symm
  · obtain ⟨source, -, rfl⟩ := List.mem_map.mp wrapped
    exact costBaseConstructorName_ne_wrapped label source.1.label named.symm

/-- Source validation recovers exact declaration membership from its label. -/
theorem mem_wrappedLabels_iff (profile : ContinuationDecorationProfile cut)
    (constructor : DeclaredConstructor theory.presentation.presentation) :
    constructor.1.label ∈ profile.wrappedLabels ↔
      constructor ∈ profile.constructorClosure := by
  constructor
  · intro member
    obtain ⟨other, included, same⟩ := List.mem_map.mp member
    have identical := ContinuationRetypingPlan.authoredConstructorLabel_injective
      theory.presentation.presentation same
    simpa [identical] using included
  · intro member
    exact List.mem_map.mpr ⟨constructor, member, rfl⟩

end ContinuationDecorationProfile

end Mettapedia.GSLT.LanguageDef
