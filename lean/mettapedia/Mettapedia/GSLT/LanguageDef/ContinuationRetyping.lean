import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationValidation

/-!
# The two-slot continuation plan

The Cost construction iterates one decoration profile: the one that selects
exactly the cut's two continuation slots and gives a wrapped copy to every
authored constructor other than the two interacting ones.  A
`ContinuationRetypingPlan` is that profile together with its one substantive
obligation: the authored contractum is covered by the closure.

Every definition here is the general one of `Continued/ContinuationDecoration`
at this profile.  The `_def` lemmas state what each unfolds to; they hold by
`rfl`.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism
open WellSorted

/-! ## The closure determined by the cut -/

/-- Finite declaration data needed to retype the exact authored contractum.
Principal interaction constructors are excluded from the wrapped closure:
otherwise the transformed contractum could expose a fresh unguarded redex. -/
def ResidualCovered {theory : IGSLT}
    (wrappedConstructors :
      List (DeclaredConstructor theory.presentation.presentation))
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
    List (DeclaredConstructor theory.presentation.presentation) :=
  theory.presentation.presentation.language.terms.attach.filter fun constructor =>
    decide (constructor ≠ cut.program.constructor ∧
      constructor ≠ cut.environment.constructor)

/-! ## The two-slot profile and its base copies -/

/-- The profile with exactly the cut's two continuation slots.  Its closure
is every authored constructor other than the two introductions. -/
def ContinuationDecorationProfile.primary {theory : IGSLT}
    (cut : InteractionCutPresentation theory) : ContinuationDecorationProfile cut where
  constructorClosure := continuationConstructors cut

/-- Retype one indexed parameter of a base constructor.  Naming this action
makes explicit that selection is positional declaration data, not a traversal
policy hidden in the generated grammar. -/
def costBaseParameter {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) (entry : TermParam × Nat) : TermParam :=
  (ContinuationDecorationProfile.primary cut).baseParameter constructor entry

theorem costBaseParameter_def {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) (entry : TermParam × Nat) :
    costBaseParameter cut constructor entry =
      if isSelectedContinuation cut constructor entry.2 then
        mapParameterType
          (costWrappedTypeExpr theory.presentation.interactingSort.1.name) entry.1
      else
        mapParameterType costBaseTypeExpr entry.1 :=
  rfl

/-- The base copy of a source constructor.  Exactly the selected continuation
positions are re-sorted; every other parameter remains in the base copy. -/
def costBaseConstructor {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) : GrammarRule :=
  (ContinuationDecorationProfile.primary cut).baseConstructor constructor

theorem costBaseConstructor_def {theory : IGSLT}
    (cut : InteractionCutPresentation theory) (constructor : GrammarRule) :
    costBaseConstructor cut constructor =
      { constructor with
        label := costBaseConstructorName constructor.label
        category := costBaseSortName constructor.category
        params := constructor.params.zipIdx.map (costBaseParameter cut constructor)
        syntaxPattern := []
        evalPolicy? := none
        algebra? := constructor.algebra?.map
          (mapCollectionAlgebra costBaseConstructorName) } :=
  rfl

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
      constructor.params.length :=
  (ContinuationDecorationProfile.primary cut).baseConstructor_params_length constructor

theorem costBaseConstructor_parameter {theory : IGSLT}
    (cut : InteractionCutPresentation theory) (constructor : GrammarRule)
    (index : Nat) (inBounds : index < constructor.params.length) :
    (costBaseConstructor cut constructor).params[index]'(by
        simpa using inBounds) =
      costBaseParameter cut constructor (constructor.params[index], index) :=
  (ContinuationDecorationProfile.primary cut).baseConstructor_parameter constructor index
    inBounds

/-- Continuation retyping changes sort annotations but not whether a
constructor uses the bare single-collection representation. -/
theorem usesBareCollection_costBaseConstructor_iff {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) :
    UsesBareCollection (costBaseConstructor cut constructor) ↔
      UsesBareCollection constructor :=
  (ContinuationDecorationProfile.primary cut).usesBareCollection_baseConstructor_iff constructor

/-! ## The plan -/

/-- A continuation plan carries only the substantive closure obligation: the
authored contractum is represented by the hereditary signature induced by the
cut. -/
structure ContinuationRetypingPlan {theory : IGSLT}
    (cut : InteractionCutPresentation theory) where
  residualCovered : ResidualCovered (continuationConstructors cut) cut.residual

/-- The plan read as a decoration profile: the cut's two slots, and a
wrapped copy of every authored constructor other than the two introductions. -/
def ContinuationDecorationProfile.ofRetypingPlan {theory : IGSLT}
    {cut : InteractionCutPresentation theory} (_plan : ContinuationRetypingPlan cut) :
    ContinuationDecorationProfile cut :=
  ContinuationDecorationProfile.primary cut

namespace ContinuationRetypingPlan

open ContinuationDecorationProfile (ofRetypingPlan)

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

@[simp]
theorem mem_continuationConstructors_iff {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : DeclaredConstructor theory.presentation.presentation) :
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
def wrappedConstructors (plan : ContinuationRetypingPlan cut) :
    List (DeclaredConstructor theory.presentation.presentation) :=
  (ofRetypingPlan plan).constructorClosure

theorem wrappedConstructors_def (plan : ContinuationRetypingPlan cut) :
    plan.wrappedConstructors = continuationConstructors cut :=
  rfl

@[simp]
theorem mem_wrappedConstructors_iff
    (plan : ContinuationRetypingPlan cut)
    (constructor : DeclaredConstructor theory.presentation.presentation) :
    constructor ∈ plan.wrappedConstructors ↔
      constructor ≠ cut.program.constructor ∧
        constructor ≠ cut.environment.constructor :=
  mem_continuationConstructors_iff cut constructor

/-- Validation makes the declaration-derived hereditary closure
duplicate-free. -/
theorem noDuplicates {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    plan.wrappedConstructors.Nodup := by
  rw [wrappedConstructors_def]
  unfold continuationConstructors
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
def wrappedLabels (plan : ContinuationRetypingPlan cut) : List String :=
  (ofRetypingPlan plan).wrappedLabels

theorem wrappedLabels_def (plan : ContinuationRetypingPlan cut) :
    plan.wrappedLabels = plan.wrappedConstructors.map (·.1.label) :=
  rfl

/-- The declaration-level signature in which wrappability is checked. -/
def generatedLanguage (plan : ContinuationRetypingPlan cut) : LanguageDef :=
  (ofRetypingPlan plan).generatedLanguage

/-- Source types embedded in the base namespace, followed by the one new
wrapped-term sort. -/
def generatedTypes (plan : ContinuationRetypingPlan cut) : List TypeDecl :=
  plan.generatedLanguage.types

theorem generatedTypes_def (plan : ContinuationRetypingPlan cut) :
    plan.generatedTypes =
      (theory.presentation.presentation.language.types.map fun declaration =>
        { declaration with name := costBaseSortName declaration.name }) ++
      [TypeDecl.plain costWrappedSortName] :=
  rfl

theorem generatedLanguage_def (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage =
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
        rewrites := [] } :=
  rfl

/-- The generated constructors: a base copy of every authored constructor,
then a wrapped copy of every constructor of the closure. -/
theorem generatedLanguage_terms (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.terms =
      theory.presentation.presentation.language.terms.map
          (costBaseConstructor cut) ++
        plan.wrappedConstructors.map
          (fun constructor =>
            costWrappedConstructor (theory := theory) constructor.1) :=
  rfl

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
    (CIGSLT.mapOneHoleContext costBaseLanguageDefSymbolMap
      cut.sourceShape.envelope)

/-! ### The general laws at this profile -/

@[simp]
theorem generatedLanguage_typeNames
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.typeNames =
      theory.presentation.presentation.language.typeNames.map
          costBaseSortName ++
        [costWrappedSortName] :=
  (ofRetypingPlan plan).generatedLanguage_typeNames

/-- The tagged source sorts and the wrapped sort form a duplicate-free
generated namespace. -/
theorem generatedTypeNames_nodup
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.typeNames.Nodup :=
  (ofRetypingPlan plan).generatedTypeNames_nodup

/-- Membership in the label projection is equivalent to membership of the
exact authored constructor.  Validation makes constructor labels unique, so
this projection loses no identity information. -/
theorem mem_wrappedLabels_iff
    (plan : ContinuationRetypingPlan cut)
    (constructor : DeclaredConstructor theory.presentation.presentation) :
    constructor.1.label ∈ plan.wrappedLabels ↔
      constructor ∈ plan.wrappedConstructors :=
  (ofRetypingPlan plan).mem_wrappedLabels_iff constructor

theorem generatedLanguage_constructorLabels
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.terms.map (·.label) =
      (theory.presentation.presentation.language.terms.map (·.label)).map
          costBaseConstructorName ++
        plan.wrappedLabels.map costWrappedConstructorName :=
  (ofRetypingPlan plan).generatedLanguage_constructorLabels

/-- Base and wrapped constructor copies remain duplicate-free and occupy
disjoint generated namespaces. -/
theorem generatedConstructorLabels_nodup
    (plan : ContinuationRetypingPlan cut) :
    (plan.generatedLanguage.terms.map (·.label)).Nodup :=
  (ofRetypingPlan plan).generatedConstructorLabels_nodup plan.noDuplicates

/-- Every generated constructor returns one of the generated sorts. -/
theorem generatedTerm_category_mem
    (plan : ContinuationRetypingPlan cut) (term : GrammarRule)
    (membership : term ∈ plan.generatedLanguage.terms) :
    term.category ∈ plan.generatedLanguage.typeNames :=
  (ofRetypingPlan plan).generatedTerm_category_mem term membership

/-- Every sort referenced by a generated constructor parameter is declared
by the generated signature. -/
theorem generatedTerm_parameter_baseName_mem
    (plan : ContinuationRetypingPlan cut) (term : GrammarRule)
    (termMembership : term ∈ plan.generatedLanguage.terms)
    (parameter : TermParam) (parameterMembership : parameter ∈ term.params)
    (name : String)
    (nameMembership : name ∈ (TermParam.typeExpr parameter).baseNames) :
    name ∈ plan.generatedLanguage.typeNames :=
  (ofRetypingPlan plan).generatedTerm_parameter_baseName_mem term termMembership
    parameter parameterMembership name nameMembership

/-- Generated typing constructors intentionally carry no parser notation or
host evaluator policy.  They are the internal signature derived from the
authored presentation, not a second source language. -/
theorem generatedTerm_syntaxPattern_eq_nil
    (plan : ContinuationRetypingPlan cut) (term : GrammarRule)
    (termMembership : term ∈ plan.generatedLanguage.terms) :
    term.syntaxPattern = [] :=
  (ofRetypingPlan plan).generatedTerm_syntaxPattern_eq_nil term termMembership

/-- The declaration-derived continuation signature passes the same
`LanguageDef.validate` gate as every authored language definition. -/
theorem generatedLanguage_validate
    (plan : ContinuationRetypingPlan cut) :
    plan.generatedLanguage.validate = [] :=
  (ofRetypingPlan plan).generatedLanguage_validate plan.noDuplicates

/-- The validated generated signature retains its derivation from the exact
source `LanguageDef`; it is not independently authored data. -/
def generatedPresentation
    (plan : ContinuationRetypingPlan cut) : ValidatedLanguageDef :=
  (ofRetypingPlan plan).generatedPresentation plan.noDuplicates

/-- Every authored source constructor has its retyped base copy in the
generated continuation signature. -/
theorem costBaseConstructor_mem_generated
    (plan : ContinuationRetypingPlan cut) (constructor : GrammarRule)
    (membership :
      constructor ∈ theory.presentation.presentation.language.terms) :
    costBaseConstructor cut constructor ∈ plan.generatedLanguage.terms :=
  (ofRetypingPlan plan).baseConstructor_mem constructor membership

/-- Every constructor selected for wrapped residual closure has its wrapped
copy in the generated continuation signature. -/
theorem costWrappedConstructor_mem_generated
    (plan : ContinuationRetypingPlan cut)
    (constructor : DeclaredConstructor theory.presentation.presentation)
    (membership : constructor ∈ plan.wrappedConstructors) :
    costWrappedConstructor (theory := theory) constructor.1 ∈
      plan.generatedLanguage.terms :=
  (ofRetypingPlan plan).wrappedConstructor_mem constructor membership

/-- Every authored source sort has its tagged base copy in the generated
continuation signature. -/
theorem costBaseSortName_mem_generated
    (plan : ContinuationRetypingPlan cut) (sort : String)
    (membership :
      sort ∈ theory.presentation.presentation.language.typeNames) :
    costBaseSortName sort ∈ plan.generatedLanguage.typeNames :=
  (ofRetypingPlan plan).costBaseSortName_mem_generated membership

/-- The distinguished wrapped sort belongs to every generated continuation
signature. -/
theorem costWrappedSortName_mem_generated
    (plan : ContinuationRetypingPlan cut) :
    costWrappedSortName ∈ plan.generatedLanguage.typeNames :=
  (ofRetypingPlan plan).costWrappedSortName_mem_generated

/-- A source constructor's tagged base label resolves uniquely in the
generated continuation signature. -/
theorem costBaseConstructor_filter_generated
    (plan : ContinuationRetypingPlan cut) (constructor : GrammarRule)
    (membership :
      constructor ∈ theory.presentation.presentation.language.terms) :
    plan.generatedLanguage.terms.filter
        (fun candidate =>
          candidate.label == (costBaseConstructor cut constructor).label) =
      [costBaseConstructor cut constructor] :=
  (ofRetypingPlan plan).baseConstructor_filter_generated plan.noDuplicates
    constructor membership

/-- A selected residual constructor's wrapped label resolves uniquely in the
generated continuation signature. -/
theorem costWrappedConstructor_filter_generated
    (plan : ContinuationRetypingPlan cut)
    (constructor : DeclaredConstructor theory.presentation.presentation)
    (membership : constructor ∈ plan.wrappedConstructors) :
    plan.generatedLanguage.terms.filter
        (fun candidate => candidate.label ==
          (costWrappedConstructor (theory := theory) constructor.1).label) =
      [costWrappedConstructor (theory := theory) constructor.1] :=
  (ofRetypingPlan plan).wrappedConstructor_filter_generated plan.noDuplicates
    constructor membership

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
      (CIGSLT.mapOneHoleContext costBaseLanguageDefSymbolMap context) := by
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
        simp [costBaseParameter_def, notSelected, mapParameterType,
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
      · simpa [CIGSLT.mapOneHoleContext, costBaseLanguageDefSymbolMap] using
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
        simp [costBaseParameter_def, notSelected, mapParameterType,
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
      · simpa [CIGSLT.mapOneHoleContext, costBaseLanguageDefSymbolMap] using
          inductionHypothesis
  | @collectionElement elementSort rule parameterName collectionType
      before after rest inner ruleMembership parameters notSelected
      innerStable inductionHypothesis =>
      apply SignatureContext.collectionElement
          (rule := costBaseConstructor cut rule)
          (parameterName := parameterName)
          (elementSort := costBaseSortName elementSort)
      · exact plan.costBaseConstructor_mem_generated rule ruleMembership
      · simp [costBaseConstructor_def, parameters, costBaseParameter_def, notSelected,
          mapParameterType, costBaseTypeExpr]
      · simpa [CIGSLT.mapOneHoleContext, costBaseLanguageDefSymbolMap] using
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
      (CIGSLT.mapOneHoleContext costBaseLanguageDefSymbolMap context) := by
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
        simp [costBaseParameter_def, notSelected, mapParameterType,
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
      · simpa [CIGSLT.mapOneHoleContext, costBaseLanguageDefSymbolMap] using
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
        simp [costBaseParameter_def, notSelected, mapParameterType,
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
      · simpa [CIGSLT.mapOneHoleContext, costBaseLanguageDefSymbolMap] using
          inductionHypothesis
  | @collectionElement elementSort rule parameterName collectionType
      before after rest inner ruleMembership parameters notSelected
      innerStable inductionHypothesis =>
      apply ContinuationStableContext.collectionElement
          (rule := costBaseConstructor sourceCut rule)
          (parameterName := parameterName)
          (elementSort := costBaseSortName elementSort)
      · exact includesConstructor rule ruleMembership
      · simp [costBaseConstructor_def, parameters, costBaseParameter_def, notSelected,
          mapParameterType, costBaseTypeExpr]
      · rw [selection rule ruleMembership 0, notSelected]
      · simpa [CIGSLT.mapOneHoleContext, costBaseLanguageDefSymbolMap] using
          inductionHypothesis

end ContinuationStableContext

namespace ContinuationRetypingPlan

open ContinuationDecorationProfile (ofRetypingPlan)

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Translate the contractum, selecting wrapped constructor copies exactly
where the cut-derived hereditary closure requires them. -/
def mapContractum (plan : ContinuationRetypingPlan cut) : Pattern → Pattern :=
  (ofRetypingPlan plan).mapContractum

theorem mapContractum_bvar (plan : ContinuationRetypingPlan cut) (index : Nat) :
    plan.mapContractum (.bvar index) = .bvar index :=
  rfl

theorem mapContractum_fvar (plan : ContinuationRetypingPlan cut) (name : String) :
    plan.mapContractum (.fvar name) = .fvar name :=
  rfl

theorem mapContractum_apply (plan : ContinuationRetypingPlan cut)
    (constructor : String) (arguments : List Pattern) :
    plan.mapContractum (.apply constructor arguments) =
      .apply
        (if constructor ∈ plan.wrappedLabels then
          costWrappedConstructorName constructor
        else
          costBaseConstructorName constructor)
        (arguments.map plan.mapContractum) := by
  change Pattern.apply _ (mapPatternList _ arguments) = _
  rw [mapPatternList_eq_map]
  rfl

theorem mapContractum_lambda (plan : ContinuationRetypingPlan cut)
    (binder : Option String) (body : Pattern) :
    plan.mapContractum (.lambda binder body) = .lambda binder (plan.mapContractum body) :=
  rfl

theorem mapContractum_multiLambda (plan : ContinuationRetypingPlan cut)
    (arity : Nat) (binders : List String) (body : Pattern) :
    plan.mapContractum (.multiLambda arity binders body) =
      .multiLambda arity binders (plan.mapContractum body) :=
  rfl

theorem mapContractum_subst (plan : ContinuationRetypingPlan cut)
    (body replacement : Pattern) :
    plan.mapContractum (.subst body replacement) =
      .subst (plan.mapContractum body) (plan.mapContractum replacement) :=
  rfl

theorem mapContractum_collection (plan : ContinuationRetypingPlan cut)
    (collectionType : CollType) (elements : List Pattern) (rest : Option String) :
    plan.mapContractum (.collection collectionType elements rest) =
      .collection collectionType (elements.map plan.mapContractum) rest := by
  change Pattern.collection collectionType (mapPatternList _ elements) rest = _
  rw [mapPatternList_eq_map]
  rfl

/-- Retype exactly the two selected continuation metavariables to the wrapped
fiber.  All other rewrite variables enter the tagged base copy. -/
def generatedFreeContext (plan : ContinuationRetypingPlan cut) : FreeTypeContext :=
  (ofRetypingPlan plan).generatedFreeContext

theorem generatedFreeContext_apply (plan : ContinuationRetypingPlan cut) (name : String) :
    plan.generatedFreeContext name =
      (lookupTypeContext
        theory.presentation.interactionRewrite.1.typeContext name).map fun type =>
        if name = cut.program.continuationVariable.name ∨
            name = cut.environment.continuationVariable.name then
          costWrappedTypeExpr theory.presentation.interactingSort.1.name type
        else
          costBaseTypeExpr type :=
  rfl

/-- The precise wrappability obligation: the exact authored interaction
contractum, translated by the finite declaration plan, has the wrapped-term
sort. -/
def Wrappable (plan : ContinuationRetypingPlan cut) : Prop :=
  (ofRetypingPlan plan).Wrappable

theorem wrappable_def (plan : ContinuationRetypingPlan cut) :
    plan.Wrappable ↔
      HasSort plan.generatedLanguage plan.generatedFreeContext []
        (plan.mapContractum theory.presentation.interactionRewrite.1.right)
        costWrappedSortName :=
  Iff.rfl

/-- The selected interaction redex remains sorted after its two continuation
positions are moved to the wrapped fiber.  This is the source-side companion
of `Wrappable`, which types the contractum. -/
def RedexRetypable (plan : ContinuationRetypingPlan cut) : Prop :=
  (ofRetypingPlan plan).RedexRetypable

theorem redexRetypable_def (plan : ContinuationRetypingPlan cut) :
    plan.RedexRetypable ↔
      HasSort plan.generatedLanguage plan.generatedFreeContext []
        (mapPattern costBaseLanguageDefSymbolMap
          theory.presentation.interactionRewrite.1.left)
        (costBaseSortName theory.presentation.interactingSort.1.name) :=
  Iff.rfl

end ContinuationRetypingPlan

/-! ## The general definitions at the plan's profile -/

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

@[simp] theorem ofRetypingPlan_selectedParameter (plan : ContinuationRetypingPlan cut)
    (constructor : GrammarRule) (index : Nat) :
    (ofRetypingPlan plan).selectedParameter constructor index =
      isSelectedContinuation cut constructor index :=
  rfl

@[simp] theorem ofRetypingPlan_baseConstructor (plan : ContinuationRetypingPlan cut)
    (constructor : GrammarRule) :
    (ofRetypingPlan plan).baseConstructor constructor = costBaseConstructor cut constructor :=
  rfl

@[simp] theorem ofRetypingPlan_generatedLanguage (plan : ContinuationRetypingPlan cut) :
    (ofRetypingPlan plan).generatedLanguage = plan.generatedLanguage :=
  rfl

@[simp] theorem ofRetypingPlan_generatedFreeContext (plan : ContinuationRetypingPlan cut) :
    (ofRetypingPlan plan).generatedFreeContext = plan.generatedFreeContext :=
  rfl

@[simp] theorem ofRetypingPlan_mapContractum (plan : ContinuationRetypingPlan cut)
    (pattern : Pattern) :
    (ofRetypingPlan plan).mapContractum pattern = plan.mapContractum pattern :=
  rfl

/-- The plan's sorting obligation is the profile's. -/
theorem ofRetypingPlan_wrappable_iff (plan : ContinuationRetypingPlan cut) :
    (ofRetypingPlan plan).Wrappable ↔ plan.Wrappable :=
  Iff.rfl

theorem ofRetypingPlan_redexRetypable_iff (plan : ContinuationRetypingPlan cut) :
    (ofRetypingPlan plan).RedexRetypable ↔ plan.RedexRetypable :=
  Iff.rfl

end ContinuationDecorationProfile

end Mettapedia.GSLT.LanguageDef
