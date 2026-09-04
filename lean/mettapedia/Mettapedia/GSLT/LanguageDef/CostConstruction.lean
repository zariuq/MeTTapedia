import Mettapedia.GSLT.LanguageDef.CostNamespace

/-!
# Declaration-derived Cost signature

This module begins the generic Cost construction at its structural boundary.
It adjoins symbolic signatures, wrapped terms, and ordered token stacks to the
validated continuation signature of a continued interactive GSLT.  Located
purses are a subsequent location-indexed refinement; they are not identified
with this location-independent core.

The output remains derived from the source `LanguageDef`.  Generated
constructors carry no parser notation or host evaluator policy, and the
result passes the ordinary `LanguageDef.validate` gate.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism
open ContinuationRetypingPlan

/-! ## Core apparatus declarations -/

def costCoreSortSuffixes : List String := ["signature", "token-stack"]

/-- Intrinsic enumeration of the apparatus sorts rendered by
`costCoreSortSuffixes`. -/
def costCoreSortKinds : List CostApparatusSort :=
  [.signature, .tokenStack]

@[simp]
theorem costCoreSortKinds_suffixes :
    costCoreSortKinds.map CostApparatusSort.suffix = costCoreSortSuffixes :=
  rfl

def costCoreTypes : List TypeDecl :=
  costCoreSortSuffixes.map fun suffix =>
    TypeDecl.plain (costApparatusSortName suffix)

/-- The serialized apparatus type declarations are exactly the rendering of
the intrinsic generated sort enumeration. -/
theorem costCoreTypes_eq_typed :
    costCoreTypes = costCoreSortKinds.map fun kind =>
      TypeDecl.plain kind.render :=
  rfl

def costSignatureUnitConstructor : GrammarRule where
  label := costSignatureUnitConstructorName
  category := costSignatureSortName
  params := []
  syntaxPattern := []

def costSignatureProductConstructor : GrammarRule where
  label := costSignatureProductConstructorName
  category := costSignatureSortName
  params :=
    [.simple "left" (.base costSignatureSortName),
      .simple "right" (.base costSignatureSortName)]
  syntaxPattern := []

def costSignedConstructor (interactingSort : String) : GrammarRule where
  label := costSignedConstructorName
  category := costWrappedSortName
  params :=
    [.simple "body" (.base (costBaseSortName interactingSort)),
      .simple "signature" (.base costSignatureSortName)]
  syntaxPattern := []

def costTokenStackEmptyConstructor : GrammarRule where
  label := costTokenStackEmptyConstructorName
  category := costTokenStackSortName
  params := []
  syntaxPattern := []

def costTokenStackConsConstructor : GrammarRule where
  label := costTokenStackConsConstructorName
  category := costTokenStackSortName
  params :=
    [.simple "head" (.base costSignatureSortName),
      .simple "tail" (.base costTokenStackSortName)]
  syntaxPattern := []

/-- Embed an ordered token stack into the wrapped interacting carrier.  This
is the administrative funding operand of the generated interaction cut. -/
def costFundingConstructor : GrammarRule where
  label := costFundingConstructorName
  category := costWrappedSortName
  params := [.simple "stack" (.base costTokenStackSortName)]
  syntaxPattern := []

/-- Explicit contact at the wrapped carrier.  Keeping this constructor
separate from the source contact avoids pretending that one `LanguageDef`
constructor has several incompatible profiles. -/
def costContactConstructor : GrammarRule where
  label := costContactConstructorName
  category := costWrappedSortName
  params :=
    [.simple "left" (.base costWrappedSortName),
      .simple "right" (.base costWrappedSortName)]
  syntaxPattern := []

/-! ## The generated forcing operands are gates, not source introductions -/

/-- The signed operand exposes the embedded source process, rather than a
continuation of the generated wrapped carrier.  Consequently the literal
outer forcing shape is not itself an `IntroductionProfile`; the continued
cut retained by Cost is the retyped source cut beneath this gate. -/
@[simp]
theorem costSignedConstructor_bodyParameter (interactingSort : String) :
    (costSignedConstructor interactingSort).params[0]? =
      some (.simple "body" (.base (costBaseSortName interactingSort))) :=
  rfl

theorem costSignedBody_not_wrappedContinuation (interactingSort : String) :
    continuationResult?
        (.simple "body" (.base (costBaseSortName interactingSort))) ≠
      some (.base costWrappedSortName) := by
  intro equality
  have sortEquality :
      costBaseSortName interactingSort = costWrappedSortName := by
    simpa [continuationResult?, WellSorted.parameterType?] using equality
  exact costBaseSortName_ne_wrapped interactingSort sortEquality

/-- The funding operand exposes a token-stack tail, not a continuation of the
generated wrapped carrier.  It therefore belongs to the structural envelope
around the retained cut, not to the pair of continuation-bearing source
introductions. -/
@[simp]
theorem costFundingConstructor_stackParameter :
    costFundingConstructor.params[0]? =
      some (.simple "stack" (.base costTokenStackSortName)) :=
  rfl

theorem costFundingStack_not_wrappedContinuation :
    continuationResult? (.simple "stack" (.base costTokenStackSortName)) ≠
      some (.base costWrappedSortName) := by
  intro equality
  have sortEquality : costTokenStackSortName = costWrappedSortName := by
    simpa [continuationResult?, WellSorted.parameterType?] using equality
  exact costWrappedSortName_ne_apparatus "token-stack" sortEquality.symm

def costCoreConstructorSuffixes : List String :=
  ["signature-unit", "signature-product", "signed",
    "token-stack-empty", "token-stack-cons", "funding", "contact"]

/-- Intrinsic enumeration of the fixed Cost apparatus constructors. -/
def costCoreConstructorKinds : List CostApparatusConstructor :=
  [.signatureUnit, .signatureProduct, .signed,
    .tokenStackEmpty, .tokenStackCons, .funding, .contact]

@[simp]
theorem costCoreConstructorKinds_suffixes :
    costCoreConstructorKinds.map CostApparatusConstructor.suffix =
      costCoreConstructorSuffixes :=
  rfl

/-- Declaration carried by one intrinsic apparatus constructor. -/
def CostApparatusConstructor.grammarRule (interactingSort : String) :
    CostApparatusConstructor → GrammarRule
  | .signatureUnit => costSignatureUnitConstructor
  | .signatureProduct => costSignatureProductConstructor
  | .signed => costSignedConstructor interactingSort
  | .tokenStackEmpty => costTokenStackEmptyConstructor
  | .tokenStackCons => costTokenStackConsConstructor
  | .funding => costFundingConstructor
  | .contact => costContactConstructor

def costCoreConstructors (interactingSort : String) : List GrammarRule :=
  [costSignatureUnitConstructor, costSignatureProductConstructor,
    costSignedConstructor interactingSort, costTokenStackEmptyConstructor,
    costTokenStackConsConstructor, costFundingConstructor,
    costContactConstructor]

/-- The serialized apparatus declarations are exactly the rendering of the
intrinsic constructor enumeration. -/
theorem costCoreConstructors_eq_typed (interactingSort : String) :
    costCoreConstructors interactingSort =
      costCoreConstructorKinds.map (·.grammarRule interactingSort) :=
  rfl

/-! ## The validated core signature -/

namespace CIGSLT

/-- Add the location-independent Cost apparatus to the exact generated
continuation signature of a continued interactive GSLT. -/
def costCoreLanguage (source : CIGSLT) : LanguageDef :=
  { source.continuationRetyping.generatedLanguage with
    name := "$cost:core:" ++ source.theory.presentation.presentation.language.name
    types := source.continuationRetyping.generatedLanguage.types ++ costCoreTypes
    terms := source.continuationRetyping.generatedLanguage.terms ++
      costCoreConstructors source.theory.presentation.interactingSort.1.name }

@[simp]
theorem costCoreLanguage_typeNames (source : CIGSLT) :
    source.costCoreLanguage.typeNames =
      source.continuationRetyping.generatedLanguage.typeNames ++
        costCoreSortSuffixes.map costApparatusSortName := by
  simp [costCoreLanguage, costCoreTypes, LanguageDef.typeNames,
    TypeDecl.plain, List.map_map]

private theorem costCoreTypeNames_nodup (source : CIGSLT) :
    source.costCoreLanguage.typeNames.Nodup := by
  rw [costCoreLanguage_typeNames, List.nodup_append]
  refine ⟨generatedTypeNames_nodup source.continuationRetyping, ?_, ?_⟩
  · exact (show costCoreSortSuffixes.Nodup by decide).map
      costApparatusSortName_injective
  · intro generated generatedMembership apparatus apparatusMembership
    rw [generatedLanguage_typeNames] at generatedMembership
    rcases List.mem_append.mp generatedMembership with
      baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with ⟨base, _, rfl⟩
      rcases List.mem_map.mp apparatusMembership with ⟨suffix, _, rfl⟩
      exact costBaseSortName_ne_apparatus base suffix
    · simp only [List.mem_singleton] at wrappedMembership
      subst generated
      rcases List.mem_map.mp apparatusMembership with ⟨suffix, _, rfl⟩
      exact costWrappedSortName_ne_apparatus suffix

theorem costCoreConstructorLabels (source : CIGSLT) :
    source.costCoreLanguage.terms.map (·.label) =
      source.continuationRetyping.generatedLanguage.terms.map (·.label) ++
        costCoreConstructorSuffixes.map costApparatusConstructorName := by
  simp [costCoreLanguage, costCoreConstructors, costCoreConstructorSuffixes,
    costSignatureUnitConstructor, costSignatureProductConstructor,
    costSignedConstructor, costTokenStackEmptyConstructor,
    costTokenStackConsConstructor, costFundingConstructor,
    costContactConstructor, costSignatureUnitConstructorName,
    costSignatureProductConstructorName, costSignedConstructorName,
    costTokenStackEmptyConstructorName, costTokenStackConsConstructorName,
    costFundingConstructorName, costContactConstructorName]

private theorem costCoreConstructorLabels_nodup (source : CIGSLT) :
    (source.costCoreLanguage.terms.map (·.label)).Nodup := by
  rw [costCoreConstructorLabels, List.nodup_append]
  refine ⟨generatedConstructorLabels_nodup source.continuationRetyping,
    ?_, ?_⟩
  · exact (show costCoreConstructorSuffixes.Nodup by decide).map
      costApparatusConstructorName_injective
  · intro generated generatedMembership apparatus apparatusMembership
    rw [ContinuationRetypingPlan.generatedLanguage_constructorLabels]
      at generatedMembership
    rcases List.mem_append.mp generatedMembership with
      baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with ⟨base, _, rfl⟩
      rcases List.mem_map.mp apparatusMembership with ⟨suffix, _, rfl⟩
      exact costBaseConstructorName_ne_apparatus base suffix
    · rcases List.mem_map.mp wrappedMembership with ⟨wrapped, _, rfl⟩
      rcases List.mem_map.mp apparatusMembership with ⟨suffix, _, rfl⟩
      exact costWrappedConstructorName_ne_apparatus wrapped suffix

private theorem costCoreTerm_category_mem (source : CIGSLT)
    (term : GrammarRule) (membership : term ∈ source.costCoreLanguage.terms) :
    term.category ∈ source.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  simp only [costCoreLanguage, List.mem_append] at membership
  rcases membership with generatedMembership | apparatusMembership
  · exact List.mem_append_left _
      (generatedTerm_category_mem source.continuationRetyping term
        generatedMembership)
  · simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at apparatusMembership
    rcases apparatusMembership with equality | equality | equality | equality |
      equality | equality | equality <;> subst term <;>
      simp [costCoreSortSuffixes, costSignatureUnitConstructor,
        costSignatureProductConstructor, costSignedConstructor,
        costTokenStackEmptyConstructor, costTokenStackConsConstructor,
        costFundingConstructor, costContactConstructor,
        costSignatureSortName, costTokenStackSortName]

private theorem costCoreTerm_parameter_baseName_mem (source : CIGSLT)
    (term : GrammarRule) (termMembership : term ∈ source.costCoreLanguage.terms)
    (parameter : TermParam) (parameterMembership : parameter ∈ term.params)
    (name : String)
    (nameMembership : name ∈ (TermParam.typeExpr parameter).baseNames) :
    name ∈ source.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  simp only [costCoreLanguage, List.mem_append] at termMembership
  rcases termMembership with generatedMembership | apparatusMembership
  · exact List.mem_append_left _
      (generatedTerm_parameter_baseName_mem source.continuationRetyping term
        generatedMembership parameter parameterMembership name nameMembership)
  · have signatureMembership : costSignatureSortName ∈
        source.continuationRetyping.generatedLanguage.typeNames ++
          costCoreSortSuffixes.map costApparatusSortName :=
      List.mem_append_right _ (by
        simp [costCoreSortSuffixes, costSignatureSortName])
    have stackMembership : costTokenStackSortName ∈
        source.continuationRetyping.generatedLanguage.typeNames ++
          costCoreSortSuffixes.map costApparatusSortName :=
      List.mem_append_right _ (by
        simp [costCoreSortSuffixes, costTokenStackSortName])
    have wrappedMembership : costWrappedSortName ∈
        source.continuationRetyping.generatedLanguage.typeNames ++
          costCoreSortSuffixes.map costApparatusSortName :=
      List.mem_append_left _ (by
        rw [generatedLanguage_typeNames]
        exact List.mem_append_right _ (by simp))
    have interactingMembership :
        costBaseSortName source.theory.presentation.interactingSort.1.name ∈
          source.continuationRetyping.generatedLanguage.typeNames ++
            costCoreSortSuffixes.map costApparatusSortName := by
      apply List.mem_append_left
      rw [generatedLanguage_typeNames]
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨source.theory.presentation.interactingSort.1.name,
        List.mem_map.mpr
          ⟨source.theory.presentation.interactingSort.1,
            source.theory.presentation.interactingSort.2, rfl⟩, rfl⟩
    simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at apparatusMembership
    rcases apparatusMembership with equality | equality | equality | equality |
      equality | equality | equality
    · subst term
      simp [costSignatureUnitConstructor] at parameterMembership
    · subst term
      simp [costSignatureProductConstructor] at parameterMembership
      rcases parameterMembership with equality | equality
      · subst parameter
        have nameEquality : name = costSignatureSortName := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact signatureMembership
      · subst parameter
        have nameEquality : name = costSignatureSortName := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact signatureMembership
    · subst term
      simp [costSignedConstructor] at parameterMembership
      rcases parameterMembership with equality | equality
      · subst parameter
        have nameEquality : name =
            costBaseSortName
              source.theory.presentation.interactingSort.1.name := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact interactingMembership
      · subst parameter
        have nameEquality : name = costSignatureSortName := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact signatureMembership
    · subst term
      simp [costTokenStackEmptyConstructor] at parameterMembership
    · subst term
      simp [costTokenStackConsConstructor] at parameterMembership
      rcases parameterMembership with equality | equality
      · subst parameter
        have nameEquality : name = costSignatureSortName := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact signatureMembership
      · subst parameter
        have nameEquality : name = costTokenStackSortName := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact stackMembership
    · subst term
      simp [costFundingConstructor] at parameterMembership
      subst parameter
      have nameEquality : name = costTokenStackSortName := by
        simpa only [TermParam.typeExpr, TypeExpr.baseNames,
          List.mem_singleton] using nameMembership
      subst name
      exact stackMembership
    · subst term
      simp [costContactConstructor] at parameterMembership
      rcases parameterMembership with equality | equality
      · subst parameter
        have nameEquality : name = costWrappedSortName := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact wrappedMembership
      · subst parameter
        have nameEquality : name = costWrappedSortName := by
          simpa only [TermParam.typeExpr, TypeExpr.baseNames,
            List.mem_singleton] using nameMembership
        subst name
        exact wrappedMembership

theorem costCoreTerm_syntaxPattern_eq_nil (source : CIGSLT)
    (term : GrammarRule) (termMembership : term ∈ source.costCoreLanguage.terms) :
    term.syntaxPattern = [] := by
  simp only [costCoreLanguage, List.mem_append] at termMembership
  rcases termMembership with generatedMembership | apparatusMembership
  · exact generatedTerm_syntaxPattern_eq_nil source.continuationRetyping term
      generatedMembership
  · simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at apparatusMembership
    rcases apparatusMembership with equality | equality | equality | equality |
      equality | equality | equality <;> subst term <;> rfl

/-- The generic signature/wrapper/ordered-stack core passes the ordinary
language validation gate. -/
theorem costCoreLanguage_validate (source : CIGSLT) :
    source.costCoreLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · exact costCoreTypeNames_nodup source
  · exact costCoreConstructorLabels_nodup source
  · exact costCoreTerm_category_mem source
  · exact costCoreTerm_parameter_baseName_mem source
  · intro term termMembership
    exact Or.inl (costCoreTerm_syntaxPattern_eq_nil source term termMembership)

/-- The exact structural output of the first Cost object-map layer. -/
def costCorePresentation (source : CIGSLT) : ValidatedLanguageDef where
  language := source.costCoreLanguage
  valid := costCoreLanguage_validate source

/-! ## Exact intrinsic classification of generated declarations -/

/-- Materialize one exact intrinsic Cost constructor as the corresponding
`GrammarRule` in the generated `LanguageDef`. -/
def materializeDeclaredCostConstructor (source : CIGSLT) :
    source.DeclaredCostConstructor → GrammarRule
  | ⟨.base constructor, _⟩ =>
      costBaseConstructor source.cut constructor.1
  | ⟨.wrapped constructor, _⟩ =>
      costWrappedConstructor (theory := source.theory) constructor.1
  | ⟨.apparatus kind, _⟩ =>
      kind.grammarRule source.theory.presentation.interactingSort.1.name

@[simp]
theorem materializeDeclaredCostConstructor_label (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    (source.materializeDeclaredCostConstructor constructor).label =
      source.renderDeclaredCostConstructor constructor := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base sourceConstructor => rfl
  | wrapped sourceConstructor => rfl
  | apparatus kind =>
      cases kind <;> rfl

/-- Intrinsic declaration identity is preserved by materialization. -/
theorem materializeDeclaredCostConstructor_injective (source : CIGSLT) :
    Function.Injective source.materializeDeclaredCostConstructor := by
  intro left right equality
  apply source.renderDeclaredCostConstructor_injective
  rw [← source.materializeDeclaredCostConstructor_label left,
    ← source.materializeDeclaredCostConstructor_label right, equality]

/-- Every intrinsic declared constructor materializes into the exact
generated Cost declaration list. -/
theorem materializeDeclaredCostConstructor_mem (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    source.materializeDeclaredCostConstructor constructor ∈
      source.costCoreLanguage.terms := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base sourceConstructor =>
      exact List.mem_append_left _
        (source.continuationRetyping.costBaseConstructor_mem_generated
          sourceConstructor.1 sourceConstructor.2)
  | wrapped sourceConstructor =>
      exact List.mem_append_left _
        (source.continuationRetyping.costWrappedConstructor_mem_generated
          sourceConstructor declared)
  | apparatus kind =>
      apply List.mem_append_right
      cases kind <;> simp [costCoreConstructors,
        materializeDeclaredCostConstructor,
        CostApparatusConstructor.grammarRule]

/-- Conversely, every generated Cost grammar declaration has an intrinsic
declared constructor. -/
theorem exists_declaredCostConstructor_of_mem (source : CIGSLT)
    (rule : GrammarRule) (membership : rule ∈ source.costCoreLanguage.terms) :
    ∃ constructor : source.DeclaredCostConstructor,
      source.materializeDeclaredCostConstructor constructor = rule := by
  simp only [costCoreLanguage, List.mem_append] at membership
  rcases membership with generatedMembership | apparatusMembership
  · simp only [ContinuationRetypingPlan.generatedLanguage,
      List.mem_append] at generatedMembership
    rcases generatedMembership with baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with
        ⟨sourceRule, sourceMembership, equality⟩
      let sourceConstructor :
          DeclaredConstructor source.theory.presentation.presentation :=
        ⟨sourceRule, sourceMembership⟩
      refine ⟨⟨.base sourceConstructor, True.intro⟩, ?_⟩
      exact equality
    · rcases List.mem_map.mp wrappedMembership with
        ⟨sourceConstructor, wrappedMembership, equality⟩
      refine ⟨⟨.wrapped sourceConstructor, wrappedMembership⟩, ?_⟩
      exact equality
  · simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at apparatusMembership
    rcases apparatusMembership with equality | equality | equality | equality |
      equality | equality | equality <;> subst rule
    · exact ⟨⟨.apparatus .signatureUnit, True.intro⟩, rfl⟩
    · exact ⟨⟨.apparatus .signatureProduct, True.intro⟩, rfl⟩
    · exact ⟨⟨.apparatus .signed, True.intro⟩, rfl⟩
    · exact ⟨⟨.apparatus .tokenStackEmpty, True.intro⟩, rfl⟩
    · exact ⟨⟨.apparatus .tokenStackCons, True.intro⟩, rfl⟩
    · exact ⟨⟨.apparatus .funding, True.intro⟩, rfl⟩
    · exact ⟨⟨.apparatus .contact, True.intro⟩, rfl⟩

/-- The intrinsic declared-constructor namespace is exactly the attached
constructor carrier of the validated generated Cost presentation. -/
noncomputable def declaredCostConstructorEquiv (source : CIGSLT) :
    source.DeclaredCostConstructor ≃
      DeclaredConstructor source.costCorePresentation :=
  Equiv.ofBijective
    (fun constructor =>
      ⟨source.materializeDeclaredCostConstructor constructor,
        source.materializeDeclaredCostConstructor_mem constructor⟩)
    ⟨by
      intro left right equality
      apply source.materializeDeclaredCostConstructor_injective
      exact congrArg Subtype.val equality,
      by
        intro target
        rcases source.exists_declaredCostConstructor_of_mem
            target.1 target.2 with ⟨sourceConstructor, equality⟩
        refine ⟨sourceConstructor, ?_⟩
        exact Subtype.ext equality⟩

/-- Finite intrinsic enumeration of the exact generated Cost constructors.
This is the executable inverse domain for faithful wire rendering. -/
def declaredCostConstructors (source : CIGSLT) :
    List source.DeclaredCostConstructor :=
  source.theory.presentation.presentation.language.terms.attach.map
      (fun constructor =>
        (⟨.base constructor, True.intro⟩ :
          source.DeclaredCostConstructor)) ++
    source.continuationRetyping.wrappedConstructors.attach.map
      (fun constructor =>
        (⟨.wrapped constructor.1, constructor.2⟩ :
          source.DeclaredCostConstructor)) ++
    costCoreConstructorKinds.map
      (fun kind =>
        (⟨.apparatus kind, True.intro⟩ :
          source.DeclaredCostConstructor))

/-- Every exact generated constructor occurs in the intrinsic enumeration. -/
theorem mem_declaredCostConstructors (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    constructor ∈ source.declaredCostConstructors := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base sourceConstructor =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨sourceConstructor, List.mem_attach _ sourceConstructor, ?_⟩
      rfl
  | wrapped sourceConstructor =>
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨⟨sourceConstructor, declared⟩,
        List.mem_attach _ ⟨sourceConstructor, declared⟩, ?_⟩
      rfl
  | apparatus kind =>
      apply List.mem_append_right
      cases kind <;> simp [costCoreConstructorKinds]

/-- Search a finite intrinsic constructor list by its faithful wire name. -/
def resolveDeclaredCostConstructor (source : CIGSLT) (name : String) :
    List source.DeclaredCostConstructor →
      Option source.DeclaredCostConstructor
  | [] => none
  | constructor :: constructors =>
      if source.renderDeclaredCostConstructor constructor = name then
        some constructor
      else
        source.resolveDeclaredCostConstructor name constructors

/-- Faithful rendering makes finite constructor resolution exact. -/
theorem resolveDeclaredCostConstructor_render_of_mem (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor)
    (constructors : List source.DeclaredCostConstructor)
    (membership : constructor ∈ constructors) :
    source.resolveDeclaredCostConstructor
        (source.renderDeclaredCostConstructor constructor) constructors =
      some constructor := by
  induction constructors with
  | nil => cases membership
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at membership
      rcases membership with equality | tailMembership
      · subst head
        simp [resolveDeclaredCostConstructor]
      · simp only [resolveDeclaredCostConstructor]
        split
        · rename_i renderedEquality
          have constructorEquality : head = constructor :=
            source.renderDeclaredCostConstructor_injective renderedEquality
          subst head
          rfl
        · exact inductionHypothesis tailMembership

/-- Executable decoding of one exact generated Cost constructor name. -/
def decodeDeclaredCostConstructor (source : CIGSLT) (name : String) :
    Option source.DeclaredCostConstructor :=
  source.resolveDeclaredCostConstructor name source.declaredCostConstructors

/-- Decoding is a left inverse of faithful constructor rendering. -/
@[simp]
theorem decodeDeclaredCostConstructor_render (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    source.decodeDeclaredCostConstructor
        (source.renderDeclaredCostConstructor constructor) = some constructor := by
  exact source.resolveDeclaredCostConstructor_render_of_mem constructor
    source.declaredCostConstructors (source.mem_declaredCostConstructors constructor)

/-- Positive control: the generic wrapper consumes the tagged source
interacting sort and a symbolic signature, and returns a wrapped term. -/
theorem costSignedConstructor_profile (source : CIGSLT) :
    costSignedConstructor source.theory.presentation.interactingSort.1.name =
      { label := costSignedConstructorName
        category := costWrappedSortName
        params :=
          [.simple "body" (.base (costBaseSortName
            source.theory.presentation.interactingSort.1.name)),
            .simple "signature" (.base costSignatureSortName)]
        syntaxPattern := [] } :=
  rfl

/-- Negative control: the generated core contains no constructor from a
wrapped term back to the tagged source interacting sort. -/
theorem no_core_unwrapper (source : CIGSLT) :
    ¬ ∃ constructor ∈ costCoreConstructors
        source.theory.presentation.interactingSort.1.name,
      constructor.category =
          costBaseSortName source.theory.presentation.interactingSort.1.name ∧
        ∃ parameter ∈ constructor.params,
          TermParam.typeExpr parameter = .base costWrappedSortName := by
  rintro ⟨constructor, membership, categoryEquality, _parameter⟩
  simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false]
    at membership
  rcases membership with equality | equality | equality | equality | equality |
      equality | equality <;> subst constructor
  · exact (costBaseSortName_ne_apparatus
      source.theory.presentation.interactingSort.1.name "signature")
        categoryEquality.symm
  · exact (costBaseSortName_ne_apparatus
      source.theory.presentation.interactingSort.1.name "signature")
        categoryEquality.symm
  · exact (costBaseSortName_ne_wrapped
      source.theory.presentation.interactingSort.1.name) categoryEquality.symm
  · exact (costBaseSortName_ne_apparatus
      source.theory.presentation.interactingSort.1.name "token-stack")
        categoryEquality.symm
  · exact (costBaseSortName_ne_apparatus
      source.theory.presentation.interactingSort.1.name "token-stack")
        categoryEquality.symm
  · exact (costBaseSortName_ne_wrapped
      source.theory.presentation.interactingSort.1.name) categoryEquality.symm
  · exact (costBaseSortName_ne_wrapped
      source.theory.presentation.interactingSort.1.name) categoryEquality.symm

end CIGSLT

end Mettapedia.GSLT.LanguageDef
