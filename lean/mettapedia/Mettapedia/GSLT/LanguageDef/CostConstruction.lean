import Mettapedia.GSLT.LanguageDef.CostNamespace
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension

/-!
# Declaration-derived Cost signature

This module begins the generic Cost construction at its structural boundary.
It adjoins symbolic signatures, wrapped terms, and ordered token stacks to the
validated continuation signature of a wrappable theory.  Located
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

def costCoreSortSuffixes : List String := ["signature", "key", "token-stack"]

/-- Intrinsic enumeration of the apparatus sorts rendered by
`costCoreSortSuffixes`. -/
def costCoreSortKinds : List CostApparatusSort :=
  [.signature, .key, .tokenStack]

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

/-- Exact keys have a finite tree grammar independently of signature product. -/
def costKeyLeafConstructor : GrammarRule where
  label := costKeyLeafConstructorName
  category := costKeySortName
  params := []
  syntaxPattern := []

def costKeyBranchConstructor : GrammarRule where
  label := costKeyBranchConstructorName
  category := costKeySortName
  params := [.simple "left" (.base costKeySortName),
    .simple "right" (.base costKeySortName)]
  syntaxPattern := []

/-- A committed key is a signature generator, rather than the monoid unit. -/
def costSignatureCommitConstructor : GrammarRule where
  label := costSignatureCommitConstructorName
  category := costSignatureSortName
  params := [.simple "key" (.base costKeySortName)]
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
outer forcing shape is not itself an `IntroductionProfile`; the cut retained
by Cost is the retyped source cut beneath this gate. -/
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
  ["signature-unit", "signature-product", "key-leaf", "key-branch", "signature-commit", "signed",
    "token-stack-empty", "token-stack-cons", "funding", "contact"]

/-- Intrinsic enumeration of the fixed Cost apparatus constructors. -/
def costCoreConstructorKinds : List CostApparatusConstructor :=
  [.signatureUnit, .signatureProduct, .keyLeaf, .keyBranch, .signatureCommit, .signed,
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
  | .keyLeaf => costKeyLeafConstructor
  | .keyBranch => costKeyBranchConstructor
  | .signatureCommit => costSignatureCommitConstructor
  | .signed => costSignedConstructor interactingSort
  | .tokenStackEmpty => costTokenStackEmptyConstructor
  | .tokenStackCons => costTokenStackConsConstructor
  | .funding => costFundingConstructor
  | .contact => costContactConstructor

/-- Apparatus rows never present an implicit collection carrier. -/
theorem CostApparatusConstructor.grammarRule_notBare (interactingSort : String)
    (kind : CostApparatusConstructor) :
    ¬ WellSorted.UsesBareCollection (kind.grammarRule interactingSort) := by
  cases kind <;>
    simp [CostApparatusConstructor.grammarRule, WellSorted.UsesBareCollection,
      costSignatureUnitConstructor, costSignatureProductConstructor,
      costKeyLeafConstructor, costKeyBranchConstructor, costSignatureCommitConstructor,
      costSignedConstructor, costTokenStackEmptyConstructor, costTokenStackConsConstructor,
      costFundingConstructor, costContactConstructor]

def costCoreConstructors (interactingSort : String) : List GrammarRule :=
  [costSignatureUnitConstructor, costSignatureProductConstructor,
    costKeyLeafConstructor, costKeyBranchConstructor, costSignatureCommitConstructor,
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

namespace ContinuationDecorationProfile

open WellSorted


variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Append the existing Cost apparatus to the exact finite continuation
signature, retaining every selected operand parameter. -/
def costCoreLanguage (profile : ContinuationDecorationProfile cut) : LanguageDef :=
  { profile.generatedLanguage with
    name := "$cost:core:" ++ theory.presentation.presentation.language.name
    types := profile.generatedLanguage.types ++ costCoreTypes
    terms := profile.generatedLanguage.terms ++
      costCoreConstructors theory.presentation.interactingSort.1.name }

theorem costCoreLanguage_typeNames (profile : ContinuationDecorationProfile cut) :
    profile.costCoreLanguage.typeNames = profile.generatedLanguage.typeNames ++
      costCoreSortSuffixes.map costApparatusSortName := by
  simp [costCoreLanguage, costCoreTypes, LanguageDef.typeNames,
    TypeDecl.plain, List.map_map]

theorem costCoreConstructorLabels (profile : ContinuationDecorationProfile cut) :
    profile.costCoreLanguage.terms.map (·.label) =
      profile.generatedLanguage.terms.map (·.label) ++
        costCoreConstructorSuffixes.map costApparatusConstructorName := by
  simp [costCoreLanguage, costCoreConstructors, costCoreConstructorSuffixes,
    costSignatureUnitConstructor, costSignatureProductConstructor,
    costKeyLeafConstructor, costKeyBranchConstructor, costSignatureCommitConstructor,
    costSignedConstructor, costTokenStackEmptyConstructor,
    costTokenStackConsConstructor, costFundingConstructor,
    costContactConstructor, costSignatureUnitConstructorName,
    costSignatureProductConstructorName, costKeyLeafConstructorName,
    costKeyBranchConstructorName, costSignatureCommitConstructorName, costSignedConstructorName,
    costTokenStackEmptyConstructorName, costTokenStackConsConstructorName,
    costFundingConstructorName, costContactConstructorName]

/-- Generated typing constructors and the apparatus carry no parser notation. -/
theorem costCoreTerm_syntaxPattern_eq_nil (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule) (termMembership : term ∈ profile.costCoreLanguage.terms) :
    term.syntaxPattern = [] := by
  simp only [costCoreLanguage, List.mem_append] at termMembership
  rcases termMembership with generatedMembership | apparatusMembership
  · exact profile.generatedTerm_syntaxPattern_eq_nil term generatedMembership
  · simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at apparatusMembership
    rcases apparatusMembership with equality | equality | equality | equality |
      equality | equality | equality | equality | equality | equality <;> subst term <;> rfl

theorem signature_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costSignatureSortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by simp [costCoreSortSuffixes, costSignatureSortName])

theorem key_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costKeySortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by simp [costCoreSortSuffixes, costKeySortName])

theorem stack_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costTokenStackSortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by simp [costCoreSortSuffixes, costTokenStackSortName])

theorem wrapped_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costWrappedSortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_left _ profile.costWrappedSortName_mem_generated

theorem interacting_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costBaseSortName theory.presentation.interactingSort.1.name ∈
      profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_left _ (profile.costBaseSortName_mem_generated
    (List.mem_map.mpr ⟨theory.presentation.interactingSort.1,
      theory.presentation.interactingSort.2, rfl⟩))

/-- Each fixed apparatus row validates from its actual declared sorts.
The generated source prefix is not expanded to establish this fact. -/
theorem apparatus_validate (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule)
    (membership : term ∈ costCoreConstructors theory.presentation.interactingSort.1.name) :
    profile.costCoreLanguage.validateTerm term = [] := by
  have signature := profile.signature_mem_costCoreLanguage
  have key := profile.key_mem_costCoreLanguage
  have stack := profile.stack_mem_costCoreLanguage
  have wrapped := profile.wrapped_mem_costCoreLanguage
  have interacting := profile.interacting_mem_costCoreLanguage
  simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [costSignatureUnitConstructor, costSignatureProductConstructor,
      costKeyLeafConstructor, costKeyBranchConstructor, costSignatureCommitConstructor,
      costSignedConstructor, costTokenStackEmptyConstructor, costTokenStackConsConstructor,
      costFundingConstructor, costContactConstructor, LanguageDef.validateTerm,
      signature, key, stack, wrapped, interacting, LanguageDef.validateTypeExpr_eq_nil_iff,
      TypeExpr.baseNames, TermParam.typeExpr]

/-- Finite continuation decoration and the fixed Cost apparatus jointly pass
ordinary language validation. Only actual duplicate declarations are excluded. -/
theorem costCoreLanguage_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) :
    profile.costCoreLanguage.validate = [] := by
  change ((ConstructorSignatureExtension.ofLists costCoreTypes
    (costCoreConstructors theory.presentation.interactingSort.1.name)
    (some ("$cost:core:" ++ theory.presentation.presentation.language.name))).apply
      { toLanguageDef := profile.generatedLanguage }).toLanguageDef.validate = []
  apply ConstructorSignatureExtension.apply_language_validate
  · exact profile.generatedLanguage_validate noDuplicates
  · rfl
  · rfl
  · change (costCoreSortSuffixes.map costApparatusSortName).Nodup
    exact (show costCoreSortSuffixes.Nodup by decide).map costApparatusSortName_injective
  · intro generated generatedMembership apparatusMembership
    rw [generatedLanguage_typeNames] at generatedMembership
    change generated ∈ costCoreSortSuffixes.map costApparatusSortName at apparatusMembership
    obtain ⟨suffix, _, apparatusEq⟩ := List.mem_map.mp apparatusMembership
    rcases List.mem_append.mp generatedMembership with base | wrapped
    · obtain ⟨name, _, rfl⟩ := List.mem_map.mp base
      exact costBaseSortName_ne_apparatus name suffix apparatusEq.symm
    · simp only [List.mem_singleton] at wrapped
      exact costWrappedSortName_ne_apparatus suffix (wrapped.symm.trans apparatusEq.symm)
  · change (costCoreConstructorSuffixes.map costApparatusConstructorName).Nodup
    exact (show costCoreConstructorSuffixes.Nodup by decide).map
      costApparatusConstructorName_injective
  · intro generated generatedMembership apparatusMembership
    rw [generatedLanguage_constructorLabels] at generatedMembership
    change generated ∈ costCoreConstructorSuffixes.map costApparatusConstructorName
      at apparatusMembership
    obtain ⟨suffix, _, apparatusEq⟩ := List.mem_map.mp apparatusMembership
    rcases List.mem_append.mp generatedMembership with base | wrapped
    · obtain ⟨name, _, rfl⟩ := List.mem_map.mp base
      exact costBaseConstructorName_ne_apparatus name suffix apparatusEq.symm
    · obtain ⟨name, _, rfl⟩ := List.mem_map.mp wrapped
      exact costWrappedConstructorName_ne_apparatus name suffix apparatusEq.symm
  · intro term membership
    exact profile.apparatus_validate term membership

/-- A validated Cost core on the existing finite continuation profile. -/
def costCorePresentation (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) : ValidatedLanguageDef where
  language := profile.costCoreLanguage
  valid := profile.costCoreLanguage_validate noDuplicates

end ContinuationDecorationProfile

namespace WrappableIGSLT

open ContinuationDecorationProfile (ofRetypingPlan)

/-- Add the location-independent Cost apparatus to the exact generated
continuation signature of a wrappable theory. -/
def costCoreLanguage (source : WrappableIGSLT) : LanguageDef :=
  (ofRetypingPlan source.continuationRetyping).costCoreLanguage

theorem costCoreLanguage_def (source : WrappableIGSLT) :
    source.costCoreLanguage =
      { source.continuationRetyping.generatedLanguage with
        name := "$cost:core:" ++ source.theory.presentation.presentation.language.name
        types := source.continuationRetyping.generatedLanguage.types ++ costCoreTypes
        terms := source.continuationRetyping.generatedLanguage.terms ++
          costCoreConstructors source.theory.presentation.interactingSort.1.name } :=
  rfl

/-- The constructors of the core: the generated ones, then the apparatus. -/
theorem costCoreLanguage_terms (source : WrappableIGSLT) :
    source.costCoreLanguage.terms =
      source.continuationRetyping.generatedLanguage.terms ++
        costCoreConstructors source.theory.presentation.interactingSort.1.name :=
  rfl

@[simp]
theorem costCoreLanguage_typeNames (source : WrappableIGSLT) :
    source.costCoreLanguage.typeNames =
      source.continuationRetyping.generatedLanguage.typeNames ++
        costCoreSortSuffixes.map costApparatusSortName :=
  (ofRetypingPlan source.continuationRetyping).costCoreLanguage_typeNames

theorem costCoreConstructorLabels (source : WrappableIGSLT) :
    source.costCoreLanguage.terms.map (·.label) =
      source.continuationRetyping.generatedLanguage.terms.map (·.label) ++
        costCoreConstructorSuffixes.map costApparatusConstructorName :=
  (ofRetypingPlan source.continuationRetyping).costCoreConstructorLabels

theorem costCoreTerm_syntaxPattern_eq_nil (source : WrappableIGSLT)
    (term : GrammarRule) (termMembership : term ∈ source.costCoreLanguage.terms) :
    term.syntaxPattern = [] :=
  (ofRetypingPlan source.continuationRetyping).costCoreTerm_syntaxPattern_eq_nil term
    termMembership

/-- The generic signature/wrapper/ordered-stack core passes the ordinary
language validation gate. -/
theorem costCoreLanguage_validate (source : WrappableIGSLT) :
    source.costCoreLanguage.validate = [] :=
  (ofRetypingPlan source.continuationRetyping).costCoreLanguage_validate
    source.continuationRetyping.noDuplicates

/-- The exact structural output of the first Cost object-map layer. -/
def costCorePresentation (source : WrappableIGSLT) : ValidatedLanguageDef :=
  (ofRetypingPlan source.continuationRetyping).costCorePresentation
    source.continuationRetyping.noDuplicates

@[simp]
theorem costCorePresentation_language (source : WrappableIGSLT) :
    source.costCorePresentation.language = source.costCoreLanguage :=
  rfl

end WrappableIGSLT

/-- The profile of a continued theory has that theory's core language. -/
@[simp]
theorem ContinuationDecorationProfile.ofRetypingPlan_costCoreLanguage (source : CIGSLT) :
    (ContinuationDecorationProfile.ofRetypingPlan source.continuationRetyping).costCoreLanguage =
      source.costCoreLanguage :=
  rfl

namespace CIGSLT

/-! ## Exact intrinsic classification of generated declarations -/

end CIGSLT

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Actual finite grammar-row interpretation. The base row uses all selected
slots, not only the two primary positions. -/
def materializeDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :
    profile.DeclaredCostConstructor → GrammarRule
  | ⟨.base authored, _⟩ => profile.baseConstructor authored.1
  | ⟨.wrapped authored, _⟩ => costWrappedConstructor (theory := theory) authored.1
  | ⟨.apparatus kind, _⟩ => kind.grammarRule theory.presentation.interactingSort.1.name

@[simp] theorem materializeDeclaredCostConstructor_label (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    (profile.materializeDeclaredCostConstructor constructor).label =
      profile.renderDeclaredCostConstructor constructor := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base authored => rfl
  | wrapped authored => rfl
  | apparatus kind => cases kind <;> rfl

theorem materializeDeclaredCostConstructor_injective (profile : ContinuationDecorationProfile cut) :
    Function.Injective profile.materializeDeclaredCostConstructor := by
  intro left right same
  apply profile.renderDeclaredCostConstructor_injective
  rw [← profile.materializeDeclaredCostConstructor_label left,
    ← profile.materializeDeclaredCostConstructor_label right, same]

theorem materializeDeclaredCostConstructor_mem (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    profile.materializeDeclaredCostConstructor constructor ∈ profile.costCoreLanguage.terms := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base authored =>
    exact List.mem_append_left _ (profile.baseConstructor_mem authored.1 authored.2)
  | wrapped authored =>
    exact List.mem_append_left _ (profile.wrappedConstructor_mem authored declared)
  | apparatus kind =>
    apply List.mem_append_right
    rw [costCoreConstructors_eq_typed]
    exact List.mem_map.mpr ⟨kind, by cases kind <;> simp [costCoreConstructorKinds], rfl⟩

/-- No generated row is omitted by intrinsic classification, including all
of the exact key, signature, stack, and funding apparatus. -/
theorem exists_declaredCostConstructor_of_mem (profile : ContinuationDecorationProfile cut)
    (rule : GrammarRule) (member : rule ∈ profile.costCoreLanguage.terms) :
    ∃ constructor : profile.DeclaredCostConstructor,
      profile.materializeDeclaredCostConstructor constructor = rule := by
  rcases List.mem_append.mp member with generated | apparatus
  · rcases List.mem_append.mp generated with base | wrapped
    · obtain ⟨authored, included, same⟩ := List.mem_map.mp base
      exact ⟨⟨.base ⟨authored, included⟩, trivial⟩, same⟩
    · obtain ⟨authored, included, same⟩ := List.mem_map.mp wrapped
      exact ⟨⟨.wrapped authored, included⟩, same⟩
  · rw [costCoreConstructors_eq_typed] at apparatus
    obtain ⟨kind, _, same⟩ := List.mem_map.mp apparatus
    exact ⟨⟨.apparatus kind, trivial⟩, same⟩

/-- Finite enumeration retaining exact source declaration identity. -/
def declaredCostConstructors (profile : ContinuationDecorationProfile cut) :
    List profile.DeclaredCostConstructor :=
  theory.presentation.presentation.language.terms.attach.map
      (fun constructor => (⟨.base constructor, trivial⟩ : profile.DeclaredCostConstructor)) ++
    profile.constructorClosure.attach.map
      (fun constructor => (⟨.wrapped constructor.1, constructor.2⟩ : profile.DeclaredCostConstructor)) ++
    costCoreConstructorKinds.map
      (fun kind => (⟨.apparatus kind, trivial⟩ : profile.DeclaredCostConstructor))

/-- Materialization recovers the exact ordered row list, not merely an
existentially equivalent signature. -/
theorem declaredCostConstructors_materialize (profile : ContinuationDecorationProfile cut) :
    profile.declaredCostConstructors.map profile.materializeDeclaredCostConstructor =
      profile.costCoreLanguage.terms := by
  change _ = (theory.presentation.presentation.language.terms.map profile.baseConstructor ++
    profile.constructorClosure.map (fun constructor => costWrappedConstructor (theory := theory) constructor.1)) ++
    costCoreConstructors theory.presentation.interactingSort.1.name
  unfold declaredCostConstructors
  rw [List.map_append, List.map_append, List.map_map, List.map_map, List.map_map]
  change (theory.presentation.presentation.language.terms.attach.map
      (fun constructor => profile.baseConstructor constructor.1) ++
    profile.constructorClosure.attach.map
      (fun constructor => costWrappedConstructor (theory := theory) constructor.1.1)) ++
    costCoreConstructorKinds.map (·.grammarRule theory.presentation.interactingSort.1.name) = _
  rw [List.attach_map_val,
    List.attach_map_val (l := profile.constructorClosure)
      (f := fun constructor => costWrappedConstructor (theory := theory) constructor.1),
    costCoreConstructors_eq_typed]

/-- Signature validation provides duplicate-freedom of the exact intrinsic
enumeration when the supplied profile has no duplicate wrapped rows. -/
theorem declaredCostConstructors_nodup (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) : profile.declaredCostConstructors.Nodup := by
  apply List.Nodup.of_map profile.materializeDeclaredCostConstructor
  rw [profile.declaredCostConstructors_materialize]
  exact List.Nodup.of_map (fun rule => rule.label)
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil _
      (profile.costCoreLanguage_validate noDuplicates))

theorem mem_declaredCostConstructors (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    constructor ∈ profile.declaredCostConstructors := by
  have member := profile.materializeDeclaredCostConstructor_mem constructor
  rw [← profile.declaredCostConstructors_materialize] at member
  obtain ⟨other, included, same⟩ := List.mem_map.mp member
  have identical := profile.materializeDeclaredCostConstructor_injective same
  simpa only [identical] using included

/-- Declaration-aware executable lookup uses the existing finite-list
search, never a wire prefix as a substitute for source membership. -/
def decodeDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) (name : String) :
    Option profile.DeclaredCostConstructor :=
  profile.declaredCostConstructors.find? (fun constructor =>
    profile.renderDeclaredCostConstructor constructor == name)

@[simp] theorem decodeDeclaredCostConstructor_render (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    profile.decodeDeclaredCostConstructor (profile.renderDeclaredCostConstructor constructor) =
      some constructor := by
  unfold decodeDeclaredCostConstructor
  cases found : profile.declaredCostConstructors.find? (fun candidate =>
      profile.renderDeclaredCostConstructor candidate == profile.renderDeclaredCostConstructor constructor) with
  | none =>
    have missing := List.find?_eq_none.mp found constructor (profile.mem_declaredCostConstructors constructor)
    simp at missing
  | some candidate =>
    have equalNames := List.find?_some found
    have same := profile.renderDeclaredCostConstructor_injective (of_decide_eq_true equalNames)
    exact congrArg some same

theorem decodeDeclaredCostConstructor_eq_some_iff (profile : ContinuationDecorationProfile cut)
    (name : String) (constructor : profile.DeclaredCostConstructor) :
    profile.decodeDeclaredCostConstructor name = some constructor ↔
      profile.renderDeclaredCostConstructor constructor = name := by
  constructor
  · intro found
    have same : (profile.renderDeclaredCostConstructor constructor == name) = true :=
      List.find?_some (p := fun candidate : profile.DeclaredCostConstructor =>
        profile.renderDeclaredCostConstructor candidate == name) found
    exact of_decide_eq_true same
  · intro same
    rw [← same]
    exact profile.decodeDeclaredCostConstructor_render constructor

theorem decodeDeclaredCostConstructor_eq_none_iff (profile : ContinuationDecorationProfile cut)
    (name : String) : profile.decodeDeclaredCostConstructor name = none ↔
      ∀ constructor : profile.DeclaredCostConstructor,
        profile.renderDeclaredCostConstructor constructor ≠ name := by
  constructor
  · intro missing constructor same
    have found := (profile.decodeDeclaredCostConstructor_eq_some_iff name constructor).mpr same
    rw [missing] at found
    cases found
  · intro absent
    cases found : profile.decodeDeclaredCostConstructor name with
    | none => rfl
    | some constructor =>
      exact False.elim (absent constructor
        ((profile.decodeDeclaredCostConstructor_eq_some_iff name constructor).mp found))

end ContinuationDecorationProfile

namespace CIGSLT

open ContinuationDecorationProfile (ofRetypingPlan)

/-- Materialize one exact intrinsic Cost constructor as the corresponding
`GrammarRule` in the generated `LanguageDef`. -/
def materializeDeclaredCostConstructor (source : CIGSLT) :
    source.DeclaredCostConstructor → GrammarRule :=
  (ofRetypingPlan source.continuationRetyping).materializeDeclaredCostConstructor

@[simp]
theorem materializeDeclaredCostConstructor_label (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    (source.materializeDeclaredCostConstructor constructor).label =
      source.renderDeclaredCostConstructor constructor :=
  (ofRetypingPlan source.continuationRetyping).materializeDeclaredCostConstructor_label
    constructor

/-- Intrinsic declaration identity is preserved by materialization. -/
theorem materializeDeclaredCostConstructor_injective (source : CIGSLT) :
    Function.Injective source.materializeDeclaredCostConstructor :=
  (ofRetypingPlan source.continuationRetyping).materializeDeclaredCostConstructor_injective

/-- Every intrinsic declared constructor materializes into the exact
generated Cost declaration list. -/
theorem materializeDeclaredCostConstructor_mem (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    source.materializeDeclaredCostConstructor constructor ∈
      source.costCoreLanguage.terms :=
  (ofRetypingPlan source.continuationRetyping).materializeDeclaredCostConstructor_mem
    constructor

/-- Conversely, every generated Cost grammar declaration has an intrinsic
declared constructor. -/
theorem exists_declaredCostConstructor_of_mem (source : CIGSLT)
    (rule : GrammarRule) (membership : rule ∈ source.costCoreLanguage.terms) :
    ∃ constructor : source.DeclaredCostConstructor,
      source.materializeDeclaredCostConstructor constructor = rule :=
  (ofRetypingPlan source.continuationRetyping).exists_declaredCostConstructor_of_mem rule
    membership

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
  (ofRetypingPlan source.continuationRetyping).declaredCostConstructors

/-- Every exact generated constructor occurs in the intrinsic enumeration. -/
theorem mem_declaredCostConstructors (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    constructor ∈ source.declaredCostConstructors :=
  (ofRetypingPlan source.continuationRetyping).mem_declaredCostConstructors constructor

/-- Executable decoding of one exact generated Cost constructor name. -/
def decodeDeclaredCostConstructor (source : CIGSLT) (name : String) :
    Option source.DeclaredCostConstructor :=
  (ofRetypingPlan source.continuationRetyping).decodeDeclaredCostConstructor name

/-- Decoding is a left inverse of faithful constructor rendering. -/
@[simp]
theorem decodeDeclaredCostConstructor_render (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    source.decodeDeclaredCostConstructor
        (source.renderDeclaredCostConstructor constructor) = some constructor :=
  (ofRetypingPlan source.continuationRetyping).decodeDeclaredCostConstructor_render
    constructor

/-- Successful decoding recovers the exact rendered wire name, and
conversely. -/
theorem decodeDeclaredCostConstructor_eq_some_iff (source : CIGSLT)
    (name : String) (constructor : source.DeclaredCostConstructor) :
    source.decodeDeclaredCostConstructor name = some constructor ↔
      source.renderDeclaredCostConstructor constructor = name :=
  (ofRetypingPlan source.continuationRetyping).decodeDeclaredCostConstructor_eq_some_iff
    name constructor

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
  rw [costCoreConstructors_eq_typed] at membership
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp membership
  cases kind <;> first
    | exact (costBaseSortName_ne_apparatus
        source.theory.presentation.interactingSort.1.name "signature") categoryEquality.symm
    | exact (costBaseSortName_ne_apparatus
        source.theory.presentation.interactingSort.1.name "key") categoryEquality.symm
    | exact (costBaseSortName_ne_apparatus
        source.theory.presentation.interactingSort.1.name "token-stack") categoryEquality.symm
    | exact (costBaseSortName_ne_wrapped
        source.theory.presentation.interactingSort.1.name) categoryEquality.symm

end CIGSLT

end Mettapedia.GSLT.LanguageDef
