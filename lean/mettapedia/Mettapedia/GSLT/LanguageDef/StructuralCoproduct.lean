import Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics

/-!
# Conservative coproducts of validated language definitions

Independent operational presentations may be placed side by side after their
symbols are embedded into disjoint namespaces.  This module separates the raw
list construction from the proof that it is conservative:

* all four authored name families are globally duplicate-free;
* every mapped constructor, equation, and rewrite row remains valid when the
  other component's declarations are present.

The second condition is the capture/interference boundary.  It rules out the
subtle case where a newly added constructor name turns an existing schema
variable into a constructor-shaped wildcard collision.  Once these exact
conditions hold, validation of the union and both structural inclusions are
derived rather than postulated.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralCoproduct

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics

/-- A rewrite is rooted at an authored constructor.  This excludes a bare
metavariable left-hand side, which would match terms belonging to every
component of a disjoint operational sum. -/
def ConstructorRooted (rewrite : RewriteRule) : Prop :=
  ∃ constructor arguments, rewrite.left = .apply constructor arguments

/-- Every namespace map of a tagged presentation embedding is injective. -/
structure InjectiveSymbolMap (symbols : PresentationSymbols) : Prop where
  sort : Function.Injective symbols.sort
  constructor : Function.Injective symbols.constructor
  relation : Function.Injective symbols.relation
  equation : Function.Injective symbols.equation
  rewrite : Function.Injective symbols.rewrite

/-- The two images of every authored namespace are disjoint. -/
structure DisjointSymbolImages
    (leftSymbols rightSymbols : PresentationSymbols) : Prop where
  sort : ∀ left right,
    leftSymbols.sort left ≠ rightSymbols.sort right
  constructor : ∀ left right,
    leftSymbols.constructor left ≠ rightSymbols.constructor right
  relation : ∀ left right,
    leftSymbols.relation left ≠ rightSymbols.relation right
  equation : ∀ left right,
    leftSymbols.equation left ≠ rightSymbols.equation right
  rewrite : ∀ left right,
    leftSymbols.rewrite left ≠ rightSymbols.rewrite right

/-- Rename every authored symbol of a language presentation while preserving
declaration order, concrete syntax, binding shape, and evaluation policy. -/
def renameLanguage (name : String) (symbols : PresentationSymbols)
    (language : LanguageDef) : LanguageDef := {
  name := name
  types := language.types.map (mapTypeDecl symbols)
  terms := language.terms.map (mapGrammarRule symbols)
  equations := language.equations.map (mapEquation symbols)
  rewrites := language.rewrites.map (mapRewriteRule symbols)
}

/-- Raw tagged union of two presentations.  Validation is deliberately not
part of this constructor; it is supplied only by `Compatibility.valid`. -/
def rawCoproduct (name : String)
    (leftSymbols rightSymbols : PresentationSymbols)
    (left right : LanguageDef) : LanguageDef :=
  let left' := renameLanguage (name ++ ".left") leftSymbols left
  let right' := renameLanguage (name ++ ".right") rightSymbols right
  { name := name
    types := left'.types ++ right'.types
    terms := left'.terms ++ right'.terms
    equations := left'.equations ++ right'.equations
    rewrites := left'.rewrites ++ right'.rewrites }

/-! ## Exact constructor lookup in a tagged sum -/

/-- The carrier names of a raw coproduct are exactly the two renamed carrier
lists, in component order. -/
theorem rawCoproduct_typeNames
    (name : String) (leftSymbols rightSymbols : PresentationSymbols)
    (left right : LanguageDef) :
    (rawCoproduct name leftSymbols rightSymbols left right).typeNames =
      left.typeNames.map leftSymbols.sort ++
        right.typeNames.map rightSymbols.sort := by
  simp [rawCoproduct, renameLanguage, LanguageDef.typeNames,
    mapTypeDecl, List.map_map, Function.comp_def]

/-- The constructor labels of a raw coproduct are exactly the two renamed
constructor-label lists, in component order. -/
theorem rawCoproduct_constructorLabels
    (name : String) (leftSymbols rightSymbols : PresentationSymbols)
    (left right : LanguageDef) :
    ((rawCoproduct name leftSymbols rightSymbols left right).terms.map
      (·.label)) =
      (left.terms.map (·.label)).map leftSymbols.constructor ++
        (right.terms.map (·.label)).map rightSymbols.constructor := by
  simp [rawCoproduct, renameLanguage, mapGrammarRule, List.map_map,
    Function.comp_def]

/-- Filtering a renamed constructor table at a renamed label is exactly the
renaming of the corresponding source filter.  This is the lookup fact that
keeps validation of composed presentations structural rather than reducing a
whole concrete signature by brute force. -/
theorem filter_mapGrammarRule_at
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (terms : List GrammarRule) (label : String) :
    (terms.map (mapGrammarRule symbols)).filter
        (fun declaration =>
          declaration.label == symbols.constructor label) =
      (terms.filter fun declaration => declaration.label == label).map
        (mapGrammarRule symbols) := by
  induction terms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      by_cases equality : term.label = label
      · subst label
        simp [mapGrammarRule, inductionHypothesis]
      · have mappedInequality :
            symbols.constructor term.label ≠ symbols.constructor label :=
          fun mappedEquality => equality (constructorInjective mappedEquality)
        simp [mapGrammarRule, equality, mappedInequality,
          inductionHypothesis]

/-- Constructors from the right component never appear in a lookup for a
left-component label when the two constructor images are disjoint. -/
theorem filter_rightGrammarRules_at_left_eq_nil
    (leftSymbols rightSymbols : PresentationSymbols)
    (constructorImagesDisjoint : ∀ left right,
      leftSymbols.constructor left ≠ rightSymbols.constructor right)
    (rightTerms : List GrammarRule) (leftLabel : String) :
    (rightTerms.map (mapGrammarRule rightSymbols)).filter
        (fun declaration =>
          declaration.label == leftSymbols.constructor leftLabel) = [] := by
  induction rightTerms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      have inequality :
          rightSymbols.constructor term.label ≠
            leftSymbols.constructor leftLabel :=
        fun equality => constructorImagesDisjoint leftLabel term.label equality.symm
      simp [mapGrammarRule, inequality, inductionHypothesis]

/-- Symmetric constructor-lookup silence for the left table at a right label. -/
theorem filter_leftGrammarRules_at_right_eq_nil
    (leftSymbols rightSymbols : PresentationSymbols)
    (constructorImagesDisjoint : ∀ left right,
      leftSymbols.constructor left ≠ rightSymbols.constructor right)
    (leftTerms : List GrammarRule) (rightLabel : String) :
    (leftTerms.map (mapGrammarRule leftSymbols)).filter
        (fun declaration =>
          declaration.label == rightSymbols.constructor rightLabel) = [] := by
  induction leftTerms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      have inequality :
          leftSymbols.constructor term.label ≠
            rightSymbols.constructor rightLabel :=
        constructorImagesDisjoint term.label rightLabel
      simp [mapGrammarRule, inequality, inductionHypothesis]

/-- Exact lookup for a left constructor in the joint constructor table. -/
theorem rawCoproduct_filter_leftConstructor
    (name : String) (leftSymbols rightSymbols : PresentationSymbols)
    (leftConstructorInjective : Function.Injective leftSymbols.constructor)
    (constructorImagesDisjoint : ∀ left right,
      leftSymbols.constructor left ≠ rightSymbols.constructor right)
    (left right : LanguageDef) (label : String) :
    (rawCoproduct name leftSymbols rightSymbols left right).terms.filter
        (fun declaration =>
          declaration.label == leftSymbols.constructor label) =
      (left.terms.filter fun declaration => declaration.label == label).map
        (mapGrammarRule leftSymbols) := by
  unfold rawCoproduct renameLanguage
  rw [List.filter_append, filter_mapGrammarRule_at leftSymbols
    leftConstructorInjective left.terms label]
  rw [filter_rightGrammarRules_at_left_eq_nil leftSymbols rightSymbols
    constructorImagesDisjoint right.terms label, List.append_nil]

/-- Exact lookup for a right constructor in the joint constructor table. -/
theorem rawCoproduct_filter_rightConstructor
    (name : String) (leftSymbols rightSymbols : PresentationSymbols)
    (rightConstructorInjective : Function.Injective rightSymbols.constructor)
    (constructorImagesDisjoint : ∀ left right,
      leftSymbols.constructor left ≠ rightSymbols.constructor right)
    (left right : LanguageDef) (label : String) :
    (rawCoproduct name leftSymbols rightSymbols left right).terms.filter
        (fun declaration =>
          declaration.label == rightSymbols.constructor label) =
      (right.terms.filter fun declaration => declaration.label == label).map
        (mapGrammarRule rightSymbols) := by
  unfold rawCoproduct renameLanguage
  rw [List.filter_append]
  rw [filter_leftGrammarRules_at_right_eq_nil leftSymbols rightSymbols
    constructorImagesDisjoint left.terms label, List.nil_append]
  exact filter_mapGrammarRule_at rightSymbols rightConstructorInjective
    right.terms label

/-! ## Constructor validation under tagged embeddings -/

/-- Structural sort renaming maps the base-sort inventory pointwise. -/
@[simp]
theorem mapTypeExpr_baseNames (symbols : PresentationSymbols)
    (type : TypeExpr) :
    (mapTypeExpr symbols type).baseNames =
      type.baseNames.map symbols.sort := by
  induction type with
  | base sort => rfl
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [mapTypeExpr, TypeExpr.baseNames, domainHypothesis,
        codomainHypothesis]
  | multiBinder body inductionHypothesis =>
      simp [mapTypeExpr, TypeExpr.baseNames, inductionHypothesis]
  | collection collectionType element inductionHypothesis =>
      simp [mapTypeExpr, TypeExpr.baseNames, inductionHypothesis]

/-- Premise traversal commutes with structural constructor renaming. -/
@[simp]
theorem premisePatterns_mapPremise (symbols : PresentationSymbols)
    (premise : Premise) :
    LanguageDef.premisePatterns (mapPremise symbols premise) =
      (LanguageDef.premisePatterns premise).map (mapPattern symbols) := by
  induction premise with
  | freshness condition => simp [mapPremise, LanguageDef.premisePatterns]
  | congruence left right =>
      simp [mapPremise, LanguageDef.premisePatterns]
  | relationQuery relation arguments =>
      simp [mapPremise, LanguageDef.premisePatterns]
  | forAll collection parameter body inductionHypothesis =>
      simpa [mapPremise, LanguageDef.premisePatterns] using inductionHypothesis

/-- The flattened pattern inventory of a premise list commutes with the same
structural action, preserving order and multiplicity. -/
@[simp]
theorem premisePatterns_mapPremises (symbols : PresentationSymbols)
    (premises : List Premise) :
    ((premises.map (mapPremise symbols)).flatMap
      LanguageDef.premisePatterns) =
      (premises.flatMap LanguageDef.premisePatterns).map
        (mapPattern symbols) := by
  induction premises with
  | nil => rfl
  | cons premise premises inductionHypothesis =>
      simp [premisePatterns_mapPremise, inductionHypothesis]

/-- Clean constructor validation of a left pattern transports into the tagged
sum whenever constructor-reference traversal commutes with the structural
action.  Error text is intentionally not equated because it contains the
renamed constructor labels. -/
theorem validatePatternConstructors_left_eq_nil
    (name sourceContext targetContext : String)
    (leftSymbols rightSymbols : PresentationSymbols)
    (leftConstructorInjective : Function.Injective leftSymbols.constructor)
    (constructorImagesDisjoint : ∀ left right,
      leftSymbols.constructor left ≠ rightSymbols.constructor right)
    (left right : LanguageDef) (pattern : Pattern)
    (references :
      (mapPattern leftSymbols pattern).constructorRefs =
        pattern.constructorRefs.map fun reference =>
          (leftSymbols.constructor reference.1, reference.2))
    (sourceClean :
      LanguageDef.validatePatternConstructors sourceContext left.terms pattern = []) :
    LanguageDef.validatePatternConstructors targetContext
        (rawCoproduct name leftSymbols rightSymbols left right).terms
        (mapPattern leftSymbols pattern) = [] := by
  unfold LanguageDef.validatePatternConstructors
  rw [references, List.flatMap_map]
  rw [List.flatMap_eq_nil_iff]
  intro reference membership
  have sourceComponent :=
    (List.flatMap_eq_nil_iff.mp sourceClean) reference membership
  rcases reference with ⟨constructor, arity⟩
  dsimp only [Prod.fst, Prod.snd]
  rw [rawCoproduct_filter_leftConstructor name leftSymbols rightSymbols
    leftConstructorInjective constructorImagesDisjoint left right constructor]
  cases filtered : left.terms.filter
      (fun declaration => declaration.label == constructor) with
  | nil => simp [filtered] at sourceComponent
  | cons declaration declarations =>
      cases declarations with
      | nil =>
          by_cases arityMatches : declaration.params.length = arity
          · simp [arityMatches, mapGrammarRule]
          · simp [filtered, arityMatches] at sourceComponent
      | cons second remaining => simp [filtered] at sourceComponent

/-- Symmetric transport of clean constructor validation for mapped right
patterns. -/
theorem validatePatternConstructors_right_eq_nil
    (name sourceContext targetContext : String)
    (leftSymbols rightSymbols : PresentationSymbols)
    (rightConstructorInjective : Function.Injective rightSymbols.constructor)
    (constructorImagesDisjoint : ∀ left right,
      leftSymbols.constructor left ≠ rightSymbols.constructor right)
    (left right : LanguageDef) (pattern : Pattern)
    (references :
      (mapPattern rightSymbols pattern).constructorRefs =
        pattern.constructorRefs.map fun reference =>
          (rightSymbols.constructor reference.1, reference.2))
    (sourceClean :
      LanguageDef.validatePatternConstructors sourceContext right.terms pattern = []) :
    LanguageDef.validatePatternConstructors targetContext
        (rawCoproduct name leftSymbols rightSymbols left right).terms
        (mapPattern rightSymbols pattern) = [] := by
  unfold LanguageDef.validatePatternConstructors
  rw [references, List.flatMap_map]
  rw [List.flatMap_eq_nil_iff]
  intro reference membership
  have sourceComponent :=
    (List.flatMap_eq_nil_iff.mp sourceClean) reference membership
  rcases reference with ⟨constructor, arity⟩
  dsimp only [Prod.fst, Prod.snd]
  rw [rawCoproduct_filter_rightConstructor name leftSymbols rightSymbols
    rightConstructorInjective constructorImagesDisjoint left right constructor]
  cases filtered : right.terms.filter
      (fun declaration => declaration.label == constructor) with
  | nil => simp [filtered] at sourceComponent
  | cons declaration declarations =>
      cases declarations with
      | nil =>
          by_cases arityMatches : declaration.params.length = arity
          · simp [arityMatches, mapGrammarRule]
          · simp [filtered, arityMatches] at sourceComponent
      | cons second remaining => simp [filtered] at sourceComponent

/-- Exact noninterference data for a proposed coproduct.  Global name
uniqueness prevents ambiguous declarations.  Row stability says that adding
the other component creates no capture, ambiguity, or dangling reference.
These are precisely the extra obligations not implied by validating the two
components separately. -/
structure Compatibility
    (name : String)
    (leftSymbols rightSymbols : PresentationSymbols)
    (left right : ValidatedLanguageDef) where
  leftSymbolsInjective : InjectiveSymbolMap leftSymbols
  rightSymbolsInjective : InjectiveSymbolMap rightSymbols
  symbolImagesDisjoint : DisjointSymbolImages leftSymbols rightSymbols
  leftRewritesRooted : ∀ rewrite ∈ left.language.rewrites,
    ConstructorRooted rewrite
  rightRewritesRooted : ∀ rewrite ∈ right.language.rewrites,
    ConstructorRooted rewrite
  typeNamesNodup :
    (rawCoproduct name leftSymbols rightSymbols left.language right.language).typeNames.Nodup
  constructorNamesNodup :
    ((rawCoproduct name leftSymbols rightSymbols left.language right.language).terms.map
      (·.label)).Nodup
  equationNamesNodup :
    ((rawCoproduct name leftSymbols rightSymbols left.language right.language).equations.map
      (·.name)).Nodup
  rewriteNamesNodup :
    ((rawCoproduct name leftSymbols rightSymbols left.language right.language).rewrites.map
      (·.name)).Nodup
  leftTermsStable : ∀ term ∈ left.language.terms,
    LanguageDef.validateTerm
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapGrammarRule leftSymbols term) = []
  rightTermsStable : ∀ term ∈ right.language.terms,
    LanguageDef.validateTerm
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapGrammarRule rightSymbols term) = []
  leftEquationsStable : ∀ equation ∈ left.language.equations,
    LanguageDef.validateEquation
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapEquation leftSymbols equation) = []
  rightEquationsStable : ∀ equation ∈ right.language.equations,
    LanguageDef.validateEquation
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapEquation rightSymbols equation) = []
  leftRewritesStable : ∀ rewrite ∈ left.language.rewrites,
    LanguageDef.validateRewrite
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapRewriteRule leftSymbols rewrite) = []
  rightRewritesStable : ∀ rewrite ∈ right.language.rewrites,
    LanguageDef.validateRewrite
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapRewriteRule rightSymbols rewrite) = []

namespace Compatibility

variable {name : String} {leftSymbols rightSymbols : PresentationSymbols}
  {left right : ValidatedLanguageDef}

/-- A compatible raw coproduct passes the ordinary `LanguageDef` validation
gate.  No component theorem is replaced: compatibility only proves that every
mapped row survives the larger signature unchanged. -/
theorem valid
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    (rawCoproduct name leftSymbols rightSymbols
      left.language right.language).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact compatible.typeNamesNodup
  · exact compatible.constructorNamesNodup
  · exact compatible.equationNamesNodup
  · exact compatible.rewriteNamesNodup
  · intro term membership
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      exact compatible.leftTermsStable source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      exact compatible.rightTermsStable source sourceMember
  · intro equation membership
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      exact compatible.leftEquationsStable source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      exact compatible.rightEquationsStable source sourceMember
  · intro rewrite membership
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      exact compatible.leftRewritesStable source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      exact compatible.rightRewritesStable source sourceMember

/-- The validated coproduct object determined by a compatibility witness. -/
def presentation
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    ValidatedLanguageDef where
  language := rawCoproduct name leftSymbols rightSymbols
    left.language right.language
  valid := compatible.valid

/-- Canonical structural inclusion of the left presentation. -/
def leftInclusion
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    StructuralMorphism left compatible.presentation where
  symbols := leftSymbols
  mapsTypes declaration membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨declaration, membership, rfl⟩)
  mapsTerms term membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨term, membership, rfl⟩)
  mapsEquations equation membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  mapsRewrites rewrite membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨rewrite, membership, rfl⟩)

/-- Canonical structural inclusion of the right presentation. -/
def rightInclusion
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    StructuralMorphism right compatible.presentation where
  symbols := rightSymbols
  mapsTypes declaration membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨declaration, membership, rfl⟩)
  mapsTerms term membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨term, membership, rfl⟩)
  mapsEquations equation membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  mapsRewrites rewrite membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨rewrite, membership, rfl⟩)

private theorem renamedRules_rewriteStep
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (rules : List RewriteRule) (term : Pattern) :
    (rules.map (mapRewriteRule symbols)).flatMap
        (fun rule => applyRule rule (mapPattern symbols term)) =
      (rules.flatMap fun rule => applyRule rule term).map
        (mapPattern symbols) := by
  induction rules with
  | nil => rfl
  | cons rule rules inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [applyRule_equivariance symbols constructorInjective rule term,
        inductionHypothesis]

/-- Renaming an operational presentation by an injective constructor map
commutes exactly with its executable one-step relation. -/
theorem renameLanguage_rewriteStep
    (language : LanguageDef) (renamedName : String)
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (term : Pattern) :
    rewriteStep (renameLanguage renamedName symbols language)
        (mapPattern symbols term) =
      (rewriteStep language term).map (mapPattern symbols) := by
  exact renamedRules_rewriteStep symbols constructorInjective
    language.rewrites term

private theorem applyRule_right_on_left_eq_nil
    (leftSymbols rightSymbols : PresentationSymbols)
    (imagesDisjoint : ∀ leftConstructor rightConstructor,
      leftSymbols.constructor leftConstructor ≠
        rightSymbols.constructor rightConstructor)
    (rewrite : RewriteRule) (rooted : ConstructorRooted rewrite)
    (term : Pattern) :
    applyRule (mapRewriteRule rightSymbols rewrite)
        (mapPattern leftSymbols term) = [] := by
  rcases rooted with ⟨root, arguments, rootEquality⟩
  unfold applyRule mapRewriteRule
  simp only [rootEquality, mapPattern]
  cases term with
  | bvar index => simp [matchPattern, mapPattern]
  | fvar name => simp [matchPattern, mapPattern]
  | apply constructor termArguments =>
      have unequal :
          rightSymbols.constructor root ≠
            leftSymbols.constructor constructor :=
        fun equality => imagesDisjoint constructor root equality.symm
      simp [matchPattern, mapPattern, unequal]
  | lambda binder body =>
      simp [matchPattern, mapPattern]
  | multiLambda arity binders body =>
      simp [matchPattern, mapPattern]
  | subst body replacement =>
      simp [matchPattern, mapPattern]
  | collection collectionType elements rest =>
      simp [matchPattern, mapPattern]

private theorem applyRule_left_on_right_eq_nil
    (leftSymbols rightSymbols : PresentationSymbols)
    (imagesDisjoint : ∀ leftConstructor rightConstructor,
      leftSymbols.constructor leftConstructor ≠
        rightSymbols.constructor rightConstructor)
    (rewrite : RewriteRule) (rooted : ConstructorRooted rewrite)
    (term : Pattern) :
    applyRule (mapRewriteRule leftSymbols rewrite)
        (mapPattern rightSymbols term) = [] := by
  rcases rooted with ⟨root, arguments, rootEquality⟩
  unfold applyRule mapRewriteRule
  simp only [rootEquality, mapPattern]
  cases term with
  | bvar index => simp [matchPattern, mapPattern]
  | fvar name => simp [matchPattern, mapPattern]
  | apply constructor termArguments =>
      exact by
        have unequal :
            leftSymbols.constructor root ≠
              rightSymbols.constructor constructor :=
          imagesDisjoint root constructor
        simp [matchPattern, mapPattern, unequal]
  | lambda binder body =>
      simp [matchPattern, mapPattern]
  | multiLambda arity binders body =>
      simp [matchPattern, mapPattern]
  | subst body replacement =>
      simp [matchPattern, mapPattern]
  | collection collectionType elements rest =>
      simp [matchPattern, mapPattern]

/-- The left component's executable one-step fibre is unchanged by adjoining
the right component.  This is exact list equality, preserving reduction order
and multiplicity. -/
theorem left_rewriteStep_exact
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (term : Pattern) :
    rewriteStep compatible.presentation.language
        (mapPattern leftSymbols term) =
      (rewriteStep left.language term).map (mapPattern leftSymbols) := by
  unfold presentation rawCoproduct rewriteStep
  simp only [renameLanguage, List.flatMap_append]
  rw [renamedRules_rewriteStep leftSymbols
    compatible.leftSymbolsInjective.constructor left.language.rewrites term]
  have rightSilent :
      (right.language.rewrites.map (mapRewriteRule rightSymbols)).flatMap
          (fun rule => applyRule rule (mapPattern leftSymbols term)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro mappedRule mappedMember
    obtain ⟨sourceRule, sourceMember, rfl⟩ := List.mem_map.mp mappedMember
    exact applyRule_right_on_left_eq_nil leftSymbols rightSymbols
      compatible.symbolImagesDisjoint.constructor sourceRule
      (compatible.rightRewritesRooted sourceRule sourceMember) term
  rw [rightSilent, List.append_nil]

/-- Symmetric exact conservativity for the right component. -/
theorem right_rewriteStep_exact
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (term : Pattern) :
    rewriteStep compatible.presentation.language
        (mapPattern rightSymbols term) =
      (rewriteStep right.language term).map (mapPattern rightSymbols) := by
  unfold presentation rawCoproduct rewriteStep
  simp only [renameLanguage, List.flatMap_append]
  have leftSilent :
      (left.language.rewrites.map (mapRewriteRule leftSymbols)).flatMap
          (fun rule => applyRule rule (mapPattern rightSymbols term)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro mappedRule mappedMember
    obtain ⟨sourceRule, sourceMember, rfl⟩ := List.mem_map.mp mappedMember
    exact applyRule_left_on_right_eq_nil leftSymbols rightSymbols
      compatible.symbolImagesDisjoint.constructor sourceRule
      (compatible.leftRewritesRooted sourceRule sourceMember) term
  rw [leftSilent, List.nil_append]
  exact renamedRules_rewriteStep rightSymbols
    compatible.rightSymbolsInjective.constructor right.language.rewrites term

end Compatibility

#print axioms Compatibility.valid
#print axioms Compatibility.leftInclusion
#print axioms Compatibility.rightInclusion
#print axioms Compatibility.left_rewriteStep_exact
#print axioms Compatibility.right_rewriteStep_exact

end Mettapedia.GSLT.LanguageDef.StructuralCoproduct
