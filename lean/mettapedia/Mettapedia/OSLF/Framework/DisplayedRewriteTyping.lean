import Mettapedia.OSLF.Framework.DisplayedRewriteSiteTransport
import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-!
# Typing evidence at displayed rewrite occurrences

A displayed rewrite site records where a source occurrence appears, but not
whether the containing rewrite or the focused occurrence is well sorted.
`LanguageDef.validate` deliberately checks only the structural wire format;
it does not supply this typing evidence.

`DisplayedRewriteTyping` is the typed input boundary for source-indexed OSLF
generation.  It retains:

* a common type for the two endpoints of the authored rewrite;
* the binder prefix introduced while descending to the displayed occurrence;
* the type of the focused source occurrence in that local context.

The evidence transports along structural language morphisms.  No
principal-typing claim is made: when a language admits several typings,
they remain distinct possible generator inputs.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A displayed source occurrence together with the sorting evidence needed
to generate type syntax for that occurrence.

`focusBoundPrefix` records binders introduced between the rewrite root and
the hole.  The rewrite's authored free-variable context remains visible in
all three judgments.
-/
structure DisplayedRewriteTyping (definition : ValidatedLanguageDef) where
  site : DisplayedRewriteSite definition.language
  rewriteType : TypeExpr
  focusBoundPrefix : List TypeExpr
  focusType : TypeExpr
  rewriteLeftTyped :
    HasType definition.language
      (FreeTypeContext.ofList site.rewrite.typeContext) []
      site.rewrite.left rewriteType
  rewriteRightTyped :
    HasType definition.language
      (FreeTypeContext.ofList site.rewrite.typeContext) []
      site.rewrite.right rewriteType
  sourceIsObject : isObjectPattern site.rewrite.left = true
  focusTyped :
    HasType definition.language
      (FreeTypeContext.ofList site.rewrite.typeContext) focusBoundPrefix
      site.focus focusType

namespace DisplayedRewriteTyping

/-- Typing evidence is determined by its occurrence and its three explicit
type indices; derivation witnesses themselves are proof-irrelevant in Lean.
-/
@[ext]
theorem ext {definition : ValidatedLanguageDef}
    {first second : DisplayedRewriteTyping definition}
    (site : first.site = second.site)
    (rewriteType : first.rewriteType = second.rewriteType)
    (focusBoundPrefix :
      first.focusBoundPrefix = second.focusBoundPrefix)
    (focusType : first.focusType = second.focusType) : first = second := by
  cases first
  cases second
  cases site
  cases rewriteType
  cases focusBoundPrefix
  cases focusType
  rfl

/-- Forget the selected occurrence while retaining the ordinary sorting
judgment for the authored rewrite row.
-/
theorem rewriteWellSorted {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) :
    RewriteWellSorted definition.language typing.site.rewrite :=
  ⟨typing.rewriteType, typing.rewriteLeftTyped,
    typing.rewriteRightTyped⟩

/-- Structural validation supplies the label-determinism premise needed to
invert typing through an occurrence context.
-/
theorem labelDeterministic (definition : ValidatedLanguageDef) :
    LabelDeterministic definition.language := by
  intro left right leftMembership rightMembership labelsEqual
  exact List.inj_on_of_nodup_map
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      definition.language definition.valid)
    leftMembership rightMembership labelsEqual

/-- A well-sorted rewrite and an object-shaped displayed source occurrence
have at least one local focus typing whenever collection typing is
deterministic.

This is an existence theorem rather than a choice of principal typing.  The
same endpoint derivation is descended on both sides of the zipper; the right
endpoint evidence is retained to certify the rewrite itself.
-/
theorem exists_of_rewrite_typing
    (definition : ValidatedLanguageDef)
    (collectionDeterministic :
      CollectionChoiceDeterministic definition.language)
    (site : DisplayedRewriteSite definition.language)
    (rewriteType : TypeExpr)
    (leftTyped :
      HasType definition.language
        (FreeTypeContext.ofList site.rewrite.typeContext) []
        site.rewrite.left rewriteType)
    (rightTyped :
      HasType definition.language
        (FreeTypeContext.ofList site.rewrite.typeContext) []
        site.rewrite.right rewriteType)
    (sourceIsObject : isObjectPattern site.rewrite.left = true) :
    ∃ typing : DisplayedRewriteTyping definition,
      typing.site = site ∧ typing.rewriteType = rewriteType := by
  have filledLeft : site.context.fill site.focus = site.rewrite.left := by
    exact site.context_fill_focus
  obtain ⟨focusBoundPrefix, focusType, focusTyped, _⟩ :=
    hasType_fill_pair_decomposition (labelDeterministic definition)
      collectionDeterministic site.context
      (filledLeft.symm ▸ leftTyped) (filledLeft.symm ▸ leftTyped)
      (filledLeft.symm ▸ sourceIsObject)
  refine ⟨{
    site := site
    rewriteType := rewriteType
    focusBoundPrefix := focusBoundPrefix
    focusType := focusType
    rewriteLeftTyped := leftTyped
    rewriteRightTyped := rightTyped
    sourceIsObject := sourceIsObject
    focusTyped := ?_ }, rfl, rfl⟩
  simpa using focusTyped

/-- Transport occurrence typing along a structural language morphism.
The result retains mapped type indices rather than recomputing a possibly
different typing in the target.
-/
noncomputable def map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typing : DisplayedRewriteTyping source) :
    DisplayedRewriteTyping target where
  site := DisplayedRewriteSite.map morphism typing.site
  rewriteType := mapTypeExpr morphism.symbols typing.rewriteType
  focusBoundPrefix :=
    typing.focusBoundPrefix.map (mapTypeExpr morphism.symbols)
  focusType := mapTypeExpr morphism.symbols typing.focusType
  rewriteLeftTyped := by
    simpa [DisplayedRewriteSite.map_rewrite, mapRewriteRule,
      FreeTypeContext.ofList_mapTypeContext] using
      typing.rewriteLeftTyped.map morphism
  rewriteRightTyped := by
    simpa [DisplayedRewriteSite.map_rewrite, mapRewriteRule,
      FreeTypeContext.ofList_mapTypeContext] using
      typing.rewriteRightTyped.map morphism
  sourceIsObject := by
    simpa [DisplayedRewriteSite.map_rewrite, mapRewriteRule,
      isObjectPattern_mapPattern] using typing.sourceIsObject
  focusTyped := by
    simpa [DisplayedRewriteSite.map_rewrite, mapRewriteRule,
      FreeTypeContext.ofList_mapTypeContext] using
      typing.focusTyped.map morphism

/-- Transporting occurrence typing along the identity language morphism
changes no data.
-/
@[simp]
theorem map_id (definition : ValidatedLanguageDef)
    (typing : DisplayedRewriteTyping definition) :
    map (StructuralMorphism.id definition) typing = typing := by
  apply DisplayedRewriteTyping.ext
  · exact DisplayedRewriteSite.map_id definition typing.site
  · exact mapTypeExpr_id typing.rewriteType
  · change typing.focusBoundPrefix.map
      (mapTypeExpr LanguageDefSymbolMap.id) = typing.focusBoundPrefix
    induction typing.focusBoundPrefix with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        simp [mapTypeExpr_id, inductionHypothesis]
  · exact mapTypeExpr_id typing.focusType

/-- Transporting occurrence typing respects composition of structural
language morphisms.
-/
theorem map_comp
    {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (typing : DisplayedRewriteTyping first) :
    map (StructuralMorphism.comp earlier later) typing =
      map later (map earlier typing) := by
  apply DisplayedRewriteTyping.ext
  · exact DisplayedRewriteSite.map_comp earlier later typing.site
  · exact mapTypeExpr_comp earlier.symbols later.symbols typing.rewriteType
  · simp only [map, List.map_map]
    apply List.map_congr_left
    intro type _
    exact mapTypeExpr_comp earlier.symbols later.symbols type
  · exact mapTypeExpr_comp earlier.symbols later.symbols typing.focusType

/-! ## Positive and negative controls -/

namespace Canary

private def termType : TypeDecl :=
  TypeDecl.plain "displayed-rewrite-typing:Term"

private def valueType : TypeDecl :=
  TypeDecl.plain "displayed-rewrite-typing:Value"

private def termConstant : GrammarRule where
  label := "displayed-rewrite-typing:term"
  category := termType.name
  params := []
  syntaxPattern := []

private def valueConstant : GrammarRule where
  label := "displayed-rewrite-typing:value"
  category := valueType.name
  params := []
  syntaxPattern := []

private def identityRewrite : RewriteRule where
  name := "displayed-rewrite-typing:identity"
  typeContext := []
  premises := []
  left := .apply termConstant.label []
  right := .apply termConstant.label []

private def mismatchedRewrite : RewriteRule where
  name := "displayed-rewrite-typing:mismatch"
  typeContext := []
  premises := []
  left := .apply termConstant.label []
  right := .apply valueConstant.label []

private def positiveLanguage : LanguageDef :=
  { name := "displayed-rewrite-typing-positive"
    types := [termType]
    terms := [termConstant]
    equations := []
    rewrites := [identityRewrite] }

private def negativeLanguage : LanguageDef :=
  { name := "displayed-rewrite-typing-negative"
    types := [termType, valueType]
    terms := [termConstant, valueConstant]
    equations := []
    rewrites := [mismatchedRewrite] }

private theorem positiveLanguage_valid : positiveLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide
  case hconstructors => decide
  case hrewrites => decide
  case hcategory => decide
  case hparams => decide
  case hsyntax => decide
  case hrewriteValid =>
    intro rewrite membership
    change List.Mem rewrite [identityRewrite] at membership
    have equality := List.mem_singleton.mp membership
    subst rewrite
    simp [LanguageDef.validateRewrite, positiveLanguage, identityRewrite,
      termConstant, termType, LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]

private theorem negativeLanguage_valid : negativeLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide
  case hconstructors => decide
  case hrewrites => decide
  case hcategory => decide
  case hparams => decide
  case hsyntax => decide
  case hrewriteValid =>
    intro rewrite membership
    change List.Mem rewrite [mismatchedRewrite] at membership
    have equality := List.mem_singleton.mp membership
    subst rewrite
    simp [LanguageDef.validateRewrite, negativeLanguage, mismatchedRewrite,
      termConstant, valueConstant, termType, valueType,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]

private def positiveDefinition : ValidatedLanguageDef :=
  ⟨positiveLanguage, positiveLanguage_valid⟩

private def negativeDefinition : ValidatedLanguageDef :=
  ⟨negativeLanguage, negativeLanguage_valid⟩

private def positiveSite : DisplayedRewriteSite positiveLanguage :=
  DisplayedRewriteSite.root positiveLanguage ⟨0, by decide⟩

private theorem termConstantTypedPositive :
    HasType positiveLanguage FreeTypeContext.empty []
      (.apply termConstant.label []) (.base termType.name) := by
  apply HasType.constructor (rule := termConstant)
  · simp [positiveLanguage]
  · simp [UsesBareCollection, termConstant]
  · exact ArgumentsHaveTypes.nil

private theorem termConstantTypedNegative :
    HasType negativeLanguage FreeTypeContext.empty []
      (.apply termConstant.label []) (.base termType.name) := by
  apply HasType.constructor (rule := termConstant)
  · simp [negativeLanguage]
  · simp [UsesBareCollection, termConstant]
  · exact ArgumentsHaveTypes.nil

private theorem valueConstantTypedNegative :
    HasType negativeLanguage FreeTypeContext.empty []
      (.apply valueConstant.label []) (.base valueType.name) := by
  apply HasType.constructor (rule := valueConstant)
  · simp [negativeLanguage]
  · simp [UsesBareCollection, valueConstant]
  · exact ArgumentsHaveTypes.nil

/-- A structurally valid, well-sorted rewrite supplies a concrete typed root
occurrence.
-/
def positiveRootTyping : DisplayedRewriteTyping positiveDefinition where
  site := positiveSite
  rewriteType := .base termType.name
  focusBoundPrefix := []
  focusType := .base termType.name
  rewriteLeftTyped := by
    simpa [positiveDefinition, positiveSite, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite, positiveLanguage, identityRewrite] using
      termConstantTypedPositive
  rewriteRightTyped := by
    simpa [positiveDefinition, positiveSite, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite, positiveLanguage, identityRewrite] using
      termConstantTypedPositive
  sourceIsObject := by decide
  focusTyped := by
    simpa [positiveDefinition, positiveSite, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite, positiveLanguage, identityRewrite] using
      termConstantTypedPositive

theorem positiveRootTyping_rewrite_wellSorted :
    RewriteWellSorted positiveLanguage identityRewrite := by
  simpa [positiveRootTyping, positiveDefinition, positiveSite,
    DisplayedRewriteSite.root, DisplayedRewriteSite.rewrite,
    positiveLanguage] using
    positiveRootTyping.rewriteWellSorted

/-- Structural `LanguageDef` validation does not imply rewrite typing.  The
negative language passes the wire-format gate but its two endpoints live
in distinct authored sorts.
-/
theorem structurally_valid_mismatch_not_wellSorted :
    ¬ RewriteWellSorted negativeLanguage mismatchedRewrite := by
  rintro ⟨sharedType, termTyped, valueTyped⟩
  have termTypeEq : sharedType = .base termType.name :=
    HasType.apply_type_unique_of_validate_eq_nil negativeLanguage_valid
      termTyped termConstantTypedNegative
  have valueTypeEq : sharedType = .base valueType.name :=
    HasType.apply_type_unique_of_validate_eq_nil negativeLanguage_valid
      valueTyped valueConstantTypedNegative
  rw [termTypeEq] at valueTypeEq
  simp [termType, valueType, TypeDecl.plain] at valueTypeEq

end Canary

#print axioms labelDeterministic
#print axioms exists_of_rewrite_typing
#print axioms map
#print axioms map_id
#print axioms map_comp
#print axioms Canary.positiveRootTyping_rewrite_wellSorted
#print axioms Canary.structurally_valid_mismatch_not_wellSorted

end DisplayedRewriteTyping

end Mettapedia.OSLF.Framework
