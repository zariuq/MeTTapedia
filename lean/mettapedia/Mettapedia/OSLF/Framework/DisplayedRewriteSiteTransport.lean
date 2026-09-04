import Mettapedia.OSLF.Framework.DisplayedRewriteSite
import Mettapedia.GSLT.LanguageDef.StructuralSelection

/-!
# Structural transport of displayed rewrite sites

The source-indexed OSLF signature construction acts on selected source occurrences, not only
on unindexed patterns.  This module lifts a structural language morphism
to those occurrences.  The target rewrite index is recovered uniquely from
validation: authored rewrite names are duplicate-free, hence the target
rewrite list itself is duplicate-free.

This is the occurrence-level morphism action needed by a later generated
typing-definition functor.  It is deliberately separate from exact semantic
modal transport, whose diamond and box laws require the stronger operational
coverage conditions packaged by `LanguageIndexedModalFunctor`.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef

namespace DisplayedRewriteSite

/-- Validation of rewrite names also makes the authored rewrite rows
duplicate-free. -/
theorem rewriteRows_nodup (definition : ValidatedLanguageDef) :
    definition.language.rewrites.Nodup :=
  List.Nodup.of_map (fun rewrite : RewriteRule => rewrite.name)
    (LanguageDef.rewriteNames_nodup_of_validate_eq_nil
      definition.language definition.valid)

/-- The unique index of an authored rewrite row in a validated language. -/
noncomputable def authoredRewriteIndex (definition : ValidatedLanguageDef)
    (rewrite : RewriteRule) (authored : rewrite ∈ definition.language.rewrites) :
    Fin definition.language.rewrites.length :=
  Classical.choose (List.get_of_mem authored)

theorem get_authoredRewriteIndex (definition : ValidatedLanguageDef)
    (rewrite : RewriteRule) (authored : rewrite ∈ definition.language.rewrites) :
    definition.language.rewrites.get
      (authoredRewriteIndex definition rewrite authored) = rewrite :=
  Classical.choose_spec (List.get_of_mem authored)

/-- Any supplied index of the same authored row is the recovered index. -/
theorem authoredRewriteIndex_eq (definition : ValidatedLanguageDef)
    (rewrite : RewriteRule) (authored : rewrite ∈ definition.language.rewrites)
    (index : Fin definition.language.rewrites.length)
    (atIndex : definition.language.rewrites.get index = rewrite) :
    authoredRewriteIndex definition rewrite authored = index := by
  apply (rewriteRows_nodup definition).injective_get
  rw [get_authoredRewriteIndex, atIndex]

/-- Target rewrite occurrence selected by a structural language map. -/
noncomputable def mappedRewriteIndex
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    Fin target.language.rewrites.length :=
  authoredRewriteIndex target
    (mapRewriteRule morphism.symbols site.rewrite)
    (morphism.mapsRewrites site.rewrite
      (List.get_mem source.language.rewrites site.rewriteIndex))

/-- Reading the target at the transported index gives exactly the mapped
source rewrite row. -/
theorem get_mappedRewriteIndex
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    target.language.rewrites[mappedRewriteIndex morphism site] =
      mapRewriteRule morphism.symbols site.rewrite := by
  exact get_authoredRewriteIndex target
    (mapRewriteRule morphism.symbols site.rewrite)
    (morphism.mapsRewrites site.rewrite
      (List.get_mem source.language.rewrites site.rewriteIndex))

/-- `List.get` spelling of `get_mappedRewriteIndex`, used by list-nodup
arguments. -/
theorem get_mappedRewriteIndex_get
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    target.language.rewrites.get (mappedRewriteIndex morphism site) =
      mapRewriteRule morphism.symbols site.rewrite := by
  exact get_authoredRewriteIndex target
    (mapRewriteRule morphism.symbols site.rewrite)
    (morphism.mapsRewrites site.rewrite
      (List.get_mem source.language.rewrites site.rewriteIndex))

/-- Carry a displayed source occurrence along a structural language map. -/
noncomputable def map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    DisplayedRewriteSite target.language where
  rewriteIndex := mappedRewriteIndex morphism site
  focus := Mettapedia.GSLT.LanguageDef.mapPattern morphism.symbols site.focus
  context := CIGSLT.mapOneHoleContext morphism.symbols site.context
  selects := by
    rw [get_mappedRewriteIndex]
    simpa [mapRewriteRule, DisplayedRewriteSite.rewrite] using
      Selects.mapPattern morphism.symbols site.selects

@[simp]
theorem map_rewriteIndex
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    (map morphism site).rewriteIndex = mappedRewriteIndex morphism site := rfl

@[simp]
theorem map_focus
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    (map morphism site).focus =
      Mettapedia.GSLT.LanguageDef.mapPattern morphism.symbols site.focus := rfl

@[simp]
theorem map_context
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    (map morphism site).context =
      CIGSLT.mapOneHoleContext morphism.symbols site.context := rfl

@[simp]
theorem map_rewrite
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (site : DisplayedRewriteSite source.language) :
    (map morphism site).rewrite =
      mapRewriteRule morphism.symbols site.rewrite :=
  get_mappedRewriteIndex morphism site

/-- The recovered index for identity transport is the original authored
occurrence. -/
theorem mappedRewriteIndex_id (definition : ValidatedLanguageDef)
    (site : DisplayedRewriteSite definition.language) :
    mappedRewriteIndex (StructuralMorphism.id definition) site =
      site.rewriteIndex := by
  apply authoredRewriteIndex_eq
  exact (mapRewriteRule_id site.rewrite).symm

/-- Displayed-site transport respects the identity structural morphism. -/
@[simp]
theorem map_id (definition : ValidatedLanguageDef)
    (site : DisplayedRewriteSite definition.language) :
    map (StructuralMorphism.id definition) site = site := by
  apply DisplayedRewriteSite.ext
  · exact mappedRewriteIndex_id definition site
  · exact Mettapedia.GSLT.LanguageDef.mapPattern_id site.focus
  · exact CIGSLT.mapOneHoleContext_id site.context

/-- Displayed-site transport respects composition. -/
theorem map_comp
    {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (site : DisplayedRewriteSite first.language) :
    map (StructuralMorphism.comp earlier later) site =
      map later (map earlier site) := by
  apply DisplayedRewriteSite.ext
  · apply (rewriteRows_nodup third).injective_get
    simp only [map_rewriteIndex]
    rw [get_mappedRewriteIndex_get, get_mappedRewriteIndex_get, map_rewrite]
    exact mapRewriteRule_comp earlier.symbols later.symbols site.rewrite
  · exact Mettapedia.GSLT.LanguageDef.mapPattern_comp
      earlier.symbols later.symbols site.focus
  · exact CIGSLT.mapOneHoleContext_comp
      earlier.symbols later.symbols site.context

/-- Map an authored-order selection pointwise. -/
noncomputable def mapSelection
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (selection : DisplayedSiteSelection source.language) :
    DisplayedSiteSelection target.language :=
  selection.map (map morphism)

theorem mapSelection_append
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (base delta : DisplayedSiteSelection source.language) :
    mapSelection morphism (base ++ delta) =
      mapSelection morphism base ++ mapSelection morphism delta := by
  unfold mapSelection
  exact List.map_append

/-- Pointwise site transport carries an append-only compilation delta to the
corresponding target delta. -/
theorem mapSelection_preserves_appendOnlyExtension
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {base extended : DisplayedSiteSelection source.language}
    (extension : DisplayedSiteSelection.AppendOnlyExtension base extended) :
    DisplayedSiteSelection.AppendOnlyExtension
      (mapSelection morphism base) (mapSelection morphism extended) := by
  obtain ⟨delta, rfl⟩ := extension
  exact ⟨mapSelection morphism delta, mapSelection_append morphism base delta⟩

/-- Logical site coverage is monotone under structural transport, even when
the morphism lawfully coalesces source occurrences. -/
theorem mapSelection_preserves_covers
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {smaller larger : DisplayedSiteSelection source.language}
    (coverage : DisplayedSiteSelection.Covers smaller larger) :
    DisplayedSiteSelection.Covers
      (mapSelection morphism smaller) (mapSelection morphism larger) := by
  intro targetSite targetMembership
  obtain ⟨sourceSite, sourceMembership, rfl⟩ :=
    List.mem_map.mp targetMembership
  exact List.mem_map.mpr
    ⟨sourceSite, coverage sourceSite sourceMembership, rfl⟩

@[simp]
theorem mapSelection_id (definition : ValidatedLanguageDef)
    (selection : DisplayedSiteSelection definition.language) :
    mapSelection (StructuralMorphism.id definition) selection = selection := by
  induction selection with
  | nil => rfl
  | cons site selection inductionHypothesis =>
      unfold mapSelection at inductionHypothesis ⊢
      rw [List.map_cons, map_id, inductionHypothesis]

theorem mapSelection_comp
    {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (selection : DisplayedSiteSelection first.language) :
    mapSelection (StructuralMorphism.comp earlier later) selection =
      mapSelection later (mapSelection earlier selection) := by
  induction selection with
  | nil => rfl
  | cons site selection inductionHypothesis =>
      unfold mapSelection at inductionHypothesis ⊢
      rw [List.map_cons, List.map_cons, List.map_cons, map_comp,
        inductionHypothesis]

end DisplayedRewriteSite

/-! ## Positive and non-injectivity controls -/

namespace DisplayedRewriteSite.TransportCanary

private def termType : TypeDecl := TypeDecl.plain "site-transport-canary:Term"

private def term : GrammarRule where
  label := "site-transport-canary:term"
  category := termType.name
  params := []
  syntaxPattern := []

private def sourceFirst : RewriteRule where
  name := "site-transport-canary:source-first"
  typeContext := []
  premises := []
  left := .apply term.label []
  right := .apply term.label []

private def sourceSecond : RewriteRule where
  name := "site-transport-canary:source-second"
  typeContext := []
  premises := []
  left := .apply term.label []
  right := .apply term.label []

private def targetOnly : RewriteRule where
  name := "site-transport-canary:target"
  typeContext := []
  premises := []
  left := .apply term.label []
  right := .apply term.label []

private def sourceLanguage : LanguageDef :=
  { name := "site-transport-canary-source"
    types := [termType]
    terms := [term]
    equations := []
    rewrites := [sourceFirst, sourceSecond] }

private def targetLanguage : LanguageDef :=
  { name := "site-transport-canary-target"
    types := [termType]
    terms := [term]
    equations := []
    rewrites := [targetOnly] }

private theorem sourceLanguage_valid : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide
  case hconstructors => decide
  case hrewrites => decide
  case hcategory => decide
  case hparams => decide
  case hsyntax => decide
  case hrewriteValid =>
    intro rule membership
    change List.Mem rule [sourceFirst, sourceSecond] at membership
    rcases List.mem_cons.mp membership with rfl | tailMembership
    · simp [LanguageDef.validateRewrite, sourceLanguage, sourceFirst,
        sourceSecond, term, termType,
        LanguageDef.validatePatternConstructors,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames,
        Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]
    · have equality := List.mem_singleton.mp tailMembership
      subst rule
      simp [LanguageDef.validateRewrite, sourceLanguage, sourceFirst,
        sourceSecond, term, termType,
        LanguageDef.validatePatternConstructors,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames,
        Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]

private theorem targetLanguage_valid : targetLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide
  case hconstructors => decide
  case hrewrites => decide
  case hcategory => decide
  case hparams => decide
  case hsyntax => decide
  case hrewriteValid =>
    intro rule membership
    change List.Mem rule [targetOnly] at membership
    have equality := List.mem_singleton.mp membership
    subst rule
    simp [LanguageDef.validateRewrite, targetLanguage, targetOnly, term,
      termType, LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]

private def source : ValidatedLanguageDef :=
  ⟨sourceLanguage, sourceLanguage_valid⟩

private def target : ValidatedLanguageDef :=
  ⟨targetLanguage, targetLanguage_valid⟩

private def coalesceRewrites : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with
    rewrite := fun _ => targetOnly.name }

private def coalescingMorphism : StructuralMorphism source target where
  symbols := coalesceRewrites
  mapsTypes declaration membership := by
    change List.Mem declaration [termType] at membership
    have equality := List.mem_singleton.mp membership
    cases equality
    change List.Mem (mapTypeDecl coalesceRewrites termType) [termType]
    exact List.Mem.head _
  mapsTerms declaration membership := by
    change List.Mem declaration [term] at membership
    have equality := List.mem_singleton.mp membership
    cases equality
    change List.Mem (mapGrammarRule coalesceRewrites term) [term]
    exact List.Mem.head _
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rule membership := by
    change List.Mem rule [sourceFirst, sourceSecond] at membership
    rcases List.mem_cons.mp membership with equality | tailMembership
    · subst rule
      change List.Mem (mapRewriteRule coalesceRewrites sourceFirst) [targetOnly]
      exact List.Mem.head _
    · have equality := List.mem_singleton.mp tailMembership
      subst rule
      change List.Mem (mapRewriteRule coalesceRewrites sourceSecond) [targetOnly]
      exact List.Mem.head _

private def firstSite : DisplayedRewriteSite source.language :=
  DisplayedRewriteSite.root source.language ⟨0, by decide⟩

private def secondSite : DisplayedRewriteSite source.language :=
  DisplayedRewriteSite.root source.language ⟨1, by decide⟩

theorem source_sites_distinct : firstSite ≠ secondSite := by
  intro equality
  have indexEquality := congrArg DisplayedRewriteSite.rewriteIndex equality
  simp [firstSite, secondSite, DisplayedRewriteSite.root] at indexEquality

theorem mapped_first_index :
    (DisplayedRewriteSite.map coalescingMorphism firstSite).rewriteIndex =
      ⟨0, by decide⟩ := by
  apply (DisplayedRewriteSite.rewriteRows_nodup target).injective_get
  simp only [DisplayedRewriteSite.map_rewriteIndex]
  rw [DisplayedRewriteSite.get_mappedRewriteIndex_get]
  rfl

theorem mapped_second_index :
    (DisplayedRewriteSite.map coalescingMorphism secondSite).rewriteIndex =
      ⟨0, by decide⟩ := by
  apply (DisplayedRewriteSite.rewriteRows_nodup target).injective_get
  simp only [DisplayedRewriteSite.map_rewriteIndex]
  rw [DisplayedRewriteSite.get_mappedRewriteIndex_get]
  rfl

/-- Structural language morphisms may lawfully quotient two authored
rewrite occurrences.  Site transport is functorial but not automatically
injective; a provenance-sensitive translation must request a stronger map or
carry a certified quotient observation. -/
theorem structural_transport_can_coalesce_sites :
    DisplayedRewriteSite.map coalescingMorphism firstSite =
      DisplayedRewriteSite.map coalescingMorphism secondSite := by
  apply DisplayedRewriteSite.ext
  · exact mapped_first_index.trans mapped_second_index.symm
  · rfl
  · rfl

theorem structural_transport_not_always_injective :
    ¬ Function.Injective (DisplayedRewriteSite.map coalescingMorphism) := by
  intro injective
  exact source_sites_distinct
    (injective structural_transport_can_coalesce_sites)

end DisplayedRewriteSite.TransportCanary

#print axioms DisplayedRewriteSite.rewriteRows_nodup
#print axioms DisplayedRewriteSite.get_authoredRewriteIndex
#print axioms DisplayedRewriteSite.map_id
#print axioms DisplayedRewriteSite.map_comp
#print axioms DisplayedRewriteSite.mapSelection_preserves_appendOnlyExtension
#print axioms DisplayedRewriteSite.mapSelection_preserves_covers
#print axioms DisplayedRewriteSite.mapSelection_comp
#print axioms DisplayedRewriteSite.TransportCanary.structural_transport_can_coalesce_sites
#print axioms DisplayedRewriteSite.TransportCanary.structural_transport_not_always_injective

end Mettapedia.OSLF.Framework
