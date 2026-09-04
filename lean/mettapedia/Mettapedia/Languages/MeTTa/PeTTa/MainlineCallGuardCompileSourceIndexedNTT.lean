import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedValidation
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.GroundFactExtension

/-!
# Source-indexed generated NTT for the cold PeTTa call-guard compiler

The cold compiler selects both universe endpoints at every one of its fifteen
authored rewrite roots.  This module discharges the source-pattern admission
once per authored root and transports that evidence to both endpoint
occurrences.  The shared source-indexed generator then attaches formation and
introduction rules whose premises and conclusions retain the literal authored
rewrite occurrence.

The covered fragment is deliberately binder-free.  Binding elimination is
absent until alpha-safe support and eigenvariable provenance are available.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
open Mettapedia.GSLT.LanguageDef.GroundFactExtension
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedValidation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

/-- Forget the star/box endpoint bit and recover the authored root index of a
selected occurrence.  Authored order is retained: slots `2 * i` and
`2 * i + 1` both name root `i`. -/
def rootIndexAt (slot : Occurrence demand) :
    Fin coldSource.language.rewrites.length :=
  ⟨slot.val / 2, by
    have bound := slot.isLt
    change slot.val < selectedOccurrences.length at bound
    rw [selectedOccurrences_count] at bound
    change slot.val / 2 < 15
    omega⟩

/-- Universe endpoint selection changes the modal profile but never the
underlying authored rewrite typing. -/
theorem typingAt_eq_rootTyping (slot : Occurrence demand) :
    typingAt demand slot = rootTyping (rootIndexAt slot) := by
  fin_cases slot <;> rfl

/-- A root occurrence has no fixed-context rely telescope. -/
theorem rootTyping_bindings_eq_nil
    (index : Fin coldSource.language.rewrites.length) :
    DisplayedContextProfile.bindings (rootTyping index) = [] := by
  simp [DisplayedContextProfile.bindings,
    DisplayedContextProfile.variableNames, rootTyping,
    DisplayedRewriteSite.root,
    DisplayedContextProfile.externalFreeFvarNames]

/-- Every authored cold transition lies in the explicit binder-free source
fragment.  The proof checks the fifteen source rows, not the generated proof
rows, so profile regeneration inherits this evidence. -/
theorem rootTyping_source_admission
    (index : Fin coldSource.language.rewrites.length) :
    TopLevelPatternAdmission (rootTyping index).site.rewrite.left ∧
      TopLevelPatternAdmission (rootTyping index).site.rewrite.right ∧
      TopLevelPatternAdmission (rootTyping index).site.focus := by
  fin_cases index <;> refine ⟨?_, ?_, ?_⟩ <;>
    apply topLevelPatternAdmission_of_check <;> decide +kernel

/-- Every exact authored cold root keeps each relation-query argument in the
matched source support.  This theorem inspects source rewrites, not generated
claims or relation answers. -/
theorem guardedRootPremises_sourceBound
    (index : Fin coldSource.language.rewrites.length) :
    PremisesSourceBound (rootTyping index).site.rewrite := by
  apply
    (allPremisesSourceBoundCheck_eq_true_iff
      (rootTyping index).site.rewrite).mp
  fin_cases index <;>
    simp [allPremisesSourceBoundCheck, premiseSourceBoundCheck,
      argumentSourceBoundCheck, rootTyping, DisplayedRewriteSite.rewrite,
      DisplayedRewriteSite.root, coldSource, language, transitions,
      finishTransition, skipHeadTransition, skipArityTransition,
      beginDeclarationTransition, argumentsFinishedTransition,
      rawInputTransition, undefinedInputTransition, holeInputTransition,
      checkedInputTransition, openInputTransition,
      undefinedResultTransition, holeResultTransition, atomResultTransition,
      checkedResultTransition, openResultTransition,
      inputStepTransition, resultStepTransition, query, v,
      compileRunning, compileArguments, compileResult,
      declarationsCons, declarationPattern, termsCons,
      Pattern.freeFvarNames]

/-- The shared typed premise decoder succeeds at every exact cold root. -/
theorem guardedRootViews_isSome
    (index : Fin coldSource.language.rewrites.length) :
    (decodeViews? (rootTyping index).site.rewrite).isSome = true := by
  obtain ⟨views, decoded⟩ :=
    exists_decodeViews?_eq_some_of_sourceBound (rootTyping index)
      (guardedRootPremises_sourceBound index)
  simp [decoded]

/-- Complete source-computed premise profile.  It records decoder success and
contains no relation result. -/
def guardProfile : SelectedNativeTypeBoundRelationClaim.Profile demand where
  supported := by
    intro slot
    rw [typingAt_eq_rootTyping]
    exact guardedRootViews_isSome _

/-- Guarded formation and introduction schemas are structurally admitted at
every selected occurrence.  The finite check consumes generated syntax only;
it grants no semantic relation evidence. -/
theorem guardView_sourceBound (slot : Occurrence demand)
    (view : SelectedNativeTypeBoundRelationPremise.View
      (typingAt demand slot).site.rewrite)
    (member : view ∈
      SelectedNativeTypeBoundRelationClaim.viewsAt guardProfile slot) :
    ∀ argument ∈ view.arguments,
      ArgumentSourceBound (typingAt demand slot).site.rewrite argument := by
  have allBound :
      PremisesSourceBound (typingAt demand slot).site.rewrite := by
    rw [typingAt_eq_rootTyping]
    exact guardedRootPremises_sourceBound _
  have encodedMember :
      view.encode ∈ (typingAt demand slot).site.rewrite.premises := by
    rw [← SelectedNativeTypeBoundRelationClaim.viewsAt_encoded
      guardProfile slot]
    exact List.mem_map_of_mem member
  obtain ⟨relation, arguments, encodedEq, argumentsBound⟩ :=
    allBound view.encode encodedMember
  cases view with
  | mk viewRelation viewArguments viewTypes =>
      simp only [SelectedNativeTypeBoundRelationPremise.View.encode,
        Premise.relationQuery.injEq] at encodedEq
      rcases encodedEq with ⟨relationEq, argumentsEq⟩
      subst relation
      subst arguments
      exact argumentsBound

/-- Exact decoded guard arguments inherit top-level admission from their
source-bound authored variables. -/
def guardArgumentAdmission (slot : Occurrence demand) :
    SelectedNativeTypeGuardedSourceIndexedIntroduction.GuardArgumentAdmission
      guardProfile slot where
  argument premise pattern membership := by
    have sourceBound := guardView_sourceBound slot
      (SelectedNativeTypeBoundRelationClaim.sourceView
        guardProfile slot premise)
      (List.get_mem
        (SelectedNativeTypeBoundRelationClaim.viewsAt guardProfile slot)
        premise)
      pattern membership
    rcases sourceBound with ⟨name, rfl, _sourceMembership⟩
    apply topLevelPatternAdmission_of_check
    simp [topLevelPatternAdmissionCheck, patternMetavariableOccurrencesAt,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      patternHasNoCollectionRest, Pattern.hasCanonicalBinderMetadata]

theorem occurrenceAdmission (slot : Occurrence demand) :
    SelectedNativeTypeGuardedSourceIndexedIntroduction.OccurrenceAdmission
      demand guardProfile slot := by
  apply
    SelectedNativeTypeGuardedSourceIndexedIntroduction.occurrenceAdmission_of_root_source
  · rw [bindingsAt, typingAt_eq_rootTyping]
    exact rootTyping_bindings_eq_nil _
  · refine { source := ?_, target := ?_, focus := ?_ }
    · rw [typingAt_eq_rootTyping]
      exact (rootTyping_source_admission _).1
    · rw [typingAt_eq_rootTyping]
      exact (rootTyping_source_admission _).2.1
    · rw [typingAt_eq_rootTyping]
      exact (rootTyping_source_admission _).2.2
  · exact guardArgumentAdmission slot

/-- Root selection has no shared focus/context variable role. -/
theorem supportSeparated : SupportSeparatedDemand demand := by
  intro slot
  have membership := List.get_mem demand.occurrences slot
  change DisplayedRewriteVariableProfile.sharedNames
    (demand.occurrences.get slot).typing.site = []
  unfold demand at membership ⊢
  unfold selectedOccurrences at membership ⊢
  simp only [List.mem_flatMap] at membership
  rcases membership with ⟨index, _indexMembership, occurrenceMembership⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMembership
  rcases occurrenceMembership with equality | equality
  · rw [equality]
    simp [profiledRoot, ProfiledRewriteOccurrence.constant, rootTyping]
  · rw [equality]
    simp [profiledRoot, ProfiledRewriteOccurrence.constant, rootTyping]

/-- One flat authored-source-plus-generated-typing calculus. -/
def generatedDefinition : CalculusLanguageDef :=
  SelectedNativeTypeGuardedSourceIndexedCalculus.definition
    demand supportSeparated guardProfile

/-- The generated typing attachment contributes no operational rewrite. -/
theorem generatedDefinition_rewrites :
    generatedDefinition.rewrites = coldSource.language.rewrites :=
  SelectedNativeTypeGuardedSourceIndexedCalculus.definition_rewrites
    demand supportSeparated guardProfile

/-- Nor does the generated typing attachment contribute object equations. -/
theorem generatedDefinition_equations :
    generatedDefinition.equations = coldSource.language.equations :=
  SelectedNativeTypeGuardedSourceIndexedCalculus.definition_equations
    demand supportSeparated guardProfile

/-- Exact generated type suffix, separated from the literal authored source
prefix. -/
def generatedTypeRows : List TypeDecl :=
  (SelectedNativeTypeContextualCalculus.signature demand).types ++
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTypes

/-- Proof-independent constructor prefix of the generated suffix. -/
def generatedBaseTermRows : List GrammarRule :=
  (SelectedNativeTypeContextualCalculus.signature demand).terms ++
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTerms ++
      SelectedNativeTypeOccurrenceStepClaim.terms demand ++
        familyApplicationTerms demand

/-- Exact generated constructor suffix.  Proof-indexed guard coordinates are
kept as one final family so their structural injectivity theorem discharges
admission without normalizing the profile while checking unrelated rows. -/
def generatedTermRows : List GrammarRule :=
  generatedBaseTermRows ++
    SelectedNativeTypeAuthoredVariableClaim.terms demand ++
      SelectedNativeTypeBoundRelationClaim.terms guardProfile

theorem generatedDefinition_types :
    generatedDefinition.types = coldSource.language.types ++
      generatedTypeRows := by
  simp [generatedDefinition, generatedTypeRows,
    SelectedNativeTypeGuardedSourceIndexedCalculus.definition_types,
    List.append_assoc]

theorem generatedDefinition_terms :
    generatedDefinition.terms = coldSource.language.terms ++
      generatedTermRows := by
  simp [generatedDefinition, generatedTermRows, generatedBaseTermRows,
    SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms,
    List.append_assoc]

/-- Generated labels inhabit a private namespace, so extending the signature
cannot capture a source metavariable, binder, or type-context name. -/
theorem generatedConstructorLabels_private :
    ∀ name ∈ generatedTermRows.map (fun declaration => declaration.label),
      name.toList.head? = some '$' := by
  intro name membership
  obtain ⟨term, termMembership, rfl⟩ := List.mem_map.mp membership
  rw [generatedTermRows] at termMembership
  rcases List.mem_append.mp termMembership with beforeGuard | guard
  · rcases List.mem_append.mp beforeGuard with base | authoredVariable
    · unfold generatedBaseTermRows at base
      simp only [List.mem_append] at base
      rcases base with beforeFamily | family
      · rcases beforeFamily with beforeOccurrence | occurrence
        · rcases beforeOccurrence with signature | carrier
          · have checked :
                (SelectedNativeTypeContextualCalculus.signature demand).terms.all
                  (fun declaration =>
                    declaration.label.toList.head? == some '$') = true := by
              decide +kernel
            exact beq_iff_eq.mp
              (List.all_eq_true.mp checked term signature)
          · have checked :
                (SelectedNativeTypeSourceIndexedCarrierSupport.extension
                  demand).newTerms.all (fun declaration =>
                    declaration.label.toList.head? == some '$') = true := by
              decide +kernel
            exact beq_iff_eq.mp
              (List.all_eq_true.mp checked term carrier)
        · obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp occurrence
          simp [SelectedNativeTypeOccurrenceStepClaim.termAt,
            SelectedNativeTypeOccurrenceStepClaim.Naming.label]
      · obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp family
        simp [familyApplicationTerm, auxiliaryLabel]
    · exact SelectedNativeTypeAuthoredVariableClaim.termLabels_private demand
        term.label (List.mem_map.mpr ⟨term, authoredVariable, rfl⟩)
  · exact SelectedNativeTypeBoundRelationClaim.termLabels_private
      guardProfile term.label (List.mem_map.mpr ⟨term, guard, rfl⟩)

/-- Authored cold constructors remain outside the generated namespace. -/
theorem sourceConstructorLabels_public :
    ∀ name ∈ coldSource.language.terms.map (fun declaration =>
        declaration.label),
      name.toList.head? ≠ some '$' := by
  intro name membership
  have checked :
      (coldSource.language.terms.map (fun declaration =>
        declaration.label)).all
          (fun candidate => candidate.toList.head? != some '$') = true := by
    decide +kernel
  exact bne_iff_ne.mp (List.all_eq_true.mp checked name membership)

/-- The source and generated constructor families are capture-free. -/
theorem constructorLabels_disjoint :
    List.Disjoint
      (coldSource.language.terms.map (fun declaration => declaration.label))
      (generatedTermRows.map (fun declaration => declaration.label)) := by
  apply List.disjoint_left.mpr
  intro name sourceMembership generatedMembership
  exact sourceConstructorLabels_public name sourceMembership
    (generatedConstructorLabels_private name generatedMembership)

/-- Appending generated constructors preserves every successful authored
constructor lookup. -/
theorem generatedConstructorArityRefines :
    ConstructorArityRefines coldSource.language
      generatedDefinition.toLanguageDef := by
  intro head arity valid
  have extended := languageHasConstructorArity_withAddedTerms
    coldSource.language generatedTermRows constructorLabels_disjoint valid
  unfold languageHasConstructorArity at extended ⊢
  simpa [withAddedTerms, generatedDefinition_terms] using extended

/-- The two endpoints of every authored root pass the fixed-constructor
checker in the small cold source signature. -/
theorem rootTyping_fixedConstructors
    (index : Fin coldSource.language.rewrites.length) :
    fixedConstructorsValid coldSource.language
        (rootTyping index).site.rewrite.left = true ∧
      fixedConstructorsValid coldSource.language
        (rootTyping index).site.rewrite.right = true := by
  fin_cases index <;> constructor <;> decide +kernel

/-- Source-local alpha-renaming plus signature refinement qualifies the exact
authored left endpoint in the flat target. -/
theorem authoredSource_fixedConstructors (slot : Occurrence demand) :
    fixedConstructorsValid generatedDefinition.toLanguageDef
      (authoredSource demand slot) = true := by
  unfold authoredSource authoredPattern
  rw [fixedConstructorsValid_renameFVars, typingAt_eq_rootTyping]
  exact fixedConstructorsValid_of_refines generatedConstructorArityRefines _
    (rootTyping_fixedConstructors _).1

/-- The exact authored right endpoint is qualified by the same transport. -/
theorem authoredTarget_fixedConstructors (slot : Occurrence demand) :
    fixedConstructorsValid generatedDefinition.toLanguageDef
      (authoredTarget demand slot) = true := by
  unfold authoredTarget authoredPattern
  rw [fixedConstructorsValid_renameFVars, typingAt_eq_rootTyping]
  exact fixedConstructorsValid_of_refines generatedConstructorArityRefines _
    (rootTyping_fixedConstructors _).2

/-- At a root site the selected focus is the authored left endpoint. -/
theorem authoredFocus_fixedConstructors (slot : Occurrence demand) :
    fixedConstructorsValid generatedDefinition.toLanguageDef
      (authoredFocus demand slot) = true := by
  unfold authoredFocus authoredPattern
  rw [fixedConstructorsValid_renameFVars, typingAt_eq_rootTyping]
  exact fixedConstructorsValid_of_refines generatedConstructorArityRefines _
    (rootTyping_fixedConstructors _).1

/-- Exact carrier-name factorization of the generated source extension. -/
theorem generatedDefinition_typeNames :
    generatedDefinition.toLanguageDef.typeNames =
      coldSource.language.typeNames ++
        generatedTypeRows.map TypeDecl.name := by
  simp [LanguageDef.typeNames, generatedDefinition_types, List.map_append]

private theorem generatedDefinition_constructorSignatures :
    constructorSignatures generatedDefinition.toLanguageDef =
      constructorSignatures coldSource.language ++
        generatedTermRows.map (fun declaration =>
          (declaration.label, declaration.params.length)) := by
  simp [constructorSignatures, generatedDefinition_terms, List.map_append]

/-- Exact constructor-label factorization of the generated source extension. -/
theorem generatedDefinition_constructorLabels :
    constructorLabels generatedDefinition.toLanguageDef =
      constructorLabels coldSource.language ++
        generatedTermRows.map (fun declaration => declaration.label) := by
  simp [constructorLabels, generatedDefinition_terms, List.map_append]

/-- Constructor labels are checked in bounded chunks.  This preserves the
ordinary kernel proof while avoiding normalization of the entire generated
signature in one dependent expression. -/
private def generatedTermLabels : List String :=
  (coldSource.language.terms ++ generatedBaseTermRows).map
    (fun declaration => declaration.label)

private def generatedTermLabelChunk (offset : Nat) : List String :=
  (generatedTermLabels.drop offset).take 32

private theorem disjoint_of_all_not_contains (first second : List String)
    (checked : first.all (fun name => !second.contains name) = true) :
    first.Disjoint second := by
  apply List.disjoint_left.mpr
  intro name firstMembership secondMembership
  have absent := List.all_eq_true.mp checked name firstMembership
  have containsFalse : second.contains name = false := by
    simpa using absent
  have containsTrue : second.contains name = true :=
    List.contains_iff_mem.mpr secondMembership
  rw [containsFalse] at containsTrue
  contradiction

private theorem generatedTermLabels_drop_nodup_of_chunk (offset : Nat)
    (head : (generatedTermLabelChunk offset).Nodup)
    (tail : (generatedTermLabels.drop (offset + 32)).Nodup)
    (apart : (generatedTermLabelChunk offset).Disjoint
      (generatedTermLabels.drop (offset + 32))) :
    (generatedTermLabels.drop offset).Nodup := by
  rw [← List.take_append_drop 32 (generatedTermLabels.drop offset)]
  apply head.append
  · simpa [List.drop_drop] using tail
  · simpa [generatedTermLabelChunk, List.drop_drop] using apart

private theorem generatedTermLabelChunk0_nodup :
    (generatedTermLabelChunk 0).Nodup := by decide +kernel

private theorem generatedTermLabelChunk0_apart :
    (generatedTermLabelChunk 0).Disjoint
      (generatedTermLabels.drop 32) := by
  apply disjoint_of_all_not_contains
  decide +kernel

private theorem generatedTermLabelChunk32_nodup :
    (generatedTermLabelChunk 32).Nodup := by decide +kernel

private theorem generatedTermLabelChunk32_apart :
    (generatedTermLabelChunk 32).Disjoint
      (generatedTermLabels.drop 64) := by
  apply disjoint_of_all_not_contains
  decide +kernel

private theorem generatedTermLabelChunk64_nodup :
    (generatedTermLabelChunk 64).Nodup := by decide +kernel

private theorem generatedTermLabelChunk64_apart :
    (generatedTermLabelChunk 64).Disjoint
      (generatedTermLabels.drop 96) := by
  apply disjoint_of_all_not_contains
  decide +kernel

private theorem generatedTermLabelChunk96_nodup :
    (generatedTermLabelChunk 96).Nodup := by decide +kernel

private theorem generatedTermLabelChunk96_apart :
    (generatedTermLabelChunk 96).Disjoint
      (generatedTermLabels.drop 128) := by
  apply disjoint_of_all_not_contains
  decide +kernel

private theorem generatedTermLabelChunk128_nodup :
    (generatedTermLabelChunk 128).Nodup := by decide +kernel

private theorem generatedTermLabelChunk128_apart :
    (generatedTermLabelChunk 128).Disjoint
      (generatedTermLabels.drop 160) := by
  apply disjoint_of_all_not_contains
  decide +kernel

private theorem generatedTermLabels_drop160_nodup :
    (generatedTermLabels.drop 160).Nodup := by decide +kernel

private theorem generatedVariableConstructorLabels_prefix :
    ∀ name ∈
        (SelectedNativeTypeAuthoredVariableClaim.terms demand).map
          GrammarRule.label,
      name.toList.take 3 = ['$', 'v', ':'] := by
  intro name membership
  obtain ⟨term, termMembership, rfl⟩ := List.mem_map.mp membership
  obtain ⟨rows, rowsMembership, termMembership⟩ :=
    List.mem_flatten.mp termMembership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowsMembership
  obtain ⟨binding, rfl⟩ := List.mem_ofFn.mp termMembership
  simp [SelectedNativeTypeAuthoredVariableClaim.termAt,
    SelectedNativeTypeAuthoredVariableClaim.Naming.label]

private theorem generatedGuardConstructorLabels_prefix :
    ∀ name ∈
        (SelectedNativeTypeBoundRelationClaim.terms guardProfile).map
          GrammarRule.label,
      name.toList.take 3 = ['$', 'q', ':'] := by
  intro name membership
  obtain ⟨term, termMembership, rfl⟩ := List.mem_map.mp membership
  obtain ⟨rows, rowsMembership, termMembership⟩ :=
    List.mem_flatten.mp termMembership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowsMembership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp termMembership
  simp [SelectedNativeTypeBoundRelationClaim.termAt,
    SelectedNativeTypeBoundRelationClaim.Naming.label]

private theorem generatedDefinition_termLabels_nodup :
    (generatedDefinition.terms.map (fun declaration => declaration.label)).Nodup := by
  have baseNodup : generatedTermLabels.Nodup := by
    have drop128 := generatedTermLabels_drop_nodup_of_chunk 128
      generatedTermLabelChunk128_nodup generatedTermLabels_drop160_nodup
      generatedTermLabelChunk128_apart
    have drop96 := generatedTermLabels_drop_nodup_of_chunk 96
      generatedTermLabelChunk96_nodup drop128 generatedTermLabelChunk96_apart
    have drop64 := generatedTermLabels_drop_nodup_of_chunk 64
      generatedTermLabelChunk64_nodup drop96 generatedTermLabelChunk64_apart
    have drop32 := generatedTermLabels_drop_nodup_of_chunk 32
      generatedTermLabelChunk32_nodup drop64 generatedTermLabelChunk32_apart
    simpa using generatedTermLabels_drop_nodup_of_chunk 0
      generatedTermLabelChunk0_nodup drop32 generatedTermLabelChunk0_apart
  have baseAvoidsGuard :
      ∀ name ∈ generatedTermLabels,
        name.toList.take 3 ≠ ['$', 'q', ':'] := by
    intro name membership
    have checked : generatedTermLabels.all (fun candidate =>
        candidate.toList.take 3 != ['$', 'q', ':']) = true := by
      decide +kernel
    exact bne_iff_ne.mp (List.all_eq_true.mp checked name membership)
  have baseAvoidsVariable :
      ∀ name ∈ generatedTermLabels,
        name.toList.take 3 ≠ ['$', 'v', ':'] := by
    intro name membership
    have checked : generatedTermLabels.all (fun candidate =>
        candidate.toList.take 3 != ['$', 'v', ':']) = true := by
      decide +kernel
    exact bne_iff_ne.mp (List.all_eq_true.mp checked name membership)
  have baseVariableApart : generatedTermLabels.Disjoint
      ((SelectedNativeTypeAuthoredVariableClaim.terms demand).map
        GrammarRule.label) := by
    apply List.disjoint_left.mpr
    intro name baseMembership variableMembership
    exact baseAvoidsVariable name baseMembership
      (generatedVariableConstructorLabels_prefix name variableMembership)
  have baseGuardApart : generatedTermLabels.Disjoint
      ((SelectedNativeTypeBoundRelationClaim.terms guardProfile).map
        GrammarRule.label) := by
    apply List.disjoint_left.mpr
    intro name baseMembership guardMembership
    exact baseAvoidsGuard name baseMembership
      (generatedGuardConstructorLabels_prefix name guardMembership)
  have variableGuardApart :
      ((SelectedNativeTypeAuthoredVariableClaim.terms demand).map
          GrammarRule.label).Disjoint
        ((SelectedNativeTypeBoundRelationClaim.terms guardProfile).map
          GrammarRule.label) := by
    apply List.disjoint_left.mpr
    intro name variableMembership guardMembership
    have variablePrefix :=
      generatedVariableConstructorLabels_prefix name variableMembership
    have guardPrefix :=
      generatedGuardConstructorLabels_prefix name guardMembership
    rw [guardPrefix] at variablePrefix
    simp at variablePrefix
  have combinedGuardApart :
      (generatedTermLabels ++
          (SelectedNativeTypeAuthoredVariableClaim.terms demand).map
            GrammarRule.label).Disjoint
        ((SelectedNativeTypeBoundRelationClaim.terms guardProfile).map
          GrammarRule.label) := by
    apply List.disjoint_left.mpr
    intro name combinedMembership guardMembership
    rcases List.mem_append.mp combinedMembership with baseMembership |
        variableMembership
    · exact (List.disjoint_left.mp baseGuardApart) baseMembership
        guardMembership
    · exact (List.disjoint_left.mp variableGuardApart) variableMembership
        guardMembership
  have baseVariableNodup :
      (generatedTermLabels ++
        (SelectedNativeTypeAuthoredVariableClaim.terms demand).map
          GrammarRule.label).Nodup :=
    baseNodup.append
      (SelectedNativeTypeAuthoredVariableClaim.termLabels_nodup demand)
      baseVariableApart
  have completeNodup :
      (generatedTermLabels ++
          (SelectedNativeTypeAuthoredVariableClaim.terms demand).map
            GrammarRule.label ++
        (SelectedNativeTypeBoundRelationClaim.terms guardProfile).map
          GrammarRule.label).Nodup :=
    baseVariableNodup.append
      (SelectedNativeTypeBoundRelationClaim.termLabels_nodup guardProfile)
      combinedGuardApart
  rw [generatedDefinition_terms, generatedTermRows, List.map_append,
    List.map_append, List.map_append]
  change (generatedTermLabels ++
    (SelectedNativeTypeAuthoredVariableClaim.terms demand).map
      GrammarRule.label ++
    (SelectedNativeTypeBoundRelationClaim.terms guardProfile).map
      GrammarRule.label).Nodup
  exact completeNodup

private def generatedExtendsFor (rewrite : RewriteRule)
    (membership : rewrite ∈ language.rewrites) :
    ExtendsFor language generatedDefinition.toLanguageDef rewrite where
  addedTypes := generatedTypeRows.map TypeDecl.name
  addedSignatures := generatedTermRows.map (fun declaration =>
    (declaration.label, declaration.params.length))
  addedLabels := generatedTermRows.map (fun declaration => declaration.label)
  typeNames := by
    simpa [coldSource] using generatedDefinition_typeNames
  signatures := by
    simpa [coldSource] using generatedDefinition_constructorSignatures
  labels := by
    simpa [coldSource] using generatedDefinition_constructorLabels
  avoidsSchema := by
    intro name schemaMembership generatedMembership
    exact transition_schemaNames_not_generatedPrefix rewrite membership name
      schemaMembership (generatedConstructorLabels_private name
        generatedMembership)

private theorem generatedDefinition_rewrites_validate :
    ∀ rewrite ∈ generatedDefinition.rewrites,
      LanguageDef.validateRewrite generatedDefinition.toLanguageDef rewrite =
        [] := by
  intro rewrite membership
  rw [generatedDefinition_rewrites] at membership
  have sourceMembership : rewrite ∈ language.rewrites := by
    simpa [coldSource] using membership
  exact validateRewrite_eq_nil generatedDefinition_termLabels_nodup
    (Certificate.extend (transition_certificate rewrite sourceMembership)
      (generatedExtendsFor rewrite sourceMembership))

private theorem generatedBaseTermRows_category :
    ∀ term ∈ coldSource.language.terms ++ generatedBaseTermRows,
      term.category ∈ generatedDefinition.toLanguageDef.typeNames := by
  decide +kernel

private theorem generatedBaseTermRows_parameters :
    ∀ term ∈ coldSource.language.terms ++ generatedBaseTermRows,
      ∀ parameter ∈ term.params,
        ∀ typeName ∈ (TermParam.typeExpr parameter).baseNames,
      typeName ∈ generatedDefinition.toLanguageDef.typeNames := by
  decide +kernel

private theorem generatedVariableTerm_category
    (term : GrammarRule)
    (membership : term ∈
      SelectedNativeTypeAuthoredVariableClaim.terms demand) :
    term.category ∈ generatedDefinition.toLanguageDef.typeNames := by
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨binding, rfl⟩ := List.mem_ofFn.mp termMembership
  change ContextualInference.formulaType.name ∈
    generatedDefinition.toLanguageDef.typeNames
  decide +kernel

private theorem generatedGuardTerm_category
    (term : GrammarRule)
    (membership : term ∈
      SelectedNativeTypeBoundRelationClaim.terms guardProfile) :
    term.category ∈ generatedDefinition.toLanguageDef.typeNames := by
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp termMembership
  change ContextualInference.formulaType.name ∈
    generatedDefinition.toLanguageDef.typeNames
  decide +kernel

private theorem retainedCarrierName_mem_generatedTypes
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        SelectedNativeTypeSourceIndexedCarrierSupport.additionalCarrierNames
          demand) :
    carrier ∈ generatedDefinition.toLanguageDef.typeNames := by
  have checked :
      ∀ candidate ∈
          SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
            SelectedNativeTypeSourceIndexedCarrierSupport.additionalCarrierNames
              demand,
        candidate ∈ generatedDefinition.toLanguageDef.typeNames := by
    decide +kernel
  exact checked carrier membership

private theorem generatedVariableTerm_parameters
    (term : GrammarRule)
    (membership : term ∈
      SelectedNativeTypeAuthoredVariableClaim.terms demand) :
    ∀ parameter ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr parameter).baseNames,
        typeName ∈ generatedDefinition.toLanguageDef.typeNames := by
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨binding, rfl⟩ := List.mem_ofFn.mp termMembership
  intro parameter parameterMembership typeName typeNameMembership
  simp only [SelectedNativeTypeAuthoredVariableClaim.termAt,
    List.mem_singleton] at parameterMembership
  subst parameter
  simp only [TermParam.typeExpr, TypeExpr.baseNames,
    List.mem_singleton] at typeNameMembership
  subst typeName
  apply retainedCarrierName_mem_generatedTypes
  apply SelectedNativeTypeSourceIndexedCarrierSupport.resolve_mem_carrierNames
  apply SelectedNativeTypeSourceIndexedCarrierSupport.authoredCarrier_mem_augmented
    demand slot
  exact SelectedNativeTypeSourceIndexedValidation.authoredBindingCarrier_mem
    demand slot (List.get_mem _ binding)

private theorem generatedGuardTerm_parameters
    (term : GrammarRule)
    (membership : term ∈
      SelectedNativeTypeBoundRelationClaim.terms guardProfile) :
    ∀ parameter ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr parameter).baseNames,
        typeName ∈ generatedDefinition.toLanguageDef.typeNames := by
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp termMembership
  intro parameter parameterMembership typeName typeNameMembership
  rw [SelectedNativeTypeBoundRelationClaim.termAt,
    List.mem_ofFn] at parameterMembership
  obtain ⟨argument, rfl⟩ := parameterMembership
  simp only [TermParam.typeExpr, TypeExpr.baseNames,
    List.mem_singleton] at typeNameMembership
  subst typeName
  apply retainedCarrierName_mem_generatedTypes
  apply SelectedNativeTypeSourceIndexedCarrierSupport.resolve_mem_carrierNames
  apply SelectedNativeTypeSourceIndexedCarrierSupport.authoredCarrier_mem_augmented
    demand slot
  exact SelectedNativeTypeBoundRelationClaim.sourceView_argumentType_mem_authored
    guardProfile slot premise (List.get_mem _ argument)

private theorem generatedDefinition_terms_category :
    ∀ term ∈ generatedDefinition.terms,
      term.category ∈ generatedDefinition.toLanguageDef.typeNames := by
  intro term membership
  rw [generatedDefinition_terms] at membership
  rcases List.mem_append.mp membership with source | rest
  · exact generatedBaseTermRows_category term
      (List.mem_append_left _ source)
  · rw [generatedTermRows] at rest
    rcases List.mem_append.mp rest with beforeGuard | guard
    · rcases List.mem_append.mp beforeGuard with base | authoredVariable
      · exact generatedBaseTermRows_category term
          (List.mem_append_right _ base)
      · exact generatedVariableTerm_category term authoredVariable
    · exact generatedGuardTerm_category term guard

private theorem generatedDefinition_terms_parameters :
    ∀ term ∈ generatedDefinition.terms,
      ∀ parameter ∈ term.params,
        ∀ typeName ∈ (TermParam.typeExpr parameter).baseNames,
          typeName ∈ generatedDefinition.toLanguageDef.typeNames := by
  intro term membership
  rw [generatedDefinition_terms] at membership
  rcases List.mem_append.mp membership with source | rest
  · exact generatedBaseTermRows_parameters term
      (List.mem_append_left _ source)
  · rw [generatedTermRows] at rest
    rcases List.mem_append.mp rest with beforeGuard | guard
    · rcases List.mem_append.mp beforeGuard with base | authoredVariable
      · exact generatedBaseTermRows_parameters term
          (List.mem_append_right _ base)
      · exact generatedVariableTerm_parameters term authoredVariable
    · exact generatedGuardTerm_parameters term guard

private theorem generatedBaseConcreteSyntaxRowsValid :
    (coldSource.language.terms ++ generatedBaseTermRows).all (fun term =>
      let boundNames := term.params.flatMap fun parameter =>
        TermParam.bodyName parameter :: TermParam.binderNames parameter
      term.syntaxPattern.all
        (LanguageDef.concreteSyntaxItemAllowed boundNames)) = true := by
  decide +kernel

private theorem generatedGuardConcreteSyntaxRowsValid :
    (SelectedNativeTypeBoundRelationClaim.terms guardProfile).all (fun term =>
      let boundNames := term.params.flatMap fun parameter =>
        TermParam.bodyName parameter :: TermParam.binderNames parameter
      term.syntaxPattern.all
        (LanguageDef.concreteSyntaxItemAllowed boundNames)) = true := by
  apply List.all_eq_true.mpr
  intro term membership
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp termMembership
  rfl

private theorem generatedVariableConcreteSyntaxRowsValid :
    (SelectedNativeTypeAuthoredVariableClaim.terms demand).all (fun term =>
      let boundNames := term.params.flatMap fun parameter =>
        TermParam.bodyName parameter :: TermParam.binderNames parameter
      term.syntaxPattern.all
        (LanguageDef.concreteSyntaxItemAllowed boundNames)) = true := by
  apply List.all_eq_true.mpr
  intro term membership
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨binding, rfl⟩ := List.mem_ofFn.mp termMembership
  rfl

private theorem generatedDefinition_concreteSyntaxRowsValid :
    LanguageDef.concreteSyntaxRowsValid
      generatedDefinition.toLanguageDef = true := by
  unfold LanguageDef.concreteSyntaxRowsValid
  rw [generatedDefinition_terms, generatedTermRows, List.all_append,
    List.all_append, List.all_append]
  have baseValid := generatedBaseConcreteSyntaxRowsValid
  rw [List.all_append, Bool.and_eq_true] at baseValid
  simp [baseValid.1, baseValid.2,
    generatedVariableConcreteSyntaxRowsValid,
    generatedGuardConcreteSyntaxRowsValid]

/-- The enlarged object signature validates by separating the finite
proof-independent constructor prefix from the source-indexed guard family.
No proof traverses the complete profile merely to rediscover that every guard
constructor returns `Formula`, uses retained source carriers, and has no
concrete syntax. -/
theorem generatedLanguage_validate :
    generatedDefinition.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · simpa [coldSource, language] using generatedDefinition_equations
  · decide +kernel
  · exact generatedDefinition_termLabels_nodup
  · decide +kernel
  · exact generatedDefinition_terms_category
  · exact generatedDefinition_terms_parameters
  · exact generatedDefinition_concreteSyntaxRowsValid
  · exact generatedDefinition_rewrites_validate

/-- Structural validation exposes duplicate-free carrier names for the exact
generated target. -/
theorem generatedDefinition_typeNames_nodup :
    generatedDefinition.toLanguageDef.typeNames.Nodup :=
  LanguageDef.typeNames_nodup_of_validate_eq_nil
    generatedDefinition.toLanguageDef generatedLanguage_validate

/-- Structural validation exposes duplicate-free constructor labels for the
exact generated target. -/
theorem generatedDefinition_constructorLabels_nodup :
    (generatedDefinition.toLanguageDef.terms.map
      (fun term => term.label)).Nodup :=
  LanguageDef.constructorLabels_nodup_of_validate_eq_nil
    generatedDefinition.toLanguageDef generatedLanguage_validate

/-- Literal authored source, target, and focus patterns are admitted in the
finished guarded target without consulting the cold compiler result. -/
theorem targetOccurrenceAdmission (slot : Occurrence demand) :
    SelectedNativeTypeGuardedSourceIndexedValidation.TargetOccurrenceAdmission
      demand supportSeparated guardProfile slot where
  source := ⟨authoredSource_fixedConstructors slot⟩
  target := ⟨authoredTarget_fixedConstructors slot⟩
  focus := ⟨authoredFocus_fixedConstructors slot⟩

/-- Every exact authored guard claim is fixed-constructor valid in the same
finished target.  Arguments are reconstructed from the source-bound premise
row and therefore cannot be supplied by another occurrence activation. -/
theorem targetGuardAdmission (slot : Occurrence demand) :
    SelectedNativeTypeGuardedSourceIndexedValidation.TargetGuardAdmission
      demand supportSeparated guardProfile slot where
  claim premise := by
    unfold SelectedNativeTypeBoundRelationClaim.authoredClaim
      SelectedNativeTypeBoundRelationClaim.claim
    apply
      SelectedNativeTypeSourceIndexedValidation.FixedPatternAdmission.apply
    · exact
        SelectedNativeTypeGuardedSourceIndexedValidation.guardClaim_has_arity
          demand supportSeparated guardProfile generatedLanguage_validate
          slot premise
    · intro argument membership
      unfold SelectedNativeTypeBoundRelationClaim.authoredArguments at membership
      obtain ⟨sourcePattern, sourceMembership, rfl⟩ :=
        List.mem_map.mp membership
      have sourceBound := guardView_sourceBound slot
        (SelectedNativeTypeBoundRelationClaim.sourceView
          guardProfile slot premise)
        (List.get_mem
          (SelectedNativeTypeBoundRelationClaim.viewsAt guardProfile slot)
          premise)
        sourcePattern sourceMembership
      rcases sourceBound with ⟨name, rfl, _sourceMembership⟩
      simpa [authoredPattern, Pattern.renameFVars] using
        SelectedNativeTypeSourceIndexedValidation.FixedPatternAdmission.fvar
          (SelectedNativeTypeGuardedSourceIndexedValidation.Target
            demand supportSeparated guardProfile).toLanguageDef
          (renameVariable demand slot name)

/-- All source-indexed formation and introduction rows pass the ordinary
local schema checker by generator-family provenance. -/
theorem generatedOccurrenceRules_locallyValid :
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.profiledRules
      demand guardProfile).all
      RuleSchema.isLocallyValid = true :=
  SelectedNativeTypeGuardedSourceIndexedIntroduction.profiledRules_locallyValid
    demand guardProfile occurrenceAdmission

/-! ## Complete flat-calculus admission -/

/-- Generated carrier and contextual judgment heads are pairwise distinct. -/
theorem generatedJudgmentHeads_nodup :
    (generatedDefinition.judgments.map JudgmentDecl.head).Nodup := by
  decide +kernel

/-- Source-independent and occurrence-indexed rule families use disjoint,
nonempty identifiers. -/
theorem generatedRuleIds_nodup : generatedDefinition.ruleIds.Nodup := by
  decide +kernel

private theorem generatedJudgmentHeads_not_guardPrefix :
    ∀ head ∈ generatedDefinition.judgmentHeads,
      head.toList.take 3 ≠ ['$', 'q', ':'] := by
  intro head membership
  have checked : generatedDefinition.judgmentHeads.all (fun candidate =>
      candidate.toList.take 3 != ['$', 'q', ':']) = true := by
    decide +kernel
  exact bne_iff_ne.mp (List.all_eq_true.mp checked head membership)

private theorem generatedJudgmentHeads_not_variablePrefix :
    ∀ head ∈ generatedDefinition.judgmentHeads,
      head.toList.take 3 ≠ ['$', 'v', ':'] := by
  intro head membership
  have checked : generatedDefinition.judgmentHeads.all (fun candidate =>
      candidate.toList.take 3 != ['$', 'v', ':']) = true := by
    decide +kernel
  exact bne_iff_ne.mp (List.all_eq_true.mp checked head membership)

private theorem generatedVariableTerms_avoidJudgmentHead
    (head : String) (membership : head ∈ generatedDefinition.judgmentHeads) :
    (SelectedNativeTypeAuthoredVariableClaim.terms demand).any
      (fun declaration => declaration.label == head) = false := by
  apply List.any_eq_false.mpr
  intro term termMembership equal
  have labelEqual : term.label = head := beq_iff_eq.mp equal
  have variableMembership : term.label ∈
      (SelectedNativeTypeAuthoredVariableClaim.terms demand).map
        GrammarRule.label :=
    List.mem_map.mpr ⟨term, termMembership, rfl⟩
  exact generatedJudgmentHeads_not_variablePrefix head membership
    (labelEqual ▸ generatedVariableConstructorLabels_prefix term.label
      variableMembership)

private theorem generatedGuardTerms_avoidJudgmentHead
    (head : String) (membership : head ∈ generatedDefinition.judgmentHeads) :
    (SelectedNativeTypeBoundRelationClaim.terms guardProfile).any
      (fun declaration => declaration.label == head) = false := by
  apply List.any_eq_false.mpr
  intro term termMembership equal
  have labelEqual : term.label = head := beq_iff_eq.mp equal
  have guardMembership : term.label ∈
      (SelectedNativeTypeBoundRelationClaim.terms guardProfile).map
        GrammarRule.label :=
    List.mem_map.mpr ⟨term, termMembership, rfl⟩
  exact generatedJudgmentHeads_not_guardPrefix head membership
    (labelEqual ▸ generatedGuardConstructorLabels_prefix term.label
      guardMembership)

/-- The generated judgment namespace is nonempty, unique, disjoint from term
constructors, and avoids reserved metasyntax heads. -/
theorem generatedJudgmentSignature_valid :
    generatedDefinition.judgmentSignatureValid = true := by
  unfold CalculusLanguageDef.judgmentSignatureValid
  simp only [Bool.and_eq_true]
  constructor
  · constructor
    · decide +kernel
    · exact
        (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup
          generatedDefinition.judgmentHeads).mpr (by
            simpa [CalculusLanguageDef.judgmentHeads] using
              generatedJudgmentHeads_nodup)
  · apply List.all_eq_true.mpr
    intro head membership
    simp only [Bool.and_eq_true]
    constructor
    · rw [Bool.not_eq_true_eq_eq_false]
      rw [generatedDefinition_terms, generatedTermRows, List.any_append,
        List.any_append, List.any_append]
      have baseAbsent :
          (coldSource.language.terms ++ generatedBaseTermRows).any
            (fun declaration => declaration.label == head) = false := by
        have checked : generatedDefinition.judgmentHeads.all (fun candidate =>
            !((coldSource.language.terms ++ generatedBaseTermRows).any
              (fun declaration => declaration.label == candidate))) = true := by
          decide +kernel
        simpa using List.all_eq_true.mp checked head membership
      rw [List.any_append, Bool.or_eq_false_iff] at baseAbsent
      rw [baseAbsent.1, baseAbsent.2,
        generatedVariableTerms_avoidJudgmentHead head membership,
        generatedGuardTerms_avoidJudgmentHead head membership]
      rfl
    · have checked : generatedDefinition.judgmentHeads.all (fun candidate =>
          !([Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains
            candidate)) = true := by
        decide +kernel
      exact List.all_eq_true.mp checked head membership

/-- This selected fragment deliberately declares no conversion authority. -/
theorem generatedConversionDeclaration_valid :
    generatedDefinition.conversionDeclarationValid = true := by
  rfl

/-- Every generated proof row passes the complete target-dependent checker.
The proof composes the signature, endpoint-carrier, canonical-context, and
guarded-occurrence generator families; it never enumerates the finished rule
array. -/
theorem generatedRules_validIn :
    generatedDefinition.rules.all
      (RuleSchema.isValidIn generatedDefinition) = true := by
  exact SelectedNativeTypeGuardedSourceIndexedValidation.rules_validIn
    demand supportSeparated guardProfile generatedLanguage_validate
    generatedJudgmentHeads_nodup occurrenceAdmission
    targetOccurrenceAdmission targetGuardAdmission

/-- Complete target-dependent admission entails the local schema coordinate
without a second normalization of the generated profile. -/
theorem generatedRules_locallyValid :
    generatedDefinition.rules.all RuleSchema.isLocallyValid = true := by
  apply List.all_eq_true.mpr
  intro rule membership
  have valid := List.all_eq_true.mp generatedRules_validIn rule membership
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at valid
  exact valid.1

/-- The complete authored-source-plus-generated-NTT calculus is admitted by
the ordinary V2 checker using generator provenance rather than a row dump. -/
theorem generatedDefinition_valid : generatedDefinition.isValid = true := by
  exact SelectedNativeTypeGuardedSourceIndexedValidation.definition_isValid
    demand supportSeparated guardProfile generatedLanguage_validate
    generatedJudgmentHeads_nodup generatedRuleIds_nodup
    generatedJudgmentSignature_valid generatedConversionDeclaration_valid
    occurrenceAdmission targetOccurrenceAdmission targetGuardAdmission

/-- Proof-carrying flat calculus consumed by semantic and lowering stages. -/
def generated : ValidatedCalculusLanguageDef :=
  ⟨generatedDefinition, generatedDefinition_valid⟩

#print axioms typingAt_eq_rootTyping
#print axioms rootTyping_source_admission
#print axioms occurrenceAdmission
#print axioms supportSeparated
#print axioms generatedOccurrenceRules_locallyValid
#print axioms generatedDefinition_rewrites
#print axioms generatedLanguage_validate
#print axioms generatedJudgmentSignature_valid
#print axioms generatedRules_validIn
#print axioms generatedDefinition_valid

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
