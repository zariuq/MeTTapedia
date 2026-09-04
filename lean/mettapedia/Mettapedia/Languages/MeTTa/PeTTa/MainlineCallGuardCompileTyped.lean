import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT

/-!
# Validated flat typed GSLT for the PeTTa call-guard compiler

The source-indexed selected-native generator already produces one ordinary
flat calculus: the authenticated cold source is its literal prefix and the
generated binder-free typing rows are its suffix.  This module records the
integration boundary of that same object.  It deliberately constructs no
second attachment and introduces no parallel proof calculus.

The source inclusion, exact row preservation, validation evidence, and
namespace-collision control below are the facts consumed by relation-aware
operational projection and later lowering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTyped

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT

/-- The exact generated delta whose application produces the flat typed
source.  It is data computed from the selected source occurrences. -/
def typedExtension : CalculusLanguageExtension :=
  extension demand supportSeparated guardProfile

/-- The flat typed source is definitionally the application of the shared
source-preserving extension construction, rather than a separately authored
calculus later compared with it. -/
theorem typedExtension_applies_to_coldSource :
    typedExtension.apply
        (SourcePreservingCalculusCoproduct.sourceBase coldSource) =
      generatedDefinition :=
  rfl

/-- Every emitted inference rule concludes one of the new generated
judgments; the authored cold source has no proof judgment that can be silently
extended. -/
theorem typedExtension_newJudgmentsOnly :
    typedExtension.policyHolds
      (SourcePreservingCalculusCoproduct.sourceBase coldSource)
      .newJudgmentsOnly = true := by
  decide +kernel

@[simp] theorem typedExtension_newTypes :
    typedExtension.newTypes = generatedTypeRows := by
  rfl

@[simp] theorem typedExtension_newTerms :
    typedExtension.newTerms = generatedTermRows := by
  have rows := congrArg (fun definition : CalculusLanguageDef =>
    definition.terms) typedExtension_applies_to_coldSource
  change coldSource.language.terms ++ typedExtension.newTerms =
    generatedDefinition.terms at rows
  rw [generatedDefinition_terms] at rows
  exact (List.append_right_inj coldSource.language.terms).mp rows

@[simp] theorem typedExtension_newEquations :
    typedExtension.newEquations = [] := by
  rfl

@[simp] theorem typedExtension_newRewrites :
    typedExtension.newRewrites = [] := by
  rfl

private theorem generatedTypeNames_disjoint :
    List.Disjoint coldSource.language.typeNames
      (generatedTypeRows.map TypeDecl.name) := by
  apply List.Nodup.disjoint
  rw [← generatedDefinition_typeNames]
  exact generatedDefinition_typeNames_nodup

private theorem generatedConstructorLabels_disjoint :
    List.Disjoint (coldSource.language.terms.map (fun term => term.label))
      (generatedTermRows.map (fun term => term.label)) := by
  apply List.Nodup.disjoint
  have labels := generatedDefinition_constructorLabels
  change generatedDefinition.toLanguageDef.terms.map
      (fun term => term.label) =
    coldSource.language.terms.map (fun term => term.label) ++
      generatedTermRows.map (fun term => term.label) at labels
  rw [← labels]
  exact generatedDefinition_constructorLabels_nodup

private theorem generatedTypes_absentFromCold :
    generatedTypeRows.all (fun declaration =>
      !(coldSource.language.types.any fun existing =>
        existing.name == declaration.name)) = true := by
  rw [List.all_eq_true]
  intro declaration declarationMembership
  rw [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro existing existingMembership namesEqual
  have coldMembership : existing.name ∈ coldSource.language.typeNames :=
    List.mem_map.mpr ⟨existing, existingMembership, rfl⟩
  have generatedMembership :
      declaration.name ∈ generatedTypeRows.map TypeDecl.name :=
    List.mem_map.mpr ⟨declaration, declarationMembership, rfl⟩
  apply (List.disjoint_left.mp generatedTypeNames_disjoint coldMembership)
  rw [beq_iff_eq.mp namesEqual]
  exact generatedMembership

private theorem generatedTerms_absentFromCold :
    generatedTermRows.all (fun declaration =>
      !(coldSource.language.terms.any fun existing =>
        existing.label == declaration.label)) = true := by
  rw [List.all_eq_true]
  intro declaration declarationMembership
  rw [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro existing existingMembership labelsEqual
  have coldMembership :
      existing.label ∈ coldSource.language.terms.map (fun term => term.label) :=
    List.mem_map.mpr ⟨existing, existingMembership, rfl⟩
  have generatedMembership :
      declaration.label ∈ generatedTermRows.map (fun term => term.label) :=
    List.mem_map.mpr ⟨declaration, declarationMembership, rfl⟩
  apply (List.disjoint_left.mp generatedConstructorLabels_disjoint
    coldMembership)
  rw [beq_iff_eq.mp labelsEqual]
  exact generatedMembership

/-- The emitted rows are namespace-disjoint from the authenticated source.
This is derived from validation of the complete generated language, not by
normalizing the complete profile inside the Boolean collision checker. -/
theorem typedExtension_disjoint :
    typedExtension.disjointFrom
      (SourcePreservingCalculusCoproduct.sourceBase coldSource) = true := by
  simp [CalculusLanguageExtension.disjointFrom,
    SourcePreservingCalculusCoproduct.sourceBase,
    InferenceExtension.ProofCalculus.empty,
    generatedTypes_absentFromCold, generatedTerms_absentFromCold]

/-- The policy expected by the shared guarded-source attachment interface. -/
theorem typedExtension_contextualPolicy :
    typedExtension.policyHolds
      (SourcePreservingCalculusCoproduct.sourceBase coldSource)
      (.extendsBaseJudgments [ContextualInference.contextualJudgment.head]) =
        true := by
  decide +kernel

/-- The generator's own compatibility record is the complete lawful
attachment certificate for this PeTTa instance. -/
def compatibility :
    Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus.Compatibility
      demand supportSeparated guardProfile where
  disjoint := typedExtension_disjoint
  policy := typedExtension_contextualPolicy
  valid := generatedDefinition_valid

/-- The ordinary validated extension view of the same generated artifact. -/
def validatedTypedExtension :
    ValidatedCalculusLanguageExtension
      (SourcePreservingCalculusCoproduct.validatedSourceBase coldSource) :=
  compatibility.validatedExtension

/-- Lawful attachment targets the one source-indexed generated calculus;
there is no separately authored typed presentation. -/
theorem validatedTypedExtension_target :
    validatedTypedExtension.target = generated := by
  apply Subtype.ext
  exact typedExtension_applies_to_coldSource

/-- The authored type rows remain a literal prefix of the qualified target. -/
theorem coldTypes_prefix :
    coldSource.language.types.IsPrefix generated.1.types := by
  change coldSource.language.types.IsPrefix generatedDefinition.types
  rw [generatedDefinition_types]
  exact List.prefix_append _ _

/-- The authored constructor rows remain a literal prefix of the qualified
target, preserving their order and multiplicity. -/
theorem coldTerms_prefix :
    coldSource.language.terms.IsPrefix generated.1.terms := by
  change coldSource.language.terms.IsPrefix generatedDefinition.terms
  rw [generatedDefinition_terms]
  exact List.prefix_append _ _

/-- Proof generation contributes no object equation. -/
theorem flatTyped_equations :
    generated.1.equations = language.equations :=
  generatedDefinition_equations

/-- Proof generation contributes no operational rewrite. -/
theorem flatTyped_rewrites :
    generated.1.rewrites = language.rewrites :=
  generatedDefinition_rewrites

/-- The authenticated cold source embeds literally in the one generated flat
calculus. -/
def coldInclusion : StructuralMorphism coldSource
    generated.toValidatedLanguageDef where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    change List.Mem declaration generatedDefinition.types
    rw [generatedDefinition_types]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    change List.Mem declaration generatedDefinition.terms
    rw [generatedDefinition_terms]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    simpa [generated, generatedDefinition_equations, mapEquation_id] using
      membership
  mapsRewrites declaration membership := by
    simpa [generated, generatedDefinition_rewrites, mapRewriteRule_id] using
      membership

/-- Audited structural counts of the sound binder-free target.  The older
standalone calculus had a different rule inventory because it included an
unqualified elimination family; it is not the qualified runtime source. -/
theorem flatTyped_equations_count : generated.1.equations.length = 0 := by
  simp [flatTyped_equations, language]

/-- A constructor row contributes none of the static equation generators
tracked by `LanguageDef.isEquationFree`. -/
private def equationNeutralTerm (declaration : GrammarRule) : Bool :=
  !(declaration.params.any fun parameter =>
      (TermParam.typeExpr parameter).mentionsCollection .hashBag) &&
    !(declaration.params.any fun parameter =>
      (TermParam.typeExpr parameter).mentionsCollection .hashSet) &&
    !declaration.algebra?.isSome

private theorem coldTerms_equationNeutral :
    coldSource.language.terms.all equationNeutralTerm = true := by
  decide +kernel

private theorem contextualTerms_equationNeutral :
    (SelectedNativeTypeContextualCalculus.signature demand).terms.all
      equationNeutralTerm = true := by
  decide +kernel

private theorem carrierTerms_equationNeutral :
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTerms.all
      equationNeutralTerm = true := by
  decide +kernel

private theorem occurrenceTerms_equationNeutral :
    (SelectedNativeTypeOccurrenceStepClaim.terms demand).all
      equationNeutralTerm = true := by
  decide +kernel

private theorem familyTerms_equationNeutral :
    (SelectedNativeTypeSourceIndexedIntroduction.familyApplicationTerms
      demand).all equationNeutralTerm = true := by
  decide +kernel

private theorem variableTerms_equationNeutral :
    (SelectedNativeTypeAuthoredVariableClaim.terms demand).all
      equationNeutralTerm = true := by
  apply List.all_eq_true.mpr
  intro declaration membership
  obtain ⟨row, rowMembership, declarationMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨binding, rfl⟩ := List.mem_ofFn.mp declarationMembership
  simp [equationNeutralTerm,
    SelectedNativeTypeAuthoredVariableClaim.termAt,
    TermParam.typeExpr, TypeExpr.mentionsCollection]

private theorem guardTerms_equationNeutral :
    (SelectedNativeTypeBoundRelationClaim.terms guardProfile).all
      equationNeutralTerm = true := by
  apply List.all_eq_true.mpr
  intro declaration membership
  obtain ⟨row, rowMembership, declarationMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp declarationMembership
  simp [equationNeutralTerm, SelectedNativeTypeBoundRelationClaim.termAt,
    TermParam.typeExpr, TypeExpr.mentionsCollection]

private theorem generatedTerms_equationNeutral :
    generatedDefinition.terms.all equationNeutralTerm = true := by
  rw [generatedDefinition_terms, generatedTermRows, generatedBaseTermRows,
    List.all_append, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append]
  simp only [coldTerms_equationNeutral, contextualTerms_equationNeutral,
    carrierTerms_equationNeutral, occurrenceTerms_equationNeutral,
    familyTerms_equationNeutral, variableTerms_equationNeutral,
    guardTerms_equationNeutral, Bool.true_and]

/-- Neither the authenticated cold source nor the generated proof signature
introduces an authored or collection-derived equation.  Keeping this fact as
a named certificate prevents downstream semantic construction from unfolding
the complete generated profile merely to rediscover equation-freedom. -/
theorem flatTyped_equationFree :
    generated.1.toLanguageDef.isEquationFree = true := by
  have noBag : generatedDefinition.terms.any (fun declaration =>
      declaration.params.any fun parameter =>
        (TermParam.typeExpr parameter).mentionsCollection .hashBag) = false := by
    apply List.any_eq_false.mpr
    intro declaration membership
    have neutral := List.all_eq_true.mp generatedTerms_equationNeutral
      declaration membership
    simp only [equationNeutralTerm, Bool.and_eq_true,
      Bool.not_eq_true'] at neutral
    simp [neutral.1.1]
  have noSet : generatedDefinition.terms.any (fun declaration =>
      declaration.params.any fun parameter =>
        (TermParam.typeExpr parameter).mentionsCollection .hashSet) = false := by
    apply List.any_eq_false.mpr
    intro declaration membership
    have neutral := List.all_eq_true.mp generatedTerms_equationNeutral
      declaration membership
    simp only [equationNeutralTerm, Bool.and_eq_true,
      Bool.not_eq_true'] at neutral
    simp [neutral.1.2]
  have noAlgebra : generatedDefinition.terms.any (fun declaration =>
      declaration.algebra?.isSome) = false := by
    apply List.any_eq_false.mpr
    intro declaration membership
    have neutral := List.all_eq_true.mp generatedTerms_equationNeutral
      declaration membership
    simp only [equationNeutralTerm, Bool.and_eq_true,
      Bool.not_eq_true'] at neutral
    simp [neutral.2]
  change generatedDefinition.toLanguageDef.isEquationFree = true
  unfold LanguageDef.isEquationFree LanguageDef.usesCollection
    LanguageDef.hasAlgebraDeclarations
  rw [generatedDefinition_equations, noBag, noSet, noAlgebra]
  simp [coldSource, language]

theorem flatTyped_rewrites_count : generated.1.rewrites.length = 15 := by
  simp [flatTyped_rewrites, language, transitions]

theorem flatTyped_judgments_count : generated.1.judgments.length = 10 := by
  rfl

theorem flatTyped_rules_count : generated.1.rules.length = 80 := by
  decide +kernel

/-! ## Namespace-collision negative control -/

private def collidingExtension : CalculusLanguageExtension :=
  { newTypes := [TypeDecl.plain "CGNat"] }

/-- Reusing an authored PeTTa carrier fails the same explicit disjointness
gate used by source-preserving extensions. -/
theorem collidingExtension_not_disjoint :
    collidingExtension.disjointFrom
      (SourcePreservingCalculusCoproduct.sourceBase coldSource) = false := by
  decide +kernel

#print axioms typedExtension_applies_to_coldSource
#print axioms typedExtension_newJudgmentsOnly
#print axioms typedExtension_disjoint
#print axioms validatedTypedExtension_target
#print axioms coldInclusion
#print axioms flatTyped_rewrites
#print axioms flatTyped_equationFree
#print axioms flatTyped_rules_count
#print axioms collidingExtension_not_disjoint

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTyped
