import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNativeTypeDemand
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedValidation
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.GroundFactExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

/-!
# Source-indexed generated NTT for FOF Skolemization

This module attaches the shared selected-native-type calculus to every root of
the authored Skolemization transformation.  Generated formation and
introduction rules retain the literal source, target, and focus patterns of
the selected rewrite occurrence.  The resulting flat calculus preserves the
authored operational rewrite table exactly and adds only proof-level rows.

The covered occurrences are binder-free rewrite roots.  Formula binders are
ordinary constructors in the already binder-resolved source representation;
the generated calculus does not perform name resolution or Skolemization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNTT

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
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNativeTypeDemand

/-- Forget the endpoint bit: slots `2 * i` and `2 * i + 1` both select
authored root `i`. -/
def rootIndexAt (slot : Occurrence demand) :
    Fin source.language.rewrites.length :=
  ⟨slot.val / 2, by
    have bound := slot.isLt
    change slot.val < selectedOccurrences.length at bound
    rw [selectedOccurrences_count] at bound
    change slot.val / 2 < 26
    omega⟩

/-- Modal endpoint selection never changes the underlying source typing. -/
theorem typingAt_eq_rootTyping (slot : Occurrence demand) :
    typingAt demand slot = rootTyping (rootIndexAt slot) := by
  fin_cases slot <;> rfl

/-- Root occurrences have no fixed-context rely telescope. -/
theorem rootTyping_bindings_eq_nil
    (index : Fin source.language.rewrites.length) :
    DisplayedContextProfile.bindings (rootTyping index) = [] := by
  simp [DisplayedContextProfile.bindings,
    DisplayedContextProfile.variableNames, rootTyping,
    DisplayedRewriteSite.root,
    DisplayedContextProfile.externalFreeFvarNames]

set_option maxHeartbeats 800000 in
/-- Every selected source endpoint is admitted by the binder-free generated
rule fragment. -/
theorem rootTyping_source_admission
    (index : Fin source.language.rewrites.length) :
    TopLevelPatternAdmission (rootTyping index).site.rewrite.left ∧
      TopLevelPatternAdmission (rootTyping index).site.rewrite.right ∧
      TopLevelPatternAdmission (rootTyping index).site.focus := by
  fin_cases index <;> refine ⟨?_, ?_, ?_⟩ <;>
    apply topLevelPatternAdmission_of_check <;> decide +kernel

/-- Both generated rule families are admitted at every selected occurrence. -/
theorem occurrenceAdmission (slot : Occurrence demand) :
    OccurrenceAdmission demand slot := by
  apply occurrenceAdmission_of_root_source
  · rw [bindingsAt, typingAt_eq_rootTyping]
    exact rootTyping_bindings_eq_nil _
  · refine { source := ?_, target := ?_, focus := ?_ }
    · rw [typingAt_eq_rootTyping]
      exact (rootTyping_source_admission _).1
    · rw [typingAt_eq_rootTyping]
      exact (rootTyping_source_admission _).2.1
    · rw [typingAt_eq_rootTyping]
      exact (rootTyping_source_admission _).2.2

/-- Root selection has no shared focus/context variable role. -/
theorem supportSeparated : SupportSeparatedDemand demand := by
  intro slot
  rw [typingAt_eq_rootTyping]
  simp [DisplayedRewriteVariableProfile.sharedNames,
    DisplayedRewriteVariableProfile.contextNames,
    DisplayedRewriteVariableProfile.focusNames,
    rootTyping, DisplayedRewriteSite.root,
    DisplayedContextProfile.externalFreeFvarNames]

/-- One flat authored-source-plus-generated-typing calculus. -/
def generatedDefinition : CalculusLanguageDef :=
  SelectedNativeTypeSourceIndexedCalculus.definition demand supportSeparated

/-- Generated typing contributes no operational rewrite. -/
theorem generatedDefinition_rewrites :
    generatedDefinition.rewrites = source.language.rewrites :=
  SelectedNativeTypeSourceIndexedCalculus.definition_rewrites
    demand supportSeparated

/-- Generated typing contributes no object equation. -/
theorem generatedDefinition_equations :
    generatedDefinition.equations = source.language.equations :=
  SelectedNativeTypeSourceIndexedCalculus.definition_equations
    demand supportSeparated

/-- Exact generated type suffix. -/
def generatedTypeRows : List TypeDecl :=
  (SelectedNativeTypeContextualCalculus.signature demand).types ++
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTypes

/-- Exact generated constructor suffix. -/
def generatedTermRows : List GrammarRule :=
  (SelectedNativeTypeContextualCalculus.signature demand).terms ++
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTerms ++
      SelectedNativeTypeOccurrenceStepClaim.terms demand ++
        familyApplicationTerms demand

theorem generatedDefinition_types :
    generatedDefinition.types = source.language.types ++ generatedTypeRows := by
  simp [generatedDefinition, generatedTypeRows,
    SelectedNativeTypeSourceIndexedCalculus.definition_types,
    List.append_assoc]

theorem generatedDefinition_terms :
    generatedDefinition.terms = source.language.terms ++ generatedTermRows := by
  simp [generatedDefinition, generatedTermRows,
    SelectedNativeTypeSourceIndexedCalculus.definition_terms,
    List.append_assoc]

/-- Generated labels occupy the private generated-calculus namespace. -/
theorem generatedConstructorLabels_private :
    ∀ name ∈ generatedTermRows.map (fun declaration => declaration.label),
      name.toList.head? = some '$' := by
  decide +kernel

/-- Authored constructor labels remain outside the generated namespace. -/
theorem sourceConstructorLabels_public :
    ∀ name ∈ source.language.terms.map (fun declaration =>
        declaration.label),
      name.toList.head? ≠ some '$' := by
  intro name membership
  have checked :
      (source.language.terms.map (fun declaration =>
        declaration.label)).all
          (fun candidate => candidate.toList.head? != some '$') = true := by
    decide +kernel
  exact bne_iff_ne.mp (List.all_eq_true.mp checked name membership)

/-- Source and generated constructor families are capture-free. -/
theorem constructorLabels_disjoint :
    List.Disjoint
      (source.language.terms.map (fun declaration => declaration.label))
      (generatedTermRows.map (fun declaration => declaration.label)) := by
  apply List.disjoint_left.mpr
  intro name sourceMembership generatedMembership
  exact sourceConstructorLabels_public name sourceMembership
    (generatedConstructorLabels_private name generatedMembership)

/-- Successful authored constructor lookups remain successful after the
generated signature is attached. -/
theorem generatedConstructorArityRefines :
    ConstructorArityRefines source.language
      generatedDefinition.toLanguageDef := by
  intro head arity valid
  have extended := languageHasConstructorArity_withAddedTerms
    source.language generatedTermRows constructorLabels_disjoint valid
  unfold languageHasConstructorArity at extended ⊢
  simpa [withAddedTerms, generatedDefinition_terms] using extended

set_option maxHeartbeats 800000 in
/-- Every source endpoint passes the fixed-constructor checker before the
signature extension. -/
theorem rootTyping_fixedConstructors
    (index : Fin source.language.rewrites.length) :
    fixedConstructorsValid source.language
        (rootTyping index).site.rewrite.left = true ∧
      fixedConstructorsValid source.language
        (rootTyping index).site.rewrite.right = true := by
  fin_cases index <;> constructor <;> decide +kernel

theorem authoredSource_fixedConstructors (slot : Occurrence demand) :
    fixedConstructorsValid generatedDefinition.toLanguageDef
      (authoredSource demand slot) = true := by
  unfold authoredSource authoredPattern
  rw [fixedConstructorsValid_renameFVars, typingAt_eq_rootTyping]
  exact fixedConstructorsValid_of_refines generatedConstructorArityRefines _
    (rootTyping_fixedConstructors _).1

theorem authoredTarget_fixedConstructors (slot : Occurrence demand) :
    fixedConstructorsValid generatedDefinition.toLanguageDef
      (authoredTarget demand slot) = true := by
  unfold authoredTarget authoredPattern
  rw [fixedConstructorsValid_renameFVars, typingAt_eq_rootTyping]
  exact fixedConstructorsValid_of_refines generatedConstructorArityRefines _
    (rootTyping_fixedConstructors _).2

theorem authoredFocus_fixedConstructors (slot : Occurrence demand) :
    fixedConstructorsValid generatedDefinition.toLanguageDef
      (authoredFocus demand slot) = true := by
  unfold authoredFocus authoredPattern
  rw [fixedConstructorsValid_renameFVars, typingAt_eq_rootTyping]
  exact fixedConstructorsValid_of_refines generatedConstructorArityRefines _
    (rootTyping_fixedConstructors _).1

/-- Literal authored source, target, and focus patterns are admitted in the
one flat signature. -/
def targetOccurrenceAdmission (slot : Occurrence demand) :
    SelectedNativeTypeSourceIndexedValidation.TargetOccurrenceAdmission
      demand supportSeparated slot where
  source := ⟨authoredSource_fixedConstructors slot⟩
  target := ⟨authoredTarget_fixedConstructors slot⟩
  focus := ⟨authoredFocus_fixedConstructors slot⟩

private theorem generatedDefinition_typeNames :
    generatedDefinition.toLanguageDef.typeNames =
      source.language.typeNames ++ generatedTypeRows.map TypeDecl.name := by
  simp [LanguageDef.typeNames, generatedDefinition_types, List.map_append]

private theorem generatedDefinition_constructorSignatures :
    constructorSignatures generatedDefinition.toLanguageDef =
      constructorSignatures source.language ++
        generatedTermRows.map (fun declaration =>
          (declaration.label, declaration.params.length)) := by
  simp [constructorSignatures, generatedDefinition_terms, List.map_append]

private theorem generatedDefinition_constructorLabels :
    constructorLabels generatedDefinition.toLanguageDef =
      constructorLabels source.language ++
        generatedTermRows.map (fun declaration => declaration.label) := by
  simp [constructorLabels, generatedDefinition_terms, List.map_append]

private theorem generatedDefinition_termLabels_nodup :
    (generatedDefinition.terms.map
      (fun declaration => declaration.label)).Nodup := by
  decide +kernel

set_option maxHeartbeats 800000 in
private theorem sourceSchemaNames_public :
    ∀ rewrite ∈ source.language.rewrites,
      ∀ name ∈ schemaNames rewrite, name.toList.head? ≠ some '$' := by
  intro rewrite rewriteMembership name nameMembership
  change rewrite ∈ TptpFofSkolemizationLanguageDef.language.rewrites at rewriteMembership
  obtain ⟨index, indexEquality⟩ := List.get_of_mem rewriteMembership
  have checked :
      (schemaNames
        (TptpFofSkolemizationLanguageDef.language.rewrites.get index)).all
          (fun candidate => candidate.toList.head? != some '$') = true := by
    fin_cases index <;>
      simp [schemaNames, TptpFofSkolemizationLanguageDef.language,
        TptpFofSkolemizationLanguageDef.rewrites,
        TptpFofSkolemizationLanguageDef.matrixRewrites,
        TptpFofSkolemizationLanguageDef.formRewrites,
        TptpFofSkolemizationLanguageDef.mkRule,
        TptpFofSkolemizationLanguageDef.typed,
        TptpFofSkolemizationLanguageDef.congruence,
        TptpFofSkolemizationLanguageDef.a,
        TptpFofSkolemizationLanguageDef.v,
        TptpFofSkolemTermLanguageDef.rewrites,
        TptpFofSkolemTermLanguageDef.mkRule,
        TptpFofSkolemTermLanguageDef.typed,
        TptpFofSkolemTermLanguageDef.congruence,
        TptpFofSkolemTermLanguageDef.a,
        TptpFofSkolemTermLanguageDef.v,
        TptpFofSkolemTermLanguageDef.indexZero,
        TptpFofSkolemTermLanguageDef.indexSucc,
        TptpFofSkolemTermLanguageDef.sourceTermVariable,
        TptpFofSkolemTermLanguageDef.sourceTermFunction,
        TptpFofSkolemTermLanguageDef.sourceTermsNil,
        TptpFofSkolemTermLanguageDef.sourceTermsCons,
        TptpFofSkolemTermLanguageDef.translateTermsConsRule,
        TptpFofSkolemTermLanguageDef.targetTermVariable,
        TptpFofSkolemTermLanguageDef.targetTermOriginal,
        TptpFofSkolemTermLanguageDef.targetTermGenerated,
        TptpFofSkolemTermLanguageDef.targetTermsNil,
        TptpFofSkolemTermLanguageDef.targetTermsCons,
        TptpFofSkolemTermLanguageDef.envNil,
        TptpFofSkolemTermLanguageDef.envCons,
        TptpFofSkolemTermLanguageDef.termShiftRequest,
        TptpFofSkolemTermLanguageDef.termShiftResult,
        TptpFofSkolemTermLanguageDef.termsShiftRequest,
        TptpFofSkolemTermLanguageDef.termsShiftResult,
        TptpFofSkolemTermLanguageDef.envShiftRequest,
        TptpFofSkolemTermLanguageDef.envShiftResult,
        TptpFofSkolemTermLanguageDef.variablesRequest,
        TptpFofSkolemTermLanguageDef.variablesResult,
        TptpFofSkolemTermLanguageDef.lookupRequest,
        TptpFofSkolemTermLanguageDef.lookupResult,
        TptpFofSkolemTermLanguageDef.translateTermRequest,
        TptpFofSkolemTermLanguageDef.translateTermResult,
        TptpFofSkolemTermLanguageDef.translateTermsRequest,
        TptpFofSkolemTermLanguageDef.translateTermsResult,
        TptpFofSkolemizationLanguageDef.matrixRequest,
        TptpFofSkolemizationLanguageDef.matrixResult,
        TptpFofSkolemizationLanguageDef.formRequest,
        TptpFofSkolemizationLanguageDef.formResult,
        TptpFofPrenexLanguageDef.matrixVerum,
        TptpFofPrenexLanguageDef.matrixFalsum,
        TptpFofPrenexLanguageDef.matrixPositive,
        TptpFofPrenexLanguageDef.matrixNegative,
        TptpFofPrenexLanguageDef.matrixEqual,
        TptpFofPrenexLanguageDef.matrixNotEqual,
        TptpFofPrenexLanguageDef.matrixAnd,
        TptpFofPrenexLanguageDef.matrixOr,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.all,
        TptpFofPrenexLanguageDef.ex,
        TptpFofPrenexLanguageDef.a,
        TptpFofSkolemLanguageDef.verum,
        TptpFofSkolemLanguageDef.falsum,
        TptpFofSkolemLanguageDef.positive,
        TptpFofSkolemLanguageDef.negative,
        TptpFofSkolemLanguageDef.equal,
        TptpFofSkolemLanguageDef.notEqual,
        TptpFofSkolemLanguageDef.and,
        TptpFofSkolemLanguageDef.or,
        TptpFofSkolemLanguageDef.all,
        TptpFofSkolemLanguageDef.introducedSymbol,
        TptpFofSkolemLanguageDef.introducedNil,
        TptpFofSkolemLanguageDef.introducedCons,
        TptpFofSkolemLanguageDef.a,
        LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames,
        LanguageDef.premiseFvarNames,
        LanguageDef.premisePatterns,
        LanguageDef.premiseForAllParams,
        Pattern.freeFvarNames] <;> aesop
  exact bne_iff_ne.mp
    (List.all_eq_true.mp checked name (by
      rw [indexEquality]
      exact nameMembership))

private def generatedExtendsFor (rewrite : RewriteRule)
    (membership : rewrite ∈ source.language.rewrites) :
    ExtendsFor source.language generatedDefinition.toLanguageDef rewrite where
  addedTypes := generatedTypeRows.map TypeDecl.name
  addedSignatures := generatedTermRows.map (fun declaration =>
    (declaration.label, declaration.params.length))
  addedLabels := generatedTermRows.map (fun declaration => declaration.label)
  typeNames := generatedDefinition_typeNames
  signatures := generatedDefinition_constructorSignatures
  labels := generatedDefinition_constructorLabels
  avoidsSchema := by
    intro name schemaMembership generatedMembership
    exact sourceSchemaNames_public rewrite membership name schemaMembership
      (generatedConstructorLabels_private name generatedMembership)

private theorem generatedDefinition_rewrites_validate :
    ∀ rewrite ∈ generatedDefinition.rewrites,
      LanguageDef.validateRewrite generatedDefinition.toLanguageDef rewrite =
        [] := by
  intro rewrite membership
  rw [generatedDefinition_rewrites] at membership
  exact validateRewrite_eq_nil generatedDefinition_termLabels_nodup
    (Certificate.extend
      (TptpFofSkolemizationLanguageDef.transition_certificate
        rewrite membership)
      (generatedExtendsFor rewrite membership))

set_option maxHeartbeats 800000 in
/-- The enlarged source-plus-generated object signature passes the ordinary
LanguageDef validator. -/
theorem generatedLanguage_validate :
    generatedDefinition.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · rw [generatedDefinition_equations]
    rfl
  all_goals try decide +kernel
  exact generatedDefinition_rewrites_validate

/-- Every source-indexed formation and introduction row is locally valid by
the shared generator-family theorem. -/
theorem generatedOccurrenceRules_locallyValid :
    (SelectedNativeTypeSourceIndexedIntroduction.profiledRules demand).all
      RuleSchema.isLocallyValid = true :=
  SelectedNativeTypeSourceIndexedIntroduction.profiledRules_locallyValid
    demand occurrenceAdmission

/-- Generated judgment heads are pairwise distinct. -/
theorem generatedJudgmentHeads_nodup :
    (generatedDefinition.judgments.map JudgmentDecl.head).Nodup := by
  decide +kernel

/-- Generated rule identifiers are nonempty and pairwise distinct. -/
theorem generatedRuleIds_nodup : generatedDefinition.ruleIds.Nodup := by
  decide +kernel

/-- The generated judgment namespace is admitted by the ordinary checker. -/
theorem generatedJudgmentSignature_valid :
    generatedDefinition.judgmentSignatureValid = true := by
  decide +kernel

/-- The selected fragment declares no conversion authority. -/
theorem generatedConversionDeclaration_valid :
    generatedDefinition.conversionDeclarationValid = true := by
  rfl

/-- Complete source-indexed Skolemization NTT admission.  Rule validity is
assembled from generator-family theorems rather than by normalizing the
finished rule array. -/
theorem generatedDefinition_valid : generatedDefinition.isValid = true := by
  exact SelectedNativeTypeSourceIndexedValidation.definition_isValid demand
    supportSeparated generatedLanguage_validate generatedJudgmentHeads_nodup
    generatedRuleIds_nodup generatedJudgmentSignature_valid
    generatedConversionDeclaration_valid occurrenceAdmission
    targetOccurrenceAdmission

/-- Proof-carrying flat typed Skolemization GSLT. -/
def generated : ValidatedCalculusLanguageDef :=
  ⟨generatedDefinition, generatedDefinition_valid⟩

set_option maxHeartbeats 800000 in
theorem generatedRows_disjoint :
    (SelectedNativeTypeSourceIndexedCalculus.extension demand
      supportSeparated).disjointFrom
        (SourcePreservingCalculusCoproduct.sourceBase source) = true := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem generatedRows_newJudgmentsOnly :
    (SelectedNativeTypeSourceIndexedCalculus.extension demand
      supportSeparated).policyHolds
        (SourcePreservingCalculusCoproduct.sourceBase source)
        .newJudgmentsOnly = true := by
  decide +kernel

/-- Complete checked attachment boundary for the generated calculus. -/
def compatibility : SelectedNativeTypeSourceIndexedCalculus.Compatibility
    demand supportSeparated where
  disjoint := generatedRows_disjoint
  policy := generatedRows_newJudgmentsOnly
  valid := generatedDefinition_valid

/-- The authored source embeds literally into the generated typed result. -/
def sourceInclusion : StructuralMorphism source
    generated.toValidatedLanguageDef :=
  compatibility.sourceInclusion

set_option maxHeartbeats 800000 in
/-- The complete source-plus-generated object language belongs to the
canonical LanguageDef wire fragment. -/
theorem generatedLanguage_supported :
    CanonicalWire.languageSupported generatedDefinition.toLanguageDef := by
  decide +kernel

theorem generatedLanguageWire_isSome :
    (CanonicalWire.renderLanguage?
      generatedDefinition.toLanguageDef).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact generatedLanguage_supported

/-- Canonical object-language wire: types, constructors, equations, and the
literal authored operational rewrites. -/
def generatedLanguageWire : String :=
  (CanonicalWire.renderLanguage?
    generatedDefinition.toLanguageDef).getD ""

/-- Checker-facing calculus wire derived from the same validated flat
definition. -/
def generatedInferenceWire : String :=
  InferenceMeTTaRender.renderDefinition generatedDefinition ++ "\n"

/-! ## Revision-bound checked source package -/

/-- SHA-256 of the complete generated object-language wire.  Lean retains the
pin as source identity; the artifact-boundary checker independently recomputes
the digest before admitting the paired object and inference projections. -/
def generatedObjectLanguageSha256 : String :=
  "5e05cc091a360fe69e1f168a0cd3ed533240c7914398626bdbd2ab3b0c3b27f5"

/-- Exact revision identity for the separately compiled generated calculus. -/
def generatedSourceIdentity : CheckedSource.SourceIdentity where
  systemId := "tptp-fof-skolemization-ntt"
  revision := "v1"
  artifactDigest := "sha256:" ++ generatedObjectLanguageSha256

/-- The source-indexed selected-native-type profile carried by this package. -/
def generatedSourceProfile : CheckedSource.SourceProfile where
  name := "source-indexed-selected-native-types"
  version := "v1"
  payload := .apply "tptp-fof-skolemization-ntt:complete-root-profile" []

/-- One revisioned package retaining the exact generated definition whose
object projection is named by `generatedSourceIdentity`. -/
def generatedSource : CheckedSource.GSLTSource where
  identity := generatedSourceIdentity
  assumptions := ⟨[]⟩
  profiles := ⟨[generatedSourceProfile]⟩
  definition := generatedDefinition

theorem generatedSource_identity_valid :
    generatedSource.identity.isValid = true := by
  rfl

theorem generatedSource_assumptions_valid :
    generatedSource.assumptions.isValid = true := by
  rfl

theorem generatedSource_profiles_valid :
    generatedSource.profiles.isValid = true := by
  rfl

/-- The revisioned package passes the generic checked-source admission using
the already established generated-calculus validity theorem. -/
theorem generatedSource_isValid : generatedSource.isValid = true := by
  unfold CheckedSource.GSLTSource.isValid
  rw [generatedSource_identity_valid, generatedSource_assumptions_valid,
    generatedSource_profiles_valid]
  exact generatedDefinition_valid

def generatedCheckedSource : CheckedSource.CheckedGSLT where
  source := generatedSource
  identityValid := generatedSource_identity_valid
  assumptionsValid := generatedSource_assumptions_valid
  profilesValid := generatedSource_profiles_valid
  definitionValid := generatedDefinition_valid

/-- Physical source package: revision identity and the exact inference
definition in one CeTTa carrier. -/
def generatedSourceWire : String :=
  InferenceMeTTaRender.renderGSLTSource generatedSource ++ "\n"

theorem generatedCheckedSource_definition_exact :
    generatedCheckedSource.definition = generated := by
  rfl

/-- The physical CeTTa inference carrier decodes to the exact checker-facing
projection of the generated flat calculus. -/
theorem generatedInferenceEncoding_roundTrip :
    InferenceCettaWire.decodeRuntimeInferenceLanguage
        (InferenceCettaWire.encodeDefinition generatedDefinition) =
      some (InferenceLanguageWire.RuntimeInferenceLanguage.ofDefinition
        generatedDefinition) := by
  exact InferenceCettaWire.decodeRuntimeInferenceLanguage_encodeDefinition _

#print axioms typingAt_eq_rootTyping
#print axioms occurrenceAdmission
#print axioms supportSeparated
#print axioms generatedDefinition_rewrites
#print axioms generatedLanguage_validate
#print axioms generatedDefinition_valid
#print axioms sourceInclusion
#print axioms generatedLanguage_supported
#print axioms generatedLanguageWire_isSome
#print axioms generatedInferenceEncoding_roundTrip
#print axioms generatedSource_isValid
#print axioms generatedCheckedSource_definition_exact

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNTT
