import Mettapedia.Languages.Megalodon.DefinitionConversionKernel
import Mettapedia.Languages.Megalodon.SortedABTRefinement

/-!
# Megalodon eta-conversion kernel

This module connects the beta-delta-eta definition kernel's single eta rule to
the two-sorted ABT `dropAt?` operation.  Successful binder removal is compiled
to the existing proof-relevant shift judgment: lifting the proposed reduct by
one must reconstruct the function beneath the lambda.  The forbidden
variable-at-cutoff case therefore has no witness.

Reusing shift keeps eta conversion independently replayable without adding a
second recursive term relation or granting normalization/search primitive
authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.EtaConversionKernel

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Megalodon
open Mettapedia.OSLF.MeTTaIL.Syntax

attribute [local simp]
  DefinitionConversionKernel.rule DefinitionConversionKernel.ruleId
  DefinitionConversionKernel.a DefinitionConversionKernel.m
  DefinitionConversionKernel.projectSignature
  DefinitionConversionKernel.reduces
  DefinitionConversionKernel.reductionPath
  DefinitionConversionKernel.scopedTerm DefinitionConversionKernel.converts
  DefinitionConversionKernel.baseProves DefinitionConversionKernel.fullProves
  DefinitionConversionKernel.reduceAppArgumentRule
  DefinitionConversionKernel.reduceImpCodomainRule
  DefinitionConversionKernel.pathReflRule
  DefinitionConversionKernel.pathStepRule
  DefinitionConversionKernel.conversionCommonRule
  DefinitionConversionKernel.fullProofRule
  DefinitionConversionKernel.compileProjection_checked
  Pattern.isGroundAt Pattern.isGroundListAt
  Pattern.hasCanonicalBinderMetadata
  Pattern.hasCanonicalBinderMetadataList

private def a (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def m (name : String) : Pattern := .fvar name

private def ruleId (value : String) : RuleId := ⟨value⟩

private def rule (id : String) (metavariables : List String)
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := metavariables.map fun name => (name, 0)
    premises
    conclusion }

private def reduces (declarations source target : Pattern) : Pattern :=
  a "MDefinitionReduces" [declarations, source, target]

private def projectSignature
    (declarations signature : Pattern) : Pattern :=
  a "MProjectSignature" [declarations, signature]

private def reductionPath
    (declarations source target : Pattern) : Pattern :=
  a "MDefinitionReductionPath" [declarations, source, target]

private def scopedTerm (declarations term : Pattern) : Pattern :=
  a "MScopedTerm" [declarations, term]

private def converts (declarations left right : Pattern) : Pattern :=
  a "MDefinitionConverts"
    [scopedTerm declarations left, scopedTerm declarations right]

private def baseProves
    (environment typeDepth termContext proofContext proposition : Pattern) :
    Pattern :=
  a "MMathdataProves"
    [environment, typeDepth, termContext, proofContext, proposition]

private def fullProves
    (environment typeDepth termContext proofContext proposition : Pattern) :
    Pattern :=
  a "MDefinitionProves"
    [environment, typeDepth, termContext, proofContext, proposition]

private def shiftTerm
    (amount cutoff source target : Pattern) : Pattern :=
  a "MShiftTerm" [amount, cutoff, source, target]

private def zero : Pattern := a "MNZero"
private def succ (value : Pattern) : Pattern := a "MNSucc" [value]
private def termVariable (index : Pattern) : Pattern := a "MTmVar" [index]

/-! ## Eta reduction -/

private def reduceEtaRule : RuleSchema :=
  rule "megalodon-def-reduce-eta"
    ["declarations", "type", "function", "result"]
    [shiftTerm (succ zero) zero (m "result") (m "function")]
    (reduces (m "declarations")
      (a "MTmLam"
        [m "type", a "MTmApp" [m "function", termVariable zero]])
      (m "result"))

def definition : CalculusLanguageDef :=
  DefinitionConversionKernel.definition

def presentation : Presentation := definition.toNested

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem presentation_valid : presentation.isValidV2 = true := by
  exact DefinitionConversionKernel.presentation_valid

def validated : ValidatedPresentation := ⟨presentation, presentation_valid⟩

def coGSLTDefinition : ExtendedLanguageDef calculusLayer :=
  definition.toExtended

def coGSLTSource : coGSLTDefinition.authoredGSLT.Term :=
  coGSLTDefinition.authoredSource

@[simp] theorem coGSLT_source_elaborates :
    calculusLayer.elaborate definition.toLanguageDef coGSLTSource =
      some definition.toCalculus :=
  definition.toExtended_elaborate_authoredSource

theorem definition_ruleLookupRefines :
    RuleLookupRefines DefinitionConversionKernel.validated validated := by
  exact RuleLookupRefines.refl DefinitionConversionKernel.validated

@[simp] private theorem lookup_reduceEtaRule :
    presentation.lookupRule? (ruleId "megalodon-def-reduce-eta") =
      some reduceEtaRule := by
  rfl

@[simp] private theorem lookup_typeNamedZeroRule :
    presentation.lookupRule?
        (ruleId "megalodon-poly-term-named-zero") =
      some PolymorphicKernel.typeNamedZeroRule := by
  rfl

@[simp] private theorem lookup_typeNamedSuccRule :
    presentation.lookupRule?
        (ruleId "megalodon-poly-term-named-succ") =
      some PolymorphicKernel.typeNamedSuccRule := by
  rfl

@[simp] private theorem lookup_typeAppRule :
    presentation.lookupRule? (ruleId "megalodon-poly-term-app") =
      some PolymorphicKernel.typeAppRule := by
  rfl

@[simp] private theorem lookup_proofHypZeroRule :
    presentation.lookupRule? (ruleId "megalodon-poly-proof-hyp-zero") =
      some PolymorphicKernel.proofHypZeroRule := by
  rfl

@[simp] private theorem lookup_proofImpIntroRule :
    presentation.lookupRule? (ruleId "megalodon-poly-proof-imp-intro") =
      some PolymorphicKernel.proofImpIntroRule := by
  rfl

@[simp] private theorem lookup_environmentProofBaseRule :
    presentation.lookupRule? (ruleId "megalodon-env-proof-base") =
      some EnvironmentKernel.proofBaseRule := by
  rfl

@[simp] private theorem lookup_reduceAppArgumentRule :
    presentation.lookupRule?
        (ruleId "megalodon-def-reduce-app-argument") =
      some DefinitionConversionKernel.reduceAppArgumentRule := by
  rfl

@[simp] private theorem lookup_reduceImpCodomainRule :
    presentation.lookupRule?
        (ruleId "megalodon-def-reduce-imp-codomain") =
      some DefinitionConversionKernel.reduceImpCodomainRule := by
  rfl

@[simp] private theorem lookup_pathReflRule :
    presentation.lookupRule? (ruleId "megalodon-def-path-refl") =
      some DefinitionConversionKernel.pathReflRule := by
  rfl

@[simp] private theorem lookup_pathStepRule :
    presentation.lookupRule? (ruleId "megalodon-def-path-step") =
      some DefinitionConversionKernel.pathStepRule := by
  rfl

@[simp] private theorem lookup_conversionCommonRule :
    presentation.lookupRule?
        (ruleId "megalodon-def-conversion-common") =
      some DefinitionConversionKernel.conversionCommonRule := by
  rfl

@[simp] private theorem lookup_fullProofRule :
    presentation.lookupRule? (ruleId "megalodon-def-proof") =
      some DefinitionConversionKernel.fullProofRule := by
  rfl

private def node (id : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

private abbrev ENat := TermQuantifiedKernel.encodeNat
private abbrev ETp := TermQuantifiedKernel.encodeTp
private abbrev ETm := TermQuantifiedKernel.encodeTm

/-- Compile a successful Mathdata unused-binder removal into the inherited
shift witness and the single eta-reduction node. -/
def compileEtaReduction (declarations : Pattern) (type : MathdataKernel.Tp)
    (function result : MathdataKernel.Tm)
    (_ : MathdataKernel.Tm.dropAt? 0 function = some result) : RawProof :=
  node "megalodon-def-reduce-eta"
    [declarations, ETp type, ETm function, ETm result]
    [(EnvironmentKernel.compileTermShift 1 0 result).2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- The eta compiler is sound: Mathdata unused-binder evidence is converted
to an accepted coGSLT shift premise, and hence to one authenticated reduction
step with the identical endpoints. -/
theorem compileEtaReduction_checked
    (declarations : Pattern) (type : MathdataKernel.Tp)
    (function result : MathdataKernel.Tm)
    (drop : MathdataKernel.Tm.dropAt? 0 function = some result)
    (declarationsGround : declarations.isGroundAt 0 = true)
    (declarationsCanonical :
      declarations.hasCanonicalBinderMetadata = true) :
    checkRaw validated
      (reduces declarations
        (ETm (.lam type (.app function (.db 0)))) (ETm result))
      (compileEtaReduction declarations type function result drop) = true := by
  have shiftResult : MathdataKernel.Tm.shift 0 1 result = function :=
    SortedABTRefinement.shift_of_dropAt?_eq_some 0 drop
  have compiledResult :
      (EnvironmentKernel.compileTermShift 1 0 result).1 = function := by
    rw [EnvironmentKernel.compileTermShift_result]
    exact shiftResult
  have childBase := EnvironmentKernel.compileTermShift_checked 1 0 result
  have child := checkRaw_true_of_ruleLookupRefines
    DefinitionConversionKernel.environment_ruleLookupRefines childBase
  have childLocal := checkRaw_true_of_ruleLookupRefines
    definition_ruleLookupRefines child
  simp only [compileEtaReduction, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_reduceEtaRule]
  simp [reduceEtaRule, rule, ruleId, shiftTerm, reduces, zero, succ,
    termVariable, a, m, argumentsValidAt, argumentValidAt,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, lookupArgumentAt?, RuleSchema.sideConditionsHold,
    checkRawChildren, declarationsGround, declarationsCanonical,
    TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a]
  simpa [validated, DefinitionConversionKernel.validated,
    DefinitionConversionKernel.presentation,
    EnvironmentKernel.validated, TermQuantifiedKernel.shiftTerm,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.encodeTp,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a,
    compiledResult] using childLocal

/-! ## Positive and negative eta canaries -/

def etaParameterName : String :=
  "0000000000000000000000000000000000000000000000000000000000000041"

private def etaDeclarations : Pattern :=
  DefinitionConversionKernel.encodeTermDeclarations
    [{ name := etaParameterName, type := .arr (.base 0) .prop,
       definition := none }]

private def etaFunction : MathdataKernel.Tm := .named etaParameterName

theorem eta_named_drop :
    MathdataKernel.Tm.dropAt? 0 etaFunction = some etaFunction := by
  rfl

/-- Positive: the coGSLT authority accepts the same named-function eta step
used by the real Megalodon source canary. -/
theorem eta_named_reduction_accepted :
    checkRaw validated
      (reduces etaDeclarations
        (ETm (.lam (.base 0) (.app etaFunction (.db 0))))
        (ETm etaFunction))
      (compileEtaReduction etaDeclarations (.base 0)
        etaFunction etaFunction eta_named_drop) = true := by
  apply compileEtaReduction_checked
  · exact DefinitionConversionKernel.encodeTermDeclarations_ground _
  · exact DefinitionConversionKernel.encodeTermDeclarations_canonical _

/-- Negative: eta cannot contract when the candidate function itself uses
the binder at cutoff zero. -/
theorem eta_bound_function_drop_rejects :
    MathdataKernel.Tm.dropAt? 0 (.db 0) = none := by
  rfl

/-! ## Exact real-Megalodon eta document -/

def etaPredicateName : String :=
  "0000000000000000000000000000000000000000000000000000000000000042"

def etaFunctionType : MathdataKernel.Tp :=
  .arr (.base 0) .prop

def etaPredicateType : MathdataKernel.Tp :=
  .arr etaFunctionType .prop

def etaFunctionDeclaration : MathdataKernel.TermDecl :=
  { name := etaParameterName, type := etaFunctionType }

def etaPredicateDeclaration : MathdataKernel.TermDecl :=
  { name := etaPredicateName, type := etaPredicateType }

/-- Megalodon prepends declarations to its environment, so the second source
parameter is the first signature entry. -/
def etaTermDeclarations : List MathdataKernel.TermDecl :=
  [etaPredicateDeclaration, etaFunctionDeclaration]

def etaEnvironment : MathdataKernel.Environment :=
  { terms := etaTermDeclarations }

def etaFunctionTerm : MathdataKernel.Tm :=
  .named etaParameterName

def etaPredicateTerm : MathdataKernel.Tm :=
  .named etaPredicateName

def etaDomain : MathdataKernel.Tm :=
  .app etaPredicateTerm etaFunctionTerm

def etaExpansion : MathdataKernel.Tm :=
  .lam (.base 0) (.app etaFunctionTerm (.db 0))

def etaCodomain : MathdataKernel.Tm :=
  .app etaPredicateTerm etaExpansion

def etaDeclaredProposition : MathdataKernel.Tm :=
  .imp etaDomain etaCodomain

def etaSynthesizedProposition : MathdataKernel.Tm :=
  .imp etaDomain etaDomain

def etaProof : MathdataKernel.Pf :=
  .proofLam etaDomain (.hyp 0)

/-- The direct Mathdata kernel accepts the proposition and proof emitted by
the real `-sexprinfo` eta specimen. -/
theorem mathdata_accepts_eta_document :
    MathdataKernel.checkProof etaEnvironment 32 0 [] []
      etaProof etaDeclaredProposition = true := by
  simp [MathdataKernel.checkProof, MathdataKernel.checkNormalizedProof,
    MathdataKernel.inferProof, etaEnvironment, etaProof,
    etaDeclaredProposition, etaCodomain,
    etaExpansion, etaDomain, etaPredicateTerm, etaFunctionTerm,
    etaTermDeclarations, etaPredicateDeclaration, etaFunctionDeclaration,
    etaPredicateType, etaFunctionType, etaPredicateName, etaParameterName,
    MathdataKernel.checkProposition, MathdataKernel.inferTerm,
    MathdataKernel.normalize, MathdataKernel.deltaNormalize,
    MathdataKernel.Tm.normalize, MathdataKernel.Tm.normalizeOne,
    MathdataKernel.Environment.lookupTerm?, MathdataKernel.lookupTermList?,
    MathdataKernel.Tm.dropAt?]

private abbrev ESig := TermQuantifiedKernel.encodeSignature
private abbrev ETyCtx := TermQuantifiedKernel.encodeTypeContext
private abbrev EPfCtx := TermQuantifiedKernel.encodeProofContext

private def etaEncodedDeclarations : Pattern :=
  DefinitionConversionKernel.encodeTermDeclarations etaTermDeclarations

@[simp] private theorem etaEncodedDeclarations_ground :
    etaEncodedDeclarations.isGroundAt 0 = true := by
  exact DefinitionConversionKernel.encodeTermDeclarations_ground _

@[simp] private theorem etaEncodedDeclarations_canonical :
    etaEncodedDeclarations.hasCanonicalBinderMetadata = true := by
  exact DefinitionConversionKernel.encodeTermDeclarations_canonical _

private def etaFunctionTailTypeArticle : RawProof :=
  node "megalodon-poly-term-named-zero"
    [ a etaParameterName, ETp etaFunctionType, ESig [], ENat 0, ETyCtx [] ]

private def etaFunctionTypeArticle : RawProof :=
  node "megalodon-poly-term-named-succ"
    [ a etaPredicateName, ETp etaPredicateType,
      ESig [etaFunctionDeclaration], ENat 0, ETyCtx [],
      a etaParameterName, ETp etaFunctionType ]
    [etaFunctionTailTypeArticle]

private def etaPredicateTypeArticle : RawProof :=
  node "megalodon-poly-term-named-zero"
    [ a etaPredicateName, ETp etaPredicateType,
      ESig [etaFunctionDeclaration], ENat 0, ETyCtx [] ]

private def etaDomainTypeArticle : RawProof :=
  node "megalodon-poly-term-app"
    [ ESig etaTermDeclarations, ENat 0, ETyCtx [],
      ETm etaPredicateTerm, ETm etaFunctionTerm,
      ETp etaFunctionType, ETp .prop ]
    [etaPredicateTypeArticle, etaFunctionTypeArticle]

private def etaHypothesisArticle : RawProof :=
  node "megalodon-poly-proof-hyp-zero"
    [ ESig etaTermDeclarations, ENat 0, ETyCtx [], EPfCtx [],
      ETm etaDomain ]
    [etaDomainTypeArticle]

private def etaBaseProofArticle : RawProof :=
  node "megalodon-poly-proof-imp-intro"
    [ ESig etaTermDeclarations, ENat 0, ETyCtx [], EPfCtx [],
      ETm etaDomain, ETm etaDomain ]
    [etaDomainTypeArticle, etaHypothesisArticle]

@[simp] private theorem eta_base_proof_article_accepted :
    checkRaw validated
      (PolymorphicKernel.proves (ESig etaTermDeclarations) (ENat 0)
        (ETyCtx []) (EPfCtx []) (ETm etaSynthesizedProposition))
      etaBaseProofArticle = true := by
  simp (config := { maxSteps := 1000000, decide := true })
    [ etaBaseProofArticle, etaHypothesisArticle, etaDomainTypeArticle,
      etaPredicateTypeArticle, etaFunctionTypeArticle,
      etaFunctionTailTypeArticle, node, checkRaw, checkRawChildren,
      validated, instantiateRule?, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
      PolymorphicKernel.proofImpIntroRule,
      PolymorphicKernel.proofHypZeroRule, PolymorphicKernel.typeAppRule,
      PolymorphicKernel.typeNamedZeroRule,
      PolymorphicKernel.typeNamedSuccRule, PolymorphicKernel.rule,
      PolymorphicKernel.ruleId, PolymorphicKernel.hasType,
      PolymorphicKernel.proves, PolymorphicKernel.a, PolymorphicKernel.m,
      TermQuantifiedKernel.encodeSignature,
      TermQuantifiedKernel.encodeTypeContext,
      TermQuantifiedKernel.encodeProofContext,
      TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
      TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
      etaSynthesizedProposition, etaDomain, etaPredicateTerm,
      etaFunctionTerm, etaTermDeclarations, etaPredicateDeclaration,
      etaFunctionDeclaration, etaPredicateType, etaFunctionType,
      etaPredicateName, etaParameterName, a ]

private def etaEnvironmentArticle : RawProof :=
  node "megalodon-env-proof-base"
    [ EnvironmentKernel.encodePrimitiveTypes [], ESig etaTermDeclarations,
      EnvironmentKernel.encodeKnown [], ENat 0, ETyCtx [], EPfCtx [],
      ETm etaSynthesizedProposition ]
    [etaBaseProofArticle]

@[simp] private theorem eta_environment_article_accepted :
    checkRaw validated
      (baseProves
        (a "MEnvironment"
          [ EnvironmentKernel.encodePrimitiveTypes [],
            ESig etaTermDeclarations, EnvironmentKernel.encodeKnown [] ])
        (ENat 0) (ETyCtx []) (EPfCtx [])
        (ETm etaSynthesizedProposition))
      etaEnvironmentArticle = true := by
  simp only [etaEnvironmentArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_environmentProofBaseRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, EnvironmentKernel.proofBaseRule,
    EnvironmentKernel.rule, EnvironmentKernel.ruleId,
    EnvironmentKernel.baseProves, EnvironmentKernel.proves,
    EnvironmentKernel.a, EnvironmentKernel.m, baseProves, a,
    EnvironmentKernel.encodePrimitiveTypes, EnvironmentKernel.encodeKnown,
    TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext,
    TermQuantifiedKernel.a, checkRawChildren,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  simpa [validated, PolymorphicKernel.proves, PolymorphicKernel.a,
    TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext, TermQuantifiedKernel.a] using
    eta_base_proof_article_accepted

private def etaReductionArticle : RawProof :=
  compileEtaReduction etaEncodedDeclarations (.base 0)
    etaFunctionTerm etaFunctionTerm eta_named_drop

@[simp] private theorem eta_reduction_article_accepted :
    checkRaw validated
      (reduces etaEncodedDeclarations (ETm etaExpansion)
        (ETm etaFunctionTerm))
      etaReductionArticle = true := by
  simpa [etaReductionArticle, etaExpansion, etaFunctionTerm,
    etaPredicateName, etaParameterName] using
    compileEtaReduction_checked etaEncodedDeclarations (.base 0)
      etaFunctionTerm etaFunctionTerm eta_named_drop
      (DefinitionConversionKernel.encodeTermDeclarations_ground _)
      (DefinitionConversionKernel.encodeTermDeclarations_canonical _)

private def etaApplicationReductionArticle : RawProof :=
  node "megalodon-def-reduce-app-argument"
    [ etaEncodedDeclarations, ETm etaPredicateTerm, ETm etaExpansion,
      ETm etaFunctionTerm ]
    [etaReductionArticle]

@[simp] private theorem eta_application_reduction_article_accepted :
    checkRaw validated
      (reduces etaEncodedDeclarations (ETm etaCodomain) (ETm etaDomain))
      etaApplicationReductionArticle = true := by
  simp only [etaApplicationReductionArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_reduceAppArgumentRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, DefinitionConversionKernel.reduceAppArgumentRule,
    reduces, etaCodomain, etaDomain, etaExpansion,
    etaPredicateTerm, etaFunctionTerm, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.encodeTp, TermQuantifiedKernel.encodeNat,
    TermQuantifiedKernel.a, checkRawChildren, a,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  simpa [validated, reduces, etaExpansion, etaFunctionTerm,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.encodeTp,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a, a] using
    eta_reduction_article_accepted

private def etaPropositionReductionArticle : RawProof :=
  node "megalodon-def-reduce-imp-codomain"
    [ etaEncodedDeclarations, ETm etaDomain, ETm etaCodomain,
      ETm etaDomain ]
    [etaApplicationReductionArticle]

@[simp] private theorem eta_proposition_reduction_article_accepted :
    checkRaw validated
      (reduces etaEncodedDeclarations (ETm etaDeclaredProposition)
        (ETm etaSynthesizedProposition))
      etaPropositionReductionArticle = true := by
  simp only [etaPropositionReductionArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_reduceImpCodomainRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, DefinitionConversionKernel.reduceImpCodomainRule,
    reduces, etaDeclaredProposition,
    etaSynthesizedProposition, checkRawChildren, a]
  simpa [validated, reduces, etaCodomain, etaDomain,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a, a] using
    eta_application_reduction_article_accepted

private def etaPathReflArticle : RawProof :=
  node "megalodon-def-path-refl"
    [etaEncodedDeclarations, ETm etaSynthesizedProposition]

@[simp] private theorem eta_path_refl_article_accepted :
    checkRaw validated
      (reductionPath etaEncodedDeclarations
        (ETm etaSynthesizedProposition) (ETm etaSynthesizedProposition))
      etaPathReflArticle = true := by
  simp only [etaPathReflArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_pathReflRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, DefinitionConversionKernel.pathReflRule,
    reductionPath, checkRawChildren, a]

private def etaDeclaredPathArticle : RawProof :=
  node "megalodon-def-path-step"
    [ etaEncodedDeclarations, ETm etaDeclaredProposition,
      ETm etaSynthesizedProposition, ETm etaSynthesizedProposition ]
    [etaPropositionReductionArticle, etaPathReflArticle]

@[simp] private theorem eta_declared_path_article_accepted :
    checkRaw validated
      (reductionPath etaEncodedDeclarations (ETm etaDeclaredProposition)
        (ETm etaSynthesizedProposition))
      etaDeclaredPathArticle = true := by
  simp only [etaDeclaredPathArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_pathStepRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, DefinitionConversionKernel.pathStepRule,
    reductionPath, checkRawChildren, a]
  constructor
  · simpa [validated, reduces, a] using
      eta_proposition_reduction_article_accepted
  · simpa [validated, reductionPath, a] using
      eta_path_refl_article_accepted

private def etaSynthesizedPathArticle : RawProof :=
  etaPathReflArticle

@[simp] private theorem eta_synthesized_path_article_accepted :
    checkRaw validated
      (reductionPath etaEncodedDeclarations
        (ETm etaSynthesizedProposition) (ETm etaSynthesizedProposition))
      etaSynthesizedPathArticle = true := by
  exact eta_path_refl_article_accepted

private def etaConversionArticle : RawProof :=
  node "megalodon-def-conversion-common"
    [ etaEncodedDeclarations, ETm etaSynthesizedProposition,
      ETm etaDeclaredProposition, ETm etaSynthesizedProposition ]
    [etaSynthesizedPathArticle, etaDeclaredPathArticle]

@[simp] private theorem eta_conversion_article_accepted :
    checkRaw validated
      (converts etaEncodedDeclarations (ETm etaSynthesizedProposition)
        (ETm etaDeclaredProposition))
      etaConversionArticle = true := by
  simp only [etaConversionArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_conversionCommonRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, DefinitionConversionKernel.conversionCommonRule,
    converts, scopedTerm,
    checkRawChildren, a]
  constructor
  · simpa [validated, reductionPath, a] using
      eta_synthesized_path_article_accepted
  · simpa [validated, reductionPath, a] using
      eta_declared_path_article_accepted

private def etaFullEnvironment : Pattern :=
  a "MFullEnvironment"
    [ EnvironmentKernel.encodePrimitiveTypes [], etaEncodedDeclarations,
      EnvironmentKernel.encodeKnown [] ]

def etaDocumentGoal : Pattern :=
  fullProves etaFullEnvironment (ENat 0) (ETyCtx []) (EPfCtx [])
    (ETm etaDeclaredProposition)

def etaDocumentArticle : RawProof :=
  node "megalodon-def-proof"
    [ EnvironmentKernel.encodePrimitiveTypes [], etaEncodedDeclarations,
      ESig etaTermDeclarations, EnvironmentKernel.encodeKnown [],
      ENat 0, ETyCtx [], EPfCtx [], ETm etaSynthesizedProposition,
      ETm etaDeclaredProposition ]
    [ DefinitionConversionKernel.compileProjection etaTermDeclarations,
      etaEnvironmentArticle, etaConversionArticle ]

def etaDocumentWrongGoal : Pattern :=
  fullProves etaFullEnvironment (ENat 0) (ETyCtx []) (EPfCtx [])
    (ETm etaSynthesizedProposition)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The complete proof article reconstructed from real Megalodon output is
accepted by the beta-delta-eta coGSLT authority. -/
theorem eta_document_article_accepted :
    checkRaw validated etaDocumentGoal etaDocumentArticle = true := by
  simp only [etaDocumentArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_fullProofRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, DefinitionConversionKernel.fullProofRule,
    fullProves, etaDocumentGoal, etaFullEnvironment, checkRawChildren, a,
    EnvironmentKernel.encodePrimitiveTypes, EnvironmentKernel.encodeKnown,
    EnvironmentKernel.a,
    TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext, TermQuantifiedKernel.a,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  constructor
  · have projectionAccepted := checkRaw_true_of_ruleLookupRefines
        definition_ruleLookupRefines
        (DefinitionConversionKernel.compileProjection_checked
          etaTermDeclarations)
    simpa [validated, projectSignature, etaEncodedDeclarations,
      DefinitionConversionKernel.validated,
      DefinitionConversionKernel.projectSignature,
      DefinitionConversionKernel.a, a] using projectionAccepted
  · constructor
    · simpa [validated, baseProves, a,
        EnvironmentKernel.encodePrimitiveTypes,
        EnvironmentKernel.encodeKnown, EnvironmentKernel.a,
        TermQuantifiedKernel.encodeTypeContext,
        TermQuantifiedKernel.encodeProofContext,
        TermQuantifiedKernel.a] using eta_environment_article_accepted
    · simpa [validated, converts, scopedTerm, a] using
        eta_conversion_article_accepted

/-- The same article cannot be replayed at its synthesized proposition in
place of the declared eta-convertible proposition. -/
theorem eta_document_wrong_goal_rejected :
    checkRaw validated etaDocumentWrongGoal etaDocumentArticle = false := by
  by_contra hypothesis
  have acceptedWrong :
      checkRaw validated etaDocumentWrongGoal etaDocumentArticle = true := by
    simpa using hypothesis
  have goalsEqual := checkRaw_goal_unique eta_document_article_accepted
    acceptedWrong
  simp [etaDocumentGoal, etaDocumentWrongGoal, etaFullEnvironment,
    fullProves,
    etaDeclaredProposition, etaSynthesizedProposition, etaCodomain,
    etaExpansion, etaDomain, etaPredicateTerm, etaFunctionTerm,
    etaPredicateName, etaParameterName, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.encodeTp, TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext, TermQuantifiedKernel.encodeNat,
    TermQuantifiedKernel.a, a] at goalsEqual

open Mettapedia.GSLT.LanguageDef.InferencePresentationWire

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Every fixed constructor occurrence in the exact eta article is declared
by the checker-facing runtime projection. -/
theorem eta_document_closed_payload :
    (RuntimePresentation.ofPresentation presentation).proofPayloadsValid
        etaDocumentArticle = true := by
  simp (config := { maxSteps := 10000000, decide := true })
    [ RuntimePresentation.ofPresentation,
      RuntimePresentation.proofPayloadsValid,
      RuntimePresentation.proofPayloadListsValid,
      RuntimePresentation.fixedConstructorListsValid,
      RuntimePresentation.fixedConstructorsValid,
      etaDocumentArticle, node,
      DefinitionConversionKernel.compileProjection_nil,
      DefinitionConversionKernel.compileProjection_parameter,
      EnvironmentKernel.compileTermShift_named_article,
      etaEnvironmentArticle, etaBaseProofArticle, etaHypothesisArticle,
      etaDomainTypeArticle, etaPredicateTypeArticle, etaFunctionTypeArticle,
      etaFunctionTailTypeArticle, etaConversionArticle,
      etaSynthesizedPathArticle, etaDeclaredPathArticle,
      etaPathReflArticle, etaPropositionReductionArticle,
      etaApplicationReductionArticle, etaReductionArticle,
      compileEtaReduction, presentation, definition,
      DefinitionConversionKernel.definition,
      DefinitionConversionKernel.additionalConstructors,
      EnvironmentKernel.definition, EnvironmentKernel.additionalConstructors,
      PolymorphicKernel.definition, TermQuantifiedKernel.definition,
      TermQuantifiedKernel.constructors,
      TermQuantifiedKernel.expressionConstructor,
      etaEncodedDeclarations, etaTermDeclarations,
      etaPredicateDeclaration, etaFunctionDeclaration,
      etaDeclaredProposition, etaSynthesizedProposition, etaCodomain,
      etaExpansion, etaDomain, etaPredicateTerm, etaFunctionTerm,
      etaPredicateType, etaFunctionType, etaPredicateName, etaParameterName,
      DefinitionConversionKernel.definitionParameterName,
      DefinitionConversionKernel.identityDefinitionName,
      MathdataKernel.polymorphicReuseName,
      EnvironmentKernel.implicationReuseTermName,
      EnvironmentKernel.implicationReuseKnownName,
      DefinitionConversionKernel.encodeTermDeclarations,
      TermQuantifiedKernel.encodeSignature,
      TermQuantifiedKernel.encodeTypeContext,
      TermQuantifiedKernel.encodeProofContext,
      TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
      TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
      EnvironmentKernel.encodePrimitiveTypes, EnvironmentKernel.encodeKnown,
      EnvironmentKernel.a, a ]

end Mettapedia.Languages.Megalodon.EtaConversionKernel
