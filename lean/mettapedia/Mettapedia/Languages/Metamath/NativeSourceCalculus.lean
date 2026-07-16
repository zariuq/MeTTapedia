import Metamath.DeclarativeSpec
import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.Languages.Metamath.MMLean4SemanticView

/-!
# First source-derived native Metamath calculus slice

This module formalizes the same narrow slice exercised operationally by
`metamath_native_source_calculus_v0.metta`: the normal proof of the small
syllogism corpus.  Its generated presentation contains ground source rules,
ordered native premises, an explicit identity-substitution witness, and an
explicit source-context witness.  The checked proof is related directly to
Mario Carneiro's declarative `Metamath.Provable` relation.

The result is intentionally a slice theorem.  General source-ledger lowering,
non-identity substitution, distinct-variable evidence, and compressed proof
elaboration remain separate obligations.
-/

namespace Mettapedia.Languages.Metamath.NativeSourceCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.Languages.Metamath.MMLean4SemanticView

/-! ## Exact source data -/

def sourceRevision : String := "metamath-test/test_compressed_simple.mm"

def sourceDigest : String :=
  "c80051de58b21dd7007d6e7650c3de5ac789ac6a9de13c756db8b02cfdb63772"

inductive SourceHypothesis where
  | floating (label typecode variableName : String)
  | essential (label : String) (formula : List String)
deriving Repr, DecidableEq

namespace SourceHypothesis

def label : SourceHypothesis → String
  | .floating label _ _ | .essential label _ => label

def formula : SourceHypothesis → List String
  | .floating _ typecode variableName => [typecode, variableName]
  | .essential _ formula => formula

end SourceHypothesis

structure SourceAssertion where
  label : String
  mandatory : List SourceHypothesis
  formula : List String
deriving Repr, DecidableEq

def rFloat : SourceHypothesis := .floating "tR" "term" "R"
def sFloat : SourceHypothesis := .floating "tS" "term" "S"
def tFloat : SourceHypothesis := .floating "tT" "term" "T"

def rsEssential : SourceHypothesis :=
  .essential "syl.1" ["|-", "R", "|=", "S"]

def stEssential : SourceHypothesis :=
  .essential "syl.2" ["|-", "S", "|=", "T"]

def theoremRSEssential : SourceHypothesis :=
  .essential "th.1" ["|-", "R", "|=", "S"]

def theoremSTEssential : SourceHypothesis :=
  .essential "th.2" ["|-", "S", "|=", "T"]

def axiomSyllogism : SourceAssertion :=
  { label := "ax-syl"
    mandatory := [rFloat, sFloat, tFloat, rsEssential, stEssential]
    formula := ["|-", "R", "|=", "T"] }

def targetHypotheses : List SourceHypothesis :=
  [rFloat, sFloat, tFloat, theoremRSEssential, theoremSTEssential]

def targetFormula : List String := ["|-", "R", "|=", "T"]

def targetProofLabels : List String :=
  ["tR", "tS", "tT", "th.1", "th.2", "ax-syl"]

/-! ## Generated generic-checker presentation -/

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

def atomPattern (value : String) : Pattern :=
  app "__metamath.String" [app value]

def atomListPattern : List String → Pattern
  | [] => app "__metamath.Nil"
  | value :: values =>
      app "__metamath.Cons" [atomPattern value, atomListPattern values]

def formulaPattern : List String → Pattern
  | [] => app "__metamath.MalformedFormula"
  | typecode :: body =>
      app "__metamath.Formula" [atomPattern typecode, atomListPattern body]

def identityPattern : Pattern :=
  app "__metamath.SourceIdentity"
    [atomPattern sourceRevision, atomPattern sourceDigest]

def provesPattern (formula : List String) : Pattern :=
  app "__metamath.SourceProves" [identityPattern, formulaPattern formula]

def bindingPattern (hypothesis : SourceHypothesis) : Option Pattern :=
  match hypothesis with
  | .floating _ typecode variableName =>
      some <| app "__metamath.Binding"
        [atomPattern variableName, formulaPattern [typecode, variableName]]
  | .essential _ _ => none

def identityBindingsPattern (hypotheses : List SourceHypothesis) : Pattern :=
  let bindings := hypotheses.filterMap bindingPattern
  bindings.foldr
    (fun binding rest => app "__metamath.Cons" [binding, rest])
    (app "__metamath.Nil")

def substitutionPattern (assertion : SourceAssertion) : Pattern :=
  app "__metamath.Substitution"
    [identityBindingsPattern assertion.mandatory]

def contextPattern (assertion : SourceAssertion) : Pattern :=
  app "__metamath.Context"
    [atomListPattern (assertion.mandatory.map SourceHypothesis.label),
     atomListPattern []]

def substitutionJudgment (assertion : SourceAssertion) : Pattern :=
  app "__metamath.SubstitutionValid"
    [identityPattern, atomPattern assertion.label,
     substitutionPattern assertion]

def contextJudgment (assertion : SourceAssertion) : Pattern :=
  app "__metamath.ContextValid"
    [identityPattern, atomPattern assertion.label,
     contextPattern assertion]

private def dataType : String := "__metamath.Data"

private def constructorRule (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := dataType
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base dataType)
    syntaxPattern := [] }

def sourceVocabulary : List String :=
  [ "th", "th.2", "th.1", "ax-syl", "syl.2", "syl.1",
    "tT", "tS", "tR", "T", "S", "R", "|=", "|-", "term",
    sourceDigest, sourceRevision ]

def staticConstructors : List (String × Nat) :=
  [ ("__metamath.String", 1), ("__metamath.Nil", 0),
    ("__metamath.Cons", 2), ("__metamath.Formula", 2),
    ("__metamath.SourceIdentity", 2), ("__metamath.Binding", 2),
    ("__metamath.Substitution", 1), ("__metamath.Context", 2) ]

def sourceLanguage : LanguageDef :=
  { name := "metamath-native-source-calculus-v0"
    types := [TypeDecl.plain dataType]
    terms :=
      staticConstructors.map (fun declaration =>
        constructorRule declaration.1 declaration.2) ++
      sourceVocabulary.map (fun value => constructorRule value 0)
    equations := []
    rewrites := [] }

private def rule (id : String) (premises : List Pattern)
    (conclusion : Pattern) : RuleSchema :=
  { id := ⟨id⟩, metavariables := [], premises, conclusion }

def hypothesisRule (hypothesis : SourceHypothesis) : RuleSchema :=
  rule hypothesis.label [] (provesPattern hypothesis.formula)

def substitutionRuleId (assertion : SourceAssertion) : String :=
  "__metamath.identity-substitution." ++ assertion.label

def contextRuleId (assertion : SourceAssertion) : String :=
  "__metamath.context." ++ assertion.label

def assertionRules (assertion : SourceAssertion) : List RuleSchema :=
  [ rule (substitutionRuleId assertion) []
      (substitutionJudgment assertion),
    rule (contextRuleId assertion) [] (contextJudgment assertion),
    rule assertion.label
      (assertion.mandatory.map
          (fun hypothesis => provesPattern hypothesis.formula) ++
        [substitutionJudgment assertion, contextJudgment assertion])
      (provesPattern assertion.formula) ]

def generatedPresentation : Presentation :=
  { language := sourceLanguage
    judgments :=
      [{ head := "__metamath.SourceProves", arity := 2 },
       { head := "__metamath.SubstitutionValid", arity := 3 },
       { head := "__metamath.ContextValid", arity := 3 }]
    rules := targetHypotheses.map hypothesisRule ++
      assertionRules axiomSyllogism }

theorem sourceLanguage_validate : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly sourceLanguage <;>
    simp [sourceLanguage, staticConstructors, sourceVocabulary,
      sourceDigest, sourceRevision, constructorRule, dataType,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

theorem generatedPresentation_valid : generatedPresentation.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  simp only [generatedPresentation]
  rw [sourceLanguage_validate]
  simp [sourceLanguage, staticConstructors, sourceVocabulary, sourceDigest,
    sourceRevision, constructorRule, dataType, targetHypotheses,
    rFloat, sFloat, tFloat, theoremRSEssential, theoremSTEssential,
    hypothesisRule, assertionRules, axiomSyllogism, rsEssential,
    stEssential, rule, app, provesPattern, identityPattern, formulaPattern,
    atomPattern, atomListPattern, substitutionJudgment,
    contextJudgment, substitutionPattern, identityBindingsPattern,
    bindingPattern, contextPattern, substitutionRuleId, contextRuleId,
    SourceHypothesis.formula, SourceHypothesis.label,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, RuleSchema.isValidIn,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

def validatedPresentation : ValidatedPresentation :=
  ⟨generatedPresentation, generatedPresentation_valid⟩

private def rawNode (id : String) (children : List RawProof := []) : RawProof :=
  .node { ruleId := ⟨id⟩, arguments := [] } children

def targetRawProof : RawProof :=
  rawNode axiomSyllogism.label
    (targetHypotheses.map (fun hypothesis => rawNode hypothesis.label) ++
      [rawNode (substitutionRuleId axiomSyllogism),
       rawNode (contextRuleId axiomSyllogism)])

def targetGoal : Pattern := provesPattern targetFormula

local macro "native_check_core" : tactic =>
  `(tactic|
    simp [checkRaw, checkRawChildren, validatedPresentation,
      generatedPresentation, targetHypotheses, rFloat, sFloat, tFloat,
      theoremRSEssential, theoremSTEssential, hypothesisRule,
      assertionRules, axiomSyllogism, rsEssential, stEssential, rule,
      app, sourceRevision, sourceDigest, provesPattern, identityPattern,
      formulaPattern, atomPattern,
      atomListPattern, substitutionJudgment, contextJudgment,
      substitutionPattern, identityBindingsPattern, bindingPattern,
      contextPattern, substitutionRuleId, contextRuleId,
      SourceHypothesis.formula, SourceHypothesis.label, rawNode,
      instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
      argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
      instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
      Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList])

theorem targetRawProof_checked :
    checkRaw validatedPresentation targetGoal targetRawProof = true := by
  simp only [targetRawProof, targetGoal, targetFormula]
  native_check_core

theorem targetRawProof_exact_derivation :
    ∃ derivation : Derivation validatedPresentation targetGoal,
      derivation.erase = targetRawProof :=
  checkRaw_exists_derivation_with_exact_erasure targetRawProof_checked

/-! ## Identity-bound checked package -/

def checkedSource : GSLTSource :=
  { identity :=
      { systemId := "Metamath"
        revision := sourceRevision
        artifactDigest := sourceDigest }
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "native-source-calculus"
             version := "v0"
             payload := app "__metamath.NativeSourceSliceV0" }] }
    presentation := generatedPresentation }

theorem checkedSource_identity_valid : checkedSource.identity.isValid = true := by
  rfl

theorem checkedSource_assumptions_valid :
    checkedSource.assumptions.isValid = true := by
  rfl

theorem checkedSource_profiles_valid : checkedSource.profiles.isValid = true := by
  rfl

theorem checkedSource_presentation_valid :
    checkedSource.presentation.isValidV2 = true := by
  exact generatedPresentation_valid

def admittedSource : CheckedGSLT :=
  { source := checkedSource
    identityValid := checkedSource_identity_valid
    assumptionsValid := checkedSource_assumptions_valid
    profilesValid := checkedSource_profiles_valid
    presentationValid := checkedSource_presentation_valid }

theorem checkedSource_validate : checkedSource.validate = .ok admittedSource := by
  have hprofilesNonempty : checkedSource.profiles.entries.isEmpty = false := by
    rfl
  simp [GSLTSource.validate, admittedSource, checkedSource_identity_valid,
    checkedSource_assumptions_valid, checkedSource_profiles_valid,
    checkedSource_presentation_valid, hprofilesNonempty]

theorem checkedSource_accepted : validationAccepted checkedSource.validate = true := by
  rw [checkedSource_validate]
  rfl

theorem checkedSource_presentation_is_generated :
    checkedSource.presentation = generatedPresentation := rfl

theorem checkedSource_exact_native_derivation :
    ∃ (checked : CheckedGSLT)
        (derivation : Derivation checked.presentation targetGoal),
      checkedSource.validate = .ok checked ∧
        derivation.erase = targetRawProof := by
  have hcheck : admittedSource.checkRaw targetGoal targetRawProof = true := by
    exact targetRawProof_checked
  rcases CheckedGSLT.checkRaw_exists_derivation_with_exact_erasure hcheck with
    ⟨derivation, herasure⟩
  exact ⟨admittedSource, derivation, checkedSource_validate, herasure⟩

/-! ## Direct declarative source semantics -/

def variableR : Metamath.VR := ⟨"term", 0⟩
def variableS : Metamath.VR := ⟨"term", 1⟩
def variableT : Metamath.VR := ⟨"term", 2⟩

def formulaR : Metamath.Formula := ("term", [Metamath.Sym.var variableR])
def formulaS : Metamath.Formula := ("term", [Metamath.Sym.var variableS])
def formulaT : Metamath.Formula := ("term", [Metamath.Sym.var variableT])

def formulaRS : Metamath.Formula :=
  ("|-", [Metamath.Sym.var variableR, Metamath.Sym.const "|=",
    Metamath.Sym.var variableS])

def formulaST : Metamath.Formula :=
  ("|-", [Metamath.Sym.var variableS, Metamath.Sym.const "|=",
    Metamath.Sym.var variableT])

def formulaRT : Metamath.Formula :=
  ("|-", [Metamath.Sym.var variableR, Metamath.Sym.const "|=",
    Metamath.Sym.var variableT])

def emptyDJ : Metamath.DJ := Metamath.DJ.mk' []

def theoremContext : Metamath.Context :=
  { hyps := [formulaR, formulaS, formulaT, formulaRS, formulaST]
    dj := emptyDJ }

def axiomStatement : Metamath.Statement :=
  { ctx := theoremContext
    fmla := formulaRT }

def sourceAxioms (statement : Metamath.Statement) : Prop :=
  statement = axiomStatement

theorem identity_respects_empty_dv :
    axiomStatement.ctx.dj.subst Metamath.VR.expr theoremContext.dj := by
  intro left right hpair
  change Metamath.DJ.mk' [] left right at hpair
  simp [Metamath.DJ.mk'] at hpair

theorem source_declarative_provable :
    Metamath.Provable sourceAxioms theoremContext formulaRT := by
  have application := Metamath.Provable.ax
    (axs := sourceAxioms) (Γ := theoremContext)
    Metamath.VR.expr (ax := axiomStatement)
    (by rfl) identity_respects_empty_dv
    (fun hypothesis membership => by
      rw [Metamath.Formula.subst_id]
      exact Metamath.Provable.hyp hypothesis membership)
    (fun sourceVariable _ => Metamath.Provable.var sourceVariable)
  simpa [axiomStatement, Metamath.Formula.subst_id] using application

/-! ## Semantic agreement with the verified source reader -/

def sourceVariableNames : List String := ["R", "S", "T"]

def runtimeSymbol (token : String) : Metamath.Verify.Sym :=
  if sourceVariableNames.contains token then .var token else .const token

def runtimeFormula (tokens : List String) : List Metamath.Verify.Sym :=
  tokens.map runtimeSymbol

def runtimeHypothesisView : SourceHypothesis → RuntimeObjectView
  | .floating label typecode variableName =>
      .hypothesis false (runtimeFormula [typecode, variableName]) label
  | .essential label formula =>
      .hypothesis true (runtimeFormula formula) label

def runtimeAssertionView (assertion : SourceAssertion) : RuntimeObjectView :=
  .assertion (runtimeFormula assertion.formula) []
    (assertion.mandatory.map SourceHypothesis.label) assertion.label

def targetAssertion : SourceAssertion :=
  { label := "th"
    mandatory := targetHypotheses
    formula := targetFormula }

/-- The complete final semantic object map expected from the selected source.
The list order is only for executable traversal; database lookup is by label. -/
def expectedRuntimeObjects : List (String × RuntimeObjectView) :=
  [ ("term", .constant "term"), ("|-", .constant "|-"),
    ("|=", .constant "|="), ("R", .variable "R"),
    ("S", .variable "S"), ("T", .variable "T") ] ++
  ([rFloat, sFloat, tFloat, rsEssential, stEssential,
      theoremRSEssential, theoremSTEssential].map fun hypothesis =>
    (hypothesis.label, runtimeHypothesisView hypothesis)) ++
  [(axiomSyllogism.label, runtimeAssertionView axiomSyllogism),
   (targetAssertion.label, runtimeAssertionView targetAssertion)]

def runtimeObjectMatches
    (database : Metamath.Verify.DB) (entry : String × RuntimeObjectView) : Bool :=
  (database.find? entry.1 |>.map runtimeObjectView) == some entry.2

/-- Semantic correspondence gate for the verified reader.  It compares the
entire final object map, requires all source scopes to be closed, and checks
every expected declaration, hypothesis, axiom, and theorem by exact view. -/
def runtimeSourceMatches (database : Metamath.Verify.DB) : Bool :=
  database.error?.isNone &&
    database.scopes.isEmpty &&
    database.frame.dj.isEmpty &&
    (database.frame.hyps.toList == ["tR", "tS", "tT"]) &&
    (database.objects.toList.length == expectedRuntimeObjects.length) &&
    expectedRuntimeObjects.all (runtimeObjectMatches database)

def RuntimeSourceAgreement (database : Metamath.Verify.DB) : Prop :=
  database.error?.isNone = true ∧
    database.scopes.isEmpty = true ∧
    database.frame.dj.isEmpty = true ∧
    (database.frame.hyps.toList == ["tR", "tS", "tT"]) = true ∧
    (database.objects.toList.length == expectedRuntimeObjects.length) = true ∧
    expectedRuntimeObjects.all (runtimeObjectMatches database) = true

theorem runtimeSourceMatches_sound {database : Metamath.Verify.DB}
    (hMatches : runtimeSourceMatches database = true) :
    RuntimeSourceAgreement database := by
  simp only [runtimeSourceMatches, Bool.and_eq_true] at hMatches
  rcases hMatches with
    ⟨⟨⟨⟨⟨herror, hscopes⟩, hdistinct⟩, hhypotheses⟩, hcount⟩, hentries⟩
  exact ⟨herror, hscopes, hdistinct, hhypotheses, hcount, hentries⟩

/-! ## One exact cross-semantics certificate -/

structure NativeSourceCertificate where
  checked : CheckedGSLT
  native : Derivation checked.presentation targetGoal
  sourceAdmission : checkedSource.validate = .ok checked
  exactErasure : native.erase = targetRawProof
  declarative : Metamath.Provable sourceAxioms theoremContext formulaRT

theorem native_source_certificate : Nonempty NativeSourceCertificate := by
  rcases checkedSource_exact_native_derivation with
    ⟨checked, native, sourceAdmission, exactErasure⟩
  exact ⟨
    { checked, native, sourceAdmission, exactErasure,
      declarative := source_declarative_provable }⟩

/-- The executable reader boundary and the native-kernel certificate are kept
in one value.  The database is supplied by `mm-lean4`; no source declaration
or inference rule is supplied by the caller. -/
structure RuntimeAnchoredNativeSourceCertificate
    (database : Metamath.Verify.DB) where
  nativeSource : NativeSourceCertificate
  readerAgreement : RuntimeSourceAgreement database

theorem runtime_anchored_native_source_certificate
    {database : Metamath.Verify.DB}
    (hMatches : runtimeSourceMatches database = true) :
    Nonempty (RuntimeAnchoredNativeSourceCertificate database) := by
  rcases native_source_certificate with ⟨nativeSource⟩
  exact ⟨
    { nativeSource
      readerAgreement := runtimeSourceMatches_sound hMatches }⟩

/-! ## Negative executable examples -/

def wrongPremiseOrderProof : RawProof :=
  rawNode axiomSyllogism.label
    ([rawNode "tS", rawNode "tR"] ++
      (targetHypotheses.drop 2).map (fun hypothesis => rawNode hypothesis.label) ++
      [rawNode (substitutionRuleId axiomSyllogism),
       rawNode (contextRuleId axiomSyllogism)])

def missingContextProof : RawProof :=
  rawNode axiomSyllogism.label
    (targetHypotheses.map (fun hypothesis => rawNode hypothesis.label) ++
      [rawNode (substitutionRuleId axiomSyllogism)])

example : checkRaw validatedPresentation targetGoal wrongPremiseOrderProof = false := by
  simp only [wrongPremiseOrderProof, targetGoal, targetFormula]
  native_check_core

example : checkRaw validatedPresentation targetGoal missingContextProof = false := by
  simp only [missingContextProof, targetGoal, targetFormula]
  native_check_core

end Mettapedia.Languages.Metamath.NativeSourceCalculus
