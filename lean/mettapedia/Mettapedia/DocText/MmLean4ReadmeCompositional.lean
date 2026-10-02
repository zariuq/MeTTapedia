import Mettapedia.Languages.GF.HandCrafted.English.Examples
import Mettapedia.Languages.GF.HandCrafted.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.MmLean4ReadmeCompositional

open Mettapedia.Languages.GF.HandCrafted.English
open Mettapedia.Languages.GF.HandCrafted.English.Nouns
open Mettapedia.Languages.GF.HandCrafted.English.Verbs
open Mettapedia.Languages.GF.HandCrafted.English.Adjectives
open Mettapedia.Languages.GF.HandCrafted.English.Syntax
open Mettapedia.Languages.GF.HandCrafted.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def verifier_N := regN "verifier"
private def checker_N := regN "checker"
private def specification_N := regN "specification"
private def proof_N := regN "proof"
private def equivalence_N := regN "equivalence"
private def toolchain_N := regN "toolchain"
private def status_N := regN "status"
private def theorem_N := regN "theorem"
private def contract_N := regN "contract"
private def diagnostic_N := regN "diagnostic"
private def boundary_N := regN "boundary"
private def review_N := regN "review"
private def checklist_N := regN "checklist"
private def layout_N := regN "layout"
private def build_N := regN "build"
private def executable_N := regN "executable"
private def claim_N := regN "claim"
private def correctness_N := regN "correctness"
private def discharge_N := regN "discharge"
private def reproduction_N := regN "reproduction"

inductive MmClaim where
  | formalizesMetamathVerifierInLean4
  | includesOperationalAndSemanticSpecifications
  | includesCorrespondenceProof
  | specPathHoldsSpecsAndEquivalence
  | verifyPathImplementsVerifier
  | kernelCorrectnessProvesSoundnessAndCompleteness
  | parserCorrectnessProvesInvariants
  | parserEquivalenceIsCanonicalEntryPoint
  | prefixProvabilityCertifiesPerEventProvenance
  | errorCodeSemanticsCertifiesTotalErrors
  | declarativeSpecHostsMarioSpecification
  | parserEquivalenceExamplesProvideUsageExamples
  | counterexampleInsertErrorProvidesCounterexample
  | parserSoundnessDemoIsDevelopmentArtifact
  | zipperTestIsDevelopmentArtifact
  | toolchainPinsLeanVersion
  | toolchainPinsBatteriesVersion
  | statusSorriesAreZero
  | statusAxiomsAreZero
  | statusBuildIsGreen
  | statusDefaultSuitePasses
  | statusReferenceDifferential
  | correctnessHasEndToEndTheorems
  | correctnessHasDiagnosticContract
  | mainClaimNormalFormatAdequacy
  | mainClaimAnyFormatAdequacy
  | mainClaimPrefixProvenance
  | mainClaimErrorCertification
  | mainClaimParserBridge
  | parserSuccessDischargesStructuralPremises
  | parserBridgeComposesFromSuccess
  | diagnosticsTaxonomyIsDocumented
  | verifierReportsFirstError
  | includeFailuresAreEnvironmentErrors
  | modesAreDistinctSpecifications
  | formalTheoremsCoverCheckBytesAndCheck
  | includeAwareExecutableIsSinglePass
  | parserEquivalenceIsReviewEntryModule
  | reviewStepReadParserEquivalence
  | reviewStepTraceDischargeChain
  | reviewStepRunBuildAndTests
  | executablesIncludeVerifierAndValidator
  | buildTargetsExecutablePair
  | reproductionNamesSpecificationSuite
  deriving Repr, DecidableEq, BEq

def renderMmClaim : MmClaim → String
  | .formalizesMetamathVerifierInLean4 =>
      mkPresPos (properNameNP "mm-lean4")
        (complV2 (mkV2 (regV "formalize"))
          (properNameNP "a Metamath verifier in Lean 4"))
  | .includesOperationalAndSemanticSpecifications =>
      let subj := properNameNP "The project"
      let obj := linConjNP and_Conj
        [ linAdjCN (linPositA (regA "operational")) (linUseN specification_N) |> linMassNP
        , linAdjCN (linPositA (regA "semantic")) (linUseN specification_N) |> linMassNP
        ]
      mkPresPos subj (complV2 (mkV2 (regV "include")) obj)
  | .includesCorrespondenceProof =>
      mkPresPos (properNameNP "The project")
        (complV2 (mkV2 (regV "include"))
          (linDetCN aIndefArt (linUseN proof_N)))
  | .specPathHoldsSpecsAndEquivalence =>
      mkPresPos (properNameNP "`Metamath/Spec/`")
        (complV2 (mkV2 (regV "hold"))
          (properNameNP "declarative and operational specifications with equivalence"))
  | .verifyPathImplementsVerifier =>
      mkPresPos (properNameNP "`Metamath/Verify.lean`")
        (complV2 (mkV2 (regV "implement"))
          (linDetCN theDefArt (linUseN verifier_N)))
  | .kernelCorrectnessProvesSoundnessAndCompleteness =>
      mkPresPos (properNameNP "`Metamath/KernelCorrectness.lean`")
        (complV2 (mkV2 (regV "prove"))
          (properNameNP "kernel soundness and completeness"))
  | .parserCorrectnessProvesInvariants =>
      mkPresPos (properNameNP "`Metamath/ParserCorrectness.lean`")
        (complV2 (mkV2 (regV "prove"))
          (properNameNP "parser invariants and correctness layers"))
  | .parserEquivalenceIsCanonicalEntryPoint =>
      mkPresPos (properNameNP "`Metamath/ParserEquivalence.lean`")
        (copulaNP (properNameNP "the canonical review entry point"))
  | .prefixProvabilityCertifiesPerEventProvenance =>
      mkPresPos (properNameNP "`Metamath/PrefixProvability/Checker.lean`")
        (complV2 (mkV2 (regV "certify"))
          (properNameNP "prefix provenance per accepted event"))
  | .errorCodeSemanticsCertifiesTotalErrors =>
      mkPresPos (properNameNP "`Metamath/ErrorCodeSemantics.lean`")
        (complV2 (mkV2 (regV "certify"))
          (properNameNP "evidence-payload agreement for every `ParseErrorCode` constructor"))
  | .declarativeSpecHostsMarioSpecification =>
      mkPresPos (properNameNP "`Metamath/DeclarativeSpec.lean`")
        (complV2 (mkV2 (regV "host"))
          (properNameNP "Mario Carneiro's declarative specification"))
  | .parserEquivalenceExamplesProvideUsageExamples =>
      mkPresPos (properNameNP "`Metamath/ParserEquivalenceExamples.lean`")
        (complV2 (mkV2 (regV "provide"))
          (properNameNP "compiling usage examples"))
  | .counterexampleInsertErrorProvidesCounterexample =>
      mkPresPos (properNameNP "`Metamath/CounterexampleInsertError.lean`")
        (complV2 (mkV2 (regV "provide"))
          (properNameNP "a counterexample for insert-with-error behavior"))
  | .parserSoundnessDemoIsDevelopmentArtifact =>
      mkPresPos (properNameNP "`Metamath/ParserSoundnessDemo.lean`")
        (copulaNP (properNameNP "a development artifact"))
  | .zipperTestIsDevelopmentArtifact =>
      mkPresPos (properNameNP "`Metamath/ZipperTest.lean`")
        (copulaNP (properNameNP "a development artifact"))
  | .toolchainPinsLeanVersion =>
      mkPresPos (properNameNP "The toolchain")
        (complV2 (mkV2 (regV "pin"))
          (properNameNP "Lean 4.33.1"))
  | .toolchainPinsBatteriesVersion =>
      mkPresPos (properNameNP "The toolchain")
        (complV2 (mkV2 (regV "pin"))
          (properNameNP "Batteries commit `4488d40`"))
  | .statusSorriesAreZero =>
      mkPresPos (properNameNP "Sorries" .AgP3Pl)
        (copulaNP (properNameNP "0"))
  | .statusAxiomsAreZero =>
      mkPresPos (properNameNP "Project-declared axioms" .AgP3Pl)
        (copulaNP (properNameNP "0; headline theorems use Lean's standard axioms"))
  | .statusBuildIsGreen =>
      mkPresPos (properNameNP "Build status")
        (copulaNP (properNameNP "successful on the pinned toolchain"))
  | .statusDefaultSuitePasses =>
      mkPresPos (properNameNP "The default `zar` specification suite")
        (copulaNP (properNameNP "187 of 187"))
  | .statusReferenceDifferential =>
      mkPresPos (properNameNP "The fail-closed reference differential")
        (copulaNP (properNameNP "an attempt of all 187 registered databases, with process failures separate from verdicts"))
  | .correctnessHasEndToEndTheorems =>
      mkPresPos (properNameNP "The development")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "end-to-end correctness theorems for the verifier"))
  | .correctnessHasDiagnosticContract =>
      mkPresPos (properNameNP "The development")
        (complV2 (mkV2 (regV "include"))
          (linDetCN aIndefArt
            (linAdjCN (linPositA (regA "formal")) (linUseN contract_N))))
  | .mainClaimNormalFormatAdequacy =>
      mkPresPos (properNameNP "`proofChecker_normal_iff_frameDerivable_in_parsedDB`")
        (copulaNP (properNameNP "the fixed-final-database normal-proof adequacy biconditional"))
  | .mainClaimAnyFormatAdequacy =>
      mkPresPos (properNameNP "`proofChecker_anyFormat_iff_frameDerivable_in_parsedDB`")
        (copulaNP (properNameNP "the fixed-final-database any-format adequacy biconditional"))
  | .mainClaimPrefixProvenance =>
      mkPresPos (properNameNP "`checkBytes_new_assert_strong_classified`")
        (copulaNP (properNameNP "the per-event prefix provenance theorem"))
  | .mainClaimErrorCertification =>
      mkPresPos (properNameNP "`checkBytes_parseErrorCode?_fullyCertified`")
        (copulaNP (properNameNP "the total error certification theorem"))
  | .mainClaimParserBridge =>
      mkPresPos (properNameNP "`parser_operational_to_frameDerivable_total` and `parser_frameDerivable_to_operational_total`")
        (copulaNP (properNameNP "the parser-specialized bridge to frame derivability"))
  | .parserSuccessDischargesStructuralPremises =>
      mkPresPos (properNameNP "Parser success")
        (complV2 (mkV2 (regV "discharge"))
          (properNameNP "WellFormedDatabaseStrong, FloatVarNoDup, and FrameVarsDisjointConsts"))
  | .parserBridgeComposesFromSuccess =>
      mkPresPos (properNameNP "`proofChecker_normal_iff_frameDerivable_in_parsedDB`")
        (complV2 (mkV2 (regV "compose"))
          (properNameNP "the full bridge from `checkBytes` success"))
  | .diagnosticsTaxonomyIsDocumented =>
      mkPresPos (properNameNP "Diagnostic taxonomy")
        (copulaNP (properNameNP "`docs/ErrorCodes.md`"))
  | .verifierReportsFirstError =>
      mkPresPos (properNameNP "The verifier")
        (complV2 (mkV2 (regV "report"))
          (properNameNP "the first error"))
  | .includeFailuresAreEnvironmentErrors =>
      mkPresPos (properNameNP "Include I/O failures" .AgP3Pl)
        (copulaNP (properNameNP "environment errors"))
  | .modesAreDistinctSpecifications =>
      mkPresPos (properNameNP "Verifier modes" .AgP3Pl)
        (copulaNP (properNameNP "distinct specifications"))
  | .formalTheoremsCoverCheckBytesAndCheck =>
      mkPresPos (properNameNP "Formal theorems" .AgP3Pl)
        (complV2 (mkV2 (regV "cover"))
          (properNameNP "both the pure `checkBytes` lane and the include-aware `check` implementation"))
  | .includeAwareExecutableIsSinglePass =>
      mkPresPos (properNameNP "The active executable frontend")
        (copulaNP (properNameNP "single-pass and include-aware"))
  | .parserEquivalenceIsReviewEntryModule =>
      mkPresPos (properNameNP "`Metamath/ParserEquivalence.lean`")
        (copulaNP (properNameNP "the review entry module for the composed chain"))
  | .reviewStepReadParserEquivalence =>
      mkPresPos (properNameNP "Reviewers" .AgP3Pl)
        (complV2 (mkV2 (regV "read"))
          (properNameNP "the theorem statements in `Metamath/SourceCompleteness.lean` and `Metamath/ParserEquivalence.lean`"))
  | .reviewStepTraceDischargeChain =>
      mkPresPos (properNameNP "Reviewers" .AgP3Pl)
        (complV2 (mkV2 (regV "trace"))
          (properNameNP "`parser_toDatabase_wellFormed_strong -> parser_frameDerivable_to_operational -> frameDerivable_to_proofValid`"))
  | .reviewStepRunBuildAndTests =>
      mkPresPos (properNameNP "Reviewers" .AgP3Pl)
        (complV2 (mkV2 (regV "run"))
          (properNameNP "`lake build` and the full test suite"))
  | .executablesIncludeVerifierAndValidator =>
      mkPresPos (properNameNP "Lake executables" .AgP3Pl)
        (copulaNP (properNameNP "`mm-lean4` and `validateDB`"))
  | .buildTargetsExecutablePair =>
      mkPresPos (properNameNP "The executable build target")
        (copulaNP (properNameNP "`lake build mm-lean4 validateDB`"))
  | .reproductionNamesSpecificationSuite =>
      mkPresPos (properNameNP "`METAMATH_TEST`")
        (copulaNP (properNameNP
          "a checkout of https://github.com/zariuq/metamath-test, branch `unit-tests`"))

def allMmClaims : List MmClaim :=
  [ .formalizesMetamathVerifierInLean4
  , .includesOperationalAndSemanticSpecifications
  , .includesCorrespondenceProof
  , .specPathHoldsSpecsAndEquivalence
  , .verifyPathImplementsVerifier
  , .kernelCorrectnessProvesSoundnessAndCompleteness
  , .parserCorrectnessProvesInvariants
  , .parserEquivalenceIsCanonicalEntryPoint
  , .prefixProvabilityCertifiesPerEventProvenance
  , .errorCodeSemanticsCertifiesTotalErrors
  , .declarativeSpecHostsMarioSpecification
  , .parserEquivalenceExamplesProvideUsageExamples
  , .counterexampleInsertErrorProvidesCounterexample
  , .parserSoundnessDemoIsDevelopmentArtifact
  , .zipperTestIsDevelopmentArtifact
  , .toolchainPinsLeanVersion
  , .toolchainPinsBatteriesVersion
  , .statusSorriesAreZero
  , .statusAxiomsAreZero
  , .statusBuildIsGreen
  , .statusDefaultSuitePasses
  , .statusReferenceDifferential
  , .correctnessHasEndToEndTheorems
  , .correctnessHasDiagnosticContract
  , .mainClaimNormalFormatAdequacy
  , .mainClaimAnyFormatAdequacy
  , .mainClaimPrefixProvenance
  , .mainClaimErrorCertification
  , .mainClaimParserBridge
  , .parserSuccessDischargesStructuralPremises
  , .parserBridgeComposesFromSuccess
  , .diagnosticsTaxonomyIsDocumented
  , .verifierReportsFirstError
  , .includeFailuresAreEnvironmentErrors
  , .modesAreDistinctSpecifications
  , .formalTheoremsCoverCheckBytesAndCheck
  , .includeAwareExecutableIsSinglePass
  , .parserEquivalenceIsReviewEntryModule
  , .reviewStepReadParserEquivalence
  , .reviewStepTraceDischargeChain
  , .reviewStepRunBuildAndTests
  , .executablesIncludeVerifierAndValidator
  , .buildTargetsExecutablePair
  , .reproductionNamesSpecificationSuite
  ]

def parseMmClaimLine? (line : String) : Option MmClaim :=
  let norm := stripTerminalPeriod line
  allMmClaims.find? (fun c => renderMmClaim c = norm)

inductive MmHeading where
  | title
  | layout
  | core
  | nonCore
  | toolchain
  | status
  | correctness
  | mainClaims
  | parserSuccessDischarge
  | diagnostics
  | trustBoundary
  | reproduction
  | quickReviewChecklist
  | build
  | executables
  deriving Repr, DecidableEq, BEq

private def headingNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassNP cn).s (.NCase .Nom)

private def headingPlNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassPluralNP cn).s (.NCase .Nom)

def renderMmHeading : MmHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "mm-lean4"))
        (linAdjCN (linPositA (regA "Metamath")) (linUseN verifier_N)))
  | .layout =>
      headingNP (linUseN layout_N)
  | .core =>
      headingNP (linAdjCN (linPositA (regA "core")) (linUseN layout_N))
  | .nonCore =>
      headingNP (linAdjCN (linPositA (compoundA "non-core")) (linUseN layout_N))
  | .toolchain =>
      headingNP (linUseN toolchain_N)
  | .status =>
      headingNP (linUseN status_N)
  | .correctness =>
      headingNP (linUseN correctness_N)
  | .mainClaims =>
      headingPlNP (linAdjCN (linPositA (regA "main")) (linUseN claim_N))
  | .parserSuccessDischarge =>
      headingNP (linAdjCN (linPositA (regA "parser")) (linUseN discharge_N))
  | .diagnostics =>
      headingPlNP (linUseN diagnostic_N)
  | .trustBoundary =>
      headingNP (linUseN boundary_N)
  | .reproduction =>
      headingNP (linUseN reproduction_N)
  | .quickReviewChecklist =>
      headingNP (linAdjCN (linPositA (regA "quick"))
        (linAdjCN (linPositA (regA "expert")) (linUseN checklist_N)))
  | .build =>
      headingNP (linUseN build_N)
  | .executables =>
      headingPlNP (linUseN executable_N)

def allMmHeadings : List MmHeading :=
  [ .title
  , .layout
  , .core
  , .nonCore
  , .toolchain
  , .status
  , .correctness
  , .mainClaims
  , .parserSuccessDischarge
  , .diagnostics
  , .trustBoundary
  , .reproduction
  , .quickReviewChecklist
  , .build
  , .executables
  ]

def parseMmHeadingLine? (line : String) : Option MmHeading :=
  allMmHeadings.find? (fun h => renderMmHeading h = line)

private def claimBullet (c : MmClaim) : ClaimBullet :=
  { text := renderMmClaim c }

def mmLean4ReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderMmHeading .title)
  , .paragraph
      [ renderMmClaim .formalizesMetamathVerifierInLean4
      , renderMmClaim .includesOperationalAndSemanticSpecifications
      , renderMmClaim .includesCorrespondenceProof
      ]
  , .heading 2 (renderMmHeading .layout)
  , .heading 3 (renderMmHeading .core)
  , .fileRef "Metamath/Spec/" (renderMmClaim .specPathHoldsSpecsAndEquivalence)
  , .fileRef "Metamath/Verify.lean" (renderMmClaim .verifyPathImplementsVerifier)
  , .fileRef "Metamath/KernelCorrectness.lean" (renderMmClaim .kernelCorrectnessProvesSoundnessAndCompleteness)
  , .fileRef "Metamath/ParserCorrectness.lean" (renderMmClaim .parserCorrectnessProvesInvariants)
  , .fileRef "Metamath/ParserEquivalence.lean" (renderMmClaim .parserEquivalenceIsCanonicalEntryPoint)
  , .fileRef "Metamath/PrefixProvability/Checker.lean" (renderMmClaim .prefixProvabilityCertifiesPerEventProvenance)
  , .fileRef "Metamath/ErrorCodeSemantics.lean" (renderMmClaim .errorCodeSemanticsCertifiesTotalErrors)
  , .fileRef "Metamath/DeclarativeSpec.lean" (renderMmClaim .declarativeSpecHostsMarioSpecification)
  , .heading 3 (renderMmHeading .nonCore)
  , .fileRef "Metamath/ParserEquivalenceExamples.lean" (renderMmClaim .parserEquivalenceExamplesProvideUsageExamples)
  , .fileRef "Metamath/CounterexampleInsertError.lean" (renderMmClaim .counterexampleInsertErrorProvidesCounterexample)
  , .fileRef "Metamath/ParserSoundnessDemo.lean" (renderMmClaim .parserSoundnessDemoIsDevelopmentArtifact)
  , .fileRef "Metamath/ZipperTest.lean" (renderMmClaim .zipperTestIsDevelopmentArtifact)
  , .heading 2 (renderMmHeading .toolchain)
  , .claimBullets
      [ claimBullet .toolchainPinsLeanVersion
      , claimBullet .toolchainPinsBatteriesVersion
      ]
  , .heading 2 (renderMmHeading .status)
  , .claimBullets
      [ claimBullet .statusSorriesAreZero
      , claimBullet .statusAxiomsAreZero
      , claimBullet .statusBuildIsGreen
      , claimBullet .statusDefaultSuitePasses
      , claimBullet .statusReferenceDifferential
      ]
  , .codeBlock "bash" "rg -n \"sorry\" Metamath/"
  , .heading 2 (renderMmHeading .correctness)
  , .paragraph
      [ renderMmClaim .correctnessHasEndToEndTheorems
      , renderMmClaim .correctnessHasDiagnosticContract
      ]
  , .heading 3 (renderMmHeading .mainClaims)
  , .claimBullets
      [ claimBullet .mainClaimNormalFormatAdequacy
      , claimBullet .mainClaimAnyFormatAdequacy
      , claimBullet .mainClaimPrefixProvenance
      , claimBullet .mainClaimErrorCertification
      , claimBullet .mainClaimParserBridge
      ]
  , .heading 3 (renderMmHeading .parserSuccessDischarge)
  , .paragraph
      [ renderMmClaim .parserSuccessDischargesStructuralPremises
      , renderMmClaim .parserBridgeComposesFromSuccess
      ]
  , .codeBlock ""
      "h_success : (checkBytes bytes).error? = none\n  -> parser_construction_wf_scoped\n  -> parser_toDatabase_wellFormed_strong\n  -> floatVarNoDup_of_uniqueFloatVars\n  -> frameVarsDisjointConsts_of_toFrame\n  -> operational_to_frameDerivable, frameDerivable_to_proofValid"
  , .heading 2 (renderMmHeading .diagnostics)
  , .claimBullets
      [ claimBullet .diagnosticsTaxonomyIsDocumented
      , claimBullet .verifierReportsFirstError
      , claimBullet .includeFailuresAreEnvironmentErrors
      , claimBullet .modesAreDistinctSpecifications
      ]
  , .heading 2 (renderMmHeading .trustBoundary)
  , .claimBullets
      [ claimBullet .formalTheoremsCoverCheckBytesAndCheck
      , claimBullet .includeAwareExecutableIsSinglePass
      , claimBullet .parserEquivalenceIsReviewEntryModule
      ]
  , .heading 2 (renderMmHeading .reproduction)
  , .paragraph [renderMmClaim .reproductionNamesSpecificationSuite]
  , .codeBlock "bash"
      "ROOT=\"$(pwd)\"\nlake build\nMM_LEAN4=\"$ROOT/.lake/build/bin/mm-lean4\" sh scripts/cli_honesty.sh\n(cd \"$METAMATH_TEST\" && MM_LEAN4=\"$ROOT/.lake/build/bin/mm-lean4\" ./run-testsuite-all ./test-mm-lean4)"
  , .heading 2 (renderMmHeading .quickReviewChecklist)
  , .claimBullets
      [ claimBullet .reviewStepReadParserEquivalence
      , claimBullet .reviewStepTraceDischargeChain
      , claimBullet .reviewStepRunBuildAndTests
      ]
  , .heading 2 (renderMmHeading .build)
  , .codeBlock "bash" "lake build"
  , .heading 2 (renderMmHeading .executables)
  , .claimBullets
      [ claimBullet .executablesIncludeVerifierAndValidator
      , claimBullet .buildTargetsExecutablePair
      ]
  ]

def mmLean4ReadmeMarkdown : String :=
  renderDoc mmLean4ReadmeBlocks

#eval mmLean4ReadmeMarkdown

inductive ParsedMmStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : MmClaim)
  | claimLine (claim : MmClaim)
  deriving Repr

def parseSelectedStructuredMmLine? (line : String) : Option ParsedMmStructuredLine :=
  match parseTechnicalLine? mmLean4ReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines mmLean4ReadmeBlocks).contains line then
        match parseClaimBulletLine? parseMmClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseMmClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredMmLines : List String :=
  technicalLines mmLean4ReadmeBlocks ++
  claimBulletLines mmLean4ReadmeBlocks ++
  [ ensurePeriod (renderMmClaim .formalizesMetamathVerifierInLean4)
  , ensurePeriod (renderMmClaim .includesOperationalAndSemanticSpecifications)
  , ensurePeriod (renderMmClaim .includesCorrespondenceProof)
  , ensurePeriod (renderMmClaim .correctnessHasEndToEndTheorems)
  , ensurePeriod (renderMmClaim .correctnessHasDiagnosticContract)
  ]

def mmLean4HardAuditPasses : Bool :=
  mmLean4ReadmeBlocks.all (blockPassesHardAuditWith parseMmClaimLine? parseMmHeadingLine?)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem mmLean4_hard_audit :
    mmLean4HardAuditPasses = true := by
  decide

def mmLean4HeadingImageCheck : Bool :=
  headingRenderImageCheck parseMmHeadingLine? renderMmHeading mmLean4ReadmeBlocks

theorem mmLean4_heading_images :
    mmLean4HeadingImageCheck = true := by
  decide

theorem mmLean4_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries mmLean4ReadmeBlocks) :
    ∃ h, parseMmHeadingLine? txt = some h ∧ renderMmHeading h = txt := by
  exact headingRenderImageWitness
    parseMmHeadingLine? renderMmHeading mmLean4ReadmeBlocks
    mmLean4_heading_images hMem

private def insertRenderedBucket (acc : List (String × List MmClaim)) (rendered : String) (c : MmClaim) :
    List (String × List MmClaim) :=
  match acc with
  | [] => [(rendered, [c])]
  | (k, cs) :: rest =>
      if k = rendered then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertRenderedBucket rest rendered c

def claimRenderedBuckets : List (String × List MmClaim) :=
  allMmClaims.foldl
    (fun acc c => insertRenderedBucket acc (renderMmClaim c) c) []

def ambiguousClaimRenderings : List (String × List MmClaim) :=
  claimRenderedBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allMmClaims.filter (fun c =>
    parseMmClaimLine? (renderMmClaim c) != some c)
  if fails.isEmpty then
    "mm-lean4 parse-back check: all claim lines roundtrip"
  else
    s!"mm-lean4 parse-back failures: {repr fails}"

#eval
  if mmLean4HardAuditPasses then
    "mm-lean4 hard audit: no prose-bearing bypass blocks detected"
  else
    "mm-lean4 hard audit: violation detected"

#eval
  let fails := selectedStructuredMmLines.filter
    (fun line =>
      match parseSelectedStructuredMmLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "mm-lean4 parse-back check: selected headings + bullet families roundtrip"
  else
    s!"mm-lean4 structured parse failures: {repr fails}"

#eval
  if ambiguousClaimRenderings.isEmpty then
    "mm-lean4 ambiguity diagnostic: no duplicate renderings across distinct claims"
  else
    s!"mm-lean4 ambiguity diagnostic: duplicate renderings found: {repr ambiguousClaimRenderings}"

end Mettapedia.DocText.MmLean4ReadmeCompositional
