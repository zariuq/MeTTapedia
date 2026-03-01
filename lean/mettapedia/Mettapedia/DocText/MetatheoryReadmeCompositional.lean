import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.MetatheoryReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def library_N := regN "library"
private def framework_N := regN "framework"
private def theorem_N := regN "theorem"
private def section_N := regN "section"
private def overview_N := regN "overview"
private def installation_N := regN "installation"
private def status_N := regN "status"
private def workflow_N := regN "workflow"
private def phase_N := regN "phase"
private def scope_N := regN "scope"
private def structure_N := regN "structure"

inductive MetatheoryClaim where
  | titleScope
  | overviewSummary
  | rewritingFrameworkSummary
  | decreasingDiagramsSummary
  | lambdaSummary
  | combinatoryLogicSummary
  | stlcSummary
  | stlcExtendedSummary
  | stlcBoolSummary
  | systemFSummary
  | trsSummary
  | whyMultipleProofTechniques
  | whyLayeredArchitecture
  | whyDeBruijn
  | whyMathlibIntegration
  | whyAxiomFree
  | whyDocumentation
  | installationPrereqLean
  | installationPrereqLake
  | installationPrereqMathlib
  | buildStepClone
  | buildStepLakeBuild
  | strictCheckScript
  | noSorriesPolicy
  | quickStartImport
  | quickStartLambdaConfluence
  | quickStartRewritingDiamond
  | quickStartStlcNormalization
  | keyTheoremsIntro
  | projectStructureIntro
  | proofTechniquesIntro
  | diamondTechniqueSummary
  | hindleyRosenSummary
  | newmanLemmaSummary
  | logicalRelationsSummary
  | mathematicalBackgroundIntro
  | deBruijnSummary
  | starClosureSummary
  | confluenceSummary
  | apiReferenceIntro
  | referencesIntro
  | papersReferenceSummary
  | booksReferenceSummary
  | relatedFormalizationsSummary
  | contributingSummary
  | devGuidelineNoSorry
  | devGuidelineDocstrings
  | devGuidelineReferences
  | devGuidelineStyle
  | runningTestsSummary
  | licenseSummary
  | acknowledgmentSummary
  | keyTheoremTableScope
  | structureMapScope
  deriving Repr, DecidableEq, BEq

def renderMetatheoryClaim : MetatheoryClaim → String
  | .titleScope =>
      mkPresPos (properNameNP "Metatheory")
        (copulaNP (properNameNP "a Lean 4 metatheory library for rewriting and type-system proofs"))
  | .overviewSummary =>
      mkPresPos (properNameNP "Metatheory")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "core programming-language metatheory results"))
  | .rewritingFrameworkSummary =>
      mkPresPos (properNameNP "The library")
        (copulaNP (properNameNP "a generic rewriting framework with multiple confluence methods"))
  | .decreasingDiagramsSummary =>
      mkPresPos (properNameNP "The library")
        (copulaNP (properNameNP "decreasing-diagram examples for non-terminating confluence"))
  | .lambdaSummary =>
      mkPresPos (properNameNP "The lambda module")
        (copulaNP (properNameNP "Church-Rosser via parallel reduction, beta-eta confluence, and call-by-value"))
  | .combinatoryLogicSummary =>
      mkPresPos (properNameNP "The combinatory-logic module")
        (copulaNP (properNameNP "SK confluence with derived combinator identities"))
  | .stlcSummary =>
      mkPresPos (properNameNP "The STLC module")
        (copulaNP (properNameNP "subject reduction and strong normalization via Tait"))
  | .stlcExtendedSummary =>
      mkPresPos (properNameNP "The extended STLC module")
        (copulaNP (properNameNP "products, sums, unit, progress, and normalization"))
  | .stlcBoolSummary =>
      mkPresPos (properNameNP "The STLC Boolean module")
        (copulaNP (properNameNP "conditionals, confluence, progress, and call-by-value determinism"))
  | .systemFSummary =>
      mkPresPos (properNameNP "The System F module")
        (copulaNP (properNameNP "polymorphic typing with subject reduction and normalization"))
  | .trsSummary =>
      mkPresPos (properNameNP "The TRS modules" .AgP3Pl)
        (copulaNP (properNameNP "term and string rewriting with Newman and completion orderings"))
  | .whyMultipleProofTechniques =>
      mkPresPos (properNameNP "Multiple proof techniques" .AgP3Pl)
        (complV2 (mkV2 (regV "provide")) (properNameNP "a way to compare Diamond, Newman, and Hindley-Rosen methods"))
  | .whyLayeredArchitecture =>
      mkPresPos (properNameNP "Layered architecture")
        (copulaNP (properNameNP "a generic framework instantiated by concrete systems"))
  | .whyDeBruijn =>
      mkPresPos (properNameNP "De Bruijn indices" .AgP3Pl)
        (copulaNP (properNameNP "capture-avoiding substitution without alpha-equivalence bookkeeping"))
  | .whyMathlibIntegration =>
      mkPresPos (properNameNP "Mathlib integration")
        (copulaNP (properNameNP "standard lemma reuse with core theorem axioms excluded"))
  | .whyAxiomFree =>
      mkPresNeg (properNameNP "The metatheory core")
        (complV2 (mkV2 (regV "contain")) (properNameNP "axioms, constants, sorries, or admits"))
  | .whyDocumentation =>
      mkPresPos (properNameNP "The public surface")
        (copulaNP (properNameNP "docstring-rich with source references"))
  | .installationPrereqLean =>
      mkPresPos (properNameNP "The installation")
        (complV2 (mkV2 (regV "require")) (properNameNP "Lean 4.27.0 or compatible"))
  | .installationPrereqLake =>
      mkPresPos (properNameNP "The installation")
        (complV2 (mkV2 (regV "require")) (properNameNP "Lake from Lean"))
  | .installationPrereqMathlib =>
      mkPresPos (properNameNP "The installation")
        (complV2 (mkV2 (regV "require")) (properNameNP "Mathlib fetched by Lake"))
  | .buildStepClone =>
      mkPresPos (properNameNP "The build workflow")
        (copulaNP (properNameNP "clone then lake build"))
  | .buildStepLakeBuild =>
      mkPresPos (properNameNP "The default check")
        (copulaNP (properNameNP "lake build over the full project"))
  | .strictCheckScript =>
      mkPresPos (properNameNP "The optional strict check")
        (copulaNP (properNameNP "scripts/check.ps1 for placeholder and axiom scans"))
  | .noSorriesPolicy =>
      mkPresPos (properNameNP "The policy")
        (copulaNP (properNameNP "all modules stay sorry-free and axiom-free"))
  | .quickStartImport =>
      mkPresPos (properNameNP "Quick start")
        (copulaNP (properNameNP "import Metatheory and focused modules"))
  | .quickStartLambdaConfluence =>
      mkPresPos (properNameNP "Quick start")
        (copulaNP (properNameNP "run a lambda confluence example"))
  | .quickStartRewritingDiamond =>
      mkPresPos (properNameNP "Quick start")
        (copulaNP (properNameNP "run a generic rewriting Diamond-to-Confluent example"))
  | .quickStartStlcNormalization =>
      mkPresPos (properNameNP "Quick start")
        (copulaNP (properNameNP "run an STLC strong-normalization example"))
  | .keyTheoremsIntro =>
      mkPresPos (properNameNP "The key theorems section")
        (copulaNP (properNameNP "a grouped index of theorem anchors by subsystem"))
  | .projectStructureIntro =>
      mkPresPos (properNameNP "The project structure section")
        (copulaNP (properNameNP "a layer-by-layer map from generic rewriting to System F"))
  | .proofTechniquesIntro =>
      mkPresPos (properNameNP "The proof techniques section")
        (copulaNP (properNameNP "the method-level bridge from diamond proofs to logical relations"))
  | .diamondTechniqueSummary =>
      mkPresPos (properNameNP "Diamond techniques" .AgP3Pl)
        (copulaNP (properNameNP "used for Lambda, combinatory logic, and tiny TRS comparisons"))
  | .hindleyRosenSummary =>
      mkPresPos (properNameNP "The Hindley-Rosen lemma")
        (copulaNP (properNameNP "used for beta-eta confluence through commuting confluent relations"))
  | .newmanLemmaSummary =>
      mkPresPos (properNameNP "The Newman lemma")
        (copulaNP (properNameNP "used for terminating systems with local confluence proofs"))
  | .logicalRelationsSummary =>
      mkPresPos (properNameNP "Logical relations" .AgP3Pl)
        (copulaNP (properNameNP "used for strong normalization via Tait-style reducibility"))
  | .mathematicalBackgroundIntro =>
      mkPresPos (properNameNP "The mathematical background section")
        (complV2 (mkV2 (regV "cover"))
          (properNameNP "de Bruijn indices, star closure, and confluence definitions"))
  | .deBruijnSummary =>
      mkPresPos (properNameNP "De Bruijn indices" .AgP3Pl)
        (copulaNP (properNameNP "used for capture-avoiding substitution without alpha-renaming overhead"))
  | .starClosureSummary =>
      mkPresPos (properNameNP "Reflexive-transitive closure")
        (copulaNP (properNameNP "formalized as an inductive Star relation"))
  | .confluenceSummary =>
      mkPresPos (properNameNP "Confluence")
        (copulaNP (properNameNP "specified as joinability for divergent multi-step reductions"))
  | .apiReferenceIntro =>
      mkPresPos (properNameNP "The API reference section")
        (complV2 (mkV2 (regV "cover"))
          (properNameNP "core definitions and typed syntax snippets for each subsystem"))
  | .referencesIntro =>
      mkPresPos (properNameNP "The references section")
        (complV2 (mkV2 (regV "cover"))
          (properNameNP "papers, books, and related formalization links"))
  | .papersReferenceSummary =>
      mkPresPos (properNameNP "The papers subsection")
        (copulaNP (properNameNP "Takahashi, Newman, van Oostrom, Tait, and Hindley source anchors"))
  | .booksReferenceSummary =>
      mkPresPos (properNameNP "The books subsection")
        (copulaNP (properNameNP "Barendregt, Terese, Girard-Lafont-Taylor, and Software Foundations"))
  | .relatedFormalizationsSummary =>
      mkPresPos (properNameNP "The related formalizations subsection")
        (copulaNP (properNameNP "Software Foundations, CoLoR, Nominal Isabelle, and PLFA links"))
  | .contributingSummary =>
      mkPresPos (properNameNP "The contributing section")
        (complV2 (mkV2 (regV "provide")) (properNameNP "issue and pull-request workflow guidance"))
  | .devGuidelineNoSorry =>
      mkPresPos (properNameNP "Development guidelines" .AgP3Pl)
        (complV2 (mkV2 (regV "require")) (properNameNP "no sorry placeholders in theorem proofs"))
  | .devGuidelineDocstrings =>
      mkPresPos (properNameNP "Development guidelines" .AgP3Pl)
        (complV2 (mkV2 (regV "require")) (properNameNP "docstrings on public definitions"))
  | .devGuidelineReferences =>
      mkPresPos (properNameNP "Development guidelines" .AgP3Pl)
        (complV2 (mkV2 (regV "require")) (properNameNP "source citations for non-trivial lemmas"))
  | .devGuidelineStyle =>
      mkPresPos (properNameNP "Development guidelines" .AgP3Pl)
        (complV2 (mkV2 (regV "follow")) (properNameNP "existing project style conventions"))
  | .runningTestsSummary =>
      mkPresPos (properNameNP "The running tests section")
        (complV2 (mkV2 (regV "use")) (properNameNP "lake build to compile and type-check all proofs"))
  | .licenseSummary =>
      mkPresPos (properNameNP "The license section")
        (complV2 (mkV2 (regV "state")) (properNameNP "MIT with a repository-local LICENSE reference"))
  | .acknowledgmentSummary =>
      mkPresPos (properNameNP "The acknowledgments section")
        (complV2 (mkV2 (regV "credit")) (properNameNP "Claude Code assistance for software engineering workflow"))
  | .keyTheoremTableScope =>
      mkPresPos (properNameNP "The key theorem table")
        (complV2 (mkV2 (regV "cover"))
          (properNameNP "confluence, normalization, and subject-reduction anchors"))
  | .structureMapScope =>
      mkPresPos (properNameNP "The structure map")
        (complV2 (mkV2 (regV "list"))
          (properNameNP "core module paths and theorem hosts"))

def allMetatheoryClaims : List MetatheoryClaim :=
  [ .titleScope
  , .overviewSummary
  , .rewritingFrameworkSummary
  , .decreasingDiagramsSummary
  , .lambdaSummary
  , .combinatoryLogicSummary
  , .stlcSummary
  , .stlcExtendedSummary
  , .stlcBoolSummary
  , .systemFSummary
  , .trsSummary
  , .whyMultipleProofTechniques
  , .whyLayeredArchitecture
  , .whyDeBruijn
  , .whyMathlibIntegration
  , .whyAxiomFree
  , .whyDocumentation
  , .installationPrereqLean
  , .installationPrereqLake
  , .installationPrereqMathlib
  , .buildStepClone
  , .buildStepLakeBuild
  , .strictCheckScript
  , .noSorriesPolicy
  , .quickStartImport
  , .quickStartLambdaConfluence
  , .quickStartRewritingDiamond
  , .quickStartStlcNormalization
  , .keyTheoremsIntro
  , .projectStructureIntro
  , .proofTechniquesIntro
  , .diamondTechniqueSummary
  , .hindleyRosenSummary
  , .newmanLemmaSummary
  , .logicalRelationsSummary
  , .mathematicalBackgroundIntro
  , .deBruijnSummary
  , .starClosureSummary
  , .confluenceSummary
  , .apiReferenceIntro
  , .referencesIntro
  , .papersReferenceSummary
  , .booksReferenceSummary
  , .relatedFormalizationsSummary
  , .contributingSummary
  , .devGuidelineNoSorry
  , .devGuidelineDocstrings
  , .devGuidelineReferences
  , .devGuidelineStyle
  , .runningTestsSummary
  , .licenseSummary
  , .acknowledgmentSummary
  , .keyTheoremTableScope
  , .structureMapScope
  ]

def parseMetatheoryClaimLine? (line : String) : Option MetatheoryClaim :=
  let norm := stripTerminalPeriod line
  allMetatheoryClaims.find? (fun c => renderMetatheoryClaim c = norm)

inductive MetatheoryHeading where
  | title
  | overview
  | whyMetatheory
  | installation
  | noSorries
  | quickStart
  | keyTheorems
  | genericRewritingFramework
  | lambdaCalculus
  | combinatoryLogic
  | simplyTypedLambdaCalculus
  | extendedSTLC
  | stlcWithBooleans
  | trsProofComparison
  | firstOrderTRS
  | systemF
  | projectStructure
  | proofTechniques
  | diamondProperty
  | hindleyRosenLemma
  | newmanLemma
  | logicalRelations
  | mathematicalBackground
  | deBruijnIndices
  | reflexiveTransitiveClosure
  | confluence
  | apiReference
  | coreDefinitions
  | lambdaCalculusApi
  | combinatoryLogicApi
  | stlcApi
  | extendedStlcApi
  | references
  | papers
  | books
  | relatedFormalizations
  | contributing
  | developmentGuidelines
  | runningTests
  | license
  | acknowledgments
  | structureMap
  deriving Repr, DecidableEq, BEq

def renderMetatheoryHeading : MetatheoryHeading → String
  | .title =>
      headingNP (linUseN (regN "Metatheory"))
  | .overview =>
      headingNP (linUseN overview_N)
  | .whyMetatheory =>
      headingNP (linAdjCN (linPositA (regA "why")) (linUseN (regN "Metatheory")))
  | .installation =>
      headingNP (linUseN installation_N)
  | .noSorries =>
      headingNP (linAdjCN (linPositA (compoundA "no sorries and axioms")) (linUseN status_N))
  | .quickStart =>
      headingNP (linAdjCN (linPositA (regA "quick")) (linUseN workflow_N))
  | .keyTheorems =>
      headingPlNP (linAdjCN (linPositA (regA "key")) (linUseN theorem_N))
  | .genericRewritingFramework =>
      headingNP (linAdjCN (linPositA (compoundA "generic rewriting")) (linUseN framework_N))
  | .lambdaCalculus =>
      headingNP (linAdjCN (linPositA (regA "lambda")) (linUseN (regN "calculus")))
  | .combinatoryLogic =>
      headingNP (linAdjCN (linPositA (regA "combinatory")) (linUseN (regN "logic")))
  | .simplyTypedLambdaCalculus =>
      headingNP (linAdjCN (linPositA (compoundA "simply typed lambda")) (linUseN (regN "calculus")))
  | .extendedSTLC =>
      headingNP (linAdjCN (linPositA (regA "extended")) (linUseN (regN "STLC")))
  | .stlcWithBooleans =>
      headingNP (linAdjCN (linPositA (compoundA "STLC with booleans")) (linUseN (regN "section")))
  | .trsProofComparison =>
      headingNP (linAdjCN (linPositA (compoundA "TRS proof")) (linUseN (regN "comparison")))
  | .firstOrderTRS =>
      headingNP (linAdjCN (linPositA (compoundA "first-order TRS")) (linUseN (regN "section")))
  | .systemF =>
      headingNP (linUseN (regN "System F"))
  | .projectStructure =>
      headingNP (linAdjCN (linPositA (regA "project")) (linUseN structure_N))
  | .proofTechniques =>
      headingPlNP (linAdjCN (linPositA (regA "proof")) (linUseN (regN "technique")))
  | .diamondProperty =>
      headingNP (linAdjCN (linPositA (regA "diamond")) (linUseN (regN "property")))
  | .hindleyRosenLemma =>
      headingNP (linUseN (regN "Hindley-Rosen lemma"))
  | .newmanLemma =>
      headingNP (linUseN (regN "Newman lemma"))
  | .logicalRelations =>
      headingPlNP (linAdjCN (linPositA (regA "logical")) (linUseN (regN "relation")))
  | .mathematicalBackground =>
      headingNP (linAdjCN (linPositA (regA "mathematical")) (linUseN (regN "background")))
  | .deBruijnIndices =>
      headingPlNP (linUseN (regN "de Bruijn index"))
  | .reflexiveTransitiveClosure =>
      headingNP (linAdjCN (linPositA (compoundA "reflexive-transitive")) (linUseN (regN "closure")))
  | .confluence =>
      headingNP (linUseN (regN "confluence"))
  | .apiReference =>
      headingNP (linAdjCN (linPositA (regA "API")) (linUseN (regN "reference")))
  | .coreDefinitions =>
      headingPlNP (linAdjCN (linPositA (regA "core")) (linUseN (regN "definition")))
  | .lambdaCalculusApi =>
      headingNP (linAdjCN (linPositA (compoundA "lambda calculus")) (linUseN (regN "section")))
  | .combinatoryLogicApi =>
      headingNP (linAdjCN (linPositA (compoundA "combinatory logic")) (linUseN (regN "section")))
  | .stlcApi =>
      headingNP (linUseN (regN "STLC"))
  | .extendedStlcApi =>
      headingNP (linAdjCN (linPositA (compoundA "extended STLC")) (linUseN (regN "section")))
  | .references =>
      headingPlNP (linUseN (regN "reference"))
  | .papers =>
      headingPlNP (linUseN (regN "paper"))
  | .books =>
      headingPlNP (linUseN (regN "book"))
  | .relatedFormalizations =>
      headingPlNP (linAdjCN (linPositA (regA "related")) (linUseN (regN "formalization")))
  | .contributing =>
      headingNP (linUseN (regN "contributing"))
  | .developmentGuidelines =>
      headingPlNP (linAdjCN (linPositA (regA "development")) (linUseN (regN "guideline")))
  | .runningTests =>
      headingPlNP (linAdjCN (linPositA (regA "running")) (linUseN (regN "test")))
  | .license =>
      headingNP (linUseN (regN "license"))
  | .acknowledgments =>
      headingPlNP (linUseN (regN "acknowledgment"))
  | .structureMap =>
      headingNP (linAdjCN (linPositA (regA "structure")) (linUseN (regN "map")))

def allMetatheoryHeadings : List MetatheoryHeading :=
  [ .title
  , .overview
  , .whyMetatheory
  , .installation
  , .noSorries
  , .quickStart
  , .keyTheorems
  , .genericRewritingFramework
  , .lambdaCalculus
  , .combinatoryLogic
  , .simplyTypedLambdaCalculus
  , .extendedSTLC
  , .stlcWithBooleans
  , .trsProofComparison
  , .firstOrderTRS
  , .systemF
  , .projectStructure
  , .proofTechniques
  , .diamondProperty
  , .hindleyRosenLemma
  , .newmanLemma
  , .logicalRelations
  , .mathematicalBackground
  , .deBruijnIndices
  , .reflexiveTransitiveClosure
  , .confluence
  , .apiReference
  , .coreDefinitions
  , .lambdaCalculusApi
  , .combinatoryLogicApi
  , .stlcApi
  , .extendedStlcApi
  , .references
  , .papers
  , .books
  , .relatedFormalizations
  , .contributing
  , .developmentGuidelines
  , .runningTests
  , .license
  , .acknowledgments
  , .structureMap
  ]

def parseMetatheoryHeadingLine? (line : String) : Option MetatheoryHeading :=
  allMetatheoryHeadings.find? (fun h => renderMetatheoryHeading h = line)

private def claimBullet (c : MetatheoryClaim) : ClaimBullet :=
  { text := renderMetatheoryClaim c }

private def q (s : String) : SynExpr := .quoted s

private def thm (name stmt file : String) : TheoremItem :=
  { name := name, statement := q stmt, file := file }

def metatheoryReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderMetatheoryHeading .title)
  , .paragraph [renderMetatheoryClaim .titleScope]
  , .codeBlock "markdown"
      "[![Lean 4](https://img.shields.io/badge/Lean-4.27.0-blue.svg)](https://lean-lang.org/)\n[![Mathlib](https://img.shields.io/badge/Mathlib-v4.27.0-green.svg)](https://github.com/leanprover-community/mathlib4)\n[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)"
  , .heading 2 (renderMetatheoryHeading .overview)
  , .claimBullets
      [ claimBullet .overviewSummary
      , claimBullet .rewritingFrameworkSummary
      , claimBullet .decreasingDiagramsSummary
      , claimBullet .lambdaSummary
      , claimBullet .combinatoryLogicSummary
      , claimBullet .stlcSummary
      , claimBullet .stlcExtendedSummary
      , claimBullet .stlcBoolSummary
      , claimBullet .systemFSummary
      , claimBullet .trsSummary
      ]
  , .heading 3 (renderMetatheoryHeading .whyMetatheory)
  , .claimBullets
      [ claimBullet .whyMultipleProofTechniques
      , claimBullet .whyLayeredArchitecture
      , claimBullet .whyDeBruijn
      , claimBullet .whyMathlibIntegration
      , claimBullet .whyAxiomFree
      , claimBullet .whyDocumentation
      ]
  , .heading 2 (renderMetatheoryHeading .installation)
  , .claimBullets
      [ claimBullet .installationPrereqLean
      , claimBullet .installationPrereqLake
      , claimBullet .installationPrereqMathlib
      , claimBullet .buildStepClone
      , claimBullet .buildStepLakeBuild
      , claimBullet .strictCheckScript
      ]
  , .codeBlock "bash"
      "git clone https://github.com/Arthur742Ramos/Metatheory.git\ncd Metatheory\nlake build"
  , .codeBlock "bash"
      "powershell -ExecutionPolicy Bypass -File scripts/check.ps1"
  , .heading 2 (renderMetatheoryHeading .noSorries)
  , .claimBullets [claimBullet .noSorriesPolicy]
  , .heading 2 (renderMetatheoryHeading .quickStart)
  , .claimBullets
      [ claimBullet .quickStartImport
      , claimBullet .quickStartLambdaConfluence
      , claimBullet .quickStartRewritingDiamond
      , claimBullet .quickStartStlcNormalization
      ]
  , .codeBlock "lean"
      "import Metatheory"
  , .codeBlock "lean"
      "import Metatheory\n\nimport Metatheory.Lambda.Term\nimport Metatheory.Lambda.Confluence\n\nopen Metatheory.Lambda\nopen Term\n\nexample {M N₁ N₂ : Term} (h1 : M →* N₁) (h2 : M →* N₂) :\n    ∃ P, (N₁ →* P) ∧ (N₂ →* P) :=\n  confluence h1 h2"
  , .codeBlock "lean"
      "import Metatheory.Rewriting.Basic\nimport Metatheory.Rewriting.Diamond\n\nopen Rewriting\n\nexample {α : Type} {r : α → α → Prop} (h : Diamond r) : Confluent r :=\n  confluent_of_diamond h"
  , .codeBlock "lean"
      "import Metatheory.STLC.Typing\nimport Metatheory.STLC.Normalization\n\nopen Metatheory.STLC\n\nexample {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) : SN M :=\n  strong_normalization h"
  , .codeBlock "lean"
      "import Metatheory.STLCext.Typing\nimport Metatheory.STLCext.Normalization\n\nopen Metatheory.STLCext\n\nexample {M : Term} {A : Ty} (h : HasType [] M A) : IsValue M ∨ ∃ N, M ⟶ N :=\n  progress h"
  , .codeBlock "lean"
      "import Metatheory.STLCextBool.CBV\n\nopen Metatheory.STLCextBool\n\nexample {M N₁ N₂ : Term} (h1 : CBVStep M N₁) (h2 : CBVStep M N₂) : N₁ = N₂ :=\n  CBVStep.deterministic h1 h2"
  , .codeBlock "lean"
      "import Metatheory.SystemF.Typing\nimport Metatheory.SystemF.SubjectReduction\n\nopen Metatheory.SystemF\n\nexample {Γ : Context} {M N : Term} {τ : Ty}\n    (hM : Γ ⊢ M : τ) (hstep : M.Step N) : Γ ⊢ N : τ :=\n  subject_reduction hM hstep"
  , .heading 2 (renderMetatheoryHeading .keyTheorems)
  , .claimBullets [claimBullet .keyTheoremsIntro, claimBullet .keyTheoremTableScope]
  , .heading 3 (renderMetatheoryHeading .genericRewritingFramework)
  , .theoremItems
      [ thm "confluent_of_diamond" "Diamond r -> Confluent r" "Metatheory/Rewriting/Diamond.lean"
      , thm "confluent_of_terminating_localConfluent" "Terminating r -> LocalConfluent r -> Confluent r" "Metatheory/Rewriting/Newman.lean"
      , thm "confluent_union" "Confluent r -> Confluent s -> Commute r s -> Confluent (Union r s)" "Metatheory/Rewriting/HindleyRosen.lean"
      , thm "confluent_of_locallyDecreasing" "WellFounded lt -> LocallyDecreasing r lt -> Confluent (LabeledUnion r)" "Metatheory/Rewriting/DecreasingDiagrams.lean"
      , thm "existsUnique_normalForm_of_terminating_confluent" "Terminating r -> Confluent r -> forall a, exists n, Star r a n /\\ NF n" "Metatheory/Rewriting/Basic.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/Rewriting/Diamond.lean"
          members := ["confluent_of_diamond"] }
      , { path := "Metatheory/Rewriting/Newman.lean"
          members := ["confluent_of_terminating_localConfluent"] }
      , { path := "Metatheory/Rewriting/HindleyRosen.lean"
          members := ["confluent_union"] }
      , { path := "Metatheory/Rewriting/DecreasingDiagrams.lean"
          members := ["confluent_of_locallyDecreasing", "church_rosser_of_locallyDecreasing"] }
      , { path := "Metatheory/Rewriting/Basic.lean"
          members := ["hasNormalForm_of_terminating", "existsUnique_normalForm_of_terminating_confluent"] }
      ]
  , .heading 3 (renderMetatheoryHeading .lambdaCalculus)
  , .theoremItems
      [ thm "confluence" "M ->* N1 -> M ->* N2 -> exists P, N1 ->* P /\\ N2 ->* P" "Metatheory/Lambda/Confluence.lean"
      , thm "parRed_diamond" "Diamond ParRed" "Metatheory/Lambda/Diamond.lean"
      , thm "parRed_complete" "M => N -> N => complete M" "Metatheory/Lambda/Complete.lean"
      , thm "CBVStep.deterministic" "CBVStep M N1 -> CBVStep M N2 -> N1 = N2" "Metatheory/Lambda/CBV.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/Lambda/Confluence.lean"
          members := ["confluence"] }
      , { path := "Metatheory/Lambda/Diamond.lean"
          members := ["parRed_diamond"] }
      , { path := "Metatheory/Lambda/Complete.lean"
          members := ["parRed_complete"] }
      , { path := "Metatheory/Lambda/Eta.lean"
          members := ["beta_eta_confluent", "beta_eta_diamond", "eta_confluent"] }
      , { path := "Metatheory/Lambda/CBV.lean"
          members := ["CBVStep.deterministic", "progress_trichotomy"] }
      ]
  , .heading 3 (renderMetatheoryHeading .combinatoryLogic)
  , .theoremItems
      [ thm "confluent" "Confluent WeakStep" "Metatheory/CL/Confluence.lean"
      , thm "I_identity" "(I · x) ->* x" "Metatheory/CL/Reduction.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/CL/Confluence.lean"
          members := ["confluent"] }
      , { path := "Metatheory/CL/Reduction.lean"
          members := ["I_identity", "K_identity", "S_identity", "B_identity", "C_identity", "W_identity"] }
      ]
  , .heading 3 (renderMetatheoryHeading .simplyTypedLambdaCalculus)
  , .theoremItems
      [ thm "subject_reduction" "HasType Γ M A -> BetaStep M N -> HasType Γ N A" "Metatheory/STLC/Typing.lean"
      , thm "strong_normalization" "HasType Γ M A -> SN M" "Metatheory/STLC/Normalization.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/STLC/Typing.lean"
          members := ["subject_reduction"] }
      , { path := "Metatheory/STLC/Normalization.lean"
          members := ["strong_normalization"] }
      ]
  , .heading 3 (renderMetatheoryHeading .extendedSTLC)
  , .theoremItems
      [ thm "progress" "HasType [] M A -> IsValue M ∨ exists N, M ⟶ N" "Metatheory/STLCext/Typing.lean"
      , thm "strong_normalization" "HasType Γ M A -> SN M" "Metatheory/STLCext/Normalization.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/STLCext/Typing.lean"
          members := ["subject_reduction", "progress"] }
      , { path := "Metatheory/STLCext/Normalization.lean"
          members := ["strong_normalization"] }
      ]
  , .heading 3 (renderMetatheoryHeading .stlcWithBooleans)
  , .theoremItems
      [ thm "cbv_deterministic" "Deterministic CBVStep" "Metatheory/STLCextBool/CBV.lean"
      , thm "confluence" "M ⟶* N1 -> M ⟶* N2 -> exists P, N1 ⟶* P /\\ N2 ⟶* P" "Metatheory/STLCextBool/Confluence.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/STLCextBool/Typing.lean"
          members := ["subject_reduction", "progress"] }
      , { path := "Metatheory/STLCextBool/Confluence.lean"
          members := ["confluence"] }
      , { path := "Metatheory/STLCextBool/CBV.lean"
          members := ["cbv_deterministic", "cbv_confluent"] }
      , { path := "Metatheory/STLCextBool/Normalization.lean"
          members := ["strong_normalization"] }
      ]
  , .heading 3 (renderMetatheoryHeading .trsProofComparison)
  , .theoremItems
      [ thm "confluence_via_diamond" "Confluent TinyStep" "Metatheory/TRS/DiamondComparison.lean"
      , thm "confluence_via_newman" "Confluent TinyStep" "Metatheory/TRS/DiamondComparison.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/TRS/DiamondComparison.lean"
          members := ["confluence_via_diamond", "confluence_via_newman"] }
      ]
  , .heading 3 (renderMetatheoryHeading .firstOrderTRS)
  , .theoremItems
      [ thm "terminating_of_kbo" "KBO orientation of all rules -> Terminating rules" "Metatheory/TRS/FirstOrder/Ordering.lean"
      , thm "confluent_of_knuthBendixComplete" "Knuth-Bendix completion certificate -> Confluent" "Metatheory/TRS/FirstOrder/Confluence.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/TRS/FirstOrder/Ordering.lean"
          members := ["terminating_of_kbo", "terminating_of_lpo"] }
      , { path := "Metatheory/TRS/FirstOrder/Confluence.lean"
          members := ["confluent_of_knuthBendixComplete"] }
      ]
  , .heading 3 (renderMetatheoryHeading .systemF)
  , .theoremItems
      [ thm "subject_reduction" "(Γ ⊢ M : τ) -> M.Step N -> (Γ ⊢ N : τ)" "Metatheory/SystemF/SubjectReduction.lean"
      , thm "progress" "(⊢ M : τ) -> IsValue M ∨ exists N, M.Step N" "Metatheory/SystemF/Typing.lean"
      , thm "strong_normalization" "(Γ ⊢ M : τ) -> SN M" "Metatheory/SystemF/StrongNormalization.lean"
      ]
  , .apiItems
      [ { path := "Metatheory/SystemF/SubjectReduction.lean"
          members := ["subject_reduction", "substitution_typing", "type_substitution_typing"] }
      , { path := "Metatheory/SystemF/Typing.lean"
          members := ["progress"] }
      , { path := "Metatheory/SystemF/Confluence.lean"
          members := ["confluence", "strongStep_confluent"] }
      , { path := "Metatheory/SystemF/Diamond.lean"
          members := ["parRed_diamond"] }
      , { path := "Metatheory/SystemF/StrongNormalization.lean"
          members := ["strong_normalization"] }
      ]
  , .heading 2 (renderMetatheoryHeading .projectStructure)
  , .claimBullets [claimBullet .projectStructureIntro, claimBullet .structureMapScope]
  , .codeBlock "text"
      "Metatheory/\n├── Metatheory.lean\n├── Metrics.lean\n├── Rewriting/\n├── Lambda/\n├── CL/\n├── TRS/\n├── StringRewriting/\n├── STLC/\n├── STLCext/\n├── STLCextBool/\n└── SystemF/"
  , .heading 2 (renderMetatheoryHeading .structureMap)
  , .pathItems
      [ { path := "Metatheory/Rewriting/" }
      , { path := "Metatheory/Lambda/" }
      , { path := "Metatheory/CombinatoryLogic/" }
      , { path := "Metatheory/STLC/" }
      , { path := "Metatheory/STLCext/" }
      , { path := "Metatheory/STLCextBool/" }
      , { path := "Metatheory/SystemF/" }
      , { path := "Metatheory/TRS/" }
      , { path := "Metatheory/StringRewriting/" }
      , { path := "Metatheory/Metrics.lean" }
      , { path := "scripts/check.ps1" }
      ]
  , .heading 2 (renderMetatheoryHeading .proofTechniques)
  , .claimBullets [claimBullet .proofTechniquesIntro]
  , .heading 3 (renderMetatheoryHeading .diamondProperty)
  , .claimBullets [claimBullet .diamondTechniqueSummary]
  , .codeBlock "text"
      "M\n/ \\\nN₁ N₂\n\\ /\nP"
  , .heading 3 (renderMetatheoryHeading .hindleyRosenLemma)
  , .claimBullets [claimBullet .hindleyRosenSummary]
  , .heading 3 (renderMetatheoryHeading .newmanLemma)
  , .claimBullets [claimBullet .newmanLemmaSummary]
  , .heading 3 (renderMetatheoryHeading .logicalRelations)
  , .claimBullets [claimBullet .logicalRelationsSummary]
  , .heading 2 (renderMetatheoryHeading .mathematicalBackground)
  , .claimBullets [claimBullet .mathematicalBackgroundIntro]
  , .heading 3 (renderMetatheoryHeading .deBruijnIndices)
  , .claimBullets [claimBullet .deBruijnSummary]
  , .heading 3 (renderMetatheoryHeading .reflexiveTransitiveClosure)
  , .claimBullets [claimBullet .starClosureSummary]
  , .codeBlock "lean"
      "inductive Star (r : α → α → Prop) : α → α → Prop where\n  | refl : Star r a a\n  | tail : Star r a b → r b c → Star r a c"
  , .heading 3 (renderMetatheoryHeading .confluence)
  , .claimBullets [claimBullet .confluenceSummary]
  , .heading 2 (renderMetatheoryHeading .apiReference)
  , .claimBullets [claimBullet .apiReferenceIntro]
  , .heading 3 (renderMetatheoryHeading .coreDefinitions)
  , .codeBlock "lean"
      "def Joinable (r : α → α → Prop) (a b : α) : Prop :=\n  ∃ c, Star r a c ∧ Star r b c\n\ndef Diamond (r : α → α → Prop) : Prop :=\n  ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d\n\ndef Confluent (r : α → α → Prop) : Prop :=\n  ∀ a b c, Star r a b → Star r a c → Joinable r b c"
  , .heading 3 (renderMetatheoryHeading .lambdaCalculusApi)
  , .codeBlock "lean"
      "inductive Term : Type where\n  | var : Nat → Term\n  | app : Term → Term → Term\n  | lam : Term → Term\n\ndef subst (j : Nat) (N : Term) : Term → Term\ninductive BetaStep : Term → Term → Prop"
  , .heading 3 (renderMetatheoryHeading .combinatoryLogicApi)
  , .codeBlock "lean"
      "inductive Term : Type where\n  | S : Term\n  | K : Term\n  | app : Term → Term → Term\n\ndef I : Term := S ⬝ K ⬝ K\ninductive WeakStep : Term → Term → Prop"
  , .heading 3 (renderMetatheoryHeading .stlcApi)
  , .codeBlock "lean"
      "inductive Ty : Type where\n  | base : Nat → Ty\n  | arr : Ty → Ty → Ty\n\ninductive HasType : Context → Term → Ty → Prop\n\ndef SN (M : Term) : Prop := Acc (fun a b => BetaStep b a) M"
  , .heading 3 (renderMetatheoryHeading .extendedStlcApi)
  , .codeBlock "lean"
      "inductive Ty where\n  | base : Nat → Ty\n  | arr : Ty → Ty → Ty\n  | prod : Ty → Ty → Ty\n  | sum : Ty → Ty → Ty\n  | unit : Ty"
  , .heading 2 (renderMetatheoryHeading .references)
  , .claimBullets [claimBullet .referencesIntro]
  , .heading 3 (renderMetatheoryHeading .papers)
  , .claimBullets [claimBullet .papersReferenceSummary]
  , .codeBlock "markdown"
      "1. Takahashi (1995). Parallel Reductions in λ-Calculus.\n2. Newman (1942). On Theories with a Combinatorial Definition of Equivalence.\n3. van Oostrom (1994). Confluence for Abstract and Higher-Order Rewriting.\n4. Tait (1967). Intensional Interpretations of Functionals of Finite Type I.\n5. Hindley (1969). An Abstract Church-Rosser Theorem."
  , .heading 3 (renderMetatheoryHeading .books)
  , .claimBullets [claimBullet .booksReferenceSummary]
  , .codeBlock "markdown"
      "1. Barendregt (1984). The Lambda Calculus.\n2. Terese (2003). Term Rewriting Systems.\n3. Girard, Lafont, and Taylor (1989). Proofs and Types.\n4. Pierce et al. (2023). Software Foundations, Volume 2."
  , .heading 3 (renderMetatheoryHeading .relatedFormalizations)
  , .claimBullets [claimBullet .relatedFormalizationsSummary]
  , .pathItems
      [ { path := "https://softwarefoundations.cis.upenn.edu/" }
      , { path := "https://github.com/fblanqui/color" }
      , { path := "https://isabelle.in.tum.de/nominal/" }
      , { path := "https://plfa.github.io/" }
      ]
  , .heading 2 (renderMetatheoryHeading .contributing)
  , .claimBullets [claimBullet .contributingSummary]
  , .heading 3 (renderMetatheoryHeading .developmentGuidelines)
  , .claimBullets
      [ claimBullet .devGuidelineNoSorry
      , claimBullet .devGuidelineDocstrings
      , claimBullet .devGuidelineReferences
      , claimBullet .devGuidelineStyle
      ]
  , .heading 3 (renderMetatheoryHeading .runningTests)
  , .claimBullets [claimBullet .runningTestsSummary]
  , .codeBlock "bash"
      "lake build"
  , .heading 2 (renderMetatheoryHeading .license)
  , .claimBullets [claimBullet .licenseSummary]
  , .heading 2 (renderMetatheoryHeading .acknowledgments)
  , .claimBullets [claimBullet .acknowledgmentSummary]
  ]
def metatheoryReadmeMarkdown : String :=
  renderDoc metatheoryReadmeBlocks

#eval metatheoryReadmeMarkdown

inductive ParsedMetatheoryStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : MetatheoryClaim)
  | claimLine (claim : MetatheoryClaim)
  deriving Repr

def parseSelectedStructuredMetatheoryLine? (line : String) : Option ParsedMetatheoryStructuredLine :=
  match parseTechnicalLine? metatheoryReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines metatheoryReadmeBlocks).contains line then
        match parseClaimBulletLine? parseMetatheoryClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseMetatheoryClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredMetatheoryLines : List String :=
  technicalLines metatheoryReadmeBlocks ++
  claimBulletLines metatheoryReadmeBlocks ++
  [ ensurePeriod (renderMetatheoryClaim .titleScope)
  , ensurePeriod (renderMetatheoryClaim .overviewSummary)
  , ensurePeriod (renderMetatheoryClaim .noSorriesPolicy)
  , ensurePeriod (renderMetatheoryClaim .keyTheoremsIntro)
  , ensurePeriod (renderMetatheoryClaim .projectStructureIntro)
  ]

def metatheoryHardAuditPasses : Bool :=
  metatheoryReadmeBlocks.all (blockPassesHardAuditWith parseMetatheoryClaimLine? parseMetatheoryHeadingLine?)

theorem metatheory_hard_audit :
    metatheoryHardAuditPasses = true := by
  native_decide

def metatheoryHeadingImageCheck : Bool :=
  headingRenderImageCheck parseMetatheoryHeadingLine? renderMetatheoryHeading metatheoryReadmeBlocks

theorem metatheory_heading_images :
    metatheoryHeadingImageCheck = true := by
  native_decide

theorem metatheory_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries metatheoryReadmeBlocks) :
    ∃ h, parseMetatheoryHeadingLine? txt = some h ∧ renderMetatheoryHeading h = txt := by
  exact headingRenderImageWitness
    parseMetatheoryHeadingLine? renderMetatheoryHeading metatheoryReadmeBlocks
    metatheory_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List MetatheoryClaim)) (surface : String)
    (c : MetatheoryClaim) : List (String × List MetatheoryClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List MetatheoryClaim) :=
  allMetatheoryClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderMetatheoryClaim c) c) []

def ambiguousClaimSurfaces : List (String × List MetatheoryClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allMetatheoryClaims.filter (fun c =>
    parseMetatheoryClaimLine? (renderMetatheoryClaim c) != some c)
  if fails.isEmpty then
    "Metatheory parse-back check: all claim lines roundtrip"
  else
    s!"Metatheory parse-back failures: {repr fails}"

#eval
  if metatheoryHardAuditPasses then
    "Metatheory hard audit: no prose-bearing bypass blocks detected"
  else
    "Metatheory hard audit: violation detected"

#eval
  let fails := selectedStructuredMetatheoryLines.filter
    (fun line =>
      match parseSelectedStructuredMetatheoryLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "Metatheory parse-back check: selected headings + bullet families roundtrip"
  else
    s!"Metatheory structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "Metatheory ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"Metatheory ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.MetatheoryReadmeCompositional
