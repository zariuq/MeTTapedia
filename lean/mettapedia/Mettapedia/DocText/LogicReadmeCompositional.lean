import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.LogicReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def module_N := regN "module"
private def network_N := regN "network"
private def bridge_N := regN "bridge"
private def tree_N := regN "tree"
private def regression_N := regN "regression"
private def theorem_N := regN "theorem"
private def proof_N := regN "proof"
private def overview_N := regN "overview"
private def thesis_N := regN "thesis"
private def subdirectory_N := regN "subdirectory"
private def package_N := regN "package"
private def family_N := regN "family"
private def index_N := regN "index"
private def graph_N := regN "graph"
private def insight_N := regN "insight"
private def fix_N := regN "fix"
private def build_N := regN "build"
private def reference_N := regN "reference"
private def section_N := regN "section"
private def command_N := regN "command"
private def canary_N := regN "canary"
private def purpose_N := regN "purpose"

inductive LogicClaim where
  | moduleFormalizesPlnAndBridges
  | moduleConnectsProbabilityHeytingQuantaleAndSolomonoff
  | semanticsDecisionTreePath
  | chapter11RegressionHasOneCommand
  | chapter11RegressionHasCheckScripts
  | chapter11RegressionHasPrimaryModules
  | chapter11RegressionHasCanarySuite
  | chapter12RegressionHasOneCommand
  | chapter12RegressionHasWrappersAndCanaries
  | chapter13RegressionHasOneCommand
  | chapter13RegressionHasSelectorCoverageCanaries
  | unificationThesisStatesEvidenceUnifiesFrameworks
  | unificationThesisStatesExchangeableCollapse
  | criticalTheoremsSectionSummarizesAnchors
  | nbBridgeTheoremExists
  | knnBridgeTheoremExists
  | rankingTransferTheoremsExist
  | tierCompositionSpineExists
  | abductionCaveatIsFormalized
  | mettaParityAnchorsAreTracked
  | narsCorrespondencePackageExists
  | narsPackageHasFourFamilies
  | subdirectoriesAreCataloged
  | fileIndexIsGroupedByPurpose
  | dependencyGraphSectionExists
  | keyInsightDistinguishesEvidenceAndInterval
  | weightSpaceFixIsDocumented
  | buildSectionListsCommands
  | referencesSectionListsSources
  deriving Repr, DecidableEq, BEq

def renderLogicClaim : LogicClaim → String
  | .moduleFormalizesPlnAndBridges =>
      mkPresPos (properNameNP "Mettapedia Logic")
        (complV2 (mkV2 (regV "formalize"))
          (properNameNP "probabilistic logic networks with theorem-level bridges"))
  | .moduleConnectsProbabilityHeytingQuantaleAndSolomonoff =>
      mkPresPos (properNameNP "The module")
        (complV2 (mkV2 (regV "connect"))
          (properNameNP "probability theory, Heyting semantics, quantales, and Solomonoff-style prediction"))
  | .semanticsDecisionTreePath =>
      mkPresPos (properNameNP "The semantics decision tree")
        (copulaNP (properNameNP "`Mettapedia/Logic/SemanticsDecisionTree.lean`"))
  | .chapter11RegressionHasOneCommand =>
      mkPresPos (properNameNP "Chapter 11 quantifier regression")
        (copulaNP (properNameNP "a one-command build target"))
  | .chapter11RegressionHasCheckScripts =>
      mkPresPos (properNameNP "Chapter 11 quantifier regression")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "`check_ch11_quantifiers.sh` and `check_ch11_fuzzy_syllogism.sh`"))
  | .chapter11RegressionHasPrimaryModules =>
      mkPresPos (properNameNP "Chapter 11 quantifier regression")
        (complV2 (mkV2 (regV "track"))
          (properNameNP "primary modules for quantifier, fuzzy, and ITV bridges"))
  | .chapter11RegressionHasCanarySuite =>
      mkPresPos (properNameNP "Chapter 11 quantifier regression")
        (complV2 (mkV2 (regV "track"))
          (linDetCN aIndefArt (linAdjCN (linPositA (regA "broad")) (linUseN canary_N))))
  | .chapter12RegressionHasOneCommand =>
      mkPresPos (properNameNP "Chapter 12 intensional inheritance regression")
        (copulaNP (properNameNP "a one-command build target"))
  | .chapter12RegressionHasWrappersAndCanaries =>
      mkPresPos (properNameNP "Chapter 12 intensional inheritance regression")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "selector-specialized one-call final-bundle wrappers with mixed-policy non-equivalence canaries"))
  | .chapter13RegressionHasOneCommand =>
      mkPresPos (properNameNP "Chapter 13 inference-control regression")
        (copulaNP (properNameNP "a one-command build target"))
  | .chapter13RegressionHasSelectorCoverageCanaries =>
      mkPresPos (properNameNP "Chapter 13 inference-control regression")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "selector, ranking, and coverage theorems with composed core modules and positive and negative canaries"))
  | .unificationThesisStatesEvidenceUnifiesFrameworks =>
      mkPresPos (properNameNP "The unification thesis")
        (complV2 (mkV2 (regV "state"))
          (properNameNP "PLN evidence unifies quantale, Heyting, and Bayesian views"))
  | .unificationThesisStatesExchangeableCollapse =>
      mkPresPos (properNameNP "The unification thesis")
        (complV2 (mkV2 (regV "state"))
          (properNameNP "exchangeable binary Solomonoff prediction collapses to evidence counts"))
  | .criticalTheoremsSectionSummarizesAnchors =>
      mkPresPos (properNameNP "The critical theorem section")
        (complV2 (mkV2 (regV "summarize"))
          (properNameNP "Frechet bounds, quantale transitivity, De Finetti, and Solomonoff collapse"))
  | .nbBridgeTheoremExists =>
      mkPresPos (properNameNP "`PLN_tensorStrength_eq_nbPosterior`")
        (copulaNP (properNameNP "the Naive Bayes bridge theorem"))
  | .knnBridgeTheoremExists =>
      mkPresPos (properNameNP "`PLN_hplusPos_eq_knnRelevance`")
        (copulaNP (properNameNP "the k-NN bridge theorem"))
  | .rankingTransferTheoremsExist =>
      mkPresPos (properNameNP "Premise-selection ranking transfer")
        (copulaNP (properNameNP "a theorem family in `PremiseSelectionOptimality.lean`"))
  | .tierCompositionSpineExists =>
      mkPresPos (properNameNP "Tier A-to-B composition")
        (copulaNP (properNameNP "a proven spine in `PLNXiDerivedBNRules.lean`"))
  | .abductionCaveatIsFormalized =>
      mkPresPos (properNameNP "Collider abduction caveat")
        (copulaNP (properNameNP "a formalized approximation warning"))
  | .mettaParityAnchorsAreTracked =>
      mkPresPos (properNameNP "MeTTa formula parity")
        (copulaNP (properNameNP "tracked with theorem anchors and a checklist"))
  | .narsCorrespondencePackageExists =>
      mkPresPos (properNameNP "`PLNNARSRuleCorrespondence.lean`")
        (copulaNP (properNameNP "the consolidated PLN↔NARS comparison package"))
  | .narsPackageHasFourFamilies =>
      mkPresPos (properNameNP "The PLN↔NARS package")
        (complV2 (mkV2 (regV "bundle"))
          (properNameNP "confidence transforms, rule correspondences, revision coherence, and informativeness adjunction"))
  | .subdirectoriesAreCataloged =>
      mkPresPos (properNameNP "Subdirectories" .AgP3Pl)
        (copulaNP (properNameNP "cataloged with scope and file counts"))
  | .fileIndexIsGroupedByPurpose =>
      mkPresPos (properNameNP "The file index")
        (copulaNP (properNameNP "grouped by purpose"))
  | .dependencyGraphSectionExists =>
      mkPresPos (properNameNP "The dependency graph section")
        (copulaNP (properNameNP "available with bridge and submodule highlights"))
  | .keyInsightDistinguishesEvidenceAndInterval =>
      mkPresPos (properNameNP "The key insight")
        (complV2 (mkV2 (regV "distinguish"))
          (properNameNP "evidence-valued PLN from interval probability semantics"))
  | .weightSpaceFixIsDocumented =>
      mkPresPos (properNameNP "The weight-space bug fix")
        (copulaNP (properNameNP "documented with corrected formulas"))
  | .buildSectionListsCommands =>
      mkPresPos (properNameNP "The build section")
        (complV2 (mkV2 (regV "list"))
          (properNameNP "core, quantifier, and full-build commands"))
  | .referencesSectionListsSources =>
      mkPresPos (properNameNP "The references section")
        (complV2 (mkV2 (regV "list"))
          (linMassPluralNP (linUseN reference_N)))

def allLogicClaims : List LogicClaim :=
  [ .moduleFormalizesPlnAndBridges
  , .moduleConnectsProbabilityHeytingQuantaleAndSolomonoff
  , .semanticsDecisionTreePath
  , .chapter11RegressionHasOneCommand
  , .chapter11RegressionHasCheckScripts
  , .chapter11RegressionHasPrimaryModules
  , .chapter11RegressionHasCanarySuite
  , .chapter12RegressionHasOneCommand
  , .chapter12RegressionHasWrappersAndCanaries
  , .chapter13RegressionHasOneCommand
  , .chapter13RegressionHasSelectorCoverageCanaries
  , .unificationThesisStatesEvidenceUnifiesFrameworks
  , .unificationThesisStatesExchangeableCollapse
  , .criticalTheoremsSectionSummarizesAnchors
  , .nbBridgeTheoremExists
  , .knnBridgeTheoremExists
  , .rankingTransferTheoremsExist
  , .tierCompositionSpineExists
  , .abductionCaveatIsFormalized
  , .mettaParityAnchorsAreTracked
  , .narsCorrespondencePackageExists
  , .narsPackageHasFourFamilies
  , .subdirectoriesAreCataloged
  , .fileIndexIsGroupedByPurpose
  , .dependencyGraphSectionExists
  , .keyInsightDistinguishesEvidenceAndInterval
  , .weightSpaceFixIsDocumented
  , .buildSectionListsCommands
  , .referencesSectionListsSources
  ]

def parseLogicClaimLine? (line : String) : Option LogicClaim :=
  let norm := stripTerminalPeriod line
  allLogicClaims.find? (fun c => renderLogicClaim c = norm)

inductive LogicHeading where
  | title
  | moduleOverview
  | semanticsDecisionTree
  | chapter11QuantifierRegression
  | chapter12IntensionalInheritanceRegression
  | chapter13InferenceControlRegression
  | unificationThesis
  | criticalProvenTheorems
  | proofsForNbAndKnn
  | proofsForNarsComparison
  | subdirectories
  | fileIndexByPurpose
  | dependencyGraph
  | keyInsight
  | weightSpaceBugFix
  | build
  | references
  deriving Repr, DecidableEq, BEq

private def headingNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassNP cn).s (.NCase .Nom)

private def headingPlNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassPluralNP cn).s (.NCase .Nom)

def renderLogicHeading : LogicHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "Mettapedia")) (linAdjCN (linPositA (regA "logic")) (linUseN module_N)))
  | .moduleOverview =>
      headingNP (linUseN overview_N)
  | .semanticsDecisionTree =>
      headingNP (linAdjCN (linPositA (regA "semantics")) (linUseN tree_N))
  | .chapter11QuantifierRegression =>
      headingNP (linAdjCN (linPositA (compoundA "Chapter-11")) (linAdjCN (linPositA (regA "quantifier")) (linUseN regression_N)))
  | .chapter12IntensionalInheritanceRegression =>
      headingNP (linAdjCN (linPositA (compoundA "Chapter-12")) (linAdjCN (linPositA (regA "intensional")) (linAdjCN (linPositA (regA "inheritance")) (linUseN regression_N))))
  | .chapter13InferenceControlRegression =>
      headingNP (linAdjCN (linPositA (compoundA "Chapter-13")) (linAdjCN (linPositA (compoundA "inference-control")) (linUseN regression_N)))
  | .unificationThesis =>
      headingNP (linAdjCN (linPositA (regA "unification")) (linUseN thesis_N))
  | .criticalProvenTheorems =>
      headingNP (linAdjCN (linPositA (regA "critical")) (linAdjCN (linPositA (regA "proven")) (linUseN theorem_N)))
  | .proofsForNbAndKnn =>
      headingNP (linAdvCN (linUseN proof_N)
        (ppAdv for_Prep (properNameNP "PLN covering NB and k-NN")))
  | .proofsForNarsComparison =>
      headingNP (linAdvCN (linUseN proof_N)
        (ppAdv for_Prep (properNameNP "PLN↔NARS rule comparison")))
  | .subdirectories =>
      headingPlNP (linUseN subdirectory_N)
  | .fileIndexByPurpose =>
      headingNP (linAdvCN (linUseN index_N) (ppAdv by_Prep (linUseN purpose_N |> linMassNP)))
  | .dependencyGraph =>
      headingNP (linAdjCN (linPositA (regA "dependency")) (linUseN graph_N))
  | .keyInsight =>
      headingNP (linAdjCN (linPositA (regA "key")) (linUseN insight_N))
  | .weightSpaceBugFix =>
      headingNP (linAdjCN (linPositA (compoundA "weight-space")) (linUseN fix_N))
  | .build =>
      headingNP (linUseN build_N)
  | .references =>
      headingPlNP (linUseN reference_N)

def allLogicHeadings : List LogicHeading :=
  [ .title
  , .moduleOverview
  , .semanticsDecisionTree
  , .chapter11QuantifierRegression
  , .chapter12IntensionalInheritanceRegression
  , .chapter13InferenceControlRegression
  , .unificationThesis
  , .criticalProvenTheorems
  , .proofsForNbAndKnn
  , .proofsForNarsComparison
  , .subdirectories
  , .fileIndexByPurpose
  , .dependencyGraph
  , .keyInsight
  , .weightSpaceBugFix
  , .build
  , .references
  ]

def parseLogicHeadingLine? (line : String) : Option LogicHeading :=
  allLogicHeadings.find? (fun h => renderLogicHeading h = line)

private def claimBullet (c : LogicClaim) : ClaimBullet :=
  { text := renderLogicClaim c }

def logicReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderLogicHeading .title)
  , .paragraph
      [ renderLogicClaim .moduleFormalizesPlnAndBridges
      , renderLogicClaim .moduleConnectsProbabilityHeytingQuantaleAndSolomonoff
      ]
  , .heading 2 (renderLogicHeading .moduleOverview)
  , .codeBlock ""
      "| Category | Files | Status |\n|----------|-------|--------|\n| Core PLN Inference | 9 | Complete |\n| Weight/Confidence | 2 | Complete |\n| Bounds/Consistency | 2 | Complete |\n| Algebraic Structure | 8 | Complete |\n| Solomonoff/Exchangeability | 6 | Complete |\n| Convergence/ | 4 | Complete |\n| Comparison/ | 3 | Complete |\n| MeasureTheoreticPLN/ | 3 | Complete |\n| PLNQuantaleSemantics/ | 4 | Complete |\n| UniversalPrediction/ | 21 | WIP |\n| Foundations/ | 90+ | Embedded |\n| System Bridges | 4 | Complete |"
  , .heading 2 (renderLogicHeading .semanticsDecisionTree)
  , .claimBullets [claimBullet .semanticsDecisionTreePath]
  , .pathItems [{path := "Mettapedia/Logic/SemanticsDecisionTree.lean"}]
  , .heading 2 (renderLogicHeading .chapter11QuantifierRegression)
  , .claimBullets
      [ claimBullet .chapter11RegressionHasOneCommand
      , claimBullet .chapter11RegressionHasCheckScripts
      , claimBullet .chapter11RegressionHasPrimaryModules
      , claimBullet .chapter11RegressionHasCanarySuite
      ]
  , .codeBlock "bash"
      "cd /home/zar/claude/lean-projects/mettapedia\nulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \\\n  lake build Mettapedia.Logic.PLNFirstOrder.QuantifierRegression"
  , .codeBlock "bash"
      "cd /home/zar/claude/lean-projects/mettapedia\n./scripts/check_ch11_quantifiers.sh\n./scripts/check_ch11_fuzzy_syllogism.sh"
  , .pathItems
      [ {path := "Mettapedia/Logic/PLNFirstOrder/QuantifierSemantics.lean"}
      , {path := "Mettapedia/Logic/PLNFirstOrder/FuzzyQuantifierSemantics.lean"}
      , {path := "Mettapedia/Logic/PLNFirstOrder/FuzzyITVBridge.lean"}
      , {path := "Mettapedia/Logic/PLNFirstOrder/QuantifierCanary.lean"}
      , {path := "Mettapedia/Logic/PLNFirstOrder/QuantifierWorkedExamples.lean"}
      ]
  , .heading 2 (renderLogicHeading .chapter12IntensionalInheritanceRegression)
  , .claimBullets
      [ claimBullet .chapter12RegressionHasOneCommand
      , claimBullet .chapter12RegressionHasWrappersAndCanaries
      ]
  , .codeBlock "bash"
      "cd /home/zar/claude/lean-projects/mettapedia\nulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \\\n  lake build Mettapedia.Logic.PLNIntensionalRegression"
  , .codeBlock "bash"
      "cd /home/zar/claude/lean-projects/mettapedia\n./scripts/check_ch12_intensional.sh"
  , .pathItems
      [ {path := "Mettapedia/Logic/PLNIntensionalWorldModel.lean"}
      , {path := "Mettapedia/Logic/IntensionalInheritanceSolomonoffBridge.lean"}
      , {path := "Mettapedia/Logic/PLNCanonicalAPI.lean"}
      , {path := "Mettapedia/Logic/PLNIntensionalCanary.lean"}
      , {path := "Mettapedia/Logic/PLNIntensionalRegression.lean"}
      ]
  , .heading 2 (renderLogicHeading .chapter13InferenceControlRegression)
  , .claimBullets
      [ claimBullet .chapter13RegressionHasOneCommand
      , claimBullet .chapter13RegressionHasSelectorCoverageCanaries
      ]
  , .codeBlock "bash"
      "cd /home/zar/claude/lean-projects/mettapedia\nulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \\\n  lake build Mettapedia.Logic.PLNInferenceControlRegression"
  , .codeBlock "bash"
      "cd /home/zar/claude/lean-projects/mettapedia\n./scripts/check_ch13_inference_control.sh"
  , .pathItems
      [ {path := "Mettapedia/Logic/PremiseSelectionSelectorSpec.lean"}
      , {path := "Mettapedia/Logic/PremiseSelectionOptimality.lean"}
      , {path := "Mettapedia/Logic/PremiseSelectionRankingStability.lean"}
      , {path := "Mettapedia/Logic/PremiseSelectionCoverage.lean"}
      , {path := "Mettapedia/Logic/PLNInferenceControlCore.lean"}
      , {path := "Mettapedia/Logic/PLNInferenceControlCanary.lean"}
      , {path := "Mettapedia/Logic/PLNInferenceControlRegression.lean"}
      ]
  , .heading 2 (renderLogicHeading .unificationThesis)
  , .claimBullets
      [ claimBullet .unificationThesisStatesEvidenceUnifiesFrameworks
      , claimBullet .unificationThesisStatesExchangeableCollapse
      ]
  , .codeBlock ""
      "PLN BinaryEvidence (n+, n-)\n  -> Quantale (tensor)\n  -> Heyting frame\n  -> Beta statistic\n  -> Solomonoff exchangeable binary collapse"
  , .heading 2 (renderLogicHeading .criticalProvenTheorems)
  , .claimBullets [claimBullet .criticalTheoremsSectionSummarizesAnchors]
  , .codeBlock ""
      "| Theorem | File |\n|---------|------|\n| Frechet bounds | PLNFrechetBounds.lean |\n| PLN consistency | PLNFrechetBounds.lean |\n| Weight-space min | PLNConfidenceWeight.lean |\n| BinaryEvidence not boolean | HeytingValuationOnEvidence.lean |\n| Quantale transitivity | EvidenceQuantale.lean |\n| Solomonoff collapse | SolomonoffExchangeable.lean |\n| De Finetti | DeFinetti.lean |"
  , .heading 2 (renderLogicHeading .proofsForNbAndKnn)
  , .claimBullets
      [ claimBullet .nbBridgeTheoremExists
      , claimBullet .knnBridgeTheoremExists
      , claimBullet .rankingTransferTheoremsExist
      , claimBullet .tierCompositionSpineExists
      , claimBullet .abductionCaveatIsFormalized
      , claimBullet .mettaParityAnchorsAreTracked
      ]
  , .pathItems
      [ {path := "Mettapedia/Logic/PLNBayesNetInference.lean:296"}
      , {path := "Mettapedia/Logic/PremiseSelectionKNN_PLNBridge.lean:111"}
      , {path := "Mettapedia/Logic/PremiseSelectionOptimality.lean:333"}
      , {path := "Mettapedia/Logic/PLNBNCompilation.lean:161"}
      , {path := "Mettapedia/Logic/PLNXiDerivedBNRules.lean:464"}
      , {path := "Mettapedia/Logic/PLNXiDerivedBNRules.lean:1172"}
      , {path := "Mettapedia/Implementation/MettaVerification.lean:77"}
      , {path := "Mettapedia/Implementation/PLNParityChecklist.lean:66"}
      ]
  , .heading 2 (renderLogicHeading .proofsForNarsComparison)
  , .claimBullets
      [ claimBullet .narsCorrespondencePackageExists
      , claimBullet .narsPackageHasFourFamilies
      ]
  , .pathItems [{path := "Mettapedia/Logic/PLNNARSRuleCorrespondence.lean"}]
  , .heading 2 (renderLogicHeading .subdirectories)
  , .claimBullets [claimBullet .subdirectoriesAreCataloged]
  , .codeBlock ""
      "Comparison/ (3 files)\nConvergence/ (4 files)\nFoundations/ (90+ files)\nMeasureTheoreticPLN/ (3 files)\nPLNQuantaleSemantics/ (4 files)\nUniversalPrediction/ (21 files)"
  , .heading 2 (renderLogicHeading .fileIndexByPurpose)
  , .claimBullets [claimBullet .fileIndexIsGroupedByPurpose]
  , .codeBlock ""
      "PLN core, inference rules, weight/confidence, bounds/consistency,\nalgebraic structure, Solomonoff/exchangeability, system bridges,\nanalysis/comparison, and other files are indexed by purpose."
  , .heading 2 (renderLogicHeading .dependencyGraph)
  , .claimBullets [claimBullet .dependencyGraphSectionExists]
  , .codeBlock ""
      "Foundations -> Core inference -> Algebraic semantics -> Bridges\n                      \\-> Quantifier regression -> Chapter 11 canaries\n                      \\-> Intensional regression -> Chapter 12 canaries\n                      \\-> Inference-control regression -> Chapter 13 canaries"
  , .heading 2 (renderLogicHeading .keyInsight)
  , .claimBullets [claimBullet .keyInsightDistinguishesEvidenceAndInterval]
  , .heading 3 (renderLogicHeading .weightSpaceBugFix)
  , .claimBullets [claimBullet .weightSpaceFixIsDocumented]
  , .heading 2 (renderLogicHeading .build)
  , .claimBullets [claimBullet .buildSectionListsCommands]
  , .codeBlock "bash"
      "cd /home/zar/claude/lean-projects/mettapedia\n# Quantifier regression\nlake build Mettapedia.Logic.PLNFirstOrder.QuantifierRegression\n# Intensional inheritance regression\nlake build Mettapedia.Logic.PLNIntensionalRegression\n# Inference-control regression\nlake build Mettapedia.Logic.PLNInferenceControlRegression\n# Core files\nlake build Mettapedia.Logic.PLNBayesNetInference Mettapedia.Logic.PremiseSelectionKNN_PLNBridge\n# Build all (slow)\nlake build"
  , .heading 2 (renderLogicHeading .references)
  , .claimBullets [claimBullet .referencesSectionListsSources]
  , .codeBlock ""
      "Blanchette et al. (2016) Hammering towards QED\nGoertzel et al. Probabilistic Logic Networks\nJakubuv & Urban (2023) Mizar60"
  ]

def logicReadmeMarkdown : String :=
  renderDoc logicReadmeBlocks

#eval logicReadmeMarkdown

inductive ParsedLogicStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : LogicClaim)
  | claimLine (claim : LogicClaim)
  deriving Repr

def parseSelectedStructuredLogicLine? (line : String) : Option ParsedLogicStructuredLine :=
  match parseTechnicalLine? logicReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines logicReadmeBlocks).contains line then
        match parseClaimBulletLine? parseLogicClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseLogicClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredLogicLines : List String :=
  technicalLines logicReadmeBlocks ++
  claimBulletLines logicReadmeBlocks ++
  [ ensurePeriod (renderLogicClaim .moduleFormalizesPlnAndBridges)
  , ensurePeriod (renderLogicClaim .moduleConnectsProbabilityHeytingQuantaleAndSolomonoff)
  ]

def logicHardAuditPasses : Bool :=
  logicReadmeBlocks.all (blockPassesHardAuditWith parseLogicClaimLine? parseLogicHeadingLine?)

theorem logic_hard_audit :
    logicHardAuditPasses = true := by
  native_decide

def logicHeadingImageCheck : Bool :=
  headingRenderImageCheck parseLogicHeadingLine? renderLogicHeading logicReadmeBlocks

theorem logic_heading_images :
    logicHeadingImageCheck = true := by
  native_decide

theorem logic_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries logicReadmeBlocks) :
    ∃ h, parseLogicHeadingLine? txt = some h ∧ renderLogicHeading h = txt := by
  exact headingRenderImageWitness
    parseLogicHeadingLine? renderLogicHeading logicReadmeBlocks
    logic_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List LogicClaim)) (surface : String) (c : LogicClaim) :
    List (String × List LogicClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List LogicClaim) :=
  allLogicClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderLogicClaim c) c) []

def ambiguousClaimSurfaces : List (String × List LogicClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allLogicClaims.filter (fun c =>
    parseLogicClaimLine? (renderLogicClaim c) != some c)
  if fails.isEmpty then
    "Logic parse-back check: all claim lines roundtrip"
  else
    s!"Logic parse-back failures: {repr fails}"

#eval
  if logicHardAuditPasses then
    "Logic hard audit: no prose-bearing bypass blocks detected"
  else
    "Logic hard audit: violation detected"

#eval
  let fails := selectedStructuredLogicLines.filter
    (fun line =>
      match parseSelectedStructuredLogicLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "Logic parse-back check: selected headings + bullet families roundtrip"
  else
    s!"Logic structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "Logic ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"Logic ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.LogicReadmeCompositional
