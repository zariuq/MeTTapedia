import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.LanguagesReadmeCompositional

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
private def formalization_N := regN "formalization"
private def pipeline_N := regN "pipeline"
private def map_N := regN "map"
private def status_N := regN "status"
private def file_N := regN "file"

inductive LanguagesClaim where
  | languagesFormalizeLinguisticsAndProcessCalculi
  | gfFormalizationScope
  | gfCzechCoverage
  | gfEnglishCoverage
  | gfSemanticBridgePipeline
  | gfProofStatus
  | gfReadmeReference
  | sumoTopDownRepair
  | sumoComparesThreeSources
  | sumoFullPipeline
  | sumoHierarchyAsRewriteSystem
  | sumoHasSixRepairPatterns
  | sumoAbstractFileRole
  | sumoBridgeFileRole
  | sumoNttFileRole
  | sumoRepairRunnerRole
  | sumoAxiomCensusRole
  | sumoRepairLogRole
  | sumoOriginalReferenceRole
  | sumoStatusStrataComplete
  | sumoStatusRepairDecisions
  | sumoStatusFoetFixes
  | sumoStatusCheckLangTyping
  | sumoStatusClassAnalysis
  | sumoStatusRelationTyping
  | sumoStatusTransitiveClosure
  | sumoStatusPainAttributeConflict
  | sumoStatusBuildClean
  | processCalculiFormalizationScope
  | processCalculiIncludesEncodingSimulation
  | processCalculiPiStats
  | processCalculiRhoStats
  | processCalculiProofStatus
  | processCalculiReadmeReference
  deriving Repr, DecidableEq, BEq

def renderLanguagesClaim : LanguagesClaim → String
  | .languagesFormalizeLinguisticsAndProcessCalculi =>
      mkPresPos (properNameNP "Mettapedia/Languages")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "formal linguistics, natural language semantics, and process calculi"))
  | .gfFormalizationScope =>
      mkPresPos (properNameNP "GF")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "a Lean 4 GF RGL subset with 170 abstract signatures, two concrete grammars, and a verified semantic bridge"))
  | .gfCzechCoverage =>
      mkPresPos (properNameNP "The Czech grammar")
        (complV2 (mkV2 (regV "include")) (properNameNP "14 declension paradigms, verb conjugation, adjectives, pronouns, and numerals"))
  | .gfEnglishCoverage =>
      mkPresPos (properNameNP "The English grammar")
        (complV2 (mkV2 (regV "include")) (properNameNP "full clause construction with tense, aspect, polarity, do-support, and relative clauses"))
  | .gfSemanticBridgePipeline =>
      mkPresPos (properNameNP "The semantic bridge")
        (copulaNP (properNameNP "GF -> Pattern -> Store -> QFormula -> BinaryEvidence -> NTT"))
  | .gfProofStatus =>
      mkPresNeg (properNameNP "The GF module")
        (complV2 (mkV2 (regV "contain")) (properNameNP "sorries or axioms"))
  | .gfReadmeReference =>
      mkPresPos (properNameNP "GF/README.md")
        (complV2 (mkV2 (regV "contain")) (properNameNP "the full architecture and file map"))
  | .sumoTopDownRepair =>
      mkPresPos (properNameNP "GF/SUMO")
        (complV2 (mkV2 (regV "run")) (properNameNP "top-down SUMO ontology repair through the GF-OSLF-WM pipeline"))
  | .sumoComparesThreeSources =>
      mkPresPos (properNameNP "The SUMO repair lane")
        (complV2 (mkV2 (regV "compare")) (properNameNP "SUMO KIF, Enache's SUMO-GF encoding, and the flattened Lean encoding"))
  | .sumoFullPipeline =>
      mkPresPos (properNameNP "The full SUMO pipeline")
        (copulaNP (properNameNP "SUMO KIF -> GF Pattern -> GSLT -> OSLF -> WM checkLang"))
  | .sumoHierarchyAsRewriteSystem =>
      mkPresPos (properNameNP "The class hierarchy")
        (copulaNP (properNameNP "a rewrite system with proven Galois connection and NTT extraction"))
  | .sumoHasSixRepairPatterns =>
      mkPresPos (properNameNP "The SUMO lane")
        (complV2 (mkV2 (regV "use")) (properNameNP "six automated repair patterns"))
  | .sumoAbstractFileRole =>
      mkPresPos (properNameNP "SumoAbstract.lean")
        (complV2 (mkV2 (regV "contain")) (properNameNP "FOET-relevant classes, function signatures, and transitive closure"))
  | .sumoBridgeFileRole =>
      mkPresPos (properNameNP "SumoOSLFBridge.lean")
        (complV2 (mkV2 (regV "contain")) (properNameNP "pipeline bridge and proven Galois connection with diagnostics"))
  | .sumoNttFileRole =>
      mkPresPos (properNameNP "SumoNTT.lean")
        (complV2 (mkV2 (regV "contain")) (properNameNP "GSLT hierarchy, NTT extraction, and WM checkLang evaluation"))
  | .sumoRepairRunnerRole =>
      mkPresPos (properNameNP "SumoRepairRunner.lean")
        (complV2 (mkV2 (regV "perform")) (properNameNP "three-source diffs with disagreement flags"))
  | .sumoAxiomCensusRole =>
      mkPresPos (properNameNP "SumoAxiomCensus.lean")
        (complV2 (mkV2 (regV "provide")) (properNameNP "per-concept usage evidence"))
  | .sumoRepairLogRole =>
      mkPresPos (properNameNP "RepairLog.lean")
        (complV2 (mkV2 (regV "track")) (properNameNP "repair decisions and strengthening proposals"))
  | .sumoOriginalReferenceRole =>
      mkPresPos (properNameNP "original/")
        (copulaNP (properNameNP "a read-only Enache and Angelov SUMO-GF reference"))
  | .sumoStatusStrataComplete =>
      mkPresPos (properNameNP "Layer 1")
        (copulaNP (properNameNP "complete with strata 0 and 1 coverage"))
  | .sumoStatusRepairDecisions =>
      mkPresPos (properNameNP "The current log")
        (copulaNP (properNameNP "20 repair decisions with 19 automatable"))
  | .sumoStatusFoetFixes =>
      mkPresPos (properNameNP "FOET KIF")
        (copulaNP (properNameNP "12 applied fixes across syntax, argument swaps, and typing"))
  | .sumoStatusCheckLangTyping =>
      mkPresPos (properNameNP "checkLang")
        (complV2 (mkV2 (regV "prove")) (properNameNP "that contraryAttribute Pleasure Pain is ill-typed"))
  | .sumoStatusClassAnalysis =>
      mkPresPos (properNameNP "The class census")
        (copulaNP (properNameNP "53 analyzed classes with agreement, missing, flattened, and FOET-only buckets"))
  | .sumoStatusRelationTyping =>
      mkPresPos (properNameNP "Relation typing")
        (copulaNP (properNameNP "three issues found and one fixed"))
  | .sumoStatusTransitiveClosure =>
      mkPresPos (properNameNP "Transitive closure")
        (copulaNP (properNameNP "54 direct edges with full closure diagnostics"))
  | .sumoStatusPainAttributeConflict =>
      mkPresPos (properNameNP "Pain-Attribute conflict")
        (copulaNP (properNameNP "automatically detected through coercion-path analysis"))
  | .sumoStatusBuildClean =>
      mkPresPos (properNameNP "All SUMO files" .AgP3Pl)
        (copulaAdj "clean with zero sorries")
  | .processCalculiFormalizationScope =>
      mkPresPos (properNameNP "ProcessCalculi")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "pi-calculus and rho-calculus with operational semantics, structural congruence, and OSLF instances"))
  | .processCalculiIncludesEncodingSimulation =>
      mkPresPos (properNameNP "The process calculi lane")
        (complV2 (mkV2 (regV "include")) (properNameNP "Lybech pi-to-rho forward simulation and Meredith spice calculus"))
  | .processCalculiPiStats =>
      mkPresPos (properNameNP "The pi-calculus module")
        (copulaNP (properNameNP "16 files for the asynchronous choice-free fragment"))
  | .processCalculiRhoStats =>
      mkPresPos (properNameNP "The rho-calculus module")
        (copulaNP (properNameNP "11 files with locally nameless COMM reduction and spice rule"))
  | .processCalculiProofStatus =>
      mkPresNeg (properNameNP "The ProcessCalculi module")
        (complV2 (mkV2 (regV "contain")) (properNameNP "sorries"))
  | .processCalculiReadmeReference =>
      mkPresPos (properNameNP "ProcessCalculi/README.md")
        (complV2 (mkV2 (regV "contain")) (properNameNP "detailed architecture and proof status"))

def allLanguagesClaims : List LanguagesClaim :=
  [ .languagesFormalizeLinguisticsAndProcessCalculi
  , .gfFormalizationScope
  , .gfCzechCoverage
  , .gfEnglishCoverage
  , .gfSemanticBridgePipeline
  , .gfProofStatus
  , .gfReadmeReference
  , .sumoTopDownRepair
  , .sumoComparesThreeSources
  , .sumoFullPipeline
  , .sumoHierarchyAsRewriteSystem
  , .sumoHasSixRepairPatterns
  , .sumoAbstractFileRole
  , .sumoBridgeFileRole
  , .sumoNttFileRole
  , .sumoRepairRunnerRole
  , .sumoAxiomCensusRole
  , .sumoRepairLogRole
  , .sumoOriginalReferenceRole
  , .sumoStatusStrataComplete
  , .sumoStatusRepairDecisions
  , .sumoStatusFoetFixes
  , .sumoStatusCheckLangTyping
  , .sumoStatusClassAnalysis
  , .sumoStatusRelationTyping
  , .sumoStatusTransitiveClosure
  , .sumoStatusPainAttributeConflict
  , .sumoStatusBuildClean
  , .processCalculiFormalizationScope
  , .processCalculiIncludesEncodingSimulation
  , .processCalculiPiStats
  , .processCalculiRhoStats
  , .processCalculiProofStatus
  , .processCalculiReadmeReference
  ]

def parseLanguagesClaimLine? (line : String) : Option LanguagesClaim :=
  let norm := stripTerminalPeriod line
  allLanguagesClaims.find? (fun c => renderLanguagesClaim c = norm)

inductive LanguagesHeading where
  | title
  | modules
  | gf
  | gfSumo
  | sumoFileMap
  | sumoCurrentStatus
  | processCalculi
  deriving Repr, DecidableEq, BEq

def renderLanguagesHeading : LanguagesHeading → String
  | .title =>
      headingPlNP (linUseN (regN "language"))
  | .modules =>
      headingPlNP (linUseN module_N)
  | .gf =>
      headingNP (linAdjCN (linPositA (regA "GF")) (linUseN formalization_N))
  | .gfSumo =>
      headingNP (linAdjCN (linPositA (compoundA "GF SUMO")) (linUseN pipeline_N))
  | .sumoFileMap =>
      headingNP (linAdjCN (linPositA (regA "SUMO file")) (linUseN map_N))
  | .sumoCurrentStatus =>
      headingNP (linAdjCN (linPositA (regA "SUMO current")) (linUseN status_N))
  | .processCalculi =>
      headingNP (linAdjCN (linPositA (compoundA "process calculi")) (linUseN formalization_N))

def allLanguagesHeadings : List LanguagesHeading :=
  [ .title, .modules, .gf, .gfSumo, .sumoFileMap, .sumoCurrentStatus, .processCalculi ]

def parseLanguagesHeadingLine? (line : String) : Option LanguagesHeading :=
  allLanguagesHeadings.find? (fun h => renderLanguagesHeading h = line)

private def claimBullet (c : LanguagesClaim) : ClaimBullet :=
  { text := renderLanguagesClaim c }

def languagesReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderLanguagesHeading .title)
  , .paragraph [renderLanguagesClaim .languagesFormalizeLinguisticsAndProcessCalculi]
  , .heading 2 (renderLanguagesHeading .modules)
  , .heading 3 (renderLanguagesHeading .gf)
  , .paragraph
      [ renderLanguagesClaim .gfFormalizationScope
      , renderLanguagesClaim .gfCzechCoverage
      , renderLanguagesClaim .gfEnglishCoverage
      ]
  , .claimBullets
      [ claimBullet .gfSemanticBridgePipeline
      , claimBullet .gfProofStatus
      , claimBullet .gfReadmeReference
      ]
  , .heading 4 (renderLanguagesHeading .gfSumo)
  , .paragraph
      [ renderLanguagesClaim .sumoTopDownRepair
      , renderLanguagesClaim .sumoComparesThreeSources
      , renderLanguagesClaim .sumoFullPipeline
      , renderLanguagesClaim .sumoHierarchyAsRewriteSystem
      ]
  , .claimBullets [claimBullet .sumoHasSixRepairPatterns]
  , .heading 4 (renderLanguagesHeading .sumoFileMap)
  , .fileRef "SumoAbstract.lean" (renderLanguagesClaim .sumoAbstractFileRole)
  , .fileRef "SumoOSLFBridge.lean" (renderLanguagesClaim .sumoBridgeFileRole)
  , .fileRef "SumoNTT.lean" (renderLanguagesClaim .sumoNttFileRole)
  , .fileRef "SumoRepairRunner.lean" (renderLanguagesClaim .sumoRepairRunnerRole)
  , .fileRef "SumoAxiomCensus.lean" (renderLanguagesClaim .sumoAxiomCensusRole)
  , .fileRef "RepairLog.lean" (renderLanguagesClaim .sumoRepairLogRole)
  , .fileRef "original/" (renderLanguagesClaim .sumoOriginalReferenceRole)
  , .heading 4 (renderLanguagesHeading .sumoCurrentStatus)
  , .claimBullets
      [ claimBullet .sumoStatusStrataComplete
      , claimBullet .sumoStatusRepairDecisions
      , claimBullet .sumoStatusFoetFixes
      , claimBullet .sumoStatusCheckLangTyping
      , claimBullet .sumoStatusClassAnalysis
      , claimBullet .sumoStatusRelationTyping
      , claimBullet .sumoStatusTransitiveClosure
      , claimBullet .sumoStatusPainAttributeConflict
      , claimBullet .sumoStatusBuildClean
      ]
  , .heading 3 (renderLanguagesHeading .processCalculi)
  , .paragraph
      [ renderLanguagesClaim .processCalculiFormalizationScope
      , renderLanguagesClaim .processCalculiIncludesEncodingSimulation
      ]
  , .claimBullets
      [ claimBullet .processCalculiPiStats
      , claimBullet .processCalculiRhoStats
      , claimBullet .processCalculiProofStatus
      , claimBullet .processCalculiReadmeReference
      ]
  ]

def languagesReadmeMarkdown : String :=
  renderDoc languagesReadmeBlocks

#eval languagesReadmeMarkdown

inductive ParsedLanguagesStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : LanguagesClaim)
  | claimLine (claim : LanguagesClaim)
  deriving Repr

def parseSelectedStructuredLanguagesLine? (line : String) : Option ParsedLanguagesStructuredLine :=
  match parseTechnicalLine? languagesReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines languagesReadmeBlocks).contains line then
        match parseClaimBulletLine? parseLanguagesClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseLanguagesClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredLanguagesLines : List String :=
  technicalLines languagesReadmeBlocks ++
  claimBulletLines languagesReadmeBlocks ++
  [ ensurePeriod (renderLanguagesClaim .languagesFormalizeLinguisticsAndProcessCalculi)
  , ensurePeriod (renderLanguagesClaim .gfFormalizationScope)
  , ensurePeriod (renderLanguagesClaim .sumoTopDownRepair)
  , ensurePeriod (renderLanguagesClaim .processCalculiFormalizationScope)
  ]

def languagesHardAuditPasses : Bool :=
  languagesReadmeBlocks.all (blockPassesHardAuditWith parseLanguagesClaimLine? parseLanguagesHeadingLine?)

theorem languages_hard_audit :
    languagesHardAuditPasses = true := by
  native_decide

def languagesHeadingImageCheck : Bool :=
  headingRenderImageCheck parseLanguagesHeadingLine? renderLanguagesHeading languagesReadmeBlocks

theorem languages_heading_images :
    languagesHeadingImageCheck = true := by
  native_decide

theorem languages_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries languagesReadmeBlocks) :
    ∃ h, parseLanguagesHeadingLine? txt = some h ∧ renderLanguagesHeading h = txt := by
  exact headingRenderImageWitness
    parseLanguagesHeadingLine? renderLanguagesHeading languagesReadmeBlocks
    languages_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List LanguagesClaim)) (surface : String)
    (c : LanguagesClaim) : List (String × List LanguagesClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List LanguagesClaim) :=
  allLanguagesClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderLanguagesClaim c) c) []

def ambiguousClaimSurfaces : List (String × List LanguagesClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allLanguagesClaims.filter (fun c =>
    parseLanguagesClaimLine? (renderLanguagesClaim c) != some c)
  if fails.isEmpty then
    "Languages parse-back check: all claim lines roundtrip"
  else
    s!"Languages parse-back failures: {repr fails}"

#eval
  if languagesHardAuditPasses then
    "Languages hard audit: no prose-bearing bypass blocks detected"
  else
    "Languages hard audit: violation detected"

#eval
  let fails := selectedStructuredLanguagesLines.filter
    (fun line =>
      match parseSelectedStructuredLanguagesLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "Languages parse-back check: selected headings + bullet families roundtrip"
  else
    s!"Languages structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "Languages ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"Languages ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.LanguagesReadmeCompositional
