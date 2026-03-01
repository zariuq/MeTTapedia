import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.BridgeReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def bridge_N := regN "bridge"
private def result_N := regN "result"
private def status_N := regN "status"
private def semantic_N := regN "semantic"
private def interpretation_N := regN "interpretation"
private def distribution_N := regN "distribution"

inductive BridgeClaim where
  | directoryConnectsFormalizations
  | bitVectorEvidenceFileProvidesGeometry
  | bitCountsMapToKnownBits
  | unknownBitsGiveUncertaintyInterpretation
  | completionsCardinalityLaw
  | completionsMeanWeightLaw
  | evidenceStrengthLaw
  | bridgeToContinuousBetaTheory
  | bridgeHasZeroSorries
  deriving Repr, DecidableEq, BEq

def renderBridgeClaim : BridgeClaim → String
  | .directoryConnectsFormalizations =>
      mkPresPos (properNameNP "Mettapedia/Bridge")
        (complV2 (mkV2 (regV "connect")) (properNameNP "cross-module formalizations"))
  | .bitVectorEvidenceFileProvidesGeometry =>
      mkPresPos (properNameNP "BitVectorEvidence.lean")
        (complV2 (mkV2 (regV "provide")) (properNameNP "a geometric semantics for PLN evidence"))
  | .bitCountsMapToKnownBits =>
      mkPresPos (properNameNP "Positive and negative evidence counts" .AgP3Pl)
        (advVP (predV (regV "correspond")) (ppAdv to_Prep (properNameNP "known bits in partial bit vectors")))
  | .unknownBitsGiveUncertaintyInterpretation =>
      mkPresPos (properNameNP "Unknown bits" .AgP3Pl)
        (complV2 (mkV2 (regV "give")) (properNameNP "a combinatorial interpretation of uncertainty"))
  | .completionsCardinalityLaw =>
      mkPresPos (properNameNP "completions_card")
        (copulaNP (properNameNP "|completions(v)| = 2^(countUnknown v)"))
  | .completionsMeanWeightLaw =>
      mkPresPos (properNameNP "completions_mean_weight")
        (copulaNP (properNameNP "average Hamming weight = (pos + unknown/2) / n"))
  | .evidenceStrengthLaw =>
      mkPresPos (properNameNP "toEvidence_strength")
        (copulaNP (properNameNP "Evidence.strength = expected fraction of 1s"))
  | .bridgeToContinuousBetaTheory =>
      mkPresPos (properNameNP "This bridge")
        (complV2 (mkV2 (regV "connect")) (properNameNP "discrete evidence to continuous Beta distribution theory"))
  | .bridgeHasZeroSorries =>
      mkPresNeg (properNameNP "This directory")
        (complV2 (mkV2 (regV "contain")) (properNameNP "sorries"))

def allBridgeClaims : List BridgeClaim :=
  [ .directoryConnectsFormalizations
  , .bitVectorEvidenceFileProvidesGeometry
  , .bitCountsMapToKnownBits
  , .unknownBitsGiveUncertaintyInterpretation
  , .completionsCardinalityLaw
  , .completionsMeanWeightLaw
  , .evidenceStrengthLaw
  , .bridgeToContinuousBetaTheory
  , .bridgeHasZeroSorries
  ]

def parseBridgeClaimLine? (line : String) : Option BridgeClaim :=
  let norm := stripTerminalPeriod line
  allBridgeClaims.find? (fun c => renderBridgeClaim c = norm)

inductive BridgeHeading where
  | title
  | files
  | keyResults
  | status
  deriving Repr, DecidableEq, BEq

def renderBridgeHeading : BridgeHeading → String
  | .title =>
      headingNP (linUseN bridge_N)
  | .files =>
      headingPlNP (linUseN (regN "file"))
  | .keyResults =>
      headingPlNP (linAdjCN (linPositA (regA "key")) (linUseN result_N))
  | .status =>
      headingNP (linUseN status_N)

def allBridgeHeadings : List BridgeHeading :=
  [ .title, .files, .keyResults, .status ]

def parseBridgeHeadingLine? (line : String) : Option BridgeHeading :=
  allBridgeHeadings.find? (fun h => renderBridgeHeading h = line)

private def claimBullet (c : BridgeClaim) : ClaimBullet :=
  { text := renderBridgeClaim c }

def bridgeReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderBridgeHeading .title)
  , .paragraph [renderBridgeClaim .directoryConnectsFormalizations]
  , .heading 2 (renderBridgeHeading .files)
  , .fileRef "BitVectorEvidence.lean" (renderBridgeClaim .bitVectorEvidenceFileProvidesGeometry)
  , .paragraph
      [ renderBridgeClaim .bitCountsMapToKnownBits
      , renderBridgeClaim .unknownBitsGiveUncertaintyInterpretation
      ]
  , .heading 2 (renderBridgeHeading .keyResults)
  , .syntaxItems
      [ { label := "completions_card"
          pattern := .infix (.call "|completions|" [ .ident "v" ]) "="
            (.call "2^" [ .call "countUnknown" [ .ident "v" ] ]) }
      , { label := "completions_mean_weight"
          pattern := .infix (.quoted "average Hamming weight") "="
            (.infix (.infix (.ident "pos") "+" (.infix (.ident "unknown") "/" (.ident "2"))) "/" (.ident "n")) }
      , { label := "toEvidence_strength"
          pattern := .infix (.ident "Evidence.strength") "=" (.quoted "expected fraction of 1s") }
      ]
  , .claimBullets
      [ claimBullet .completionsCardinalityLaw
      , claimBullet .completionsMeanWeightLaw
      , claimBullet .evidenceStrengthLaw
      , claimBullet .bridgeToContinuousBetaTheory
      ]
  , .heading 2 (renderBridgeHeading .status)
  , .claimBullets [claimBullet .bridgeHasZeroSorries]
  ]

def bridgeReadmeMarkdown : String :=
  renderDoc bridgeReadmeBlocks

#eval bridgeReadmeMarkdown

inductive ParsedBridgeStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : BridgeClaim)
  | claimLine (claim : BridgeClaim)
  deriving Repr

def parseSelectedStructuredBridgeLine? (line : String) : Option ParsedBridgeStructuredLine :=
  match parseTechnicalLine? bridgeReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines bridgeReadmeBlocks).contains line then
        match parseClaimBulletLine? parseBridgeClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseBridgeClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredBridgeLines : List String :=
  technicalLines bridgeReadmeBlocks ++
  claimBulletLines bridgeReadmeBlocks ++
  [ ensurePeriod (renderBridgeClaim .directoryConnectsFormalizations)
  , ensurePeriod (renderBridgeClaim .bitVectorEvidenceFileProvidesGeometry)
  , ensurePeriod (renderBridgeClaim .bitCountsMapToKnownBits)
  , ensurePeriod (renderBridgeClaim .unknownBitsGiveUncertaintyInterpretation)
  ]

def bridgeHardAuditPasses : Bool :=
  bridgeReadmeBlocks.all (blockPassesHardAuditWith parseBridgeClaimLine? parseBridgeHeadingLine?)

theorem bridge_hard_audit :
    bridgeHardAuditPasses = true := by
  native_decide

def bridgeHeadingImageCheck : Bool :=
  headingRenderImageCheck parseBridgeHeadingLine? renderBridgeHeading bridgeReadmeBlocks

theorem bridge_heading_images :
    bridgeHeadingImageCheck = true := by
  native_decide

theorem bridge_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries bridgeReadmeBlocks) :
    ∃ h, parseBridgeHeadingLine? txt = some h ∧ renderBridgeHeading h = txt := by
  exact headingRenderImageWitness
    parseBridgeHeadingLine? renderBridgeHeading bridgeReadmeBlocks
    bridge_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List BridgeClaim)) (surface : String)
    (c : BridgeClaim) : List (String × List BridgeClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List BridgeClaim) :=
  allBridgeClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderBridgeClaim c) c) []

def ambiguousClaimSurfaces : List (String × List BridgeClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allBridgeClaims.filter (fun c =>
    parseBridgeClaimLine? (renderBridgeClaim c) != some c)
  if fails.isEmpty then
    "Bridge parse-back check: all claim lines roundtrip"
  else
    s!"Bridge parse-back failures: {repr fails}"

#eval
  if bridgeHardAuditPasses then
    "Bridge hard audit: no prose-bearing bypass blocks detected"
  else
    "Bridge hard audit: violation detected"

#eval
  let fails := selectedStructuredBridgeLines.filter
    (fun line =>
      match parseSelectedStructuredBridgeLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "Bridge parse-back check: selected headings + bullet families roundtrip"
  else
    s!"Bridge structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "Bridge ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"Bridge ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.BridgeReadmeCompositional
