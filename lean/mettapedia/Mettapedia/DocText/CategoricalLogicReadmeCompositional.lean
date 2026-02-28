import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.CategoricalLogicReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def port_N := regN "port"
private def directory_N := regN "directory"
private def structure_N := regN "structure"
private def system_N := regN "system"
private def model_N := regN "model"
private def formalization_N := regN "formalization"

inductive CatLogicClaim where
  | formalizesCategoricalLogicInLean
  | projectDocsAreHostedOnline
  | lean427PortBuildsWithLake
  | categoryTheoryDirectoryPurpose
  | deductionDirectoryPurpose
  | semanticsDirectoryPurpose
  deriving Repr, DecidableEq, BEq

def renderCatLogicClaim : CatLogicClaim → String
  | .formalizesCategoricalLogicInLean =>
      mkPresPos (properNameNP "This directory")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "categorical logic in the Lean proof assistant"))
  | .projectDocsAreHostedOnline =>
      mkPresPos (properNameNP "The project documentation")
        (copulaNP (properNameNP "https://lean-catLogic.github.io"))
  | .lean427PortBuildsWithLake =>
      mkPresPos (properNameNP "The Lean 4.27.0 port")
        (complV2 (mkV2 (regV "build")) (properNameNP "with lake under Lean 4.27.0 and mathlib v4.27.0"))
  | .categoryTheoryDirectoryPurpose =>
      mkPresPos (properNameNP "src/categoryTheory")
        (complV2 (mkV2 (regV "implement")) (properNameNP "category-theoretic structures for categorical logic"))
  | .deductionDirectoryPurpose =>
      mkPresPos (properNameNP "src/deduction")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "proof systems and calculi"))
  | .semanticsDirectoryPurpose =>
      mkPresPos (properNameNP "src/semantics")
        (complV2 (mkV2 (regV "interpret")) (properNameNP "formal languages in posets, categories, and Kripke models"))

def allCatLogicClaims : List CatLogicClaim :=
  [ .formalizesCategoricalLogicInLean
  , .projectDocsAreHostedOnline
  , .lean427PortBuildsWithLake
  , .categoryTheoryDirectoryPurpose
  , .deductionDirectoryPurpose
  , .semanticsDirectoryPurpose
  ]

def parseCatLogicClaimLine? (line : String) : Option CatLogicClaim :=
  let norm := stripTerminalPeriod line
  allCatLogicClaims.find? (fun c => renderCatLogicClaim c = norm)

inductive CatLogicHeading where
  | title
  | directories
  deriving Repr, DecidableEq, BEq

def renderCatLogicHeading : CatLogicHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "categorical")) (linUseN formalization_N))
  | .directories =>
      headingPlNP (linUseN directory_N)

def allCatLogicHeadings : List CatLogicHeading :=
  [ .title, .directories ]

def parseCatLogicHeadingLine? (line : String) : Option CatLogicHeading :=
  allCatLogicHeadings.find? (fun h => renderCatLogicHeading h = line)

private def claimBullet (c : CatLogicClaim) : ClaimBullet :=
  { text := renderCatLogicClaim c }

def categoricalLogicReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderCatLogicHeading .title)
  , .paragraph
      [ renderCatLogicClaim .formalizesCategoricalLogicInLean
      , renderCatLogicClaim .projectDocsAreHostedOnline
      , renderCatLogicClaim .lean427PortBuildsWithLake
      ]
  , .heading 2 (renderCatLogicHeading .directories)
  , .fileRef "src/categoryTheory" (renderCatLogicClaim .categoryTheoryDirectoryPurpose)
  , .fileRef "src/deduction" (renderCatLogicClaim .deductionDirectoryPurpose)
  , .fileRef "src/semantics" (renderCatLogicClaim .semanticsDirectoryPurpose)
  ]

def categoricalLogicReadmeMarkdown : String :=
  renderDoc categoricalLogicReadmeBlocks

#eval categoricalLogicReadmeMarkdown

inductive ParsedCatLogicStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : CatLogicClaim)
  | claimLine (claim : CatLogicClaim)
  deriving Repr

def parseSelectedStructuredCatLogicLine? (line : String) : Option ParsedCatLogicStructuredLine :=
  match parseTechnicalLine? categoricalLogicReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines categoricalLogicReadmeBlocks).contains line then
        match parseClaimBulletLine? parseCatLogicClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseCatLogicClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredCatLogicLines : List String :=
  technicalLines categoricalLogicReadmeBlocks ++
  claimBulletLines categoricalLogicReadmeBlocks ++
  [ ensurePeriod (renderCatLogicClaim .formalizesCategoricalLogicInLean)
  , ensurePeriod (renderCatLogicClaim .projectDocsAreHostedOnline)
  , ensurePeriod (renderCatLogicClaim .lean427PortBuildsWithLake)
  ]

def categoricalLogicHardAuditPasses : Bool :=
  categoricalLogicReadmeBlocks.all (blockPassesHardAuditWith parseCatLogicClaimLine? parseCatLogicHeadingLine?)

theorem categoricalLogic_hard_audit :
    categoricalLogicHardAuditPasses = true := by
  native_decide

def categoricalLogicHeadingImageCheck : Bool :=
  headingRenderImageCheck parseCatLogicHeadingLine? renderCatLogicHeading categoricalLogicReadmeBlocks

theorem categoricalLogic_heading_images :
    categoricalLogicHeadingImageCheck = true := by
  native_decide

theorem categoricalLogic_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries categoricalLogicReadmeBlocks) :
    ∃ h, parseCatLogicHeadingLine? txt = some h ∧ renderCatLogicHeading h = txt := by
  exact headingRenderImageWitness
    parseCatLogicHeadingLine? renderCatLogicHeading categoricalLogicReadmeBlocks
    categoricalLogic_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List CatLogicClaim)) (surface : String)
    (c : CatLogicClaim) : List (String × List CatLogicClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List CatLogicClaim) :=
  allCatLogicClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderCatLogicClaim c) c) []

def ambiguousClaimSurfaces : List (String × List CatLogicClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allCatLogicClaims.filter (fun c =>
    parseCatLogicClaimLine? (renderCatLogicClaim c) != some c)
  if fails.isEmpty then
    "CategoricalLogic parse-back check: all claim lines roundtrip"
  else
    s!"CategoricalLogic parse-back failures: {repr fails}"

#eval
  if categoricalLogicHardAuditPasses then
    "CategoricalLogic hard audit: no prose-bearing bypass blocks detected"
  else
    "CategoricalLogic hard audit: violation detected"

#eval
  let fails := selectedStructuredCatLogicLines.filter
    (fun line =>
      match parseSelectedStructuredCatLogicLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "CategoricalLogic parse-back check: selected headings + bullet families roundtrip"
  else
    s!"CategoricalLogic structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "CategoricalLogic ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"CategoricalLogic ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.CategoricalLogicReadmeCompositional
