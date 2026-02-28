import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.GFReadmeCompositional

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
private def grammar_N := regN "grammar"
private def syntax_N := regN "syntax"
private def subset_N := regN "subset"
private def engine_N := regN "engine"
private def profile_N := regN "profile"
private def theorem_N := regN "theorem"
private def scope_N := regN "scope"
private def status_N := regN "status"
private def pattern_N := regN "pattern"

inductive GFClaim where
  | formalizesGFInLean4
  | includesAbstractSyntax
  | includesConcreteGrammars
  | includesSemanticBridge
  | primaryAuthorAI
  | humanLeadZar
  | formalizesSubsetRGL
  | doesNotPortFullRGL
  | abstractSyntaxHas170Signatures
  | czechHasMorphologyEngine
  | czechLinearizationIsPartial
  | englishHasClauseConstruction
  | englishCoverageIsBroaderThanCzech
  | semanticBridgeTargetsOSLF
  | excludesPGFRuntime
  | excludesPMCFGParsing
  | excludesChartParsing
  | excludesFullConjunctionLinearization
  | excludesFullEnglishNumeralLinearization
  | codebaseHasNoSorries
  | codebaseHasNoAxioms
  | everyTheoremIsProven
  | kernelConfluenceIsProven
  | crossLinguisticInvarianceIsProven
  | roundtripRegressionHasZeroFailures
  | workedExamplesProveEndToEndPipeline
  | referenceRanta2004
  | referenceMeredithStay
  | referenceGFRGL
  deriving Repr, DecidableEq, BEq

def renderGFClaim : GFClaim → String
  | .formalizesGFInLean4 =>
      mkPresPos (properNameNP "This project")
        (complV2 (mkV2 (regV "formalize"))
          (properNameNP "Grammatical Framework in Lean 4"))
  | .includesAbstractSyntax =>
      mkPresPos (properNameNP "It")
        (complV2 (mkV2 (regV "include"))
          (linDetCN aIndefArt
            (linAdjCN (linPositA (regA "abstract")) (linUseN syntax_N))))
  | .includesConcreteGrammars =>
      mkPresPos (properNameNP "It")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "two concrete grammars for Czech and English"))
  | .includesSemanticBridge =>
      mkPresPos (properNameNP "It")
        (complV2 (mkV2 (regV "include"))
          (linDetCN aIndefArt
            (linAdjCN (linPositA (regA "semantic")) (linUseN bridge_N))))
  | .primaryAuthorAI =>
      mkPresPos (properNameNP "The primary author")
        (copulaNP (properNameNP "Oruzi (AI)"))
  | .humanLeadZar =>
      mkPresPos (properNameNP "The human lead editor")
        (copulaNP (properNameNP "Zar"))
  | .formalizesSubsetRGL =>
      mkPresPos (properNameNP "This formalization")
        (complV2 (mkV2 (regV "cover"))
          (linDetCN aIndefArt
            (linAdjCN (linPositA (regA "strict")) (linUseN subset_N))))
  | .doesNotPortFullRGL =>
      mkPresNeg (properNameNP "This formalization")
        (complV2 (mkV2 (regV "port")) (properNameNP "the full RGL"))
  | .abstractSyntaxHas170Signatures =>
      mkPresPos (properNameNP "The abstract syntax")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "170 core GF RGL function signatures"))
  | .czechHasMorphologyEngine =>
      mkPresPos (properNameNP "The Czech concrete grammar")
        (complV2 (mkV2 (regV "include"))
          (linDetCN aIndefArt (linUseN engine_N)))
  | .czechLinearizationIsPartial =>
      mkPresPos (properNameNP "The Czech linearization")
        (copulaAdj "partial")
  | .englishHasClauseConstruction =>
      mkPresPos (properNameNP "The English concrete grammar")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "morphology and clause construction"))
  | .englishCoverageIsBroaderThanCzech =>
      mkPresPos (properNameNP "The English syntactic coverage")
        (copulaAdj "broader than Czech")
  | .semanticBridgeTargetsOSLF =>
      mkPresPos (properNameNP "The semantic bridge")
        (complV2 (mkV2 (regV "target"))
          (properNameNP "OSLF evidence semantics"))
  | .excludesPGFRuntime =>
      mkPresNeg (properNameNP "This profile")
        (complV2 (mkV2 (regV "include")) (properNameNP "the PGF runtime"))
  | .excludesPMCFGParsing =>
      mkPresNeg (properNameNP "This profile")
        (complV2 (mkV2 (regV "include")) (properNameNP "PMCFG parsing"))
  | .excludesChartParsing =>
      mkPresNeg (properNameNP "This profile")
        (complV2 (mkV2 (regV "include")) (properNameNP "chart parsing"))
  | .excludesFullConjunctionLinearization =>
      mkPresNeg (properNameNP "This profile")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "full conjunction linearization"))
  | .excludesFullEnglishNumeralLinearization =>
      mkPresNeg (properNameNP "This profile")
        (complV2 (mkV2 (regV "include"))
          (properNameNP "full English numeral linearization"))
  | .codebaseHasNoSorries =>
      mkPresNeg (properNameNP "The codebase")
        (complV2 (mkV2 (regV "contain")) (properNameNP "sorries"))
  | .codebaseHasNoAxioms =>
      mkPresNeg (properNameNP "The codebase")
        (complV2 (mkV2 (regV "contain")) (properNameNP "axioms"))
  | .everyTheoremIsProven =>
      mkPresPos (properNameNP "Every theorem") (copulaAdj "proven")
  | .kernelConfluenceIsProven =>
      mkPresPos (properNameNP "Kernel confluence") (copulaAdj "proven")
  | .crossLinguisticInvarianceIsProven =>
      mkPresPos (properNameNP "Cross-linguistic invariance") (copulaAdj "proven")
  | .roundtripRegressionHasZeroFailures =>
      mkPresPos (properNameNP "Roundtrip regression")
        (complV2 (mkV2 (regV "show"))
          (properNameNP "zero failures across 36 corpus entries"))
  | .workedExamplesProveEndToEndPipeline =>
      mkPresPos (properNameNP "Worked examples" .AgP3Pl)
        (complV2 (mkV2 (regV "prove")) (properNameNP "the end-to-end pipeline"))
  | .referenceRanta2004 =>
      mkPresPos (properNameNP "Aarne Ranta 2004")
        (copulaNP (properNameNP "the core GF reference"))
  | .referenceMeredithStay =>
      mkPresPos (properNameNP "Meredith and Stay" .AgP3Pl)
        (copulaNP (properNameNP "a core OSLF reference"))
  | .referenceGFRGL =>
      mkPresPos (properNameNP "The GF RGL source")
        (copulaNP (properNameNP "https://github.com/GrammaticalFramework/gf-rgl"))

def allGFClaims : List GFClaim :=
  [ .formalizesGFInLean4
  , .includesAbstractSyntax
  , .includesConcreteGrammars
  , .includesSemanticBridge
  , .primaryAuthorAI
  , .humanLeadZar
  , .formalizesSubsetRGL
  , .doesNotPortFullRGL
  , .abstractSyntaxHas170Signatures
  , .czechHasMorphologyEngine
  , .czechLinearizationIsPartial
  , .englishHasClauseConstruction
  , .englishCoverageIsBroaderThanCzech
  , .semanticBridgeTargetsOSLF
  , .excludesPGFRuntime
  , .excludesPMCFGParsing
  , .excludesChartParsing
  , .excludesFullConjunctionLinearization
  , .excludesFullEnglishNumeralLinearization
  , .codebaseHasNoSorries
  , .codebaseHasNoAxioms
  , .everyTheoremIsProven
  , .kernelConfluenceIsProven
  , .crossLinguisticInvarianceIsProven
  , .roundtripRegressionHasZeroFailures
  , .workedExamplesProveEndToEndPipeline
  , .referenceRanta2004
  , .referenceMeredithStay
  , .referenceGFRGL
  ]

def parseGFClaimLine? (line : String) : Option GFClaim :=
  let norm := stripTerminalPeriod line
  allGFClaims.find? (fun c => renderGFClaim c = norm)

inductive GFHeading where
  | title
  | authorship
  | scope
  | proofStatus
  | architecture
  | typedSymbolPatterns
  | keyResults
  | references
  deriving Repr, DecidableEq, BEq

private def headingNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassNP cn).s (.NCase .Nom)

private def headingPlNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassPluralNP cn).s (.NCase .Nom)

def renderGFHeading : GFHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "GF"))
        (linAdjCN (linPositA (regA "Lean")) (linUseN (regN "formalization"))))
  | .authorship =>
      headingNP (linUseN (regN "authorship"))
  | .scope =>
      headingNP (linUseN scope_N)
  | .proofStatus =>
      headingNP (linAdjCN (linPositA (regA "proof")) (linUseN status_N))
  | .architecture =>
      headingNP (linUseN (regN "architecture"))
  | .typedSymbolPatterns =>
      headingPlNP (linAdjCN (linPositA (compoundA "typed-symbol")) (linUseN pattern_N))
  | .keyResults =>
      headingPlNP (linAdjCN (linPositA (regA "key")) (linUseN (regN "result")))
  | .references =>
      headingPlNP (linUseN (regN "reference"))

def allGFHeadings : List GFHeading :=
  [ .title
  , .authorship
  , .scope
  , .proofStatus
  , .architecture
  , .typedSymbolPatterns
  , .keyResults
  , .references
  ]

def parseGFHeadingLine? (line : String) : Option GFHeading :=
  allGFHeadings.find? (fun h => renderGFHeading h = line)

private def claimBullets (claims : List GFClaim) : ReadmeBlock :=
  .claimBullets (claims.map fun c => { text := renderGFClaim c })

private def gfArchitectureBlock : String :=
  String.intercalate "\n"
    [ "Core.lean            GF categories (112), AbstractTree, ConcreteForm, Grammar"
    , "Abstract.lean        Core RGL function signatures and abstract nodes"
    , "Concrete.lean        Inflection tables and morphophonological operations"
    , "Typing.lean          GF-to-OSLF type checking and compositionality"
    , "OSLFBridge.lean      GF abstract syntax as OSLF LanguageDef"
    , "WorldModelSem.lean   Evidence-valued denotational semantics for GF trees"
    , "English/             English morphology and clause construction"
    , "Czech/               Czech morphology engine"
    , "Examples/            End-to-end pipeline examples"
    ]

private def symbolPatternItems : List SyntaxItem :=
  [ { label := "Tree to pattern bridge"
      pattern := .infix (.ident "GF_tree") "->" (.ident "Pattern") }
  , { label := "Pattern to formula bridge"
      pattern := .infix (.ident "Pattern") "->" (.ident "QFormula") }
  , { label := "Pipeline composition"
      pattern := .seq
        [ .ident "GF_tree"
        , .ident "Pattern"
        , .ident "Store"
        , .ident "QFormula"
        , .ident "Evidence"
        ] " -> " }
  ]

def gfReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderGFHeading .title)
  , .paragraph
      [ renderGFClaim .formalizesGFInLean4
      , renderGFClaim .includesAbstractSyntax
      , renderGFClaim .includesConcreteGrammars
      , renderGFClaim .includesSemanticBridge
      ]
  , .heading 2 (renderGFHeading .authorship)
  , claimBullets [.primaryAuthorAI, .humanLeadZar]
  , .heading 2 (renderGFHeading .scope)
  , .paragraph [renderGFClaim .formalizesSubsetRGL, renderGFClaim .doesNotPortFullRGL]
  , claimBullets
      [ .abstractSyntaxHas170Signatures
      , .czechHasMorphologyEngine
      , .czechLinearizationIsPartial
      , .englishHasClauseConstruction
      , .englishCoverageIsBroaderThanCzech
      , .semanticBridgeTargetsOSLF
      ]
  , claimBullets
      [ .excludesPGFRuntime
      , .excludesPMCFGParsing
      , .excludesChartParsing
      , .excludesFullConjunctionLinearization
      , .excludesFullEnglishNumeralLinearization
      ]
  , .heading 2 (renderGFHeading .proofStatus)
  , .paragraph
      [ renderGFClaim .codebaseHasNoSorries
      , renderGFClaim .codebaseHasNoAxioms
      , renderGFClaim .everyTheoremIsProven
      ]
  , .heading 2 (renderGFHeading .architecture)
  , .codeBlock "" gfArchitectureBlock
  , .heading 3 (renderGFHeading .typedSymbolPatterns)
  , .syntaxItems symbolPatternItems
  , .heading 2 (renderGFHeading .keyResults)
  , claimBullets
      [ .kernelConfluenceIsProven
      , .crossLinguisticInvarianceIsProven
      , .roundtripRegressionHasZeroFailures
      , .workedExamplesProveEndToEndPipeline
      ]
  , .heading 2 (renderGFHeading .references)
  , claimBullets [.referenceRanta2004, .referenceMeredithStay, .referenceGFRGL]
  ]

def gfReadmeMarkdown : String :=
  renderDoc gfReadmeBlocks

#eval gfReadmeMarkdown

inductive ParsedGFStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : GFClaim)
  deriving Repr

def parseSelectedStructuredGFLine? (line : String) : Option ParsedGFStructuredLine :=
  match parseTechnicalLine? gfReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines gfReadmeBlocks).contains line then
        match parseClaimBulletLine? parseGFClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        none

def selectedStructuredGFLines : List String :=
  technicalLines gfReadmeBlocks ++
  claimBulletLines gfReadmeBlocks

def gfHardAuditPasses : Bool :=
  gfReadmeBlocks.all (blockPassesHardAuditWith parseGFClaimLine? parseGFHeadingLine?)

theorem gf_hard_audit :
    gfHardAuditPasses = true := by
  native_decide

def gfHeadingImageCheck : Bool :=
  headingRenderImageCheck parseGFHeadingLine? renderGFHeading gfReadmeBlocks

theorem gf_heading_images :
    gfHeadingImageCheck = true := by
  native_decide

theorem gf_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries gfReadmeBlocks) :
    ∃ h, parseGFHeadingLine? txt = some h ∧ renderGFHeading h = txt := by
  exact headingRenderImageWitness
    parseGFHeadingLine? renderGFHeading gfReadmeBlocks
    gf_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List GFClaim)) (surface : String) (c : GFClaim) :
    List (String × List GFClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List GFClaim) :=
  allGFClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderGFClaim c) c) []

def ambiguousClaimSurfaces : List (String × List GFClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

theorem anchor_formalization :
    renderGFClaim .formalizesGFInLean4 =
      "This project formalizes Grammatical Framework in Lean 4" := by
  native_decide

theorem anchor_no_sorries :
    renderGFClaim .codebaseHasNoSorries =
      "The codebase doesn't contain sorries" := by
  native_decide

#eval
  let fails := allGFClaims.filter (fun c =>
    parseGFClaimLine? (renderGFClaim c) != some c)
  if fails.isEmpty then
    "GF README parse-back check: all claim lines roundtrip"
  else
    s!"GF README parse-back failures: {repr fails}"

#eval
  if gfHardAuditPasses then
    "GF README hard audit: no prose-bearing bypass blocks detected"
  else
    "GF README hard audit: violation detected"

#eval
  let fails := selectedStructuredGFLines.filter
    (fun line =>
      match parseSelectedStructuredGFLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "GF README parse-back check: selected headings + bullet families roundtrip"
  else
    s!"GF README structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "GF README ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"GF README ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.GFReadmeCompositional
