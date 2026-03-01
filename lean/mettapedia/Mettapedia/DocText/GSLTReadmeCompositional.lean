import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.GSLTReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def spec_N := regN "spec"
private def interface_N := regN "interface"
private def definition_N := regN "definition"
private def workflow_N := regN "workflow"
private def demo_N := regN "demo"
private def connection_N := regN "connection"
private def status_N := regN "status"
private def module_N := regN "module"

inductive GSLTClaim where
  | titleScope
  | titlePurpose
  | whereSpecLives
  | coreDefinitionSummary
  | subobjectFibrationSummary
  | lambdaTheoryWithEqualitySummary
  | changeOfBaseSummary
  | beckChevalleySummary
  | lambdaTheoryWithFibrationSummary
  | languageDefFrontEndSummary
  | grammarSummary
  | patternSummary
  | premiseSummary
  | fullLanguageDefSummary
  | pipelineEntryPointsSummary
  | practicalContractSummary
  | mustProvideSorts
  | mustProvideConstructors
  | mustProvideEquations
  | mustProvideRewrites
  | mustProvidePremises
  | relationEnvOptional
  | anyLanguageScope
  | typicalFunctionalPattern
  | typicalImperativePattern
  | typicalConcurrentPattern
  | demosSummary
  | relationToToposSummary
  | nttConnectionSummary
  | nttPredicateFibrationRole
  | nttClaimTrackerAuthority
  | statusBoundarySummary
  deriving Repr, DecidableEq, BEq

def renderGSLTClaim : GSLTClaim → String
  | .titleScope =>
      mkPresPos (properNameNP "GSLT")
        (copulaNP (properNameNP "Graph-Structured Lambda Theories in Mettapedia"))
  | .titlePurpose =>
      mkPresPos (properNameNP "This README")
        (complV2 (mkV2 (regV "specify")) (properNameNP "the formal GSLT contract that OSLF consumes"))
  | .whereSpecLives =>
      mkPresPos (properNameNP "The formal specification")
        (copulaNP (properNameNP "the GSLT module family and OSLF MeTTaIL syntax modules"))
  | .coreDefinitionSummary =>
      mkPresPos (properNameNP "The core GSLT object")
        (copulaNP (properNameNP "a lambda theory with equality and fibration structure"))
  | .subobjectFibrationSummary =>
      mkPresPos (properNameNP "SubobjectFibration")
        (copulaNP (properNameNP "a Sub fiber over each object with frame structure"))
  | .lambdaTheoryWithEqualitySummary =>
      mkPresPos (properNameNP "LambdaTheoryWithEquality")
        (copulaNP (properNameNP "a categorical object with cartesian closed structure, finite limits, and attached fibration"))
  | .changeOfBaseSummary =>
      mkPresPos (properNameNP "ChangeOfBase")
        (copulaNP (properNameNP "pullback and quantifier images with adjunctions exists_f left f* left forall_f"))
  | .beckChevalleySummary =>
      mkPresPos (properNameNP "Beck-Chevalley")
        (copulaNP (properNameNP "substitution and quantification compatibility on pullback squares"))
  | .lambdaTheoryWithFibrationSummary =>
      mkPresPos (properNameNP "LambdaTheoryWithFibration")
        (copulaNP (properNameNP "the bundled core object consumed by later semantics"))
  | .languageDefFrontEndSummary =>
      mkPresPos (properNameNP "LanguageDef")
        (copulaNP (properNameNP "the operational front-end for OSLF synthesis"))
  | .grammarSummary =>
      mkPresPos (properNameNP "TypeExpr, CollType, GrammarRule, and TermParam" .AgP3Pl)
        (copulaNP (properNameNP "the grammar layer"))
  | .patternSummary =>
      mkPresPos (properNameNP "Pattern")
        (copulaNP (properNameNP "the equation and rewrite pattern language with binders and collections"))
  | .premiseSummary =>
      mkPresPos (properNameNP "Premise")
        (copulaNP (properNameNP "freshness, congruence, and relationQuery constraints"))
  | .fullLanguageDefSummary =>
      mkPresPos (properNameNP "LanguageDef")
        (copulaNP (properNameNP "name, types, terms, equations, rewrites, and congruence collection defaults"))
  | .pipelineEntryPointsSummary =>
      mkPresPos (properNameNP "TypeSynthesis entry points" .AgP3Pl)
        (copulaNP (properNameNP "langRewriteSystem, langDiamond, langBox, langGalois, and langOSLF"))
  | .practicalContractSummary =>
      mkPresPos (properNameNP "The practical contract")
        (copulaNP (properNameNP "LanguageDef plus optional RelationEnv maps to langOSLF"))
  | .mustProvideSorts =>
      mkPresPos (properNameNP "A new language spec")
        (complV2 (mkV2 (regV "require")) (properNameNP "sort declarations and a process sort designation"))
  | .mustProvideConstructors =>
      mkPresPos (properNameNP "A new language spec")
        (complV2 (mkV2 (regV "require")) (properNameNP "constructor terms for syntax and state"))
  | .mustProvideEquations =>
      mkPresPos (properNameNP "A new language spec")
        (complV2 (mkV2 (regV "require")) (properNameNP "equations for structural equality and normalization"))
  | .mustProvideRewrites =>
      mkPresPos (properNameNP "A new language spec")
        (complV2 (mkV2 (regV "require")) (properNameNP "small-step rewrite rules"))
  | .mustProvidePremises =>
      mkPresPos (properNameNP "A new language spec")
        (complV2 (mkV2 (regV "require")) (properNameNP "premise constraints where needed"))
  | .relationEnvOptional =>
      mkPresPos (properNameNP "RelationEnv")
        (copulaNP (properNameNP "optional unless relationQuery premises are used"))
  | .anyLanguageScope =>
      mkPresPos (properNameNP "The interface")
        (copulaNP (properNameNP "any language encoded as small-step rewrites over structured states"))
  | .typicalFunctionalPattern =>
      mkPresPos (properNameNP "Functional languages" .AgP3Pl)
        (copulaNP (properNameNP "typically encoded by term-reduction rules"))
  | .typicalImperativePattern =>
      mkPresPos (properNameNP "Imperative languages" .AgP3Pl)
        (copulaNP (properNameNP "typically encoded as rewrites over machine states"))
  | .typicalConcurrentPattern =>
      mkPresPos (properNameNP "Concurrent languages" .AgP3Pl)
        (copulaNP (properNameNP "typically encoded as rewrites over process and message networks"))
  | .demosSummary =>
      mkPresPos (properNameNP "The codebase")
        (copulaNP (properNameNP "TinyML, MeTTa, and premise-aware demos to copy"))
  | .relationToToposSummary =>
      mkPresPos (properNameNP "LanguageDef")
        (copulaNP (properNameNP "the executable ingestion layer, while GSLT Topos modules provide categorical semantics"))
  | .nttConnectionSummary =>
      mkPresPos (properNameNP "The GSLT presheaf layer")
        (copulaNP (properNameNP "the direct infrastructure for Native Type Theory formalization"))
  | .nttPredicateFibrationRole =>
      mkPresPos (properNameNP "PredicateFibration.lean")
        (copulaNP (properNameNP "presheaf change-of-base, frame fibers, and Beck-Chevalley components used by NTT"))
  | .nttClaimTrackerAuthority =>
      mkPresPos (properNameNP "NTTClaimTracker.lean")
        (copulaNP (properNameNP "the authoritative strict claim tracker for counts and assumption-scoped items"))
  | .statusBoundarySummary =>
      mkPresPos (properNameNP "Paper-parity status")
        (copulaNP (properNameNP "tracked in NTTClaimTracker, PaperClaimTracker, and FULLStatus modules"))

def allGSLTClaims : List GSLTClaim :=
  [ .titleScope
  , .titlePurpose
  , .whereSpecLives
  , .coreDefinitionSummary
  , .subobjectFibrationSummary
  , .lambdaTheoryWithEqualitySummary
  , .changeOfBaseSummary
  , .beckChevalleySummary
  , .lambdaTheoryWithFibrationSummary
  , .languageDefFrontEndSummary
  , .grammarSummary
  , .patternSummary
  , .premiseSummary
  , .fullLanguageDefSummary
  , .pipelineEntryPointsSummary
  , .practicalContractSummary
  , .mustProvideSorts
  , .mustProvideConstructors
  , .mustProvideEquations
  , .mustProvideRewrites
  , .mustProvidePremises
  , .relationEnvOptional
  , .anyLanguageScope
  , .typicalFunctionalPattern
  , .typicalImperativePattern
  , .typicalConcurrentPattern
  , .demosSummary
  , .relationToToposSummary
  , .nttConnectionSummary
  , .nttPredicateFibrationRole
  , .nttClaimTrackerAuthority
  , .statusBoundarySummary
  ]

def parseGSLTClaimLine? (line : String) : Option GSLTClaim :=
  let norm := stripTerminalPeriod line
  allGSLTClaims.find? (fun c => renderGSLTClaim c = norm)

inductive GSLTHeading where
  | title
  | whereSpecLives
  | coreDefinition
  | operationalInterface
  | oslfEntryPoints
  | newLanguageChecklist
  | anyLanguage
  | practicalDemos
  | relationToTopos
  | nttConnection
  deriving Repr, DecidableEq, BEq

def renderGSLTHeading : GSLTHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "GSLT")) (linUseN module_N))
  | .whereSpecLives =>
      headingNP (linAdjCN (linPositA (regA "formal spec")) (linUseN status_N))
  | .coreDefinition =>
      headingNP (linAdjCN (linPositA (regA "category-theoretic")) (linUseN definition_N))
  | .operationalInterface =>
      headingNP (linAdjCN (linPositA (regA "grammar operational")) (linUseN interface_N))
  | .oslfEntryPoints =>
      headingNP (linAdjCN (linPositA (regA "OSLF")) (linUseN interface_N))
  | .newLanguageChecklist =>
      headingNP (linAdjCN (linPositA (regA "new language")) (linUseN workflow_N))
  | .anyLanguage =>
      headingNP (linAdjCN (linPositA (regA "any language")) (linUseN interface_N))
  | .practicalDemos =>
      headingPlNP (linAdjCN (linPositA (regA "practical")) (linUseN (regN "example")))
  | .relationToTopos =>
      headingNP (linAdjCN (linPositA (regA "relation to topos")) (linUseN spec_N))
  | .nttConnection =>
      headingNP (linAdjCN (linPositA (regA "Native Type Theory")) (linUseN connection_N))

def allGSLTHeadings : List GSLTHeading :=
  [ .title, .whereSpecLives, .coreDefinition, .operationalInterface, .oslfEntryPoints
  , .newLanguageChecklist, .anyLanguage, .practicalDemos, .relationToTopos, .nttConnection ]

def parseGSLTHeadingLine? (line : String) : Option GSLTHeading :=
  allGSLTHeadings.find? (fun h => renderGSLTHeading h = line)

private def claimBullet (c : GSLTClaim) : ClaimBullet :=
  { text := renderGSLTClaim c }

def gsltReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderGSLTHeading .title)
  , .paragraph
      [ renderGSLTClaim .titleScope
      , renderGSLTClaim .titlePurpose
      ]
  , .heading 2 (renderGSLTHeading .whereSpecLives)
  , .claimBullets [claimBullet .whereSpecLives]
  , .pathItems
      [ { path := "Mettapedia/GSLT.lean" }
      , { path := "Mettapedia/GSLT/Core/LambdaTheoryCategory.lean" }
      , { path := "Mettapedia/GSLT/Core/ChangeOfBase.lean" }
      , { path := "Mettapedia/GSLT/Topos/SubobjectClassifier.lean" }
      , { path := "Mettapedia/GSLT/Topos/PredicateFibration.lean" }
      ]
  , .heading 2 (renderGSLTHeading .coreDefinition)
  , .claimBullets
      [ claimBullet .coreDefinitionSummary
      , claimBullet .subobjectFibrationSummary
      , claimBullet .lambdaTheoryWithEqualitySummary
      , claimBullet .changeOfBaseSummary
      , claimBullet .beckChevalleySummary
      , claimBullet .lambdaTheoryWithFibrationSummary
      ]
  , .heading 2 (renderGSLTHeading .operationalInterface)
  , .claimBullets
      [ claimBullet .languageDefFrontEndSummary
      , claimBullet .grammarSummary
      , claimBullet .patternSummary
      , claimBullet .premiseSummary
      , claimBullet .fullLanguageDefSummary
      ]
  , .heading 2 (renderGSLTHeading .oslfEntryPoints)
  , .claimBullets
      [ claimBullet .pipelineEntryPointsSummary
      , claimBullet .practicalContractSummary
      ]
  , .pathItems
      [ { path := "langRewriteSystemUsing / langRewriteSystem" }
      , { path := "langDiamondUsing / langDiamond" }
      , { path := "langBoxUsing / langBox" }
      , { path := "langGaloisUsing / langGalois" }
      , { path := "langOSLF" }
      ]
  , .heading 2 (renderGSLTHeading .newLanguageChecklist)
  , .claimBullets
      [ claimBullet .mustProvideSorts
      , claimBullet .mustProvideConstructors
      , claimBullet .mustProvideEquations
      , claimBullet .mustProvideRewrites
      , claimBullet .mustProvidePremises
      , claimBullet .relationEnvOptional
      ]
  , .codeBlock "lean"
      "import Mettapedia.OSLF.MeTTaIL.Syntax\nimport Mettapedia.OSLF.Framework.TypeSynthesis\nimport Mettapedia.OSLF.MeTTaIL.Engine\n\nopen Mettapedia.OSLF.MeTTaIL.Syntax\nopen Mettapedia.OSLF.Framework.TypeSynthesis\nopen Mettapedia.OSLF.MeTTaIL.Engine\n\ndef myLang : LanguageDef := { ... }\ndef myRelEnv : RelationEnv := RelationEnv.empty\n\ndef myOSLF := langOSLF myLang \"Proc\"\ndef myDiamond := langDiamondUsing myRelEnv myLang\ndef myBox := langBoxUsing myRelEnv myLang"
  , .heading 2 (renderGSLTHeading .anyLanguage)
  , .claimBullets
      [ claimBullet .anyLanguageScope
      , claimBullet .typicalFunctionalPattern
      , claimBullet .typicalImperativePattern
      , claimBullet .typicalConcurrentPattern
      ]
  , .heading 2 (renderGSLTHeading .practicalDemos)
  , .claimBullets [claimBullet .demosSummary]
  , .pathItems
      [ { path := "Mettapedia/OSLF/Framework/TinyMLInstance.lean" }
      , { path := "Mettapedia/OSLF/Framework/MeTTaMinimalInstance.lean" }
      , { path := "Mettapedia/OSLF/Framework/MeTTaFullInstance.lean" }
      , { path := "Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean" }
      , { path := "Mettapedia/OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean" }
      ]
  , .heading 2 (renderGSLTHeading .relationToTopos)
  , .claimBullets [claimBullet .relationToToposSummary]
  , .heading 2 (renderGSLTHeading .nttConnection)
  , .claimBullets
      [ claimBullet .nttConnectionSummary
      , claimBullet .nttPredicateFibrationRole
      , claimBullet .nttClaimTrackerAuthority
      , claimBullet .statusBoundarySummary
      ]
  , .pathItems
      [ { path := "Mettapedia/OSLF/Framework/NTTClaimTracker.lean" }
      , { path := "Mettapedia/OSLF/Framework/PaperClaimTracker.lean" }
      , { path := "Mettapedia/OSLF/Framework/FULLStatus.lean" }
      ]
  ]

def gsltReadmeMarkdown : String :=
  renderDoc gsltReadmeBlocks

#eval gsltReadmeMarkdown

inductive ParsedGSLTStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : GSLTClaim)
  | claimLine (claim : GSLTClaim)
  deriving Repr

def parseSelectedStructuredGSLTLine? (line : String) : Option ParsedGSLTStructuredLine :=
  match parseTechnicalLine? gsltReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines gsltReadmeBlocks).contains line then
        match parseClaimBulletLine? parseGSLTClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseGSLTClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredGSLTLines : List String :=
  technicalLines gsltReadmeBlocks ++
  claimBulletLines gsltReadmeBlocks ++
  [ ensurePeriod (renderGSLTClaim .titleScope)
  , ensurePeriod (renderGSLTClaim .coreDefinitionSummary)
  , ensurePeriod (renderGSLTClaim .practicalContractSummary)
  , ensurePeriod (renderGSLTClaim .nttConnectionSummary)
  ]

def gsltHardAuditPasses : Bool :=
  gsltReadmeBlocks.all (blockPassesHardAuditWith parseGSLTClaimLine? parseGSLTHeadingLine?)

theorem gslt_hard_audit :
    gsltHardAuditPasses = true := by
  native_decide

def gsltHeadingImageCheck : Bool :=
  headingRenderImageCheck parseGSLTHeadingLine? renderGSLTHeading gsltReadmeBlocks

theorem gslt_heading_images :
    gsltHeadingImageCheck = true := by
  native_decide

theorem gslt_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries gsltReadmeBlocks) :
    ∃ h, parseGSLTHeadingLine? txt = some h ∧ renderGSLTHeading h = txt := by
  exact headingRenderImageWitness
    parseGSLTHeadingLine? renderGSLTHeading gsltReadmeBlocks
    gslt_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List GSLTClaim)) (surface : String)
    (c : GSLTClaim) : List (String × List GSLTClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List GSLTClaim) :=
  allGSLTClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderGSLTClaim c) c) []

def ambiguousClaimSurfaces : List (String × List GSLTClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allGSLTClaims.filter (fun c =>
    parseGSLTClaimLine? (renderGSLTClaim c) != some c)
  if fails.isEmpty then
    "GSLT parse-back check: all claim lines roundtrip"
  else
    s!"GSLT parse-back failures: {repr fails}"

#eval
  if gsltHardAuditPasses then
    "GSLT hard audit: no prose-bearing bypass blocks detected"
  else
    "GSLT hard audit: violation detected"

#eval
  let fails := selectedStructuredGSLTLines.filter
    (fun line =>
      match parseSelectedStructuredGSLTLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "GSLT parse-back check: selected headings + bullet families roundtrip"
  else
    s!"GSLT structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "GSLT ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"GSLT ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.GSLTReadmeCompositional
