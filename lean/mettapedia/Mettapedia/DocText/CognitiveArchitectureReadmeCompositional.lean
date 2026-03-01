import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.CognitiveArchitectureReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def framework_N := regN "framework"
private def module_N := regN "module"
private def result_N := regN "result"
private def status_N := regN "status"

inductive CognitiveArchitectureClaim where
  | titleScope
  | fileCountAndSorryStatus
  | metamoSummary
  | openPsiSummary
  | microPsiSummary
  | bridgesSummary
  | valuesSummary
  | metamoBasicRole
  | metamoAppraisalRole
  | metamoDecisionRole
  | metamoCommutativityRole
  | metamoDynamicsRole
  | metamoMainRole
  | openPsiBasicRole
  | openPsiFuzzyLogicRole
  | openPsiActionSelectionRole
  | openPsiMetaMoInstanceRole
  | microPsiBasicRole
  | microPsiMetaMoInstanceRole
  | bridgePlnMetaMoRole
  | bridgeOpenPsiMicroPsiRole
  | bridgeModelExpressivenessRole
  | bridgeMissingValueSystemsRole
  | valueSchwartzRole
  | valueMoralFoundationsRole
  | valueDeontologicalLayerRole
  | valueRelationalValuesRole
  | valueTemporalValuesRole
  | valueMetaValuesRole
  | valueFoetBridgeRole
  | keyResultBothQModules
  | keyResultCommutativity
  | keyResultBanach
  | keyResultConsequentialistGap
  deriving Repr, DecidableEq, BEq

def renderCognitiveArchitectureClaim : CognitiveArchitectureClaim → String
  | .titleScope =>
      mkPresPos (properNameNP "Mettapedia/CognitiveArchitecture")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "MetaMo, OpenPsi, MicroPsi, and their mathematical bridges"))
  | .fileCountAndSorryStatus =>
      mkPresNeg (properNameNP "This module")
        (complV2 (mkV2 (regV "contain")) (properNameNP "sorries across thirty-one files"))
  | .metamoSummary =>
      mkPresPos (properNameNP "MetaMo")
        (copulaNP (properNameNP "a six-file motivational Q-module framework"))
  | .openPsiSummary =>
      mkPresPos (properNameNP "OpenPsi")
        (copulaNP (properNameNP "a five-file formalization of Dorner Psi with six demands and four modulators"))
  | .microPsiSummary =>
      mkPresPos (properNameNP "MicroPsi")
        (copulaNP (properNameNP "a three-file formalization with seven demands and PAD decomposition"))
  | .bridgesSummary =>
      mkPresPos (properNameNP "Bridges" .AgP3Pl)
        (copulaNP (properNameNP "five files of cross-architecture comparison and limits"))
  | .valuesSummary =>
      mkPresPos (properNameNP "Values" .AgP3Pl)
        (copulaNP (properNameNP "nine files extending beyond consequentialism"))
  | .metamoBasicRole =>
      mkPresPos (properNameNP "MetaMo/Basic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "Q-module structure with scalar multiplication"))
  | .metamoAppraisalRole =>
      mkPresPos (properNameNP "MetaMo/Appraisal.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "environmental stimulus appraisal functors"))
  | .metamoDecisionRole =>
      mkPresPos (properNameNP "MetaMo/Decision.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "action selection functors"))
  | .metamoCommutativityRole =>
      mkPresPos (properNameNP "MetaMo/Commutativity.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "appraisal-decision commutativity"))
  | .metamoDynamicsRole =>
      mkPresPos (properNameNP "MetaMo/Dynamics.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "stability via Banach fixed-point arguments"))
  | .metamoMainRole =>
      mkPresPos (properNameNP "MetaMo/Main.lean")
        (complV2 (mkV2 (regV "aggregate")) (properNameNP "the MetaMo module surface"))
  | .openPsiBasicRole =>
      mkPresPos (properNameNP "OpenPsi/Basic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "demands, modulators, and action-selection rules"))
  | .openPsiFuzzyLogicRole =>
      mkPresPos (properNameNP "OpenPsi/FuzzyLogic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "fuzzy satisfaction computation"))
  | .openPsiActionSelectionRole =>
      mkPresPos (properNameNP "OpenPsi/ActionSelection.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "demand-driven action selection"))
  | .openPsiMetaMoInstanceRole =>
      mkPresPos (properNameNP "OpenPsi/MetaMoInstance.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "OpenPsi as a QModule over ENNReal"))
  | .microPsiBasicRole =>
      mkPresPos (properNameNP "MicroPsi/Basic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "demands, PAD model, and utility action selection"))
  | .microPsiMetaMoInstanceRole =>
      mkPresPos (properNameNP "MicroPsi/MetaMoInstance.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "MicroPsi as a QModule over ENNReal"))
  | .bridgePlnMetaMoRole =>
      mkPresPos (properNameNP "Bridges/PLNMetaMoBridge.lean")
        (complV2 (mkV2 (regV "connect")) (properNameNP "PLN evidence quantales to MetaMo"))
  | .bridgeOpenPsiMicroPsiRole =>
      mkPresPos (properNameNP "Bridges/OpenPsiMicroPsiBridge.lean")
        (complV2 (mkV2 (regV "compare")) (properNameNP "OpenPsi and MicroPsi as MetaMo instances"))
  | .bridgeModelExpressivenessRole =>
      mkPresPos (properNameNP "Bridges/ModelExpressiveness.lean")
        (complV2 (mkV2 (regV "analyze")) (properNameNP "expressiveness boundaries"))
  | .bridgeMissingValueSystemsRole =>
      mkPresPos (properNameNP "Bridges/MissingValueSystems.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "value-system gaps outside consequentialism"))
  | .valueSchwartzRole =>
      mkPresPos (properNameNP "Values/SchwartzValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "Schwartz ten-value circumplex structure"))
  | .valueMoralFoundationsRole =>
      mkPresPos (properNameNP "Values/MoralFoundations.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "Haidt six moral foundations"))
  | .valueDeontologicalLayerRole =>
      mkPresPos (properNameNP "Values/DeontologicalLayer.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "duty constraints above consequential utility"))
  | .valueRelationalValuesRole =>
      mkPresPos (properNameNP "Values/RelationalValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "individual-dependent relational values"))
  | .valueTemporalValuesRole =>
      mkPresPos (properNameNP "Values/TemporalValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "legacy and future-generation value structure"))
  | .valueMetaValuesRole =>
      mkPresPos (properNameNP "Values/MetaValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "values about values including corrigibility"))
  | .valueFoetBridgeRole =>
      mkPresPos (properNameNP "Values/FOETBridge.lean")
        (complV2 (mkV2 (regV "connect")) (properNameNP "value formalization to FOET"))
  | .keyResultBothQModules =>
      mkPresPos (properNameNP "OpenPsi and MicroPsi" .AgP3Pl)
        (copulaNP (properNameNP "MetaMo QModule instances"))
  | .keyResultCommutativity =>
      mkPresPos (properNameNP "Appraisal-decision commutativity")
        (copulaNP (properNameNP "proven when the quantale is commutative"))
  | .keyResultBanach =>
      mkPresPos (properNameNP "Contractivity")
        (copulaNP (properNameNP "a sufficient condition for unique motivational equilibrium"))
  | .keyResultConsequentialistGap =>
      mkPresPos (properNameNP "Gap analysis")
        (complV2 (mkV2 (regV "show")) (properNameNP "that both base architectures are fundamentally consequentialist"))

def allCognitiveArchitectureClaims : List CognitiveArchitectureClaim :=
  [ .titleScope
  , .fileCountAndSorryStatus
  , .metamoSummary
  , .openPsiSummary
  , .microPsiSummary
  , .bridgesSummary
  , .valuesSummary
  , .metamoBasicRole
  , .metamoAppraisalRole
  , .metamoDecisionRole
  , .metamoCommutativityRole
  , .metamoDynamicsRole
  , .metamoMainRole
  , .openPsiBasicRole
  , .openPsiFuzzyLogicRole
  , .openPsiActionSelectionRole
  , .openPsiMetaMoInstanceRole
  , .microPsiBasicRole
  , .microPsiMetaMoInstanceRole
  , .bridgePlnMetaMoRole
  , .bridgeOpenPsiMicroPsiRole
  , .bridgeModelExpressivenessRole
  , .bridgeMissingValueSystemsRole
  , .valueSchwartzRole
  , .valueMoralFoundationsRole
  , .valueDeontologicalLayerRole
  , .valueRelationalValuesRole
  , .valueTemporalValuesRole
  , .valueMetaValuesRole
  , .valueFoetBridgeRole
  , .keyResultBothQModules
  , .keyResultCommutativity
  , .keyResultBanach
  , .keyResultConsequentialistGap
  ]

def parseCognitiveArchitectureClaimLine? (line : String) : Option CognitiveArchitectureClaim :=
  let norm := stripTerminalPeriod line
  allCognitiveArchitectureClaims.find? (fun c => renderCognitiveArchitectureClaim c = norm)

inductive CognitiveArchitectureHeading where
  | title
  | modules
  | metamo
  | openPsi
  | microPsi
  | bridges
  | values
  | keyResults
  deriving Repr, DecidableEq, BEq

def renderCognitiveArchitectureHeading : CognitiveArchitectureHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "cognitive architecture")) (linUseN framework_N))
  | .modules =>
      headingPlNP (linUseN module_N)
  | .metamo =>
      headingNP (linUseN (regN "MetaMo"))
  | .openPsi =>
      headingNP (linUseN (regN "OpenPsi"))
  | .microPsi =>
      headingNP (linUseN (regN "MicroPsi"))
  | .bridges =>
      headingPlNP (linUseN (regN "bridge"))
  | .values =>
      headingPlNP (linUseN (regN "value"))
  | .keyResults =>
      headingPlNP (linAdjCN (linPositA (regA "key")) (linUseN result_N))

def allCognitiveArchitectureHeadings : List CognitiveArchitectureHeading :=
  [ .title, .modules, .metamo, .openPsi, .microPsi, .bridges, .values, .keyResults ]

def parseCognitiveArchitectureHeadingLine? (line : String) : Option CognitiveArchitectureHeading :=
  allCognitiveArchitectureHeadings.find? (fun h => renderCognitiveArchitectureHeading h = line)

private def claimBullet (c : CognitiveArchitectureClaim) : ClaimBullet :=
  { text := renderCognitiveArchitectureClaim c }

def cognitiveArchitectureReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderCognitiveArchitectureHeading .title)
  , .paragraph
      [ renderCognitiveArchitectureClaim .titleScope
      , renderCognitiveArchitectureClaim .fileCountAndSorryStatus
      ]
  , .heading 2 (renderCognitiveArchitectureHeading .modules)
  , .heading 3 (renderCognitiveArchitectureHeading .metamo)
  , .paragraph [renderCognitiveArchitectureClaim .metamoSummary]
  , .fileRef "MetaMo/Basic.lean" (renderCognitiveArchitectureClaim .metamoBasicRole)
  , .fileRef "MetaMo/Appraisal.lean" (renderCognitiveArchitectureClaim .metamoAppraisalRole)
  , .fileRef "MetaMo/Decision.lean" (renderCognitiveArchitectureClaim .metamoDecisionRole)
  , .fileRef "MetaMo/Commutativity.lean" (renderCognitiveArchitectureClaim .metamoCommutativityRole)
  , .fileRef "MetaMo/Dynamics.lean" (renderCognitiveArchitectureClaim .metamoDynamicsRole)
  , .fileRef "MetaMo/Main.lean" (renderCognitiveArchitectureClaim .metamoMainRole)
  , .heading 3 (renderCognitiveArchitectureHeading .openPsi)
  , .paragraph [renderCognitiveArchitectureClaim .openPsiSummary]
  , .fileRef "OpenPsi/Basic.lean" (renderCognitiveArchitectureClaim .openPsiBasicRole)
  , .fileRef "OpenPsi/FuzzyLogic.lean" (renderCognitiveArchitectureClaim .openPsiFuzzyLogicRole)
  , .fileRef "OpenPsi/ActionSelection.lean" (renderCognitiveArchitectureClaim .openPsiActionSelectionRole)
  , .fileRef "OpenPsi/MetaMoInstance.lean" (renderCognitiveArchitectureClaim .openPsiMetaMoInstanceRole)
  , .heading 3 (renderCognitiveArchitectureHeading .microPsi)
  , .paragraph [renderCognitiveArchitectureClaim .microPsiSummary]
  , .fileRef "MicroPsi/Basic.lean" (renderCognitiveArchitectureClaim .microPsiBasicRole)
  , .fileRef "MicroPsi/MetaMoInstance.lean" (renderCognitiveArchitectureClaim .microPsiMetaMoInstanceRole)
  , .heading 3 (renderCognitiveArchitectureHeading .bridges)
  , .paragraph [renderCognitiveArchitectureClaim .bridgesSummary]
  , .fileRef "Bridges/PLNMetaMoBridge.lean" (renderCognitiveArchitectureClaim .bridgePlnMetaMoRole)
  , .fileRef "Bridges/OpenPsiMicroPsiBridge.lean" (renderCognitiveArchitectureClaim .bridgeOpenPsiMicroPsiRole)
  , .fileRef "Bridges/ModelExpressiveness.lean" (renderCognitiveArchitectureClaim .bridgeModelExpressivenessRole)
  , .fileRef "Bridges/MissingValueSystems.lean" (renderCognitiveArchitectureClaim .bridgeMissingValueSystemsRole)
  , .heading 3 (renderCognitiveArchitectureHeading .values)
  , .paragraph [renderCognitiveArchitectureClaim .valuesSummary]
  , .fileRef "Values/SchwartzValues.lean" (renderCognitiveArchitectureClaim .valueSchwartzRole)
  , .fileRef "Values/MoralFoundations.lean" (renderCognitiveArchitectureClaim .valueMoralFoundationsRole)
  , .fileRef "Values/DeontologicalLayer.lean" (renderCognitiveArchitectureClaim .valueDeontologicalLayerRole)
  , .fileRef "Values/RelationalValues.lean" (renderCognitiveArchitectureClaim .valueRelationalValuesRole)
  , .fileRef "Values/TemporalValues.lean" (renderCognitiveArchitectureClaim .valueTemporalValuesRole)
  , .fileRef "Values/MetaValues.lean" (renderCognitiveArchitectureClaim .valueMetaValuesRole)
  , .fileRef "Values/FOETBridge.lean" (renderCognitiveArchitectureClaim .valueFoetBridgeRole)
  , .heading 2 (renderCognitiveArchitectureHeading .keyResults)
  , .claimBullets
      [ claimBullet .keyResultBothQModules
      , claimBullet .keyResultCommutativity
      , claimBullet .keyResultBanach
      , claimBullet .keyResultConsequentialistGap
      ]
  ]

def cognitiveArchitectureReadmeMarkdown : String :=
  renderDoc cognitiveArchitectureReadmeBlocks

#eval cognitiveArchitectureReadmeMarkdown

inductive ParsedCognitiveArchitectureStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : CognitiveArchitectureClaim)
  | claimLine (claim : CognitiveArchitectureClaim)
  deriving Repr

def parseSelectedStructuredCognitiveArchitectureLine? (line : String) : Option ParsedCognitiveArchitectureStructuredLine :=
  match parseTechnicalLine? cognitiveArchitectureReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines cognitiveArchitectureReadmeBlocks).contains line then
        match parseClaimBulletLine? parseCognitiveArchitectureClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseCognitiveArchitectureClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredCognitiveArchitectureLines : List String :=
  technicalLines cognitiveArchitectureReadmeBlocks ++
  claimBulletLines cognitiveArchitectureReadmeBlocks ++
  [ ensurePeriod (renderCognitiveArchitectureClaim .titleScope)
  , ensurePeriod (renderCognitiveArchitectureClaim .fileCountAndSorryStatus)
  , ensurePeriod (renderCognitiveArchitectureClaim .metamoSummary)
  ]

def cognitiveArchitectureHardAuditPasses : Bool :=
  cognitiveArchitectureReadmeBlocks.all (blockPassesHardAuditWith parseCognitiveArchitectureClaimLine? parseCognitiveArchitectureHeadingLine?)

theorem cognitiveArchitecture_hard_audit :
    cognitiveArchitectureHardAuditPasses = true := by
  native_decide

def cognitiveArchitectureHeadingImageCheck : Bool :=
  headingRenderImageCheck parseCognitiveArchitectureHeadingLine? renderCognitiveArchitectureHeading cognitiveArchitectureReadmeBlocks

theorem cognitiveArchitecture_heading_images :
    cognitiveArchitectureHeadingImageCheck = true := by
  native_decide

theorem cognitiveArchitecture_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries cognitiveArchitectureReadmeBlocks) :
    ∃ h, parseCognitiveArchitectureHeadingLine? txt = some h ∧ renderCognitiveArchitectureHeading h = txt := by
  exact headingRenderImageWitness
    parseCognitiveArchitectureHeadingLine? renderCognitiveArchitectureHeading cognitiveArchitectureReadmeBlocks
    cognitiveArchitecture_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List CognitiveArchitectureClaim)) (surface : String)
    (c : CognitiveArchitectureClaim) : List (String × List CognitiveArchitectureClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List CognitiveArchitectureClaim) :=
  allCognitiveArchitectureClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderCognitiveArchitectureClaim c) c) []

def ambiguousClaimSurfaces : List (String × List CognitiveArchitectureClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allCognitiveArchitectureClaims.filter (fun c =>
    parseCognitiveArchitectureClaimLine? (renderCognitiveArchitectureClaim c) != some c)
  if fails.isEmpty then
    "CognitiveArchitecture parse-back check: all claim lines roundtrip"
  else
    s!"CognitiveArchitecture parse-back failures: {repr fails}"

#eval
  if cognitiveArchitectureHardAuditPasses then
    "CognitiveArchitecture hard audit: no prose-bearing bypass blocks detected"
  else
    "CognitiveArchitecture hard audit: violation detected"

#eval
  let fails := selectedStructuredCognitiveArchitectureLines.filter
    (fun line =>
      match parseSelectedStructuredCognitiveArchitectureLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "CognitiveArchitecture parse-back check: selected headings + bullet families roundtrip"
  else
    s!"CognitiveArchitecture structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "CognitiveArchitecture ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"CognitiveArchitecture ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.CognitiveArchitectureReadmeCompositional
