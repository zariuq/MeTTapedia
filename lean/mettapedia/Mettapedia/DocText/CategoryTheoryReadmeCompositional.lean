import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.CategoryTheoryReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def foundation_N := regN "foundation"
private def architecture_N := regN "architecture"
private def strand_N := regN "strand"
private def status_N := regN "status"
private def flow_N := regN "flow"
private def file_N := regN "file"

inductive CategoryTheoryClaim where
  | titleScope
  | architectureHasThreeStrands
  | strandOneSummary
  | strandTwoSummary
  | strandThreeSummary
  | lambdaTheoryFileRole
  | nativeTypeTheoryFileRole
  | plnInstanceFileRole
  | plnTermsFileRole
  | modalTypesFileRole
  | hypercubeFileRole
  | plnSemiringQuantaleFileRole
  | deFinettiCategoricalInterfaceFileRole
  | deFinettiPermutationConeFileRole
  | deFinettiKernelInterfaceFileRole
  | deFinettiSequenceKernelConeFileRole
  | deFinettiHausdorffBridgeFileRole
  | deFinettiPerNDiagramFileRole
  | deFinettiGlobalFinitaryDiagramFileRole
  | deFinettiLimitConePackageFileRole
  | deFinettiKleisliGirySkeletonFileRole
  | deFinettiMarkovCategoryBridgeFileRole
  | deFinettiExternalBridgeFileRole
  | deFinettiStableExportsFileRole
  | deFinettiExportsFileRole
  | fuzzyFrameFileRole
  | toglFileRole
  | toposInternalLanguageFileRole
  | proofStatusMajorityProven
  | proofStatusRemainingFiles
  | dependencyFlowCaption
  deriving Repr, DecidableEq, BEq

def renderCategoryTheoryClaim : CategoryTheoryClaim → String
  | .titleScope =>
      mkPresPos (properNameNP "Mettapedia/CategoryTheory")
        (complV2 (mkV2 (regV "provide")) (properNameNP "categorical foundations for OSLF, PLN, and de Finetti formalization"))
  | .architectureHasThreeStrands =>
      mkPresPos (properNameNP "The architecture")
        (copulaNP (properNameNP "three main strands"))
  | .strandOneSummary =>
      mkPresPos (properNameNP "Strand one")
        (copulaNP (properNameNP "lambda theory and native type theory across seven files"))
  | .strandTwoSummary =>
      mkPresPos (properNameNP "Strand two")
        (copulaNP (properNameNP "categorical de Finetti across thirteen files"))
  | .strandThreeSummary =>
      mkPresPos (properNameNP "Strand three")
        (copulaNP (properNameNP "supporting files for fuzzy frames, graph theory, and internal language"))
  | .lambdaTheoryFileRole =>
      mkPresPos (properNameNP "LambdaTheory.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "SubobjectFibration and LambdaTheory with finite limits and Heyting fibers"))
  | .nativeTypeTheoryFileRole =>
      mkPresPos (properNameNP "NativeTypeTheory.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "NativeTypeBundle as a Grothendieck construction"))
  | .plnInstanceFileRole =>
      mkPresPos (properNameNP "PLNInstance.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "PLN as a frame-fiber instance with modal composition"))
  | .plnTermsFileRole =>
      mkPresPos (properNameNP "PLNTerms.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "PLN term syntax and reduction relation"))
  | .modalTypesFileRole =>
      mkPresPos (properNameNP "ModalTypes.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "modal types via comprehension and rely-possibly semantics"))
  | .hypercubeFileRole =>
      mkPresPos (properNameNP "Hypercube.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "the H_Sigma endofunctor for modal type generation"))
  | .plnSemiringQuantaleFileRole =>
      mkPresPos (properNameNP "PLNSemiringQuantale.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "a semiring quantale on Evidence with tensor and plus"))
  | .deFinettiCategoricalInterfaceFileRole =>
      mkPresPos (properNameNP "DeFinettiCategoricalInterface.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "a qualitative factorization interface"))
  | .deFinettiPermutationConeFileRole =>
      mkPresPos (properNameNP "DeFinettiPermutationCone.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "permutation commutation of finite-prefix laws"))
  | .deFinettiKernelInterfaceFileRole =>
      mkPresPos (properNameNP "DeFinettiKernelInterface.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "kernel-level categorical de Finetti interfaces"))
  | .deFinettiSequenceKernelConeFileRole =>
      mkPresPos (properNameNP "DeFinettiSequenceKernelCone.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "sequence-kernel permutation cones on Bool power N"))
  | .deFinettiHausdorffBridgeFileRole =>
      mkPresPos (properNameNP "DeFinettiHausdorffBridge.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "Hausdorff moment uniqueness links"))
  | .deFinettiPerNDiagramFileRole =>
      mkPresPos (properNameNP "DeFinettiPerNDiagram.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "per-n permutation diagram surfaces"))
  | .deFinettiGlobalFinitaryDiagramFileRole =>
      mkPresPos (properNameNP "DeFinettiGlobalFinitaryDiagram.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "global finitary-permutation indexing"))
  | .deFinettiLimitConePackageFileRole =>
      mkPresPos (properNameNP "DeFinettiLimitConePackage.lean")
        (complV2 (mkV2 (regV "package")) (properNameNP "the universal-property layer"))
  | .deFinettiKleisliGirySkeletonFileRole =>
      mkPresPos (properNameNP "DeFinettiKleisliGirySkeleton.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "Kleisli Giry global diagrams and IID cones"))
  | .deFinettiMarkovCategoryBridgeFileRole =>
      mkPresPos (properNameNP "DeFinettiMarkovCategoryBridge.lean")
        (complV2 (mkV2 (regV "provide")) (properNameNP "a MarkovCategoryCore viewpoint"))
  | .deFinettiExternalBridgeFileRole =>
      mkPresPos (properNameNP "DeFinettiExternalBridge.lean")
        (complV2 (mkV2 (regV "provide")) (properNameNP "bridges to vendored exchangeability formalization"))
  | .deFinettiStableExportsFileRole =>
      mkPresPos (properNameNP "DeFinettiStableExports.lean")
        (complV2 (mkV2 (regV "provide")) (properNameNP "stable alias exports"))
  | .deFinettiExportsFileRole =>
      mkPresPos (properNameNP "DeFinettiExports.lean")
        (complV2 (mkV2 (regV "provide")) (properNameNP "the recommended import surface"))
  | .fuzzyFrameFileRole =>
      mkPresPos (properNameNP "FuzzyFrame.lean")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "the unit interval frame for PLN truth values"))
  | .toglFileRole =>
      mkPresPos (properNameNP "TOGL.lean")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "Greg Meredith's theory of graphs"))
  | .toposInternalLanguageFileRole =>
      mkPresPos (properNameNP "Topos/InternalLanguage.lean")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "Kripke-Joyal semantics for OSLF"))
  | .proofStatusMajorityProven =>
      mkPresPos (properNameNP "Nineteen of twenty-three files" .AgP3Pl)
        (copulaAdj "fully proven with zero sorries")
  | .proofStatusRemainingFiles =>
      mkPresPos (properNameNP "The remaining four files" .AgP3Pl)
        (copulaNP (properNameNP "TOGL one sorry, FuzzyFrame two sorries, ModalTypes one sorry, and Hypercube two sorries"))
  | .dependencyFlowCaption =>
      mkPresPos (properNameNP "The dependency flow")
        (copulaNP (properNameNP "the following architecture diagram"))

def allCategoryTheoryClaims : List CategoryTheoryClaim :=
  [ .titleScope
  , .architectureHasThreeStrands
  , .strandOneSummary
  , .strandTwoSummary
  , .strandThreeSummary
  , .lambdaTheoryFileRole
  , .nativeTypeTheoryFileRole
  , .plnInstanceFileRole
  , .plnTermsFileRole
  , .modalTypesFileRole
  , .hypercubeFileRole
  , .plnSemiringQuantaleFileRole
  , .deFinettiCategoricalInterfaceFileRole
  , .deFinettiPermutationConeFileRole
  , .deFinettiKernelInterfaceFileRole
  , .deFinettiSequenceKernelConeFileRole
  , .deFinettiHausdorffBridgeFileRole
  , .deFinettiPerNDiagramFileRole
  , .deFinettiGlobalFinitaryDiagramFileRole
  , .deFinettiLimitConePackageFileRole
  , .deFinettiKleisliGirySkeletonFileRole
  , .deFinettiMarkovCategoryBridgeFileRole
  , .deFinettiExternalBridgeFileRole
  , .deFinettiStableExportsFileRole
  , .deFinettiExportsFileRole
  , .fuzzyFrameFileRole
  , .toglFileRole
  , .toposInternalLanguageFileRole
  , .proofStatusMajorityProven
  , .proofStatusRemainingFiles
  , .dependencyFlowCaption
  ]

def parseCategoryTheoryClaimLine? (line : String) : Option CategoryTheoryClaim :=
  let norm := stripTerminalPeriod line
  allCategoryTheoryClaims.find? (fun c => renderCategoryTheoryClaim c = norm)

inductive CategoryTheoryHeading where
  | title
  | architecture
  | strandOne
  | strandTwo
  | strandThree
  | proofStatus
  | dependencyFlow
  deriving Repr, DecidableEq, BEq

def renderCategoryTheoryHeading : CategoryTheoryHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "CategoryTheory")) (linUseN foundation_N))
  | .architecture =>
      headingNP (linUseN architecture_N)
  | .strandOne =>
      headingNP (linAdjCN (linPositA (compoundA "Lambda theory and native type theory")) (linUseN strand_N))
  | .strandTwo =>
      headingNP (linAdjCN (linPositA (compoundA "categorical de Finetti")) (linUseN strand_N))
  | .strandThree =>
      headingNP (linUseN (regN "other"))
  | .proofStatus =>
      headingNP (linAdjCN (linPositA (regA "proof")) (linUseN status_N))
  | .dependencyFlow =>
      headingNP (linAdjCN (linPositA (regA "dependency")) (linUseN flow_N))

def allCategoryTheoryHeadings : List CategoryTheoryHeading :=
  [ .title, .architecture, .strandOne, .strandTwo, .strandThree, .proofStatus, .dependencyFlow ]

def parseCategoryTheoryHeadingLine? (line : String) : Option CategoryTheoryHeading :=
  allCategoryTheoryHeadings.find? (fun h => renderCategoryTheoryHeading h = line)

private def claimBullet (c : CategoryTheoryClaim) : ClaimBullet :=
  { text := renderCategoryTheoryClaim c }

def categoryTheoryReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderCategoryTheoryHeading .title)
  , .paragraph [renderCategoryTheoryClaim .titleScope]
  , .heading 2 (renderCategoryTheoryHeading .architecture)
  , .claimBullets
      [ claimBullet .architectureHasThreeStrands
      , claimBullet .strandOneSummary
      , claimBullet .strandTwoSummary
      , claimBullet .strandThreeSummary
      ]
  , .heading 3 (renderCategoryTheoryHeading .strandOne)
  , .fileRef "LambdaTheory.lean" (renderCategoryTheoryClaim .lambdaTheoryFileRole)
  , .fileRef "NativeTypeTheory.lean" (renderCategoryTheoryClaim .nativeTypeTheoryFileRole)
  , .fileRef "PLNInstance.lean" (renderCategoryTheoryClaim .plnInstanceFileRole)
  , .fileRef "PLNTerms.lean" (renderCategoryTheoryClaim .plnTermsFileRole)
  , .fileRef "ModalTypes.lean" (renderCategoryTheoryClaim .modalTypesFileRole)
  , .fileRef "Hypercube.lean" (renderCategoryTheoryClaim .hypercubeFileRole)
  , .fileRef "PLNSemiringQuantale.lean" (renderCategoryTheoryClaim .plnSemiringQuantaleFileRole)
  , .heading 3 (renderCategoryTheoryHeading .strandTwo)
  , .fileRef "DeFinettiCategoricalInterface.lean" (renderCategoryTheoryClaim .deFinettiCategoricalInterfaceFileRole)
  , .fileRef "DeFinettiPermutationCone.lean" (renderCategoryTheoryClaim .deFinettiPermutationConeFileRole)
  , .fileRef "DeFinettiKernelInterface.lean" (renderCategoryTheoryClaim .deFinettiKernelInterfaceFileRole)
  , .fileRef "DeFinettiSequenceKernelCone.lean" (renderCategoryTheoryClaim .deFinettiSequenceKernelConeFileRole)
  , .fileRef "DeFinettiHausdorffBridge.lean" (renderCategoryTheoryClaim .deFinettiHausdorffBridgeFileRole)
  , .fileRef "DeFinettiPerNDiagram.lean" (renderCategoryTheoryClaim .deFinettiPerNDiagramFileRole)
  , .fileRef "DeFinettiGlobalFinitaryDiagram.lean" (renderCategoryTheoryClaim .deFinettiGlobalFinitaryDiagramFileRole)
  , .fileRef "DeFinettiLimitConePackage.lean" (renderCategoryTheoryClaim .deFinettiLimitConePackageFileRole)
  , .fileRef "DeFinettiKleisliGirySkeleton.lean" (renderCategoryTheoryClaim .deFinettiKleisliGirySkeletonFileRole)
  , .fileRef "DeFinettiMarkovCategoryBridge.lean" (renderCategoryTheoryClaim .deFinettiMarkovCategoryBridgeFileRole)
  , .fileRef "DeFinettiExternalBridge.lean" (renderCategoryTheoryClaim .deFinettiExternalBridgeFileRole)
  , .fileRef "DeFinettiStableExports.lean" (renderCategoryTheoryClaim .deFinettiStableExportsFileRole)
  , .fileRef "DeFinettiExports.lean" (renderCategoryTheoryClaim .deFinettiExportsFileRole)
  , .heading 3 (renderCategoryTheoryHeading .strandThree)
  , .fileRef "FuzzyFrame.lean" (renderCategoryTheoryClaim .fuzzyFrameFileRole)
  , .fileRef "TOGL.lean" (renderCategoryTheoryClaim .toglFileRole)
  , .fileRef "Topos/InternalLanguage.lean" (renderCategoryTheoryClaim .toposInternalLanguageFileRole)
  , .heading 2 (renderCategoryTheoryHeading .proofStatus)
  , .claimBullets
      [ claimBullet .proofStatusMajorityProven
      , claimBullet .proofStatusRemainingFiles
      ]
  , .heading 2 (renderCategoryTheoryHeading .dependencyFlow)
  , .paragraph [renderCategoryTheoryClaim .dependencyFlowCaption]
  , .codeBlock ""
      "LambdaTheory -> PLNInstance -> NativeTypeTheory\n                    |\n              PLNTerms -> ModalTypes -> Hypercube\n\nDeFinettiCategoricalInterface -> PermutationCone -> KernelInterface\n  -> SequenceKernelCone -> HausdorffBridge -> PerNDiagram\n  -> GlobalFinitaryDiagram -> KleisliGirySkeleton -> StableExports -> Exports"
  ]

def categoryTheoryReadmeMarkdown : String :=
  renderDoc categoryTheoryReadmeBlocks

#eval categoryTheoryReadmeMarkdown

inductive ParsedCategoryTheoryStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : CategoryTheoryClaim)
  | claimLine (claim : CategoryTheoryClaim)
  deriving Repr

def parseSelectedStructuredCategoryTheoryLine? (line : String) : Option ParsedCategoryTheoryStructuredLine :=
  match parseTechnicalLine? categoryTheoryReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines categoryTheoryReadmeBlocks).contains line then
        match parseClaimBulletLine? parseCategoryTheoryClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseCategoryTheoryClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredCategoryTheoryLines : List String :=
  technicalLines categoryTheoryReadmeBlocks ++
  claimBulletLines categoryTheoryReadmeBlocks ++
  [ ensurePeriod (renderCategoryTheoryClaim .titleScope)
  , ensurePeriod (renderCategoryTheoryClaim .architectureHasThreeStrands)
  , ensurePeriod (renderCategoryTheoryClaim .proofStatusMajorityProven)
  ]

def categoryTheoryHardAuditPasses : Bool :=
  categoryTheoryReadmeBlocks.all (blockPassesHardAuditWith parseCategoryTheoryClaimLine? parseCategoryTheoryHeadingLine?)

theorem categoryTheory_hard_audit :
    categoryTheoryHardAuditPasses = true := by
  native_decide

def categoryTheoryHeadingImageCheck : Bool :=
  headingRenderImageCheck parseCategoryTheoryHeadingLine? renderCategoryTheoryHeading categoryTheoryReadmeBlocks

theorem categoryTheory_heading_images :
    categoryTheoryHeadingImageCheck = true := by
  native_decide

theorem categoryTheory_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries categoryTheoryReadmeBlocks) :
    ∃ h, parseCategoryTheoryHeadingLine? txt = some h ∧ renderCategoryTheoryHeading h = txt := by
  exact headingRenderImageWitness
    parseCategoryTheoryHeadingLine? renderCategoryTheoryHeading categoryTheoryReadmeBlocks
    categoryTheory_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List CategoryTheoryClaim)) (surface : String)
    (c : CategoryTheoryClaim) : List (String × List CategoryTheoryClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List CategoryTheoryClaim) :=
  allCategoryTheoryClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderCategoryTheoryClaim c) c) []

def ambiguousClaimSurfaces : List (String × List CategoryTheoryClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allCategoryTheoryClaims.filter (fun c =>
    parseCategoryTheoryClaimLine? (renderCategoryTheoryClaim c) != some c)
  if fails.isEmpty then
    "CategoryTheory parse-back check: all claim lines roundtrip"
  else
    s!"CategoryTheory parse-back failures: {repr fails}"

#eval
  if categoryTheoryHardAuditPasses then
    "CategoryTheory hard audit: no prose-bearing bypass blocks detected"
  else
    "CategoryTheory hard audit: violation detected"

#eval
  let fails := selectedStructuredCategoryTheoryLines.filter
    (fun line =>
      match parseSelectedStructuredCategoryTheoryLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "CategoryTheory parse-back check: selected headings + bullet families roundtrip"
  else
    s!"CategoryTheory structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "CategoryTheory ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"CategoryTheory ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.CategoryTheoryReadmeCompositional
