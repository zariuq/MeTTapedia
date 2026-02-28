import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.MettapediaReadmeCompositional

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
private def dependency_N := regN "dependency"
private def build_N := regN "build"
private def completeness_N := regN "completeness"
private def contribution_N := regN "contribution"
private def command_N := regN "command"
private def target_N := regN "target"
private def proof_N := regN "proof"
private def policy_N := regN "policy"
private def structure_N := regN "structure"
private def review_N := regN "review"
private def subproject_N := regN "subproject"
private def ontology_N := regN "ontology"
private def theorem_N := regN "theorem"
private def area_N := regN "area"
private def row_N := regN "row"
private def exporter_N := regN "exporter"
private def benchmark_N := regN "benchmark"
private def roundtrip_N := regN "roundtrip"
private def check_N := regN "check"
private def source_N := regN "source"
private def gap_N := regN "gap"
private def root_N := regN "root"

inductive MettapediaClaim where
  | libraryFormalizesCoreAreas
  | layoutPresentsHighLevelStructure
  | toolchainUsesLean4270
  | toolchainUsesMathlib4270
  | dependenciesAreVendoredWhenNeeded
  | buildRunsFromMettapediaRoot
  | firstBuildRunsUpdateAndCache
  | buildUsesLakeJobsThree
  | buildCapsMemoryAtSixGiB
  | buildRunsNiceLakeBuild
  | subprojectKnuthSkilling
  | subprojectCox
  | subprojectShannon
  | subprojectLogic
  | subprojectBorelDeterminacy
  | subprojectOSLF
  | subprojectGSLT
  | subprojectGF
  | subprojectProcessCalculi
  | subprojectCategoryTheory
  | subprojectCognitiveArchitecture
  | subprojectOrderedSemigroups
  | mettailRoundtripChecksExportBuildRewrite
  | mettailBenchmarkRunsThreeRounds
  | mettailExporterPath
  | proofCompletenessVariesBySubproject
  | sorryScanChecksLocalProofGaps
  | knuthSkillingReadmeCarriesBuildTargets
  | contributionKeepProofsExplicit
  | contributionDocumentSources
  | contributionBuildFrequently
  | policyUsesGodelclawOrigin
  | policyUsesZariuqUpstream
  | policyReferencesExternalRepos
  deriving Repr, DecidableEq, BEq

def renderMettapediaClaim : MettapediaClaim → String
  | .libraryFormalizesCoreAreas =>
      let subj := properNameNP "Mettapedia"
      let obj := properNameNP "formalizations across probability theory, information theory, logic, set theory, and related areas"
      mkPresPos subj (complV2 (mkV2 (regV "host")) obj)
  | .layoutPresentsHighLevelStructure =>
      let subj := linDetCN theDefArt (linUseN structure_N)
      let obj := properNameNP "the high-level Mettapedia directory layout"
      mkPresPos subj (complV2 (mkV2 (regV "present")) obj)
  | .toolchainUsesLean4270 =>
      let subj := properNameNP "The toolchain"
      mkPresPos subj (complV2 (mkV2 (regV "use")) (properNameNP "Lean 4.27.0 (see lean-toolchain)"))
  | .toolchainUsesMathlib4270 =>
      let subj := properNameNP "The toolchain"
      mkPresPos subj (complV2 (mkV2 (regV "use")) (properNameNP "Mathlib v4.27.0 (see lakefile.toml)"))
  | .dependenciesAreVendoredWhenNeeded =>
      let subj := properNameNP "Local dependencies" .AgP3Pl
      let vp := advVP (predV (regV "live")) (ppAdv in_Prep (properNameNP "local subdirectories when needed"))
      mkPresPos subj vp
  | .buildRunsFromMettapediaRoot =>
      let subj := linDetCN theDefArt (linUseN build_N)
      let vp := advVP (predV (regV "run")) (ppAdv from_Prep (properNameNP "lean-projects/mettapedia"))
      mkPresPos subj vp
  | .firstBuildRunsUpdateAndCache =>
      let subj := properNameNP "The first build"
      mkPresPos subj (complV2 (mkV2 (regV "run")) (properNameNP "lake update and lake exe cache get"))
  | .buildUsesLakeJobsThree =>
      let subj := linDetCN theDefArt (linUseN build_N)
      mkPresPos subj (complV2 (mkV2 (regV "use")) (properNameNP "LAKE_JOBS=3 by default"))
  | .buildCapsMemoryAtSixGiB =>
      let subj := linDetCN theDefArt (linUseN build_N)
      mkPresPos subj (complV2 (mkV2 (regV "use")) (properNameNP "a 6 GiB memory cap via ulimit -Sv 6291456"))
  | .buildRunsNiceLakeBuild =>
      let subj := linDetCN theDefArt (linUseN build_N)
      mkPresPos subj (complV2 (mkV2 (regV "run")) (properNameNP "nice -n 19 lake build"))
  | .subprojectKnuthSkilling =>
      let subj := properNameNP "ProbabilityTheory/KnuthSkilling"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "Knuth-Skilling Foundations of Inference proofs"))
  | .subprojectCox =>
      let subj := properNameNP "ProbabilityTheory/Cox"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "Cox-style probability calculus formalization"))
  | .subprojectShannon =>
      let subj := properNameNP "InformationTheory/ShannonEntropy"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "Shannon entropy formalization"))
  | .subprojectLogic =>
      let subj := properNameNP "Logic"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "PLN, evidence quantales, Solomonoff induction, exchangeability, and world model calculus"))
  | .subprojectBorelDeterminacy =>
      let subj := properNameNP "SetTheory/BorelDeterminacy"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "Borel determinacy formalization"))
  | .subprojectOSLF =>
      let subj := properNameNP "OSLF"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "core OSLF and GSLT formalizations"))
  | .subprojectGSLT =>
      let subj := properNameNP "GSLT"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "the categorical specification layer for OSLF"))
  | .subprojectGF =>
      let subj := properNameNP "Languages/GF"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "GF abstract syntax, Czech morphology, English clause construction, and an NTT semantic bridge"))
  | .subprojectProcessCalculi =>
      let subj := properNameNP "Languages/ProcessCalculi"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "pi-calculus, rho-calculus, spice calculus, and pi-to-rho encoding"))
  | .subprojectCategoryTheory =>
      let subj := properNameNP "CategoryTheory"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "NativeTypeTheory, a PLN categorical instance, and de Finetti categorical development"))
  | .subprojectCognitiveArchitecture =>
      let subj := properNameNP "CognitiveArchitecture"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "MetaMo, OpenPsi, MicroPsi, and value-system models"))
  | .subprojectOrderedSemigroups =>
      let subj := properNameNP "Algebra/OrderedSemigroups"
      mkPresPos subj (complV2 (mkV2 (regV "host")) (properNameNP "ordered semigroup formalization"))
  | .mettailRoundtripChecksExportBuildRewrite =>
      let subj := properNameNP "The roundtrip script"
      mkPresPos subj (complV2 (mkV2 (regV "check")) (properNameNP "Lean export, Rust build, and one-step rewrite behavior"))
  | .mettailBenchmarkRunsThreeRounds =>
      let subj := properNameNP "The benchmark script"
      mkPresPos subj (complV2 (mkV2 (regV "run")) (properNameNP "three rounds by default"))
  | .mettailExporterPath =>
      let subj := linDetCN theDefArt (linUseN exporter_N)
      mkPresPos subj (copulaNP (properNameNP "hyperon/mettail-rust/scripts/lean/ExportMeTTaMinimalRoundTrip.lean"))
  | .proofCompletenessVariesBySubproject =>
      let subj := linDetCN theDefArt (linAdjCN (linPositA (regA "proof")) (linUseN completeness_N))
      let vp := advVP (predV (regV "vary")) (ppAdv by_Prep (linDetCN theDefArt (linUseN subproject_N)))
      mkPresPos subj vp
  | .sorryScanChecksLocalProofGaps =>
      let subj := linDetCN theDefArt (linAdjCN (linPositA (regA "local")) (linUseN check_N))
      mkPresPos subj (complV2 (mkV2 (regV "run")) (properNameNP "rg -n \"sorry\" Mettapedia/ to find proof gaps"))
  | .knuthSkillingReadmeCarriesBuildTargets =>
      let subj := properNameNP "Mettapedia/ProbabilityTheory/KnuthSkilling/README.md"
      mkPresPos subj (complV2 (mkV2 (regV "contain")) (properNameNP "the Knuth-Skilling structure and build targets"))
  | .contributionKeepProofsExplicit =>
      let subj := linDetCN theDefArt (linUseN contribution_N)
      mkPresPos subj (complV2 (mkV2 (regV "require")) (properNameNP "explicit proofs"))
  | .contributionDocumentSources =>
      let subj := linDetCN theDefArt (linUseN contribution_N)
      mkPresPos subj (complV2 (mkV2 (regV "require")) (properNameNP "documented theorem sources"))
  | .contributionBuildFrequently =>
      let subj := linDetCN theDefArt (linUseN contribution_N)
      mkPresPos subj (complV2 (mkV2 (regV "require")) (properNameNP "frequent lake build checks"))
  | .policyUsesGodelclawOrigin =>
      let subj := linDetCN theDefArt (linUseN policy_N)
      mkPresPos subj (complV2 (mkV2 (regV "use")) (properNameNP "godelclaw forks as origin remotes"))
  | .policyUsesZariuqUpstream =>
      let subj := linDetCN theDefArt (linUseN policy_N)
      mkPresPos subj (complV2 (mkV2 (regV "use")) (properNameNP "zariuq repos as upstream remotes"))
  | .policyReferencesExternalRepos =>
      let subj := linDetCN theDefArt (linUseN policy_N)
      mkPresPos subj (complV2 (mkV2 (regV "reference")) (properNameNP "EXTERNAL_REPOS.md for exact commands"))


def allMettapediaClaims : List MettapediaClaim :=
  [ .libraryFormalizesCoreAreas
  , .layoutPresentsHighLevelStructure
  , .toolchainUsesLean4270
  , .toolchainUsesMathlib4270
  , .dependenciesAreVendoredWhenNeeded
  , .buildRunsFromMettapediaRoot
  , .firstBuildRunsUpdateAndCache
  , .buildUsesLakeJobsThree
  , .buildCapsMemoryAtSixGiB
  , .buildRunsNiceLakeBuild
  , .subprojectKnuthSkilling
  , .subprojectCox
  , .subprojectShannon
  , .subprojectLogic
  , .subprojectBorelDeterminacy
  , .subprojectOSLF
  , .subprojectGSLT
  , .subprojectGF
  , .subprojectProcessCalculi
  , .subprojectCategoryTheory
  , .subprojectCognitiveArchitecture
  , .subprojectOrderedSemigroups
  , .mettailRoundtripChecksExportBuildRewrite
  , .mettailBenchmarkRunsThreeRounds
  , .mettailExporterPath
  , .proofCompletenessVariesBySubproject
  , .sorryScanChecksLocalProofGaps
  , .knuthSkillingReadmeCarriesBuildTargets
  , .contributionKeepProofsExplicit
  , .contributionDocumentSources
  , .contributionBuildFrequently
  , .policyUsesGodelclawOrigin
  , .policyUsesZariuqUpstream
  , .policyReferencesExternalRepos
  ]

def parseMettapediaClaimLine? (line : String) : Option MettapediaClaim :=
  let norm := stripTerminalPeriod line
  allMettapediaClaims.find? (fun c => renderMettapediaClaim c = norm)

inductive MettapediaHeading where
  | title
  | layoutHighLevel
  | toolchain
  | build
  | notableSubprojects
  | leanToMettailExample
  | statusAndReview
  | contributing
  | externalRepoPolicy
  deriving Repr, DecidableEq, BEq

def renderMettapediaHeading : MettapediaHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (compoundA "Mettapedia"))
        (linAdjCN (linPositA (compoundA "formalized mathematics")) (linUseN (regN "encyclopedia"))))
  | .layoutHighLevel =>
      headingNP (linAdjCN (linPositA (compoundA "high-level")) (linUseN structure_N))
  | .toolchain =>
      headingNP (linUseN (regN "toolchain"))
  | .build =>
      headingNP (linUseN build_N)
  | .notableSubprojects =>
      headingPlNP (linAdjCN (linPositA (regA "notable")) (linUseN subproject_N))
  | .leanToMettailExample =>
      headingNP (linAdjCN (linPositA (compoundA "Lean to mettail-rust")) (linUseN (regN "example")))
  | .statusAndReview =>
      headingNP (linAdjCN (linPositA (regA "status")) (linUseN review_N))
  | .contributing =>
      headingNP (linUseN contribution_N)
  | .externalRepoPolicy =>
      headingNP (linAdjCN (linPositA (regA "external repo")) (linUseN policy_N))

def allMettapediaHeadings : List MettapediaHeading :=
  [ .title
  , .layoutHighLevel
  , .toolchain
  , .build
  , .notableSubprojects
  , .leanToMettailExample
  , .statusAndReview
  , .contributing
  , .externalRepoPolicy
  ]

def parseMettapediaHeadingLine? (line : String) : Option MettapediaHeading :=
  allMettapediaHeadings.find? (fun h => renderMettapediaHeading h = line)

private def claimBullet (c : MettapediaClaim) : ClaimBullet :=
  { text := renderMettapediaClaim c }

def mettapediaReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderMettapediaHeading .title)
  , .paragraph [renderMettapediaClaim .libraryFormalizesCoreAreas]
  , .heading 2 (renderMettapediaHeading .layoutHighLevel)
  , .paragraph [renderMettapediaClaim .layoutPresentsHighLevelStructure]
  , .codeBlock ""
      "Mettapedia/\n├── Algebra/\n├── Bridge/\n├── CategoricalLogic/\n├── CategoryTheory/\n├── CognitiveArchitecture/\n├── Computability/\n├── Examples/\n├── GraphTheory/\n├── GSLT/\n├── Implementation/\n├── InformationTheory/\n├── Languages/\n├── Logic/\n├── MeasureTheory/\n├── Metatheory/\n├── OSLF/\n├── ProbabilityTheory/\n├── QuantumTheory/\n├── SetTheory/\n├── UniversalAI/\n└── external/"
  , .heading 2 (renderMettapediaHeading .toolchain)
  , .claimBullets
      [ claimBullet .toolchainUsesLean4270
      , claimBullet .toolchainUsesMathlib4270
      , claimBullet .dependenciesAreVendoredWhenNeeded
      ]
  , .heading 2 (renderMettapediaHeading .build)
  , .codeBlock "bash"
      "cd lean-projects/mettapedia\nlake update && lake exe cache get\n\nexport LAKE_JOBS=3\nulimit -Sv 6291456\nnice -n 19 lake build"
  , .claimBullets
      [ claimBullet .buildRunsFromMettapediaRoot
      , claimBullet .firstBuildRunsUpdateAndCache
      , claimBullet .buildUsesLakeJobsThree
      , claimBullet .buildCapsMemoryAtSixGiB
      , claimBullet .buildRunsNiceLakeBuild
      ]
  , .heading 2 (renderMettapediaHeading .notableSubprojects)
  , .fileRef "ProbabilityTheory/KnuthSkilling/" (renderMettapediaClaim .subprojectKnuthSkilling)
  , .fileRef "ProbabilityTheory/Cox/" (renderMettapediaClaim .subprojectCox)
  , .fileRef "InformationTheory/ShannonEntropy/" (renderMettapediaClaim .subprojectShannon)
  , .fileRef "Logic/" (renderMettapediaClaim .subprojectLogic)
  , .fileRef "SetTheory/BorelDeterminacy/" (renderMettapediaClaim .subprojectBorelDeterminacy)
  , .fileRef "OSLF/" (renderMettapediaClaim .subprojectOSLF)
  , .fileRef "GSLT/" (renderMettapediaClaim .subprojectGSLT)
  , .fileRef "Languages/GF/" (renderMettapediaClaim .subprojectGF)
  , .fileRef "Languages/ProcessCalculi/" (renderMettapediaClaim .subprojectProcessCalculi)
  , .fileRef "CategoryTheory/" (renderMettapediaClaim .subprojectCategoryTheory)
  , .fileRef "CognitiveArchitecture/" (renderMettapediaClaim .subprojectCognitiveArchitecture)
  , .fileRef "Algebra/OrderedSemigroups/" (renderMettapediaClaim .subprojectOrderedSemigroups)
  , .heading 2 (renderMettapediaHeading .leanToMettailExample)
  , .paragraph
      [ renderMettapediaClaim .mettailRoundtripChecksExportBuildRewrite
      , renderMettapediaClaim .mettailBenchmarkRunsThreeRounds
      ]
  , .codeBlock "bash"
      "cd ~/claude/hyperon/mettail-rust\n\n./scripts/roundtrip_mettaminimal.sh\n./scripts/bench_mettaminimal_roundtrip.sh"
  , .claimBullets [claimBullet .mettailExporterPath]
  , .heading 2 (renderMettapediaHeading .statusAndReview)
  , .claimBullets
      [ claimBullet .proofCompletenessVariesBySubproject
      , claimBullet .sorryScanChecksLocalProofGaps
      , claimBullet .knuthSkillingReadmeCarriesBuildTargets
      ]
  , .codeBlock "bash"
      "rg -n \"sorry\" Mettapedia/"
  , .heading 2 (renderMettapediaHeading .contributing)
  , .claimBullets
      [ claimBullet .contributionKeepProofsExplicit
      , claimBullet .contributionDocumentSources
      , claimBullet .contributionBuildFrequently
      ]
  , .heading 2 (renderMettapediaHeading .externalRepoPolicy)
  , .claimBullets
      [ claimBullet .policyUsesGodelclawOrigin
      , claimBullet .policyUsesZariuqUpstream
      , claimBullet .policyReferencesExternalRepos
      ]
  ]

def mettapediaReadmeMarkdown : String :=
  renderDoc mettapediaReadmeBlocks

#eval mettapediaReadmeMarkdown

inductive ParsedMettapediaStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : MettapediaClaim)
  | claimLine (claim : MettapediaClaim)
  deriving Repr

def parseSelectedStructuredMettapediaLine? (line : String) : Option ParsedMettapediaStructuredLine :=
  match parseTechnicalLine? mettapediaReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines mettapediaReadmeBlocks).contains line then
        match parseClaimBulletLine? parseMettapediaClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseMettapediaClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredMettapediaLines : List String :=
  technicalLines mettapediaReadmeBlocks ++
  claimBulletLines mettapediaReadmeBlocks ++
  [ ensurePeriod (renderMettapediaClaim .libraryFormalizesCoreAreas)
  , ensurePeriod (renderMettapediaClaim .layoutPresentsHighLevelStructure)
  , ensurePeriod (renderMettapediaClaim .mettailRoundtripChecksExportBuildRewrite)
  , ensurePeriod (renderMettapediaClaim .mettailBenchmarkRunsThreeRounds)
  ]

def mettapediaHardAuditPasses : Bool :=
  mettapediaReadmeBlocks.all (blockPassesHardAuditWith parseMettapediaClaimLine? parseMettapediaHeadingLine?)

theorem mettapedia_hard_audit :
    mettapediaHardAuditPasses = true := by
  native_decide

def mettapediaHeadingImageCheck : Bool :=
  headingRenderImageCheck parseMettapediaHeadingLine? renderMettapediaHeading mettapediaReadmeBlocks

theorem mettapedia_heading_images :
    mettapediaHeadingImageCheck = true := by
  native_decide

theorem mettapedia_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries mettapediaReadmeBlocks) :
    ∃ h, parseMettapediaHeadingLine? txt = some h ∧ renderMettapediaHeading h = txt := by
  exact headingRenderImageWitness
    parseMettapediaHeadingLine? renderMettapediaHeading mettapediaReadmeBlocks
    mettapedia_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List MettapediaClaim)) (surface : String)
    (c : MettapediaClaim) : List (String × List MettapediaClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List MettapediaClaim) :=
  allMettapediaClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderMettapediaClaim c) c) []

def ambiguousClaimSurfaces : List (String × List MettapediaClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allMettapediaClaims.filter (fun c =>
    parseMettapediaClaimLine? (renderMettapediaClaim c) != some c)
  if fails.isEmpty then
    "Mettapedia parse-back check: all claim lines roundtrip"
  else
    s!"Mettapedia parse-back failures: {repr fails}"

#eval
  if mettapediaHardAuditPasses then
    "Mettapedia hard audit: no prose-bearing bypass blocks detected"
  else
    "Mettapedia hard audit: violation detected"

#eval
  let fails := selectedStructuredMettapediaLines.filter
    (fun line =>
      match parseSelectedStructuredMettapediaLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "Mettapedia parse-back check: selected headings + bullet families roundtrip"
  else
    s!"Mettapedia structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "Mettapedia ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"Mettapedia ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.MettapediaReadmeCompositional
