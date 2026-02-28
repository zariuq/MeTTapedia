import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.AtpsReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def premise_N := regN "premise"
private def selection_N := regN "selection"
private def experiment_N := regN "experiment"
private def selector_N := regN "selector"
private def inference_N := regN "inference"
private def script_N := regN "script"
private def preparation_N := regN "preparation"
private def evaluation_N := regN "evaluation"
private def result_N := regN "result"
private def structure_N := regN "structure"
private def start_N := regN "start"
private def limit_N := regN "limit"
private def dependency_N := regN "dependency"
private def reference_N := regN "reference"
private def table_N := regN "table"
private def driver_N := regN "driver"
private def library_N := regN "library"
private def machine_N := regN "machine"

inductive AtpsClaim where
  | runPlnPremiseSelectionExperiments
  | selectorsRunPeTTaInference
  | pythonDriversHandlePreparationAndEvaluation
  | resultMashNb
  | resultPlnNb
  | resultPlnNormalNb
  | resultChainyBaseline
  | resultPlnKnnNb
  | resultPlnEnhanced
  | resultPlnRule
  | resultPlnKnn
  | resultMashKnn
  | selectorPlnNb
  | selectorPlnRule
  | selectorPlnKnn
  | selectorPlnKnnNb
  | selectorPlnEnhanced
  | selectorPlnNormalNb
  | pettASelectorsPath
  | pythonDriversPath
  | coreLimit
  | timeoutLimit
  | memoryLimit
  | dependencyPeTTa
  | dependencyPlnLibraries
  | dependencyEProver
  | dependencyPython
  | referenceBlanchette
  | referenceGoertzel
  | referenceJakubuv
  deriving Repr, DecidableEq, BEq

def renderAtpsClaim : AtpsClaim → String
  | .runPlnPremiseSelectionExperiments =>
      let subj := linMassPluralNP
        (linAdjCN (linPositA (regA "premise")) (linUseN experiment_N))
      let obj := properNameNP "Probabilistic Logic Networks on the extended MPTP 5k dataset"
      mkPresPos subj (complV2 (mkV2 (regV "use")) obj)
  | .selectorsRunPeTTaInference =>
      let subj := linMassPluralNP (linUseN selector_N)
      let obj := linMassNP
        (linAdjCN (linPositA (regA "PeTTa")) (linUseN inference_N))
      mkPresPos subj (complV2 (mkV2 (regV "run")) obj)
  | .pythonDriversHandlePreparationAndEvaluation =>
      let subj := properNameNP "Python drivers" .AgP3Pl
      let obj := linConjNP and_Conj
        [ linMassNP (linUseN preparation_N)
        , linMassNP (linUseN evaluation_N)
        ]
      mkPresPos subj (complV2 (mkV2 (regV "handle")) obj)
  | .resultMashNb =>
      let subj := properNameNP "MaSh NB"
      let obj := properNameNP "283 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultPlnNb =>
      let subj := properNameNP "PLN-NB"
      let obj := properNameNP "281 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultPlnNormalNb =>
      let subj := properNameNP "PLN-Normal-NB"
      let obj := properNameNP "279 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultChainyBaseline =>
      let subj := properNameNP "Chainy baseline"
      let obj := properNameNP "278 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultPlnKnnNb =>
      let subj := properNameNP "PLN-kNN+NB"
      let obj := properNameNP "276 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultPlnEnhanced =>
      let subj := properNameNP "PLN-Enhanced"
      let obj := properNameNP "276 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultPlnRule =>
      let subj := properNameNP "PLN-Rule"
      let obj := properNameNP "275 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultPlnKnn =>
      let subj := properNameNP "PLN-kNN"
      let obj := properNameNP "272 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .resultMashKnn =>
      let subj := properNameNP "MaSh kNN"
      let obj := properNameNP "272 of 800 validation problems"
      let vp := advVP
        (complV2 (mkV2 (regV "solve")) obj)
        (ppAdv at_Prep (properNameNP "top-256 with E 5s"))
      mkPresPos subj vp
  | .selectorPlnNb =>
      let subj := properNameNP "PLN-NB"
      let obj := properNameNP "`pln_idf_nb_selector.metta` with `select_pln_nb.py`"
      mkPresPos subj (complV2 (mkV2 (regV "use")) obj)
  | .selectorPlnRule =>
      let subj := properNameNP "PLN-Rule"
      let obj := properNameNP "`pln_premise_selector.metta` with `select_pln_rule.py`"
      mkPresPos subj (complV2 (mkV2 (regV "use")) obj)
  | .selectorPlnKnn =>
      let subj := properNameNP "PLN-kNN"
      let obj := properNameNP "`pln_knn_selector.metta` with `select_pln_knn.py`"
      mkPresPos subj (complV2 (mkV2 (regV "use")) obj)
  | .selectorPlnKnnNb =>
      let subj := properNameNP "PLN-kNN+NB"
      let obj := properNameNP "`select_pln_knn.py --merge-nb`"
      mkPresPos subj (complV2 (mkV2 (regV "use")) obj)
  | .selectorPlnEnhanced =>
      let subj := properNameNP "PLN-Enhanced"
      let obj := properNameNP "`pln_enhanced_selector.metta` with `select_pln_enhanced.py`"
      mkPresPos subj (complV2 (mkV2 (regV "use")) obj)
  | .selectorPlnNormalNb =>
      let subj := properNameNP "PLN-Normal-NB"
      let obj := properNameNP "`pln_normal_nb_selector.metta` with `select_pln_normal_nb.py`"
      mkPresPos subj (complV2 (mkV2 (regV "use")) obj)
  | .pettASelectorsPath =>
      let subj := properNameNP "PeTTa selectors" .AgP3Pl
      let vp := advVP (predV (regV "live"))
        (ppAdv in_Prep (properNameNP "`../hyperon/PeTTa/demos/`"))
      mkPresPos subj vp
  | .pythonDriversPath =>
      let subj := properNameNP "Python drivers" .AgP3Pl
      let vp := advVP (predV (regV "live"))
        (ppAdv in_Prep (properNameNP "`scripts/`"))
      mkPresPos subj vp
  | .coreLimit =>
      let subj := linDetCN theDefArt (linUseN limit_N)
      let obj := properNameNP "8 cores with `nice -n 19`"
      let vp := advVP (copulaNP obj) (ppAdv for_Prep (linDetCN theDefArt (linUseN machine_N)))
      mkPresPos subj vp
  | .timeoutLimit =>
      let subj := linDetCN theDefArt (linAdjCN (linPositA (regA "per-problem")) (linUseN limit_N))
      mkPresPos subj (copulaNP (properNameNP "5 seconds for E prover"))
  | .memoryLimit =>
      let subj := linDetCN theDefArt (linUseN limit_N)
      mkPresPos subj (copulaNP (properNameNP "`ulimit -v 6291456` for PeTTa subprocesses"))
  | .dependencyPeTTa =>
      let subj := properNameNP "PeTTa"
      mkPresPos subj (copulaNP (properNameNP "`../hyperon/PeTTa/`"))
  | .dependencyPlnLibraries =>
      let subj := properNameNP "PLN libraries" .AgP3Pl
      mkPresPos subj (copulaNP (properNameNP "`../hyperon/PeTTa/lib/lib_pln_xi.metta` and `../hyperon/PeTTa/pln_inference/`"))
  | .dependencyEProver =>
      let subj := properNameNP "E prover"
      mkPresPos subj (copulaNP (properNameNP "`eprover-standard/PROVER/eprover`"))
  | .dependencyPython =>
      let subj := properNameNP "Python dependencies" .AgP3Pl
      mkPresPos subj (copulaNP (properNameNP "numpy and scikit-learn in venv"))
  | .referenceBlanchette =>
      let subj := properNameNP "Blanchette et al. 2016"
      mkPresPos subj (copulaNP (linDetCN aIndefArt (linAdjCN (linPositA (regA "core")) (linUseN reference_N))))
  | .referenceGoertzel =>
      let subj := properNameNP "Goertzel et al."
      mkPresPos subj (copulaNP (linDetCN aIndefArt (linAdjCN (linPositA (regA "core")) (linUseN reference_N))))
  | .referenceJakubuv =>
      let subj := properNameNP "Jakubuv and Urban 2023"
      mkPresPos subj (copulaNP (linDetCN aIndefArt (linAdjCN (linPositA (regA "core")) (linUseN reference_N))))

def allAtpsClaims : List AtpsClaim :=
  [ .runPlnPremiseSelectionExperiments
  , .selectorsRunPeTTaInference
  , .pythonDriversHandlePreparationAndEvaluation
  , .resultMashNb
  , .resultPlnNb
  , .resultPlnNormalNb
  , .resultChainyBaseline
  , .resultPlnKnnNb
  , .resultPlnEnhanced
  , .resultPlnRule
  , .resultPlnKnn
  , .resultMashKnn
  , .selectorPlnNb
  , .selectorPlnRule
  , .selectorPlnKnn
  , .selectorPlnKnnNb
  , .selectorPlnEnhanced
  , .selectorPlnNormalNb
  , .pettASelectorsPath
  , .pythonDriversPath
  , .coreLimit
  , .timeoutLimit
  , .memoryLimit
  , .dependencyPeTTa
  , .dependencyPlnLibraries
  , .dependencyEProver
  , .dependencyPython
  , .referenceBlanchette
  , .referenceGoertzel
  , .referenceJakubuv
  ]

def parseAtpsClaimLine? (line : String) : Option AtpsClaim :=
  let norm := stripTerminalPeriod line
  allAtpsClaims.find? (fun c => renderAtpsClaim c = norm)

inductive AtpsHeading where
  | title
  | results
  | selectors
  | directoryStructure
  | quickStart
  | buildMashTables
  | runSelector
  | evaluateWithE
  | resourceLimits
  | dependencies
  | references
  deriving Repr, DecidableEq, BEq

private def headingNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassNP cn).s (.NCase .Nom)

private def headingPlNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassPluralNP cn).s (.NCase .Nom)

def renderAtpsHeading : AtpsHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "PLN"))
        (linAdjCN (linPositA (regA "premise"))
          (linAdjCN (linPositA (regA "automated")) (linUseN (regN "theorem proving")))))
  | .results =>
      headingPlNP (linUseN result_N)
  | .selectors =>
      headingPlNP (linUseN selector_N)
  | .directoryStructure =>
      headingNP (linUseN structure_N)
  | .quickStart =>
      headingNP (linAdjCN (linPositA (regA "quick")) (linUseN start_N))
  | .buildMashTables =>
      headingNP (linAdjCN (linPositA (regA "MaSh")) (linUseN table_N))
  | .runSelector =>
      headingNP (linUseN selector_N)
  | .evaluateWithE =>
      headingNP (linAdjCN (linPositA (regA "E")) (linUseN evaluation_N))
  | .resourceLimits =>
      headingPlNP (linAdjCN (linPositA (regA "resource")) (linUseN limit_N))
  | .dependencies =>
      headingPlNP (linUseN dependency_N)
  | .references =>
      headingPlNP (linUseN reference_N)

def allAtpsHeadings : List AtpsHeading :=
  [ .title
  , .results
  , .selectors
  , .directoryStructure
  , .quickStart
  , .buildMashTables
  , .runSelector
  , .evaluateWithE
  , .resourceLimits
  , .dependencies
  , .references
  ]

def parseAtpsHeadingLine? (line : String) : Option AtpsHeading :=
  allAtpsHeadings.find? (fun h => renderAtpsHeading h = line)

private def claimBullet (c : AtpsClaim) : ClaimBullet :=
  { text := renderAtpsClaim c }

def atpsReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderAtpsHeading .title)
  , .paragraph
      [ renderAtpsClaim .runPlnPremiseSelectionExperiments
      , renderAtpsClaim .selectorsRunPeTTaInference
      , renderAtpsClaim .pythonDriversHandlePreparationAndEvaluation
      ]
  , .heading 2 (renderAtpsHeading .results)
  , .claimBullets
      [ claimBullet .resultMashNb
      , claimBullet .resultPlnNb
      , claimBullet .resultPlnNormalNb
      , claimBullet .resultChainyBaseline
      , claimBullet .resultPlnKnnNb
      , claimBullet .resultPlnEnhanced
      , claimBullet .resultPlnRule
      , claimBullet .resultPlnKnn
      , claimBullet .resultMashKnn
      ]
  , .heading 2 (renderAtpsHeading .selectors)
  , .claimBullets
      [ claimBullet .selectorPlnNb
      , claimBullet .selectorPlnRule
      , claimBullet .selectorPlnKnn
      , claimBullet .selectorPlnKnnNb
      , claimBullet .selectorPlnEnhanced
      , claimBullet .selectorPlnNormalNb
      ]
  , .paragraph
      [ renderAtpsClaim .pettASelectorsPath
      , renderAtpsClaim .pythonDriversPath
      ]
  , .heading 2 (renderAtpsHeading .directoryStructure)
  , .codeBlock ""
      "atps/\n├── scripts/\n│   ├── select_pln_*.py\n│   ├── select_mash_*.py\n│   ├── mash_*_build_tables.py\n│   ├── mash_*_scorer.py\n│   ├── run_eprover.py\n│   └── run_eprover_parallel.sh\n├── datasets/\n│   └── extended_mptp5k/\n│       ├── chainy/train/\n│       ├── chainy/val/\n│       ├── deps/\n│       ├── features_chainy/\n│       ├── features_chainy_val/\n│       ├── models/\n│       ├── baselines/\n│       └── proofs_*/\n└── eprover-standard/"
  , .heading 2 (renderAtpsHeading .quickStart)
  , .heading 3 (renderAtpsHeading .buildMashTables)
  , .codeBlock "bash"
      "source atps/venv/bin/activate\npython3 scripts/mash_nb_build_tables.py\npython3 scripts/mash_knn_build_tables.py"
  , .heading 3 (renderAtpsHeading .runSelector)
  , .codeBlock "bash"
      "python3 scripts/select_pln_knn.py --merge-nb \\\n  --output datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json\n\npython3 scripts/select_pln_normal_nb.py \\\n  --output datasets/extended_mptp5k/baselines/selections_pln_normal_nb_top256.json"
  , .heading 3 (renderAtpsHeading .evaluateWithE)
  , .codeBlock "bash"
      "python3 scripts/run_eprover.py \\\n  --selections datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json \\\n  --problems-dir datasets/extended_mptp5k/chainy/val \\\n  --output-dir datasets/extended_mptp5k/proofs_pln_knn_nb_top256_5s \\\n  --timeout 5\n\nbash scripts/run_eprover_parallel.sh \\\n  datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json \\\n  datasets/extended_mptp5k/chainy/val \\\n  datasets/extended_mptp5k/proofs_pln_knn_nb_top256_5s \\\n  6 5"
  , .heading 2 (renderAtpsHeading .resourceLimits)
  , .claimBullets
      [ claimBullet .coreLimit
      , claimBullet .timeoutLimit
      , claimBullet .memoryLimit
      ]
  , .heading 2 (renderAtpsHeading .dependencies)
  , .claimBullets
      [ claimBullet .dependencyPeTTa
      , claimBullet .dependencyPlnLibraries
      , claimBullet .dependencyEProver
      , claimBullet .dependencyPython
      ]
  , .heading 2 (renderAtpsHeading .references)
  , .claimBullets
      [ claimBullet .referenceBlanchette
      , claimBullet .referenceGoertzel
      , claimBullet .referenceJakubuv
      ]
  ]

def atpsReadmeMarkdown : String :=
  renderDoc atpsReadmeBlocks

#eval atpsReadmeMarkdown

inductive ParsedAtpsStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : AtpsClaim)
  | claimLine (claim : AtpsClaim)
  deriving Repr

def parseSelectedStructuredAtpsLine? (line : String) : Option ParsedAtpsStructuredLine :=
  match parseTechnicalLine? atpsReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines atpsReadmeBlocks).contains line then
        match parseClaimBulletLine? parseAtpsClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseAtpsClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredAtpsLines : List String :=
  technicalLines atpsReadmeBlocks ++
  claimBulletLines atpsReadmeBlocks ++
  [ ensurePeriod (renderAtpsClaim .runPlnPremiseSelectionExperiments)
  , ensurePeriod (renderAtpsClaim .selectorsRunPeTTaInference)
  , ensurePeriod (renderAtpsClaim .pythonDriversHandlePreparationAndEvaluation)
  , ensurePeriod (renderAtpsClaim .pettASelectorsPath)
  , ensurePeriod (renderAtpsClaim .pythonDriversPath)
  ]

def atpsHardAuditPasses : Bool :=
  atpsReadmeBlocks.all (blockPassesHardAuditWith parseAtpsClaimLine? parseAtpsHeadingLine?)

theorem atps_hard_audit :
    atpsHardAuditPasses = true := by
  native_decide

def atpsHeadingImageCheck : Bool :=
  headingRenderImageCheck parseAtpsHeadingLine? renderAtpsHeading atpsReadmeBlocks

theorem atps_heading_images :
    atpsHeadingImageCheck = true := by
  native_decide

theorem atps_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries atpsReadmeBlocks) :
    ∃ h, parseAtpsHeadingLine? txt = some h ∧ renderAtpsHeading h = txt := by
  exact headingRenderImageWitness
    parseAtpsHeadingLine? renderAtpsHeading atpsReadmeBlocks
    atps_heading_images hMem

private def insertSurfaceBucket (acc : List (String × List AtpsClaim)) (surface : String) (c : AtpsClaim) :
    List (String × List AtpsClaim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List AtpsClaim) :=
  allAtpsClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderAtpsClaim c) c) []

def ambiguousClaimSurfaces : List (String × List AtpsClaim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allAtpsClaims.filter (fun c =>
    parseAtpsClaimLine? (renderAtpsClaim c) != some c)
  if fails.isEmpty then
    "ATPS parse-back check: all claim lines roundtrip"
  else
    s!"ATPS parse-back failures: {repr fails}"

#eval
  if atpsHardAuditPasses then
    "ATPS hard audit: no prose-bearing bypass blocks detected"
  else
    "ATPS hard audit: violation detected"

#eval
  let fails := selectedStructuredAtpsLines.filter
    (fun line =>
      match parseSelectedStructuredAtpsLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "ATPS parse-back check: selected headings + bullet families roundtrip"
  else
    s!"ATPS structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "ATPS ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"ATPS ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

end Mettapedia.DocText.AtpsReadmeCompositional
