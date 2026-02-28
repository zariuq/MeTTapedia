/-
# Main README — Compositional GF Semantics

Goal:
- Canonical source is a typed semantic tree (not prose strings).
- English prose is generated via GF English morphology/syntax.
- Technical literals (paths, commands) remain literal leaves.

This module targets `/home/zar/claude/README.md`.
-/

import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.MainReadmeCompositional

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

/-! ## Domain-Specific Infrastructure -/

/-- Preposition not in the base lexicon -/
private def inside_Prep : EnglishPrep := mkPrep "inside"

/-! ## Domain Lexicon -/

private def workspace_N := regN "workspace"
private def verifier_N := regN "verifier"
private def library_N := regN "library"
private def theorem_N := regN "theorem"
private def prototype_N := regN "prototype"
private def pipeline_N := regN "pipeline"
private def folder_N := regN "folder"
private def subdirectory_N := regN "subdirectory"
private def status_N := regN "status"
private def proof_N := regN "proof"
private def tooling_N := regN "tooling"
private def soundness_N := regN "soundness"
private def review_N := regN "review"
private def interoperability_N := regN "interoperability"

private def between_Prep : EnglishPrep := mkPrep "between"

/-! ## Compositional Repo Paths -/

inductive TopDir where
  | leanProjects
  | hyperon
  | tools
  deriving DecidableEq, Repr

inductive RepoId where
  | mettapedia
  | fourcolor
  | ramsey36
  | mmLean4
  | pverify
  | tptpMetta
  deriving DecidableEq, Repr

structure RepoPath where
  top : TopDir
  rest : List String
  deriving Repr

def topDirToken : TopDir → String
  | .leanProjects => "lean-projects"
  | .hyperon => "hyperon"
  | .tools => "tools"

def repoPath : RepoId → RepoPath
  | .mettapedia => ⟨.leanProjects, ["mettapedia"]⟩
  | .fourcolor => ⟨.leanProjects, ["fourcolor"]⟩
  | .ramsey36 => ⟨.leanProjects, ["ramsey36"]⟩
  | .mmLean4 => ⟨.hyperon, ["metamath", "mm-lean4"]⟩
  | .pverify => ⟨.hyperon, ["metamath", "pverify"]⟩
  | .tptpMetta => ⟨.tools, ["tptp-metta"]⟩

def renderRepoPath (p : RepoPath) : String :=
  String.intercalate "/" (topDirToken p.top :: p.rest)

private def lastSegment : List String → String
  | [] => "repo"
  | xs =>
      match xs.reverse with
      | [] => "repo"
      | x :: _ => x

private def lexicalizeRepoToken (raw : String) : String :=
  if raw = "mettapedia" then "Mettapedia"
  else if raw = "fourcolor" then "Fourcolor"
  else if raw = "ramsey36" then "Ramsey36"
  else raw

def repoDisplayName (r : RepoId) : String :=
  lexicalizeRepoToken (lastSegment (repoPath r).rest)

/-- Repo display name as proper-name NP -/
private def repoNP (r : RepoId) : EnglishNP :=
  properNameNP (repoDisplayName r)

/-! ## Semantic Claim Tree -/

inductive Tooling where
  | lean
  | metamath
  | atp
  deriving DecidableEq, Repr

/-- Tooling label as a mass-noun NP (for coordination) -/
private def toolingNP : Tooling → EnglishNP
  | .lean => properNameNP "Lean"
  | .metamath => properNameNP "Metamath"
  | .atp => properNameNP "ATP"

inductive Claim where
  | workspaceIncludes (items : List Tooling)
  | repoProvidesBroadLibrary (repo : RepoId)
  | repoFormalizesFourColor (repo : RepoId)
  | repoFormalizesRamseyR36 (repo : RepoId)
  | repoHostsInferenceProofs (repo : RepoId)
  | repoProvesVerifierInLean (repo : RepoId)
  | repoProvesVerifierSoundnessInLean (repo : RepoId)
  | repoProvidesPrologPettaVerifier (repo : RepoId)
  | repoExercisesInteropPipeline (repo : RepoId)
  | repoProvidesConvertersPrototype (repo : RepoId)
  | statusVariesBySubdirectory
  | checkLocalStatusDocs
  | runRgSorryToSeeGaps
  deriving Repr, DecidableEq, BEq

/-! ## GF Clause Construction -/

def renderClaim : Claim → String
  | .workspaceIncludes items =>
      -- "This workspace includes Lean, Metamath and ATP tooling"
      let coordNP := linConjNP and_Conj (items.map toolingNP)
      let objNP := linMassNP
        (linAdjCN
          { s := fun _ => coordNP.s (.NCase .Nom), isPre := true }
          (linUseN tooling_N))
      mkPresPos
        (linDetCN This_Det (linUseN workspace_N))
        (complV2 (mkV2 (regV "include")) objNP)
  | .repoProvidesBroadLibrary repo =>
      -- "Mettapedia provides a broad Lean formalization library"
      mkPresPos (repoNP repo)
        (complV2 (mkV2 (regV "provide"))
          (linDetCN aIndefArt
            (linAdjCN (linPositA (compoundA "broad"))
              (linAdjCN (linPositA (regA "Lean"))
                (linAdjCN (linPositA (compoundA "formalization"))
                  (linUseN library_N))))))
  | .repoFormalizesFourColor repo =>
      -- "fourcolor formalizes the Four‑color theorem in Lean"
      let objNP := linDetCN theDefArt
        (linAdjCN (linPositA (compoundA "Four‑color")) (linUseN theorem_N))
      let vp := advVP
        (complV2 (mkV2 (regV "formalize")) objNP)
        (ppAdv in_Prep (properNameNP "Lean"))
      mkPresPos (repoNP repo) vp
  | .repoFormalizesRamseyR36 repo =>
      -- "ramsey36 formalizes Ramsey R(3,6) in Lean"
      let vp := advVP
        (complV2 (mkV2 (regV "formalize")) (properNameNP "Ramsey R(3,6)"))
        (ppAdv in_Prep (properNameNP "Lean"))
      mkPresPos (repoNP repo) vp
  | .repoHostsInferenceProofs repo =>
      -- "Mettapedia hosts the Knuth–Skilling Foundations-of-Inference proofs"
      let objNP := linDetCN theDefArtPl
        (linAdjCN (linPositA (compoundA "Knuth–Skilling"))
          (linAdjCN (linPositA (compoundA "Foundations of Inference"))
            (linUseN proof_N)))
      mkPresPos (repoNP repo) (complV2 (mkV2 (regV "host")) objNP)
  | .repoProvesVerifierInLean repo =>
      -- "mm-lean4 proves a Metamath verifier inside Lean"
      let verifierNP := linDetCN aIndefArt
        (linAdjCN (linPositA (regA "Metamath")) (linUseN verifier_N))
      let vp := advVP
        (complV2 (mkV2 (regV "prove")) verifierNP)
        (ppAdv inside_Prep (properNameNP "Lean"))
      mkPresPos (repoNP repo) vp
  | .repoProvesVerifierSoundnessInLean repo =>
      -- "mm-lean4 proves the soundness of a Metamath verifier in Lean
      --  (see CURRENT_STATUS.md)"
      let innerNP := linDetCN aIndefArt
        (linAdjCN (linPositA (regA "Metamath")) (linUseN verifier_N))
      let objNP := linDetCN theDefArt
        (linAdvCN (linUseN soundness_N) (ppAdv of_Prep innerNP))
      let vp := advVP (complV2 (mkV2 (regV "prove")) objNP)
        (ppAdv in_Prep (properNameNP "Lean"))
      withParenRef (mkPresPos (repoNP repo) vp) "CURRENT_STATUS.md"
  | .repoProvidesPrologPettaVerifier repo =>
      -- "pverify provides a Prolog + PeTTa Metamath verifier
      --  (see STATUS.md and CANONICAL_TEST_RESULTS.md)"
      let objNP := linDetCN aIndefArt
        (linAdjCN (linPositA (compoundA "Prolog + PeTTa"))
          (linAdjCN (linPositA (regA "Metamath")) (linUseN verifier_N)))
      let clause := mkPresPos (repoNP repo)
        (complV2 (mkV2 (regV "provide")) objNP)
      withParenRef clause "STATUS.md and CANONICAL_TEST_RESULTS.md"
  | .repoExercisesInteropPipeline repo =>
      -- "pverify exercises a cross-language verification pipeline
      --  for interoperability between logic programming and MeTTa"
      let pipelineNP := linDetCN aIndefArt
        (linAdjCN (linPositA (compoundA "cross-language"))
          (linAdjCN (linPositA (compoundA "verification"))
            (linUseN pipeline_N)))
      let purposePP := ppAdv for_Prep
        (linMassNP (linAdvCN (linUseN interoperability_N)
          (ppAdv between_Prep (properNameNP "logic programming and MeTTa"))))
      let vp := advVP (complV2 (mkV2 (regV "exercise")) pipelineNP) purposePP
      mkPresPos (repoNP repo) vp
  | .repoProvidesConvertersPrototype repo =>
      -- "tptp-metta provides a propositional resolution prototype
      --  for TPTP ↔ S‑expression ↔ MeTTa conversion"
      let prototypeNP := linDetCN aIndefArt
        (linAdjCN (linPositA (compoundA "propositional"))
          (linAdjCN (linPositA (compoundA "resolution"))
            (linUseN prototype_N)))
      let purposePP := ppAdv for_Prep
        (properNameNP "TPTP ↔ S‑expression ↔ MeTTa conversion")
      let vp := advVP (complV2 (mkV2 (regV "provide")) prototypeNP) purposePP
      mkPresPos (repoNP repo) vp
  | .statusVariesBySubdirectory =>
      -- "Project status varies by subdirectory"
      let subj := linMassNP
        (linAdjCN (linPositA (compoundA "Project")) (linUseN status_N))
      mkPresPos subj
        (advVP (predV (regV "vary")) (ppAdv by_Prep (linMassNP (linUseN subdirectory_N))))
  | .checkLocalStatusDocs =>
      -- "Maintainers check the local README/CURRENT_STATUS"
      let subj := properNameNP "Maintainers" .AgP3Pl
      let obj := linDetCN theDefArt
        (linAdjCN (linPositA (regA "local"))
          (linUseN (regN "README/CURRENT_STATUS")))
      mkPresPos subj (complV2 (mkV2 (regV "check")) obj)
  | .runRgSorryToSeeGaps =>
      -- "Maintainers run `rg "sorry"` in the relevant code folders
      --  for proof-gap review"
      let subj := properNameNP "Maintainers" .AgP3Pl
      let locPP := ppAdv in_Prep
        (linDetCN theDefArtPl
          (linAdjCN (linPositA (regA "relevant"))
            (linAdjCN (linPositA (compoundA "code"))
              (linUseN folder_N))))
      let purposePP := ppAdv for_Prep
        (linMassNP (linAdjCN (linPositA (compoundA "proof-gap")) (linUseN review_N)))
      let vp := advVP
        (advVP
          (complV2 (mkV2 (regV "run")) (properNameNP "`rg \"sorry\"`"))
          locPP)
        purposePP
      mkPresPos subj vp

/-! ## Document Tree -/

inductive MainHeading where
  | title
  | primaryLeanRepos
  | whyInteresting
  | metamathTooling
  | resolutionTools
  | statusReview
  deriving Repr, DecidableEq, BEq

private def repository_N := regN "repository"
private def tool_N := regN "tool"

def renderMainHeading : MainHeading → String
  | .title =>
      capitalizeFirst <| (linMassPluralNP
        (linAdjCN (linPositA (compoundA "AI-assisted"))
          (linAdjCN (linPositA (regA "formal"))
            (linAdjCN (linPositA (compoundA "mathematics"))
              (linUseN (regN "project")))))).s (.NCase .Nom)
  | .primaryLeanRepos =>
      capitalizeFirst <| (linMassPluralNP
        (linAdjCN (linPositA (regA "primary"))
          (linAdjCN (linPositA (regA "Lean")) (linUseN repository_N)))).s (.NCase .Nom)
  | .whyInteresting =>
      capitalizeFirst <| (linMassPluralNP
        (linAdjCN (linPositA (regA "interesting")) (linUseN repository_N))).s (.NCase .Nom)
  | .metamathTooling =>
      capitalizeFirst <| (linMassPluralNP
        (linAdjCN (linPositA (regA "Metamath"))
          (linAdjCN (linPositA (compoundA "verification")) (linUseN tool_N)))).s (.NCase .Nom)
  | .resolutionTools =>
      capitalizeFirst <| (linMassPluralNP
        (linAdjCN (linPositA (regA "resolution"))
          (linAdjCN (linPositA (regA "TPTP")) (linUseN tool_N)))).s (.NCase .Nom)
  | .statusReview =>
      capitalizeFirst <| (linMassNP
        (linAdjCN (linPositA (regA "status")) (linUseN review_N))).s (.NCase .Nom)

def allMainHeadings : List MainHeading :=
  [ .title
  , .primaryLeanRepos
  , .whyInteresting
  , .metamathTooling
  , .resolutionTools
  , .statusReview
  ]

def parseMainHeadingLine? (line : String) : Option MainHeading :=
  allMainHeadings.find? (fun h => renderMainHeading h = line)

structure RepoEntry where
  repo : RepoId
  summary : Claim
  deriving Repr

structure Section where
  heading : MainHeading
  subheading : Option String := none
  prose : List Claim := []
  entries : List RepoEntry := []
  deriving Repr

def mainSections : List Section :=
  [ { heading := .primaryLeanRepos
      entries :=
        [ { repo := .mettapedia, summary := .repoProvidesBroadLibrary .mettapedia }
        , { repo := .fourcolor, summary := .repoFormalizesFourColor .fourcolor }
        , { repo := .ramsey36, summary := .repoFormalizesRamseyR36 .ramsey36 }
        ] }
  , { heading := .whyInteresting
      subheading := some "###"
      prose :=
        [ .repoHostsInferenceProofs .mettapedia
        , .repoProvesVerifierInLean .mmLean4
        , .repoExercisesInteropPipeline .pverify
        ] }
  , { heading := .metamathTooling
      entries :=
        [ { repo := .mmLean4, summary := .repoProvesVerifierSoundnessInLean .mmLean4 }
        , { repo := .pverify, summary := .repoProvidesPrologPettaVerifier .pverify }
        ] }
  , { heading := .resolutionTools
      entries :=
        [ { repo := .tptpMetta, summary := .repoProvidesConvertersPrototype .tptpMetta }
        ] }
  , { heading := .statusReview
      prose :=
        [ .statusVariesBySubdirectory
        , .checkLocalStatusDocs
        , .runRgSorryToSeeGaps
        ] }
  ]

def allMainReadmeClaims : List Claim :=
  let intro := [.workspaceIncludes [.lean, .metamath, .atp]]
  let sectionClaims :=
    mainSections.foldr (fun s acc => s.prose ++ (s.entries.map fun e => e.summary) ++ acc) []
  intro ++ sectionClaims

def canonicalMainReadmeClaims : List Claim :=
  allMainReadmeClaims.eraseDups

private def stripTerminalPeriod (s : String) : String :=
  match s.toList.reverse with
  | '.' :: cs => String.ofList cs.reverse
  | _ => s

def parseClaimLine? (line : String) : Option Claim :=
  let norm := stripTerminalPeriod line
  canonicalMainReadmeClaims.find? (fun c => renderClaim c = norm)

private def allEntries : List RepoEntry :=
  mainSections.foldr (fun s acc => s.entries ++ acc) []

private def renderSectionHeading (s : Section) : String :=
  match s.subheading with
  | some "###" => "### " ++ renderMainHeading s.heading
  | _ => "## " ++ renderMainHeading s.heading

private def renderEntryLine (e : RepoEntry) : String :=
  "- **`" ++ renderRepoPath (repoPath e.repo) ++ "/`** — " ++ ensurePeriod (renderClaim e.summary)

inductive ParsedReadmeLine where
  | title
  | sectionHeading (line : String)
  | claim (c : Claim)
  | entry (repo : RepoId) (summary : Claim)
  deriving Repr, DecidableEq

def parseStructuredLine? (line : String) : Option ParsedReadmeLine :=
  if line = "# " ++ renderMainHeading .title then
    some .title
  else
    match mainSections.find? (fun s => renderSectionHeading s = line) with
    | some s => some (.sectionHeading (renderSectionHeading s))
    | none =>
        match allEntries.find? (fun e => renderEntryLine e = line) with
        | some e => some (.entry e.repo e.summary)
        | none =>
            match parseClaimLine? line with
            | some c => some (.claim c)
            | none => none

private def insertSurfaceBucket (acc : List (String × List Claim)) (surface : String) (c : Claim) :
    List (String × List Claim) :=
  match acc with
  | [] => [(surface, [c])]
  | (k, cs) :: rest =>
      if k = surface then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertSurfaceBucket rest surface c

def claimSurfaceBuckets : List (String × List Claim) :=
  canonicalMainReadmeClaims.foldl
    (fun acc c => insertSurfaceBucket acc (renderClaim c) c) []

def ambiguousClaimSurfaces : List (String × List Claim) :=
  claimSurfaceBuckets.filter (fun p => p.snd.length > 1)

def mainReadmeStructuredLines : List String :=
  let title := ["# " ++ renderMainHeading .title]
  let intro := [ensurePeriod <| renderClaim (.workspaceIncludes [.lean, .metamath, .atp])]
  let sectionLines :=
    mainSections.foldr
      (fun s acc =>
        [renderSectionHeading s] ++
        (s.prose.map (ensurePeriod ∘ renderClaim)) ++
        (s.entries.map renderEntryLine) ++
        acc)
      []
  title ++ intro ++ sectionLines

private def sectionHeadingLevel (s : Section) : Nat :=
  match s.subheading with
  | some "###" => 3
  | _ => 2

private def sectionBlocks (s : Section) : List ReadmeBlock :=
  let heading : ReadmeBlock := .heading (sectionHeadingLevel s) (renderMainHeading s.heading)
  let proseBlocks : List ReadmeBlock :=
    if s.prose.isEmpty then [] else [.paragraph (s.prose.map renderClaim)]
  let entryBlocks : List ReadmeBlock :=
    s.entries.map (fun e =>
      .fileRef (renderRepoPath (repoPath e.repo) ++ "/")
        (ensurePeriod (renderClaim e.summary)))
  [heading] ++ proseBlocks ++ entryBlocks

def mainReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderMainHeading .title)
  , .paragraph [renderClaim (.workspaceIncludes [.lean, .metamath, .atp])]
  ] ++ (mainSections.foldr (fun s acc => sectionBlocks s ++ acc) [])

inductive ParsedMainStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claim (c : Claim)
  deriving Repr

def parseSelectedStructuredMainLine? (line : String) : Option ParsedMainStructuredLine :=
  match parseTechnicalLine? mainReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      match parseClaimLine? line with
      | some c => some (.claim c)
      | none => none

def selectedStructuredMainReadmeLines : List String :=
  technicalLines mainReadmeBlocks ++
  [ensurePeriod <| renderClaim (.workspaceIncludes [.lean, .metamath, .atp])] ++
  (mainSections.foldr (fun s acc => (s.prose.map (ensurePeriod ∘ renderClaim)) ++ acc) [])

def mainHardAuditPasses : Bool :=
  mainReadmeBlocks.all (blockPassesHardAuditWith parseClaimLine? parseMainHeadingLine?)

theorem main_hard_audit :
    mainHardAuditPasses = true := by
  native_decide

def mainHeadingImageCheck : Bool :=
  headingRenderImageCheck parseMainHeadingLine? renderMainHeading mainReadmeBlocks

theorem main_heading_images :
    mainHeadingImageCheck = true := by
  native_decide

theorem main_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries mainReadmeBlocks) :
    ∃ h, parseMainHeadingLine? txt = some h ∧ renderMainHeading h = txt := by
  exact headingRenderImageWitness
    parseMainHeadingLine? renderMainHeading mainReadmeBlocks
    main_heading_images hMem

/-! ## Markdown Rendering -/

private def renderEntry (e : RepoEntry) : String :=
  renderEntryLine e

private def renderSection (s : Section) : String :=
  let heading := renderSectionHeading s
  let proseLines := s.prose.map (ensurePeriod ∘ renderClaim)
  let entryLines := s.entries.map renderEntry
  let body := String.intercalate "\n" (proseLines ++ entryLines)
  heading ++ "\n\n" ++ body

def mainReadmeMarkdown : String :=
  let title := "# " ++ renderMainHeading .title
  let intro := ensurePeriod <| renderClaim (.workspaceIncludes [.lean, .metamath, .atp])
  let sections := String.intercalate "\n\n" (mainSections.map renderSection)
  title ++ "\n\n" ++ intro ++ "\n\n" ++ sections ++ "\n"

#eval mainReadmeMarkdown

/-! ## Checks -/

-- Sentence-level output checks
theorem intro_sentence :
    renderClaim (.workspaceIncludes [.lean, .metamath, .atp]) =
      "This workspace includes Lean, Metamath and ATP tooling" := by
  decide

theorem mmlean4_sentence :
    renderClaim (.repoProvesVerifierInLean .mmLean4) =
      "mm-lean4 proves a Metamath verifier inside Lean" := by
  decide

theorem status_sentence :
    renderClaim .statusVariesBySubdirectory =
      "Project status varies by subdirectory" := by
  decide

theorem path_rendering :
    renderRepoPath (repoPath .mmLean4) = "hyperon/metamath/mm-lean4" := by
  decide

-- Parse-back roundtrip proofs
theorem parse_roundtrip_intro :
    parseClaimLine? "This workspace includes Lean, Metamath and ATP tooling." =
      some (.workspaceIncludes [.lean, .metamath, .atp]) := by
  native_decide

theorem parse_roundtrip_mmlean4 :
    parseClaimLine? "mm-lean4 proves a Metamath verifier inside Lean." =
      some (.repoProvesVerifierInLean .mmLean4) := by
  native_decide

theorem parse_roundtrip_status :
    parseClaimLine? "Project status varies by subdirectory." =
      some .statusVariesBySubdirectory := by
  native_decide

theorem parse_roundtrip_section_heading :
    parseStructuredLine? ("## " ++ renderMainHeading .metamathTooling) =
      some (.sectionHeading ("## " ++ renderMainHeading .metamathTooling)) := by
  native_decide

theorem parse_roundtrip_entry :
    parseStructuredLine?
      "- **`tools/tptp-metta/`** — tptp-metta provides a propositional resolution prototype for TPTP ↔ S‑expression ↔ MeTTa conversion." =
      some (.entry .tptpMetta (.repoProvidesConvertersPrototype .tptpMetta)) := by
  native_decide

-- Runtime diagnostics
#eval
  let fails := allMainReadmeClaims.filter (fun c => parseClaimLine? (renderClaim c ++ ".") != some c)
  if fails.isEmpty then
    "parse-back check: all README claim lines roundtrip"
  else
    s!"parse-back check failures: {repr fails}"

#eval
  let fails := mainReadmeStructuredLines.filter (fun line => parseStructuredLine? line = none)
  if fails.isEmpty then
    "parse-back check: all selected structured README lines parse"
  else
    s!"structured parse failures: {repr fails}"

#eval
  if mainHardAuditPasses then
    "main hard audit: no prose-bearing bypass blocks detected"
  else
    "main hard audit: violation detected"

#eval
  let fails := selectedStructuredMainReadmeLines.filter
    (fun line =>
      match parseSelectedStructuredMainLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "main parse-back check: selected headings + bullet families roundtrip"
  else
    s!"main structured parse failures: {repr fails}"

#eval
  if ambiguousClaimSurfaces.isEmpty then
    "ambiguity diagnostic: no duplicate surfaces across distinct claims"
  else
    s!"ambiguity diagnostic: duplicate surfaces found: {repr ambiguousClaimSurfaces}"

/-! ## Coverage Guardrails

properNameNP audit (legitimate proper-name / technical-literal uses only):
- repoNP: repo display names (e.g. "mm-lean4", "Mettapedia") — proper names
- toolingNP: technology names ("Lean", "Metamath", "ATP") — proper names
- "Lean" in PP contexts (in_Prep, inside_Prep) — technology proper name
- "Ramsey R(3,6)": mathematical proper name
- "Maintainers": role noun (proper-name-like, plural)
- "`rg \"sorry\"`": code command literal
- "logic programming and MeTTa": technical compound inside between_Prep PP
- "TPTP ↔ S‑expression ↔ MeTTa conversion": technical symbol sequence
- "README/CURRENT_STATUS" inside linDetCN (file path as noun stem)

Decomposed (no longer properNameNP):
- "the soundness of a Metamath verifier" → linDetCN + linAdvCN + of_Prep
- "a Prolog + PeTTa Metamath verifier" → linDetCN + linAdjCN chain
- "Lean (see CURRENT_STATUS.md)" → properNameNP "Lean" + withParenRef
- "interoperability between ..." → linAdvCN + between_Prep
- "proof-gap review" → linAdjCN + linUseN

Raw string adverbials: 0
Parentheticals: 2 (via withParenRef — metalinguistic, outside GF grammar)
-/

end Mettapedia.DocText.MainReadmeCompositional
