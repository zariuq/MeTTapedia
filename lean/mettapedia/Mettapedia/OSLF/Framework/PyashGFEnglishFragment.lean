import Mettapedia.OSLF.Framework.PyashGF
import Mettapedia.OSLF.Framework.PyashGFInventory

/-!
# Pyash GF Controlled-English Fragment

A strict, well-defined English fragment aligned with the current PyashGF clause
inventory. This module is intentionally controlled: it does not claim full
natural-English parsing.
-/

namespace Mettapedia.OSLF.Framework.PyashGFEnglishFragment

open Mettapedia.Languages.GF.Abstract
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.PyashGF
open Mettapedia.OSLF.Framework.PyashGFInventory

/-- Canonical controlled-English clause inventory aligned with `pyashGFClauseMapCases`. -/
inductive PyashEnglishWDFClause where
  | readDo
  | writeDo
  | sayDo
  | mapDo
  | mapDef
  | commandDo
  | searchDo
  | listDo
  | inputDo
  | streamDo
  | mindDo
  | readThenErr
  | configureThenErr
  | worldThenErr
  | pipelineThenErr
  | chipDo
  | chipSeriesDo
  | chipBoundedDo
  | hearDo
  | hearMicDo
  | hearSrtDo
  | configureDo
  | configureDef
  | configureCommandMapDef
  | configureSandboxMapDef
  | configureVerifyLoopMapDef
  | worldDo
  | worldPathIoDo
  | pipelineDo
  | pipelineChirpDo
  | pipelineReentryDo
  | compileDo
  | importDo
  | downloadDo
  | translationDo
  | dispatchErrorInstr
  deriving DecidableEq, Repr

/-- Canonical controlled-English fragment as an explicit finite list. -/
def pyashEnglishWDFAll : List PyashEnglishWDFClause :=
  [ .readDo
  , .writeDo
  , .sayDo
  , .mapDo
  , .mapDef
  , .commandDo
  , .searchDo
  , .listDo
  , .inputDo
  , .streamDo
  , .mindDo
  , .readThenErr
  , .configureThenErr
  , .worldThenErr
  , .pipelineThenErr
  , .chipDo
  , .chipSeriesDo
  , .chipBoundedDo
  , .hearDo
  , .hearMicDo
  , .hearSrtDo
  , .configureDo
  , .configureDef
  , .configureCommandMapDef
  , .configureSandboxMapDef
  , .configureVerifyLoopMapDef
  , .worldDo
  , .worldPathIoDo
  , .pipelineDo
  , .pipelineChirpDo
  , .pipelineReentryDo
  , .compileDo
  , .importDo
  , .downloadDo
  , .translationDo
  , .dispatchErrorInstr
  ]

theorem pyashEnglishWDFAll_nodup : pyashEnglishWDFAll.Nodup := by
  decide

theorem pyashEnglishWDFAll_length : pyashEnglishWDFAll.length = 36 := by
  decide

/-- Canonical controlled-English mood/head pair for each aligned clause. -/
def PyashEnglishWDFClause.toCanonicalEnglish : PyashEnglishWDFClause → String × String
  | .readDo => ("do", "read")
  | .writeDo => ("do", "write")
  | .sayDo => ("do", "say")
  | .mapDo => ("do", "map")
  | .mapDef => ("def", "map")
  | .commandDo => ("do", "command")
  | .searchDo => ("do", "search")
  | .listDo => ("do", "list")
  | .inputDo => ("do", "input")
  | .streamDo => ("do", "stream")
  | .mindDo => ("do", "mind")
  | .readThenErr => ("then", "read")
  | .configureThenErr => ("then", "configure")
  | .worldThenErr => ("then", "world")
  | .pipelineThenErr => ("then", "pipeline")
  | .chipDo => ("do", "chip")
  | .chipSeriesDo => ("do", "series")
  | .chipBoundedDo => ("do", "chip_bounded")
  | .hearDo => ("do", "hear")
  | .hearMicDo => ("do", "hear_mic")
  | .hearSrtDo => ("do", "hear_srt")
  | .configureDo => ("do", "configure")
  | .configureDef => ("def", "configure")
  | .configureCommandMapDef => ("def", "command")
  | .configureSandboxMapDef => ("def", "sandbox")
  | .configureVerifyLoopMapDef => ("def", "verify_loop")
  | .worldDo => ("do", "world")
  | .worldPathIoDo => ("do", "world_path_io")
  | .pipelineDo => ("do", "pipeline")
  | .pipelineChirpDo => ("do", "pipeline_chirp")
  | .pipelineReentryDo => ("do", "pipeline_reentry")
  | .compileDo => ("do", "compile")
  | .importDo => ("do", "import")
  | .downloadDo => ("do", "download")
  | .translationDo => ("do", "translate")
  | .dispatchErrorInstr => ("error", "dispatch_error")

def PyashEnglishWDFClause.toLabel : PyashEnglishWDFClause → String
  | .readDo => "read_do"
  | .writeDo => "write_do"
  | .sayDo => "say_do"
  | .mapDo => "map_do"
  | .mapDef => "map_def"
  | .commandDo => "command_do"
  | .searchDo => "search_do"
  | .listDo => "list_do"
  | .inputDo => "input_do"
  | .streamDo => "stream_do"
  | .mindDo => "mind_do"
  | .readThenErr => "read_then_err"
  | .configureThenErr => "configure_then_err"
  | .worldThenErr => "world_then_err"
  | .pipelineThenErr => "pipeline_then_err"
  | .chipDo => "chip_do"
  | .chipSeriesDo => "chip_series_do"
  | .chipBoundedDo => "chip_bounded_do"
  | .hearDo => "hear_do"
  | .hearMicDo => "hear_mic_do"
  | .hearSrtDo => "hear_srt_do"
  | .configureDo => "configure_do"
  | .configureDef => "configure_def"
  | .configureCommandMapDef => "configure_command_map_def"
  | .configureSandboxMapDef => "configure_sandbox_map_def"
  | .configureVerifyLoopMapDef => "configure_verify_loop_map_def"
  | .worldDo => "world_do"
  | .worldPathIoDo => "world_path_io_do"
  | .pipelineDo => "pipeline_do"
  | .pipelineChirpDo => "pipeline_chirp_do"
  | .pipelineReentryDo => "pipeline_reentry_do"
  | .compileDo => "compile_do"
  | .importDo => "import_do"
  | .downloadDo => "download_do"
  | .translationDo => "translation_do"
  | .dispatchErrorInstr => "dispatch_error_instr"

/-- Aligned GF clause node for each controlled-English clause constructor. -/
def PyashEnglishWDFClause.toGFClause : PyashEnglishWDFClause → AbstractNode
  | .readDo => pyashGFReadDoClause
  | .writeDo => pyashGFWriteDoClause
  | .sayDo => pyashGFSayDoClause
  | .mapDo => pyashGFMapDoClause
  | .mapDef => pyashGFMapDefClause
  | .commandDo => pyashGFCommandDoClause
  | .searchDo => pyashGFSearchDoClause
  | .listDo => pyashGFListDoClause
  | .inputDo => pyashGFInputDoClause
  | .streamDo => pyashGFStreamDoClause
  | .mindDo => pyashGFMindDoClause
  | .readThenErr => pyashGFReadThenClause
  | .configureThenErr => pyashGFConfigureThenClause
  | .worldThenErr => pyashGFWorldThenClause
  | .pipelineThenErr => pyashGFPipelineThenClause
  | .chipDo => pyashGFChipDoClause
  | .chipSeriesDo => pyashGFChipSeriesDoClause
  | .chipBoundedDo => pyashGFChipBoundedDoClause
  | .hearDo => pyashGFHearDoClause
  | .hearMicDo => pyashGFHearMicDoClause
  | .hearSrtDo => pyashGFHearSrtDoClause
  | .configureDo => pyashGFConfigureDoClause
  | .configureDef => pyashGFConfigureDefClause
  | .configureCommandMapDef => pyashGFConfigureCommandMapDefClause
  | .configureSandboxMapDef => pyashGFConfigureSandboxMapDefClause
  | .configureVerifyLoopMapDef => pyashGFConfigureVerifyLoopMapDefClause
  | .worldDo => pyashGFWorldDoClause
  | .worldPathIoDo => pyashGFWorldPathDoClause
  | .pipelineDo => pyashGFPipelineDoClause
  | .pipelineChirpDo => pyashGFPipelineChirpDoClause
  | .pipelineReentryDo => pyashGFPipelineReentryDoClause
  | .compileDo => pyashGFCompileDoClause
  | .importDo => pyashGFImportDoClause
  | .downloadDo => pyashGFDownloadDoClause
  | .translationDo => pyashGFTranslationDoClause
  | .dispatchErrorInstr => pyashGFDispatchErrorClause

/-- Expected Pyash state for each controlled-English aligned clause. -/
def PyashEnglishWDFClause.expectedState : PyashEnglishWDFClause → Pattern
  | .readDo => PyashCoreInstance.pyashStateReadDerive
  | .writeDo => PyashCoreInstance.pyashStateWriteDerive
  | .sayDo => PyashCoreInstance.pyashStateSayDerive
  | .mapDo => PyashCoreInstance.pyashStateMapDerive
  | .mapDef => PyashCoreInstance.pyashStateMapDefDerive
  | .commandDo => PyashCoreInstance.pyashStateCommandDerive
  | .searchDo => PyashCoreInstance.pyashStateSearchDerive
  | .listDo => PyashCoreInstance.pyashStateListDerive
  | .inputDo => PyashCoreInstance.pyashStateInputDerive
  | .streamDo => PyashCoreInstance.pyashStateStreamDerive
  | .mindDo => PyashCoreInstance.pyashStateMindDerive
  | .readThenErr => PyashCoreInstance.pyashStateDispatchThenError
  | .configureThenErr => pyashStateConfigureThenError
  | .worldThenErr => pyashStateWorldThenError
  | .pipelineThenErr => pyashStatePipelineThenError
  | .chipDo => PyashCoreInstance.pyashStateChipDerive
  | .chipSeriesDo => PyashCoreInstance.pyashStateChipSeriesDerive
  | .chipBoundedDo => PyashCoreInstance.pyashStateChipBoundedDerive
  | .hearDo => PyashCoreInstance.pyashStateHearDerive
  | .hearMicDo => PyashCoreInstance.pyashStateHearMicRecordDerive
  | .hearSrtDo => PyashCoreInstance.pyashStateHearFileSrtDerive
  | .configureDo => PyashCoreInstance.pyashStateConfigureDerive
  | .configureDef => PyashCoreInstance.pyashStateConfigureDefDerive
  | .configureCommandMapDef => PyashCoreInstance.pyashStateConfigureCommandMapDefDerive
  | .configureSandboxMapDef => PyashCoreInstance.pyashStateConfigureSandboxMapDefDerive
  | .configureVerifyLoopMapDef => PyashCoreInstance.pyashStateConfigureVerifyLoopMapDefDerive
  | .worldDo => PyashCoreInstance.pyashStateWorldDerive
  | .worldPathIoDo => PyashCoreInstance.pyashStateWorldPathIODerive
  | .pipelineDo => PyashCoreInstance.pyashStatePipelineDerive
  | .pipelineChirpDo => PyashCoreInstance.pyashStatePipelineChirpDerive
  | .pipelineReentryDo => PyashCoreInstance.pyashStatePipelineReentryDerive
  | .compileDo => PyashCoreInstance.pyashStateCompileDerive
  | .importDo => PyashCoreInstance.pyashStateImportDerive
  | .downloadDo => PyashCoreInstance.pyashStateDownloadDerive
  | .translationDo => PyashCoreInstance.pyashStateTranslationDerive
  | .dispatchErrorInstr => PyashCoreInstance.pyashStateDispatchErrorInstr

def pyashEnglishWDFCasePair (c : PyashEnglishWDFClause) : AbstractNode × Pattern :=
  (c.toGFClause, c.expectedState)

theorem pyashEnglishWDFCasePair_mem_cases (c : PyashEnglishWDFClause) :
    pyashEnglishWDFCasePair c ∈ pyashGFClauseMapCases := by
  cases c <;> simp [pyashEnglishWDFCasePair, PyashEnglishWDFClause.toGFClause,
    PyashEnglishWDFClause.expectedState, pyashGFClauseMapCases]

theorem pyashEnglishWDFClause_state_sound (c : PyashEnglishWDFClause) :
    pyashGFClauseToState? c.toGFClause = some c.expectedState := by
  exact pyashGF_clause_map_cases_sound (pyashEnglishWDFCasePair c)
    (pyashEnglishWDFCasePair_mem_cases c)

/-- Controlled parser from normalized English mood/head tokens to aligned clause IDs. -/
def pyashEnglishMoodHeadToWDFClause? (mood head : String) : Option PyashEnglishWDFClause :=
  let m := mood
  let h := head
  if m == "do" then
    if h == "read" then some .readDo
    else if h == "write" then some .writeDo
    else if h == "say" then some .sayDo
    else if h == "map" then some .mapDo
    else if h == "command" then some .commandDo
    else if h == "search" then some .searchDo
    else if h == "list" then some .listDo
    else if h == "input" then some .inputDo
    else if h == "stream" then some .streamDo
    else if h == "mind" then some .mindDo
    else if h == "chip" then some .chipDo
    else if h == "series" || h == "chip_series" then some .chipSeriesDo
    else if h == "chip_bounded" then some .chipBoundedDo
    else if h == "hear" then some .hearDo
    else if h == "hear_mic" || h == "microphone" then some .hearMicDo
    else if h == "hear_srt" || h == "srt" then some .hearSrtDo
    else if h == "configure" then some .configureDo
    else if h == "world" then some .worldDo
    else if h == "world_path_io" then some .worldPathIoDo
    else if h == "pipeline" || h == "refinery" then some .pipelineDo
    else if h == "pipeline_chirp" || h == "chirp" then some .pipelineChirpDo
    else if h == "pipeline_reentry" || h == "reentry" || h == "re_entry_cycle" then
      some .pipelineReentryDo
    else if h == "compile" then some .compileDo
    else if h == "import" then some .importDo
    else if h == "download" then some .downloadDo
    else if h == "translate" || h == "translation" then some .translationDo
    else none
  else if m == "def" then
    if h == "map" then some .mapDef
    else if h == "configure" then some .configureDef
    else if h == "command" then some .configureCommandMapDef
    else if h == "sandbox" then some .configureSandboxMapDef
    else if h == "verify_loop" || h == "loop" then some .configureVerifyLoopMapDef
    else none
  else if m == "then" then
    if h == "read" then some .readThenErr
    else if h == "configure" then some .configureThenErr
    else if h == "world" then some .worldThenErr
    else if h == "pipeline" then some .pipelineThenErr
    else none
  else if m == "error" then
    if h == "dispatch_error" || h == "dispatch" || h == "error" then
      some .dispatchErrorInstr
    else
      none
  else
    none

/-- Normalize broader surface mood tokens into controlled WDF moods. -/
def pyashEnglishNormalizeMood (mood : String) : String :=
  if mood == "imperative" || mood == "execute" || mood == "run" ||
      mood == "action" || mood == "instruction" || mood == "request" then "do"
  else if mood == "define" || mood == "definition" || mood == "declaration" ||
      mood == "binding" then "def"
  else if mood == "conditional" || mood == "fallback" || mood == "on_error" ||
      mood == "recovery" then "then"
  else if mood == "invalid" || mood == "error" || mood == "failure" ||
      mood == "failed" then "error"
  else mood

/-- Normalize broader surface head tokens into controlled WDF heads. -/
def pyashEnglishNormalizeHead (head : String) : String :=
  if head == "reads" || head == "reading" || head == "reader" ||
      head == "load" || head == "loads" || head == "loading" ||
      head == "fetch" || head == "fetched" then "read"
  else if head == "writes" || head == "writing" || head == "writer" ||
      head == "save" || head == "saves" || head == "saving" ||
      head == "output" || head == "outputs" then "write"
  else if head == "speak" || head == "speaks" || head == "speaking" ||
      head == "spoken" || head == "talk" || head == "talks" ||
      head == "talking" || head == "said" || head == "speech" ||
      head == "espeak" then "say"
  else if head == "maps" || head == "mapping" || head == "mapped" ||
      head == "associate" || head == "associates" ||
      head == "association" then "map"
  else if head == "commands" || head == "cmd" || head == "tool" then "command"
  else if head == "searches" || head == "searching" || head == "find" ||
      head == "finds" || head == "lookup" || head == "look_up" then "search"
  else if head == "lists" || head == "listing" || head == "listed" ||
      head == "collect" || head == "collects" || head == "group" ||
      head == "groups" || head == "enumerate" then "list"
  else if head == "inputs" || head == "entering" || head == "entry" ||
      head == "insertion" || head == "insert" || head == "inserted" ||
      head == "prompt" || head == "prompts" then "input"
  else if head == "streams" || head == "streaming" || head == "streamed" ||
      head == "pipe" || head == "piping" then "stream"
  else if head == "minds" || head == "memory" || head == "remember" ||
      head == "remembers" then "mind"
  else if head == "chips" || head == "chipset" then "chip"
  else if head == "serial" || head == "chip_series" || head == "series_mode" then
    "series"
  else if head == "bounded_chip" || head == "chipbounded" then "chip_bounded"
  else if head == "hears" || head == "hearing" || head == "heard" ||
      head == "listen" || head == "listens" || head == "listening" then "hear"
  else if head == "microphone" || head == "mic" || head == "audio_mic" then
    "hear_mic"
  else if head == "subtitle" || head == "subtitles" || head == "caption" ||
      head == "captions" then "hear_srt"
  else if head == "config" || head == "configure_map" || head == "configuration" ||
      head == "settings" || head == "setting" then "configure"
  else if head == "state" || head == "world_state" || head == "worldview" then
    "world"
  else if head == "worldpathio" || head == "world_path" || head == "path_io" ||
      head == "world_io" || head == "world_pathio" then "world_path_io"
  else if head == "pipeline_reentry_cycle" || head == "reentry_cycle" then
    "pipeline_reentry"
  else if head == "re-entry" || head == "re_entry_cycle" then "pipeline_reentry"
  else if head == "pipeline_refinery" || head == "refinery" then
    "pipeline"
  else if head == "process" || head == "processing" || head == "workflow" then
    "pipeline"
  else if head == "chirps" then "pipeline_chirp"
  else if head == "compiles" || head == "compiled" || head == "compiling" ||
      head == "build" || head == "builds" then "compile"
  else if head == "imports" || head == "importing" || head == "imported" ||
      head == "include" || head == "includes" then "import"
  else if head == "downloads" || head == "downloading" || head == "downloaded" ||
      head == "fetch_remote" then "download"
  else if head == "translates" || head == "translated" || head == "translating" ||
      head == "interpret" || head == "interprets" then "translate"
  else if head == "translation" then "translate"
  else if head == "dispatch" || head == "dispatch_error_instr" ||
      head == "error_dispatch" || head == "raise_error" then "dispatch_error"
  else head

/-- Surface-to-controlled normalization layer used by broader English parse fronts. -/
def pyashEnglishNormalizeMoodHead (mood head : String) : String × String :=
  (pyashEnglishNormalizeMood mood, pyashEnglishNormalizeHead head)

/-- Normalized parser: broader English moods/heads routed into the controlled WDF interface. -/
def pyashEnglishNormalizedMoodHeadToWDFClause? (mood head : String) :
    Option PyashEnglishWDFClause :=
  let mh := pyashEnglishNormalizeMoodHead mood head
  pyashEnglishMoodHeadToWDFClause? mh.1 mh.2

/-- Normalized state projection for broader English parse fronts. -/
def pyashEnglishNormalizedMoodHeadToState? (mood head : String) : Option Pattern := do
  let clause ← pyashEnglishNormalizedMoodHeadToWDFClause? mood head
  pyashGFClauseToState? clause.toGFClause

/-- Positive examples showing broader English forms normalize to controlled clauses. -/
def pyashEnglishNormalizationPositiveExamples :
    List (String × String × PyashEnglishWDFClause) :=
  [ ("imperative", "reads", .readDo)
  , ("execute", "talk", .sayDo)
  , ("run", "mapping", .mapDo)
  , ("instruction", "collect", .listDo)
  , ("action", "insertion", .inputDo)
  , ("request", "microphone", .hearMicDo)
  , ("imperative", "subtitle", .hearSrtDo)
  , ("action", "workflow", .pipelineDo)
  , ("action", "builds", .compileDo)
  , ("action", "includes", .importDo)
  , ("action", "downloads", .downloadDo)
  , ("action", "interprets", .translationDo)
  , ("failure", "raise_error", .dispatchErrorInstr)
  , ("definition", "configuration", .configureDef)
  , ("declaration", "settings", .configureDef)
  , ("binding", "loop", .configureVerifyLoopMapDef)
  , ("conditional", "pipeline_refinery", .pipelineThenErr)
  , ("fallback", "world_state", .worldThenErr)
  , ("on_error", "configure_map", .configureThenErr)
  , ("invalid", "dispatch", .dispatchErrorInstr)
  ]

theorem pyashEnglishNormalizationPositiveExamples_sound :
    ∀ row ∈ pyashEnglishNormalizationPositiveExamples,
      pyashEnglishNormalizedMoodHeadToWDFClause? row.1 row.2.1 = some row.2.2 ∧
      pyashEnglishNormalizedMoodHeadToState? row.1 row.2.1 = some row.2.2.expectedState := by
  decide

/-- End-to-end controlled-English parser result projected to focused Pyash state. -/
def pyashEnglishMoodHeadToState? (mood head : String) : Option Pattern := do
  let clause ← pyashEnglishMoodHeadToWDFClause? mood head
  pyashGFClauseToState? clause.toGFClause

theorem pyashEnglishCanonicalMoodHead_roundtrip (c : PyashEnglishWDFClause) :
    pyashEnglishMoodHeadToWDFClause?
        c.toCanonicalEnglish.1 c.toCanonicalEnglish.2 = some c := by
  cases c <;> simp [PyashEnglishWDFClause.toCanonicalEnglish, pyashEnglishMoodHeadToWDFClause?]

theorem pyashEnglishMoodHeadToState_sound
    {mood head : String} {c : PyashEnglishWDFClause}
    (hmap : pyashEnglishMoodHeadToWDFClause? mood head = some c) :
    pyashEnglishMoodHeadToState? mood head = some c.expectedState := by
  unfold pyashEnglishMoodHeadToState?
  simp [hmap, pyashEnglishWDFClause_state_sound c]

theorem pyashEnglishCanonicalMoodHead_state_sound (c : PyashEnglishWDFClause) :
    pyashEnglishMoodHeadToState? c.toCanonicalEnglish.1 c.toCanonicalEnglish.2 =
      some c.expectedState := by
  exact pyashEnglishMoodHeadToState_sound (pyashEnglishCanonicalMoodHead_roundtrip c)

theorem pyashEnglishWDFAll_state_sound :
    ∀ c ∈ pyashEnglishWDFAll,
      pyashEnglishMoodHeadToState? c.toCanonicalEnglish.1 c.toCanonicalEnglish.2 =
        some c.expectedState := by
  intro c _hmem
  exact pyashEnglishCanonicalMoodHead_state_sound c

/-- Positive canary bundle: canonical controlled-English pairs all map to states. -/
def pyashEnglishWDFCanaries : List (String × Bool) :=
  pyashEnglishWDFAll.map (fun c =>
    let p := c.toCanonicalEnglish
    ("pyash_en_wdf_" ++ c.toLabel, (pyashEnglishMoodHeadToState? p.1 p.2).isSome))

/-- Explicitly unsupported controlled-English mood/head pairs (negative examples). -/
def pyashEnglishUnsupportedPairs : List (String × String) :=
  [ ("do", "concatenate")
  , ("do", "evoke")
  , ("do", "calendar")
  , ("do", "trace")
  , ("do", "least")
  ]

theorem pyashEnglishUnsupportedPairs_unmapped :
    ∀ row ∈ pyashEnglishUnsupportedPairs,
      pyashEnglishMoodHeadToWDFClause? row.1 row.2 = none := by
  intro row hrow
  simp [pyashEnglishUnsupportedPairs] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl
  all_goals simp [pyashEnglishMoodHeadToWDFClause?]

/-- Negative canary bundle for unsupported pairs. -/
def pyashEnglishUnsupportedCanaries : List (String × Bool) :=
  pyashEnglishUnsupportedPairs.map (fun row =>
    ("pyash_en_gap_" ++ row.1 ++ "_" ++ row.2,
      (pyashEnglishMoodHeadToWDFClause? row.1 row.2).isNone))

/-- Moods used for controlled-English semantic classification. -/
def pyashEnglishMoodCandidates : List String :=
  [ "do", "def", "then", "error" ]

/-- Canonical English heads required by the current WDF clause map. -/
def pyashEnglishCanonicalHeads : List String :=
  pyashEnglishWDFAll.map (fun c => c.toCanonicalEnglish.2)

/-- Semantic English head inventory:
observed corpus heads plus canonical heads needed by the bridge. -/
def pyashEnglishSemanticHeadInventory : List String :=
  pyashEnglishHeadInventory ++ pyashEnglishCanonicalHeads

theorem pyashEnglishCanonicalHead_mem_semantic_inventory (c : PyashEnglishWDFClause) :
    c.toCanonicalEnglish.2 ∈ pyashEnglishSemanticHeadInventory := by
  have hc : c ∈ pyashEnglishWDFAll := by
    cases c <;> simp [pyashEnglishWDFAll]
  unfold pyashEnglishSemanticHeadInventory pyashEnglishCanonicalHeads
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨c, hc, rfl⟩))

/-- Every WDF clause has at least one controlled-English pair in the semantic inventory. -/
theorem pyashEnglishSemantic_inventory_clause_complete (c : PyashEnglishWDFClause) :
    ∃ mood head,
      head ∈ pyashEnglishSemanticHeadInventory ∧
      pyashEnglishMoodHeadToWDFClause? mood head = some c ∧
      pyashEnglishMoodHeadToState? mood head = some c.expectedState := by
  refine ⟨c.toCanonicalEnglish.1, c.toCanonicalEnglish.2, ?_, ?_, ?_⟩
  · exact pyashEnglishCanonicalHead_mem_semantic_inventory c
  · exact pyashEnglishCanonicalMoodHead_roundtrip c
  · exact pyashEnglishCanonicalMoodHead_state_sound c

/-- Head-level semantic classifier over controlled mood candidates. -/
def pyashEnglishHeadIsMapped (head : String) : Bool :=
  pyashEnglishMoodCandidates.any (fun mood =>
    (pyashEnglishNormalizedMoodHeadToWDFClause? mood head).isSome)

theorem pyashEnglishCanonicalHeads_mapped :
    ∀ c ∈ pyashEnglishWDFAll, pyashEnglishHeadIsMapped c.toCanonicalEnglish.2 = true := by
  intro c _hmem
  cases c <;>
    simp [pyashEnglishHeadIsMapped, pyashEnglishMoodCandidates,
      PyashEnglishWDFClause.toCanonicalEnglish, pyashEnglishNormalizedMoodHeadToWDFClause?,
      pyashEnglishNormalizeMoodHead, pyashEnglishNormalizeMood, pyashEnglishNormalizeHead,
      pyashEnglishMoodHeadToWDFClause?]

/-- Observed corpus heads that map to at least one WDF clause. -/
def pyashEnglishObservedMappedHeads : List String :=
  pyashEnglishHeadInventory.filter (fun head => pyashEnglishHeadIsMapped head)

/-- Observed corpus heads currently outside the controlled WDF fragment. -/
def pyashEnglishObservedUnmappedHeads : List String :=
  pyashEnglishHeadInventory.filter (fun head => !(pyashEnglishHeadIsMapped head))

/-- Number of observed heads mapped by the controlled-English normalization bridge. -/
def pyashEnglishObservedMappedHeadCount : Nat :=
  pyashEnglishObservedMappedHeads.length

/-- Number of observed heads currently outside the controlled-English bridge. -/
def pyashEnglishObservedUnmappedHeadCount : Nat :=
  pyashEnglishObservedUnmappedHeads.length

/-- Percentage (integer floor) of observed heads mapped by the bridge. -/
def pyashEnglishObservedMappedHeadPercent : Nat :=
  let total := pyashEnglishHeadInventory.length
  if total == 0 then
    0
  else
    (100 * pyashEnglishObservedMappedHeads.length) / total

/-- Per-mood mapped-head count under normalized mood/head parsing. -/
def pyashEnglishMappedHeadCountForMood (mood : String) : Nat :=
  pyashEnglishHeadInventory.foldl
    (fun acc head =>
      if (pyashEnglishNormalizedMoodHeadToWDFClause? mood head).isSome then
        acc + 1
      else
        acc)
    0

/-- Per-mood semantic coverage summary over observed English heads. -/
def pyashEnglishMoodCoverageRows : List (String × Nat) :=
  pyashEnglishMoodCandidates.map (fun mood =>
    (mood, pyashEnglishMappedHeadCountForMood mood))

/-- Connector/function-word heads tracked separately from clause-head coverage. -/
def pyashEnglishConnectorHeads : List String :=
  [ "and", "or", "not", "be", "su", "ya", "ve" ]

theorem pyashEnglishConnectorHeads_unmapped :
    ∀ head ∈ pyashEnglishConnectorHeads, pyashEnglishHeadIsMapped head = false := by
  intro head hhead
  simp [pyashEnglishConnectorHeads] at hhead
  rcases hhead with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [pyashEnglishHeadIsMapped, pyashEnglishMoodCandidates,
      pyashEnglishNormalizedMoodHeadToWDFClause?, pyashEnglishNormalizeMoodHead,
      pyashEnglishNormalizeMood, pyashEnglishNormalizeHead, pyashEnglishMoodHeadToWDFClause?]

/-- Positive alias examples from observed English heads into WDF clauses. -/
def pyashEnglishAliasPositiveExamples : List (String × String × PyashEnglishWDFClause) :=
  [ ("do", "microphone", .hearMicDo)
  , ("do", "srt", .hearSrtDo)
  , ("do", "refinery", .pipelineDo)
  , ("do", "chirp", .pipelineChirpDo)
  , ("do", "reentry", .pipelineReentryDo)
  , ("do", "translation", .translationDo)
  ]

theorem pyashEnglishAliasPositiveExamples_sound :
    ∀ row ∈ pyashEnglishAliasPositiveExamples,
      pyashEnglishMoodHeadToWDFClause? row.1 row.2.1 = some row.2.2 ∧
      pyashEnglishMoodHeadToState? row.1 row.2.1 = some row.2.2.expectedState := by
  intro row hrow
  simp [pyashEnglishAliasPositiveExamples] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [pyashEnglishMoodHeadToWDFClause?,
      pyashEnglishMoodHeadToState?, pyashEnglishWDFClause_state_sound]

/-- Guardrail floor for observed-head semantic mapping coverage. -/
def pyashEnglishObservedMappedHeadFloor : Nat := 15

theorem pyashEnglishObservedMappedHeadFloor_holds :
    pyashEnglishObservedMappedHeads.length ≥ pyashEnglishObservedMappedHeadFloor := by
  decide

/-- Semantic coverage canary bundle for controlled-English integration. -/
def pyashEnglishSemanticCoverageCanaries : List (String × Bool) :=
  [ ("pyash_en_wdf_all_canonical_heads_mapped",
      pyashEnglishWDFAll.all (fun c => pyashEnglishHeadIsMapped c.toCanonicalEnglish.2))
  , ("pyash_en_observed_mapped_head_floor",
      decide (pyashEnglishObservedMappedHeads.length ≥ pyashEnglishObservedMappedHeadFloor))
  , ("pyash_en_connector_heads_unmapped",
      pyashEnglishConnectorHeads.all (fun head => !(pyashEnglishHeadIsMapped head)))
  ]

theorem pyashEnglishSemanticCoverageCanaries_all_true :
    pyashEnglishSemanticCoverageCanaries.all (fun row => row.2) = true := by
  unfold pyashEnglishSemanticCoverageCanaries
  have hcanon :
      pyashEnglishWDFAll.all (fun c => pyashEnglishHeadIsMapped c.toCanonicalEnglish.2) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    exact pyashEnglishCanonicalHeads_mapped c hc
  have hfloor :
      decide (pyashEnglishObservedMappedHeads.length ≥ pyashEnglishObservedMappedHeadFloor) = true := by
    exact decide_eq_true pyashEnglishObservedMappedHeadFloor_holds
  have hconn :
      pyashEnglishConnectorHeads.all (fun head => !(pyashEnglishHeadIsMapped head)) = true := by
    apply List.all_eq_true.mpr
    intro head hhead
    have hfalse := pyashEnglishConnectorHeads_unmapped head hhead
    simp [hfalse]
  simp [hcanon, hfloor, hconn]

end Mettapedia.OSLF.Framework.PyashGFEnglishFragment
