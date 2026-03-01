import Mettapedia.Languages.GF.Abstract
import Mettapedia.OSLF.Framework.PyashCoreModel

/-!
# Pyash GF Bridge (Initial)

Minimal GF-connected bridge from a tiny Pyash clause fragment into the
`PyashCore` OSLF model, with executable bridge claims.
-/

namespace Mettapedia.OSLF.Framework.PyashGF

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.PyashCoreInstance

/-- Lightweight multi-step closure for focused PyashCore reductions. -/
inductive PyashCoreReducesStar : Pattern → Pattern → Prop where
  | refl (p : Pattern) : PyashCoreReducesStar p p
  | step {p q r : Pattern} :
      langReduces pyashCore p q →
        PyashCoreReducesStar q r →
          PyashCoreReducesStar p r

namespace PyashCoreReducesStar

/-- Lift one-step reduction into closure. -/
theorem single {p q : Pattern}
    (h : langReduces pyashCore p q) :
    PyashCoreReducesStar p q :=
  .step h (.refl q)

/-- Transitivity of closure. -/
theorem trans {p q r : Pattern}
    (h₁ : PyashCoreReducesStar p q)
    (h₂ : PyashCoreReducesStar q r) :
    PyashCoreReducesStar p r := by
  induction h₁ with
  | refl _ => exact h₂
  | step hstep hrest ih => exact .step hstep (ih h₂)

end PyashCoreReducesStar

/-- Tiny GF-side categories for a focused Pyash clause fragment. -/
def pyashMoodCat : Category := .base "PyashMood"
def pyashVerbCat : Category := .base "PyashVerb"
def pyashClauseCat : Category := .base "PyashClause"

/-- Tiny GF-side constructors for focused Pyash bridge cases. -/
def PyDo : FunctionSig := ⟨"PyDo", pyashMoodCat⟩
def PyDef : FunctionSig := ⟨"PyDef", pyashMoodCat⟩
def PyThen : FunctionSig := ⟨"PyThen", pyashMoodCat⟩
def PyRead : FunctionSig := ⟨"PyRead", pyashVerbCat⟩
def PyWrite : FunctionSig := ⟨"PyWrite", pyashVerbCat⟩
def PySay : FunctionSig := ⟨"PySay", pyashVerbCat⟩
def PyMap : FunctionSig := ⟨"PyMap", pyashVerbCat⟩
def PyCommand : FunctionSig := ⟨"PyCommand", pyashVerbCat⟩
def PySearch : FunctionSig := ⟨"PySearch", pyashVerbCat⟩
def PyList : FunctionSig := ⟨"PyList", pyashVerbCat⟩
def PyInput : FunctionSig := ⟨"PyInput", pyashVerbCat⟩
def PyStream : FunctionSig := ⟨"PyStream", pyashVerbCat⟩
def PyMind : FunctionSig := ⟨"PyMind", pyashVerbCat⟩
def PyChip : FunctionSig := ⟨"PyChip", pyashVerbCat⟩
def PyChipSeries : FunctionSig := ⟨"PyChipSeries", pyashVerbCat⟩
def PyChipBounded : FunctionSig := ⟨"PyChipBounded", pyashVerbCat⟩
def PyHear : FunctionSig := ⟨"PyHear", pyashVerbCat⟩
def PyHearMic : FunctionSig := ⟨"PyHearMic", pyashVerbCat⟩
def PyHearSrt : FunctionSig := ⟨"PyHearSrt", pyashVerbCat⟩
def PyConfigure : FunctionSig := ⟨"PyConfigure", pyashVerbCat⟩
def PyConfigureCommandMapDef : FunctionSig := ⟨"PyConfigureCommandMapDef", pyashVerbCat⟩
def PyConfigureSandboxMapDef : FunctionSig := ⟨"PyConfigureSandboxMapDef", pyashVerbCat⟩
def PyConfigureVerifyLoopMapDef : FunctionSig := ⟨"PyConfigureVerifyLoopMapDef", pyashVerbCat⟩
def PyWorld : FunctionSig := ⟨"PyWorld", pyashVerbCat⟩
def PyWorldPathIO : FunctionSig := ⟨"PyWorldPathIO", pyashVerbCat⟩
def PyPipeline : FunctionSig := ⟨"PyPipeline", pyashVerbCat⟩
def PyPipelineRefinery : FunctionSig := ⟨"PyPipelineRefinery", pyashVerbCat⟩
def PyPipelineChirp : FunctionSig := ⟨"PyPipelineChirp", pyashVerbCat⟩
def PyPipelineReentry : FunctionSig := ⟨"PyPipelineReentry", pyashVerbCat⟩
def PyCompile : FunctionSig := ⟨"PyCompile", pyashVerbCat⟩
def PyImport : FunctionSig := ⟨"PyImport", pyashVerbCat⟩
def PyDownload : FunctionSig := ⟨"PyDownload", pyashVerbCat⟩
def PyTranslation : FunctionSig := ⟨"PyTranslation", pyashVerbCat⟩
def PyDispatchError : FunctionSig := ⟨"PyDispatchError", pyashClauseCat⟩
def PyClause : FunctionSig :=
  ⟨"PyClause", .arrow pyashMoodCat (.arrow pyashVerbCat pyashClauseCat)⟩

/-- Focused GF clause canaries. -/
def pyashGFReadDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyRead []]

def pyashGFMindDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyMind []]

def pyashGFWriteDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyWrite []]

def pyashGFSayDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PySay []]

def pyashGFMapDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyMap []]

def pyashGFMapDefClause : AbstractNode :=
  .apply PyClause [.apply PyDef [], .apply PyMap []]

def pyashGFCommandDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyCommand []]

def pyashGFSearchDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PySearch []]

def pyashGFListDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyList []]

def pyashGFInputDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyInput []]

def pyashGFStreamDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyStream []]

def pyashGFReadThenClause : AbstractNode :=
  .apply PyClause [.apply PyThen [], .apply PyRead []]

def pyashGFConfigureThenClause : AbstractNode :=
  .apply PyClause [.apply PyThen [], .apply PyConfigure []]

def pyashGFWorldThenClause : AbstractNode :=
  .apply PyClause [.apply PyThen [], .apply PyWorld []]

def pyashGFPipelineThenClause : AbstractNode :=
  .apply PyClause [.apply PyThen [], .apply PyPipeline []]

def pyashGFChipDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyChip []]

def pyashGFChipSeriesDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyChipSeries []]

def pyashGFChipBoundedDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyChipBounded []]

def pyashGFHearDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyHear []]

def pyashGFHearMicDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyHearMic []]

def pyashGFHearSrtDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyHearSrt []]

def pyashGFConfigureDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyConfigure []]

def pyashGFConfigureDefClause : AbstractNode :=
  .apply PyClause [.apply PyDef [], .apply PyConfigure []]

def pyashGFConfigureCommandMapDefClause : AbstractNode :=
  .apply PyClause [.apply PyDef [], .apply PyConfigureCommandMapDef []]

def pyashGFConfigureSandboxMapDefClause : AbstractNode :=
  .apply PyClause [.apply PyDef [], .apply PyConfigureSandboxMapDef []]

def pyashGFConfigureVerifyLoopMapDefClause : AbstractNode :=
  .apply PyClause [.apply PyDef [], .apply PyConfigureVerifyLoopMapDef []]

def pyashGFWorldDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyWorld []]

def pyashGFWorldPathDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyWorldPathIO []]

def pyashGFPipelineDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyPipeline []]

def pyashGFPipelineRefineryDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyPipelineRefinery []]

def pyashGFPipelineChirpDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyPipelineChirp []]

def pyashGFPipelineReentryDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyPipelineReentry []]

def pyashGFCompileDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyCompile []]

def pyashGFImportDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyImport []]

def pyashGFDownloadDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyDownload []]

def pyashGFTranslationDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyTranslation []]

def pyashGFDispatchErrorClause : AbstractNode :=
  .apply PyDispatchError []

private def ctorName? : AbstractNode → Option String
  | .apply f [] => some f.name
  | .leaf name _ => some name
  | _ => none

private def doMoodVerbToState? (verbName : String) : Option Pattern :=
  if verbName == "PyRead" then
    some pyashStateReadDerive
  else if verbName == "PyWrite" then
    some pyashStateWriteDerive
  else if verbName == "PySay" then
    some pyashStateSayDerive
  else if verbName == "PyMap" then
    some pyashStateMapDerive
  else if verbName == "PyCommand" then
    some pyashStateCommandDerive
  else if verbName == "PySearch" then
    some pyashStateSearchDerive
  else if verbName == "PyList" then
    some pyashStateListDerive
  else if verbName == "PyInput" then
    some pyashStateInputDerive
  else if verbName == "PyStream" then
    some pyashStateStreamDerive
  else if verbName == "PyMind" then
    some pyashStateMindDerive
  else if verbName == "PyChip" then
    some pyashStateChipDerive
  else if verbName == "PyChipSeries" then
    some pyashStateChipSeriesDerive
  else if verbName == "PyChipBounded" then
    some pyashStateChipBoundedDerive
  else if verbName == "PyHear" then
    some pyashStateHearDerive
  else if verbName == "PyHearMic" then
    some pyashStateHearMicRecordDerive
  else if verbName == "PyHearSrt" then
    some pyashStateHearFileSrtDerive
  else if verbName == "PyConfigure" then
    some pyashStateConfigureDerive
  else if verbName == "PyWorld" then
    some pyashStateWorldDerive
  else if verbName == "PyWorldPathIO" then
    some pyashStateWorldPathIODerive
  else if verbName == "PyPipeline" then
    some pyashStatePipelineDerive
  else if verbName == "PyPipelineRefinery" then
    some pyashStatePipelineRefineryDerive
  else if verbName == "PyPipelineChirp" then
    some pyashStatePipelineChirpDerive
  else if verbName == "PyPipelineReentry" then
    some pyashStatePipelineReentryDerive
  else if verbName == "PyCompile" then
    some pyashStateCompileDerive
  else if verbName == "PyImport" then
    some pyashStateImportDerive
  else if verbName == "PyDownload" then
    some pyashStateDownloadDerive
  else if verbName == "PyTranslation" then
    some pyashStateTranslationDerive
  else
    none

def pyashStateConfigureThenError : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MThen" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Ok" []
  ]

def pyashStateConfigureThenDoneDispatchErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrDispatch" []
  ]

def pyashStateWorldThenError : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MThen" [], .apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Ok" []
  ]

def pyashStateWorldThenDoneDispatchErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrDispatch" []
  ]

def pyashStatePipelineThenError : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MThen" [], .apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Signature" [.apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Ok" []
  ]

def pyashStatePipelineThenDoneDispatchErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesPipeline],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrDispatch" []
  ]

private def thenMoodVerbToState? (verbName : String) : Option Pattern :=
  if verbName == "PyRead" then
    some pyashStateDispatchThenError
  else if verbName == "PyConfigure" then
    some pyashStateConfigureThenError
  else if verbName == "PyWorld" then
    some pyashStateWorldThenError
  else if verbName == "PyPipeline" then
    some pyashStatePipelineThenError
  else
    none

/-- Bridge from tiny GF-side clause nodes into focused PyashCore states. -/
def pyashGFClauseToState? : AbstractNode → Option Pattern
  | .apply f [] =>
      if f.name == "PyDispatchError" then
        some pyashStateDispatchErrorInstr
      else
        none
  | .apply f [moodNode, verbNode] =>
      if f.name == "PyClause" then
        match ctorName? moodNode, ctorName? verbNode with
        | some moodName, some verbName =>
            if moodName == "PyDo" then
              doMoodVerbToState? verbName
            else if moodName == "PyDef" then
              if verbName == "PyConfigure" then
                some pyashStateConfigureDefDerive
              else if verbName == "PyConfigureCommandMapDef" then
                some pyashStateConfigureCommandMapDefDerive
              else if verbName == "PyConfigureSandboxMapDef" then
                some pyashStateConfigureSandboxMapDefDerive
              else if verbName == "PyConfigureVerifyLoopMapDef" then
                some pyashStateConfigureVerifyLoopMapDefDerive
              else if verbName == "PyMap" then
                some pyashStateMapDefDerive
              else
                none
            else if moodName == "PyThen" then
              thenMoodVerbToState? verbName
            else
              none
        | _, _ => none
      else
        none
  | _ => none

/-- Total bridge endpoint for runtime/export paths (fallback = explicit dispatch error seed). -/
def pyashGFInputOf (n : AbstractNode) : Pattern :=
  (pyashGFClauseToState? n).getD pyashStateDispatchThenError

/-- Single-source case inventory for GF clause-to-state mapping assertions. -/
def pyashGFClauseMapCases : List (AbstractNode × Pattern) :=
  [ (pyashGFReadDoClause, pyashStateReadDerive)
  , (pyashGFWriteDoClause, pyashStateWriteDerive)
  , (pyashGFSayDoClause, pyashStateSayDerive)
  , (pyashGFMapDoClause, pyashStateMapDerive)
  , (pyashGFMapDefClause, pyashStateMapDefDerive)
  , (pyashGFCommandDoClause, pyashStateCommandDerive)
  , (pyashGFSearchDoClause, pyashStateSearchDerive)
  , (pyashGFListDoClause, pyashStateListDerive)
  , (pyashGFInputDoClause, pyashStateInputDerive)
  , (pyashGFStreamDoClause, pyashStateStreamDerive)
  , (pyashGFMindDoClause, pyashStateMindDerive)
  , (pyashGFReadThenClause, pyashStateDispatchThenError)
  , (pyashGFConfigureThenClause, pyashStateConfigureThenError)
  , (pyashGFWorldThenClause, pyashStateWorldThenError)
  , (pyashGFPipelineThenClause, pyashStatePipelineThenError)
  , (pyashGFChipDoClause, pyashStateChipDerive)
  , (pyashGFChipSeriesDoClause, pyashStateChipSeriesDerive)
  , (pyashGFChipBoundedDoClause, pyashStateChipBoundedDerive)
  , (pyashGFHearDoClause, pyashStateHearDerive)
  , (pyashGFHearMicDoClause, pyashStateHearMicRecordDerive)
  , (pyashGFHearSrtDoClause, pyashStateHearFileSrtDerive)
  , (pyashGFConfigureDoClause, pyashStateConfigureDerive)
  , (pyashGFConfigureDefClause, pyashStateConfigureDefDerive)
  , (pyashGFConfigureCommandMapDefClause, pyashStateConfigureCommandMapDefDerive)
  , (pyashGFConfigureSandboxMapDefClause, pyashStateConfigureSandboxMapDefDerive)
  , (pyashGFConfigureVerifyLoopMapDefClause, pyashStateConfigureVerifyLoopMapDefDerive)
  , (pyashGFWorldDoClause, pyashStateWorldDerive)
  , (pyashGFWorldPathDoClause, pyashStateWorldPathIODerive)
  , (pyashGFPipelineDoClause, pyashStatePipelineDerive)
  , (pyashGFPipelineRefineryDoClause, pyashStatePipelineRefineryDerive)
  , (pyashGFPipelineChirpDoClause, pyashStatePipelineChirpDerive)
  , (pyashGFPipelineReentryDoClause, pyashStatePipelineReentryDerive)
  , (pyashGFCompileDoClause, pyashStateCompileDerive)
  , (pyashGFImportDoClause, pyashStateImportDerive)
  , (pyashGFDownloadDoClause, pyashStateDownloadDerive)
  , (pyashGFTranslationDoClause, pyashStateTranslationDerive)
  , (pyashGFDispatchErrorClause, pyashStateDispatchErrorInstr)
  ]

/-- Batched correctness theorem for all canonical GF clause mapping cases. -/
theorem pyashGF_clause_map_cases_sound :
    ∀ clauseCase ∈ pyashGFClauseMapCases,
      pyashGFClauseToState? clauseCase.1 = some clauseCase.2 := by
  decide +kernel

private theorem pyashGF_clause_map_of_mem
    {clause : AbstractNode} {state : Pattern}
    (hmem : (clause, state) ∈ pyashGFClauseMapCases) :
    pyashGFClauseToState? clause = some state := by
  exact pyashGF_clause_map_cases_sound (clause, state) hmem

theorem pyashGF_read_clause_maps :
    pyashGFClauseToState? pyashGFReadDoClause = some pyashStateReadDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_write_clause_maps :
    pyashGFClauseToState? pyashGFWriteDoClause = some pyashStateWriteDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_say_clause_maps :
    pyashGFClauseToState? pyashGFSayDoClause = some pyashStateSayDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_map_clause_maps :
    pyashGFClauseToState? pyashGFMapDoClause = some pyashStateMapDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_map_def_clause_maps :
    pyashGFClauseToState? pyashGFMapDefClause = some pyashStateMapDefDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_command_clause_maps :
    pyashGFClauseToState? pyashGFCommandDoClause = some pyashStateCommandDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_search_clause_maps :
    pyashGFClauseToState? pyashGFSearchDoClause = some pyashStateSearchDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_list_clause_maps :
    pyashGFClauseToState? pyashGFListDoClause = some pyashStateListDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_input_clause_maps :
    pyashGFClauseToState? pyashGFInputDoClause = some pyashStateInputDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_stream_clause_maps :
    pyashGFClauseToState? pyashGFStreamDoClause = some pyashStateStreamDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_mind_clause_maps :
    pyashGFClauseToState? pyashGFMindDoClause = some pyashStateMindDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_read_then_clause_maps :
    pyashGFClauseToState? pyashGFReadThenClause = some pyashStateDispatchThenError := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_configure_then_clause_maps :
    pyashGFClauseToState? pyashGFConfigureThenClause = some pyashStateConfigureThenError := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_world_then_clause_maps :
    pyashGFClauseToState? pyashGFWorldThenClause = some pyashStateWorldThenError := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_pipeline_then_clause_maps :
    pyashGFClauseToState? pyashGFPipelineThenClause = some pyashStatePipelineThenError := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_chip_clause_maps :
    pyashGFClauseToState? pyashGFChipDoClause = some pyashStateChipDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_chip_series_clause_maps :
    pyashGFClauseToState? pyashGFChipSeriesDoClause = some pyashStateChipSeriesDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_chip_bounded_clause_maps :
    pyashGFClauseToState? pyashGFChipBoundedDoClause = some pyashStateChipBoundedDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_hear_clause_maps :
    pyashGFClauseToState? pyashGFHearDoClause = some pyashStateHearDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_hear_mic_clause_maps :
    pyashGFClauseToState? pyashGFHearMicDoClause = some pyashStateHearMicRecordDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_hear_srt_clause_maps :
    pyashGFClauseToState? pyashGFHearSrtDoClause = some pyashStateHearFileSrtDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_configure_clause_maps :
    pyashGFClauseToState? pyashGFConfigureDoClause = some pyashStateConfigureDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_configure_def_clause_maps :
    pyashGFClauseToState? pyashGFConfigureDefClause = some pyashStateConfigureDefDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_configure_command_map_def_clause_maps :
    pyashGFClauseToState? pyashGFConfigureCommandMapDefClause =
      some pyashStateConfigureCommandMapDefDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_configure_sandbox_map_def_clause_maps :
    pyashGFClauseToState? pyashGFConfigureSandboxMapDefClause =
      some pyashStateConfigureSandboxMapDefDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_configure_verify_loop_map_def_clause_maps :
    pyashGFClauseToState? pyashGFConfigureVerifyLoopMapDefClause =
      some pyashStateConfigureVerifyLoopMapDefDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_world_clause_maps :
    pyashGFClauseToState? pyashGFWorldDoClause = some pyashStateWorldDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_world_path_clause_maps :
    pyashGFClauseToState? pyashGFWorldPathDoClause = some pyashStateWorldPathIODerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_pipeline_clause_maps :
    pyashGFClauseToState? pyashGFPipelineDoClause = some pyashStatePipelineDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_pipeline_refinery_clause_maps :
    pyashGFClauseToState? pyashGFPipelineRefineryDoClause = some pyashStatePipelineRefineryDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_pipeline_chirp_clause_maps :
    pyashGFClauseToState? pyashGFPipelineChirpDoClause = some pyashStatePipelineChirpDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_pipeline_reentry_clause_maps :
    pyashGFClauseToState? pyashGFPipelineReentryDoClause = some pyashStatePipelineReentryDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_compile_clause_maps :
    pyashGFClauseToState? pyashGFCompileDoClause = some pyashStateCompileDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_import_clause_maps :
    pyashGFClauseToState? pyashGFImportDoClause = some pyashStateImportDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_download_clause_maps :
    pyashGFClauseToState? pyashGFDownloadDoClause = some pyashStateDownloadDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_translation_clause_maps :
    pyashGFClauseToState? pyashGFTranslationDoClause = some pyashStateTranslationDerive := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

theorem pyashGF_dispatch_error_clause_maps :
    pyashGFClauseToState? pyashGFDispatchErrorClause = some pyashStateDispatchErrorInstr := by
  exact pyashGF_clause_map_of_mem (by simp [pyashGFClauseMapCases])

end Mettapedia.OSLF.Framework.PyashGF
