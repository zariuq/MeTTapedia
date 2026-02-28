import Mettapedia.Languages.GF.Abstract
import Mettapedia.OSLF.Framework.PyashCoreInstance

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
def PyMind : FunctionSig := ⟨"PyMind", pyashVerbCat⟩
def PyChip : FunctionSig := ⟨"PyChip", pyashVerbCat⟩
def PyHear : FunctionSig := ⟨"PyHear", pyashVerbCat⟩
def PyConfigure : FunctionSig := ⟨"PyConfigure", pyashVerbCat⟩
def PyWorld : FunctionSig := ⟨"PyWorld", pyashVerbCat⟩
def PyWorldPathIO : FunctionSig := ⟨"PyWorldPathIO", pyashVerbCat⟩
def PyPipeline : FunctionSig := ⟨"PyPipeline", pyashVerbCat⟩
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

def pyashGFHearDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyHear []]

def pyashGFConfigureDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyConfigure []]

def pyashGFConfigureDefClause : AbstractNode :=
  .apply PyClause [.apply PyDef [], .apply PyConfigure []]

def pyashGFWorldDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyWorld []]

def pyashGFWorldPathDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyWorldPathIO []]

def pyashGFPipelineDoClause : AbstractNode :=
  .apply PyClause [.apply PyDo [], .apply PyPipeline []]

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
  else if verbName == "PyMind" then
    some pyashStateMindDerive
  else if verbName == "PyChip" then
    some pyashStateChipDerive
  else if verbName == "PyHear" then
    some pyashStateHearDerive
  else if verbName == "PyConfigure" then
    some pyashStateConfigureDerive
  else if verbName == "PyWorld" then
    some pyashStateWorldDerive
  else if verbName == "PyWorldPathIO" then
    some pyashStateWorldDerive
  else if verbName == "PyPipeline" then
    some pyashStatePipelineDerive
  else if verbName == "PyPipelineChirp" then
    some pyashStatePipelineDerive
  else if verbName == "PyPipelineReentry" then
    some pyashStatePipelineDerive
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

private def pyashStateConfigureThenError : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MThen" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Ok" []
  ]

private def pyashStateConfigureThenDoneDispatchErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrDispatch" []
  ]

private def pyashStateWorldThenError : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MThen" [], .apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Ok" []
  ]

private def pyashStateWorldThenDoneDispatchErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrDispatch" []
  ]

private def pyashStatePipelineThenError : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MThen" [], .apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Signature" [.apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Ok" []
  ]

private def pyashStatePipelineThenDoneDispatchErr : Pattern :=
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
            else if moodName == "PyDef" ∧ verbName == "PyConfigure" then
              some pyashStateConfigureDefDerive
            else if moodName == "PyDef" ∧ verbName == "PyMap" then
              some pyashStateMapDefDerive
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

theorem pyashGF_read_clause_maps :
    pyashGFClauseToState? pyashGFReadDoClause = some pyashStateReadDerive := by
  decide +kernel

theorem pyashGF_write_clause_maps :
    pyashGFClauseToState? pyashGFWriteDoClause = some pyashStateWriteDerive := by
  decide +kernel

theorem pyashGF_say_clause_maps :
    pyashGFClauseToState? pyashGFSayDoClause = some pyashStateSayDerive := by
  decide +kernel

theorem pyashGF_map_clause_maps :
    pyashGFClauseToState? pyashGFMapDoClause = some pyashStateMapDerive := by
  decide +kernel

theorem pyashGF_map_def_clause_maps :
    pyashGFClauseToState? pyashGFMapDefClause = some pyashStateMapDefDerive := by
  decide +kernel

theorem pyashGF_command_clause_maps :
    pyashGFClauseToState? pyashGFCommandDoClause = some pyashStateCommandDerive := by
  decide +kernel

theorem pyashGF_search_clause_maps :
    pyashGFClauseToState? pyashGFSearchDoClause = some pyashStateSearchDerive := by
  decide +kernel

theorem pyashGF_mind_clause_maps :
    pyashGFClauseToState? pyashGFMindDoClause = some pyashStateMindDerive := by
  decide +kernel

theorem pyashGF_read_then_clause_maps :
    pyashGFClauseToState? pyashGFReadThenClause = some pyashStateDispatchThenError := by
  decide +kernel

theorem pyashGF_configure_then_clause_maps :
    pyashGFClauseToState? pyashGFConfigureThenClause = some pyashStateConfigureThenError := by
  decide +kernel

theorem pyashGF_world_then_clause_maps :
    pyashGFClauseToState? pyashGFWorldThenClause = some pyashStateWorldThenError := by
  decide +kernel

theorem pyashGF_pipeline_then_clause_maps :
    pyashGFClauseToState? pyashGFPipelineThenClause = some pyashStatePipelineThenError := by
  decide +kernel

theorem pyashGF_chip_clause_maps :
    pyashGFClauseToState? pyashGFChipDoClause = some pyashStateChipDerive := by
  decide +kernel

theorem pyashGF_hear_clause_maps :
    pyashGFClauseToState? pyashGFHearDoClause = some pyashStateHearDerive := by
  decide +kernel

theorem pyashGF_configure_clause_maps :
    pyashGFClauseToState? pyashGFConfigureDoClause = some pyashStateConfigureDerive := by
  decide +kernel

theorem pyashGF_configure_def_clause_maps :
    pyashGFClauseToState? pyashGFConfigureDefClause = some pyashStateConfigureDefDerive := by
  decide +kernel

theorem pyashGF_world_clause_maps :
    pyashGFClauseToState? pyashGFWorldDoClause = some pyashStateWorldDerive := by
  decide +kernel

theorem pyashGF_world_path_clause_maps :
    pyashGFClauseToState? pyashGFWorldPathDoClause = some pyashStateWorldDerive := by
  decide +kernel

theorem pyashGF_pipeline_clause_maps :
    pyashGFClauseToState? pyashGFPipelineDoClause = some pyashStatePipelineDerive := by
  decide +kernel

theorem pyashGF_pipeline_chirp_clause_maps :
    pyashGFClauseToState? pyashGFPipelineChirpDoClause = some pyashStatePipelineDerive := by
  decide +kernel

theorem pyashGF_pipeline_reentry_clause_maps :
    pyashGFClauseToState? pyashGFPipelineReentryDoClause = some pyashStatePipelineDerive := by
  decide +kernel

theorem pyashGF_compile_clause_maps :
    pyashGFClauseToState? pyashGFCompileDoClause = some pyashStateCompileDerive := by
  decide +kernel

theorem pyashGF_import_clause_maps :
    pyashGFClauseToState? pyashGFImportDoClause = some pyashStateImportDerive := by
  decide +kernel

theorem pyashGF_download_clause_maps :
    pyashGFClauseToState? pyashGFDownloadDoClause = some pyashStateDownloadDerive := by
  decide +kernel

theorem pyashGF_translation_clause_maps :
    pyashGFClauseToState? pyashGFTranslationDoClause = some pyashStateTranslationDerive := by
  decide +kernel

theorem pyashGF_dispatch_error_clause_maps :
    pyashGFClauseToState? pyashGFDispatchErrorClause = some pyashStateDispatchErrorInstr := by
  decide +kernel

/-- Bridge claim 1 (OSLF): GF read/do clause reaches the PyashCore read dispatch stage. -/
theorem pyashGF_read_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFReadDoClause)
      pyashStateReadDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_read_clause_maps] using pyashCore_read_derive_signature_step

/-- Bridge claim (OSLF): GF write/do clause reaches the PyashCore write dispatch stage. -/
theorem pyashGF_write_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFWriteDoClause)
      pyashStateWriteDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_write_clause_maps] using pyashCore_write_derive_signature_step

/-- Bridge claim (OSLF): GF say/do clause reaches the PyashCore say dispatch stage. -/
theorem pyashGF_say_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFSayDoClause)
      pyashStateSayDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_say_clause_maps] using pyashCore_say_derive_signature_step

/-- Bridge claim (OSLF): GF map/do clause reaches the PyashCore map dispatch stage. -/
theorem pyashGF_map_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFMapDoClause)
      pyashStateMapDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_map_clause_maps] using pyashCore_map_derive_signature_step

/-- Bridge claim (OSLF): GF map/def clause reaches the PyashCore map-def dispatch stage. -/
theorem pyashGF_map_def_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFMapDefClause)
      pyashStateMapDefDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_map_def_clause_maps] using pyashCore_map_def_derive_signature_step

/-- Bridge claim (OSLF): GF command/do clause reaches the PyashCore command dispatch stage. -/
theorem pyashGF_command_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFCommandDoClause)
      pyashStateCommandDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_command_clause_maps] using pyashCore_command_derive_signature_step

/-- Bridge claim (OSLF): GF search/do clause reaches the PyashCore search dispatch stage. -/
theorem pyashGF_search_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFSearchDoClause)
      pyashStateSearchDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_search_clause_maps] using pyashCore_search_derive_signature_step

/-- Bridge claim 2 (OSLF): GF mind/do clause reaches the PyashCore mind dispatch stage. -/
theorem pyashGF_mind_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFMindDoClause)
      pyashStateMindDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_mind_clause_maps] using pyashCore_mind_derive_signature_step

/-- Bridge claim 2b (OSLF modal): GF mind/do clause has the expected one-step witness. -/
theorem pyashGF_mind_clause_diamond_bridge :
    langDiamond pyashCore (fun q => q = pyashStateMindDispatched)
      (pyashGFInputOf pyashGFMindDoClause) := by
  rw [langDiamond_spec]
  exact ⟨pyashStateMindDispatched, pyashGF_mind_clause_dispatch_bridge, rfl⟩

/-- Bridge claim 3 (OSLF, negative): unsupported GF `then` clause hits dispatch error path. -/
theorem pyashGF_read_then_negative_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFReadThenClause)
      pyashStateDoneDispatchErr := by
  unfold pyashGFInputOf
  simpa [pyashGF_read_then_clause_maps] using pyashCore_dispatch_then_surfaces_dispatch_error

/-- Bridge claim (OSLF, negative): unsupported GF `then/configure` hits dispatch error path. -/
theorem pyashGF_configure_then_negative_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFConfigureThenClause)
      pyashStateConfigureThenDoneDispatchErr := by
  unfold langReduces
  apply (langReducesUsing_iff_execUsing (relEnv := RelationEnv.empty) (lang := pyashCore)
    (p := pyashGFInputOf pyashGFConfigureThenClause)
    (q := pyashStateConfigureThenDoneDispatchErr)).2
  unfold langReducesExecUsing pyashGFInputOf
  simpa [pyashGF_configure_then_clause_maps] using
    (show pyashStateConfigureThenDoneDispatchErr ∈
      rewriteWithContextWithPremisesUsing RelationEnv.empty pyashCore pyashStateConfigureThenError by
        decide +kernel)

/-- Bridge claim (OSLF, negative): unsupported GF `then/world` hits dispatch error path. -/
theorem pyashGF_world_then_negative_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFWorldThenClause)
      pyashStateWorldThenDoneDispatchErr := by
  unfold langReduces
  apply (langReducesUsing_iff_execUsing (relEnv := RelationEnv.empty) (lang := pyashCore)
    (p := pyashGFInputOf pyashGFWorldThenClause)
    (q := pyashStateWorldThenDoneDispatchErr)).2
  unfold langReducesExecUsing pyashGFInputOf
  simpa [pyashGF_world_then_clause_maps] using
    (show pyashStateWorldThenDoneDispatchErr ∈
      rewriteWithContextWithPremisesUsing RelationEnv.empty pyashCore pyashStateWorldThenError by
        decide +kernel)

/-- Bridge claim (OSLF, negative): unsupported GF `then/pipeline` hits dispatch error path. -/
theorem pyashGF_pipeline_then_negative_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFPipelineThenClause)
      pyashStatePipelineThenDoneDispatchErr := by
  unfold langReduces
  apply (langReducesUsing_iff_execUsing (relEnv := RelationEnv.empty) (lang := pyashCore)
    (p := pyashGFInputOf pyashGFPipelineThenClause)
    (q := pyashStatePipelineThenDoneDispatchErr)).2
  unfold langReducesExecUsing pyashGFInputOf
  simpa [pyashGF_pipeline_then_clause_maps] using
    (show pyashStatePipelineThenDoneDispatchErr ∈
      rewriteWithContextWithPremisesUsing RelationEnv.empty pyashCore pyashStatePipelineThenError by
        decide +kernel)

/-- Multi-step closure (negative): GF `then/configure` reaches dispatch-error terminal state. -/
theorem pyashGF_configure_then_negative_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFConfigureThenClause)
      pyashStateConfigureThenDoneDispatchErr := by
  exact PyashCoreReducesStar.single pyashGF_configure_then_negative_bridge

/-- Multi-step closure (negative): GF `then/world` reaches dispatch-error terminal state. -/
theorem pyashGF_world_then_negative_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFWorldThenClause)
      pyashStateWorldThenDoneDispatchErr := by
  exact PyashCoreReducesStar.single pyashGF_world_then_negative_bridge

/-- Multi-step closure (negative): GF `then/pipeline` reaches dispatch-error terminal state. -/
theorem pyashGF_pipeline_then_negative_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFPipelineThenClause)
      pyashStatePipelineThenDoneDispatchErr := by
  exact PyashCoreReducesStar.single pyashGF_pipeline_then_negative_bridge

/-- Terminal closure (negative): configure `then` error terminal is stable. -/
theorem pyashGF_configure_then_terminal_closure :
    PyashCoreReducesStar
      pyashStateConfigureThenDoneDispatchErr
      pyashStateConfigureThenDoneDispatchErr := by
  exact PyashCoreReducesStar.refl pyashStateConfigureThenDoneDispatchErr

/-- Terminal closure (negative): world `then` error terminal is stable. -/
theorem pyashGF_world_then_terminal_closure :
    PyashCoreReducesStar
      pyashStateWorldThenDoneDispatchErr
      pyashStateWorldThenDoneDispatchErr := by
  exact PyashCoreReducesStar.refl pyashStateWorldThenDoneDispatchErr

/-- Terminal closure (negative): pipeline `then` error terminal is stable. -/
theorem pyashGF_pipeline_then_terminal_closure :
    PyashCoreReducesStar
      pyashStatePipelineThenDoneDispatchErr
      pyashStatePipelineThenDoneDispatchErr := by
  exact PyashCoreReducesStar.refl pyashStatePipelineThenDoneDispatchErr

/-- Bridge claim 4 (OSLF, negative): explicit GF dispatch-error clause reaches dispatch error. -/
theorem pyashGF_dispatch_error_negative_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFDispatchErrorClause)
      pyashStateDoneDispatchErr := by
  unfold pyashGFInputOf
  simpa [pyashGF_dispatch_error_clause_maps] using
    pyashCore_dispatch_error_instr_surfaces_dispatch_error

/-- `write` derive step (decomposed bridge lemma). -/
theorem pyashGF_write_derive_step :
    langReduces pyashCore pyashStateWriteDerive pyashStateWriteDispatched := by
  simpa using pyashCore_write_derive_signature_step

/-- `write` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_write_dispatch_step :
    langReduces pyashCore pyashStateWriteDispatched pyashStateWriteRunning := by
  simpa using pyashCore_write_dispatch_do_step

/-- `write` run step (decomposed bridge lemma). -/
theorem pyashGF_write_run_step :
    langReduces pyashCore pyashStateWriteRunning pyashStateWriteDoneOk := by
  simpa using pyashCore_write_run_do_step

/-- `say` derive step (decomposed bridge lemma). -/
theorem pyashGF_say_derive_step :
    langReduces pyashCore pyashStateSayDerive pyashStateSayDispatched := by
  simpa using pyashCore_say_derive_signature_step

/-- `say` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_say_dispatch_step :
    langReduces pyashCore pyashStateSayDispatched pyashStateSayRunning := by
  simpa using pyashCore_say_dispatch_do_step

/-- `say` run step (decomposed bridge lemma). -/
theorem pyashGF_say_run_step :
    langReduces pyashCore pyashStateSayRunning pyashStateSayDoneOk := by
  simpa using pyashCore_say_run_do_step

/-- `map` derive step (decomposed bridge lemma). -/
theorem pyashGF_map_derive_step :
    langReduces pyashCore pyashStateMapDerive pyashStateMapDispatched := by
  simpa using pyashCore_map_derive_signature_step

/-- `map` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_map_dispatch_step :
    langReduces pyashCore pyashStateMapDispatched pyashStateMapRunning := by
  simpa using pyashCore_map_dispatch_do_step

/-- `map` run step (decomposed bridge lemma). -/
theorem pyashGF_map_run_step :
    langReduces pyashCore pyashStateMapRunning pyashStateMapDoneOk := by
  simpa using pyashCore_map_run_do_step

/-- `map/def` derive step (decomposed bridge lemma). -/
theorem pyashGF_map_def_derive_step :
    langReduces pyashCore pyashStateMapDefDerive pyashStateMapDefDispatched := by
  simpa using pyashCore_map_def_derive_signature_step

/-- `map/def` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_map_def_dispatch_step :
    langReduces pyashCore pyashStateMapDefDispatched pyashStateMapDefDoneOk := by
  simpa using pyashCore_map_def_dispatch_def_step

/-- `command` derive step (decomposed bridge lemma). -/
theorem pyashGF_command_derive_step :
    langReduces pyashCore pyashStateCommandDerive pyashStateCommandDispatched := by
  simpa using pyashCore_command_derive_signature_step

/-- `command` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_command_dispatch_step :
    langReduces pyashCore pyashStateCommandDispatched pyashStateCommandRunning := by
  simpa using pyashCore_command_dispatch_do_step

/-- `command` run step (decomposed bridge lemma). -/
theorem pyashGF_command_run_step :
    langReduces pyashCore pyashStateCommandRunning pyashStateCommandDoneOk := by
  simpa using pyashCore_command_run_do_step

/-- `search` derive step (decomposed bridge lemma). -/
theorem pyashGF_search_derive_step :
    langReduces pyashCore pyashStateSearchDerive pyashStateSearchDispatched := by
  simpa using pyashCore_search_derive_signature_step

/-- `search` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_search_dispatch_step :
    langReduces pyashCore pyashStateSearchDispatched pyashStateSearchRunning := by
  simpa using pyashCore_search_dispatch_do_step

/-- `search` run step (decomposed bridge lemma). -/
theorem pyashGF_search_run_step :
    langReduces pyashCore pyashStateSearchRunning pyashStateSearchDoneOk := by
  simpa using pyashCore_search_run_do_step

/-- `compile` derive step (decomposed bridge lemma). -/
theorem pyashGF_compile_derive_step :
    langReduces pyashCore pyashStateCompileDerive pyashStateCompileDispatched := by
  simpa using pyashCore_compile_derive_signature_step

/-- `compile` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_compile_dispatch_step :
    langReduces pyashCore pyashStateCompileDispatched pyashStateCompileRunning := by
  simpa using pyashCore_compile_dispatch_do_step

/-- `compile` run step (decomposed bridge lemma). -/
theorem pyashGF_compile_run_step :
    langReduces pyashCore pyashStateCompileRunning pyashStateCompileDoneOk := by
  simpa using pyashCore_compile_run_do_step

/-- `import` derive step (decomposed bridge lemma). -/
theorem pyashGF_import_derive_step :
    langReduces pyashCore pyashStateImportDerive pyashStateImportDispatched := by
  simpa using pyashCore_import_derive_signature_step

/-- `import` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_import_dispatch_step :
    langReduces pyashCore pyashStateImportDispatched pyashStateImportRunning := by
  simpa using pyashCore_import_dispatch_do_step

/-- `import` run step (decomposed bridge lemma). -/
theorem pyashGF_import_run_step :
    langReduces pyashCore pyashStateImportRunning pyashStateImportDoneOk := by
  simpa using pyashCore_import_run_do_step

/-- `download` derive step (decomposed bridge lemma). -/
theorem pyashGF_download_derive_step :
    langReduces pyashCore pyashStateDownloadDerive pyashStateDownloadDispatched := by
  simpa using pyashCore_download_derive_signature_step

/-- `download` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_download_dispatch_step :
    langReduces pyashCore pyashStateDownloadDispatched pyashStateDownloadRunning := by
  simpa using pyashCore_download_dispatch_do_step

/-- `download` run step (decomposed bridge lemma). -/
theorem pyashGF_download_run_step :
    langReduces pyashCore pyashStateDownloadRunning pyashStateDownloadDoneOk := by
  simpa using pyashCore_download_run_do_step

/-- `translation` derive step (decomposed bridge lemma). -/
theorem pyashGF_translation_derive_step :
    langReduces pyashCore pyashStateTranslationDerive pyashStateTranslationDispatched := by
  simpa using pyashCore_translation_derive_signature_step

/-- `translation` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_translation_dispatch_step :
    langReduces pyashCore pyashStateTranslationDispatched pyashStateTranslationRunning := by
  simpa using pyashCore_translation_dispatch_do_step

/-- `translation` run step (decomposed bridge lemma). -/
theorem pyashGF_translation_run_step :
    langReduces pyashCore pyashStateTranslationRunning pyashStateTranslationDoneOk := by
  simpa using pyashCore_translation_run_do_step

/-- Bridge claim (OSLF): GF compile/do clause reaches PyashCore compile dispatch stage. -/
theorem pyashGF_compile_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFCompileDoClause)
      pyashStateCompileDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_compile_clause_maps] using pyashGF_compile_derive_step

/-- Bridge claim (OSLF): GF import/do clause reaches PyashCore import dispatch stage. -/
theorem pyashGF_import_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFImportDoClause)
      pyashStateImportDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_import_clause_maps] using pyashGF_import_derive_step

/-- Bridge claim (OSLF): GF download/do clause reaches PyashCore download dispatch stage. -/
theorem pyashGF_download_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFDownloadDoClause)
      pyashStateDownloadDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_download_clause_maps] using pyashGF_download_derive_step

/-- Bridge claim (OSLF): GF translation/do clause reaches PyashCore translation dispatch stage. -/
theorem pyashGF_translation_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFTranslationDoClause)
      pyashStateTranslationDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_translation_clause_maps] using pyashGF_translation_derive_step

/-- Multi-step closure bridge: GF compile/do reaches focused done state. -/
theorem pyashGF_compile_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFCompileDoClause)
      pyashStateCompileDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_compile_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_compile_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_compile_run_step))

/-- Multi-step closure bridge: GF import/do reaches focused done state. -/
theorem pyashGF_import_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFImportDoClause)
      pyashStateImportDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_import_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_import_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_import_run_step))

/-- Multi-step closure bridge: GF download/do reaches focused done state. -/
theorem pyashGF_download_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFDownloadDoClause)
      pyashStateDownloadDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_download_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_download_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_download_run_step))

/-- Multi-step closure bridge: GF translation/do reaches focused done state. -/
theorem pyashGF_translation_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFTranslationDoClause)
      pyashStateTranslationDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_translation_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_translation_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_translation_run_step))

/-- Multi-step closure bridge: GF write/do reaches focused done state. -/
theorem pyashGF_write_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFWriteDoClause)
      pyashStateWriteDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_write_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_write_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_write_run_step))

/-- Multi-step closure bridge: GF say/do reaches focused done state. -/
theorem pyashGF_say_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFSayDoClause)
      pyashStateSayDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_say_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_say_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_say_run_step))

/-- Multi-step closure bridge: GF map/do reaches focused done state. -/
theorem pyashGF_map_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFMapDoClause)
      pyashStateMapDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_map_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_map_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_map_run_step))

/-- Multi-step closure bridge: GF map/def reaches focused done state. -/
theorem pyashGF_map_def_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFMapDefClause)
      pyashStateMapDefDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_map_def_clause_dispatch_bridge).trans
      (PyashCoreReducesStar.single pyashGF_map_def_dispatch_step)

/-- Multi-step closure bridge: GF command/do reaches focused done state. -/
theorem pyashGF_command_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFCommandDoClause)
      pyashStateCommandDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_command_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_command_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_command_run_step))

/-- Multi-step closure bridge: GF search/do reaches focused done state. -/
theorem pyashGF_search_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFSearchDoClause)
      pyashStateSearchDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_search_clause_dispatch_bridge).trans
      ((PyashCoreReducesStar.single pyashGF_search_dispatch_step).trans
        (PyashCoreReducesStar.single pyashGF_search_run_step))

/-- Bridge claim 5 (OSLF): GF chip/do clause reaches the PyashCore chip dispatch stage. -/
theorem pyashGF_chip_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFChipDoClause)
      pyashStateChipDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_chip_clause_maps] using pyashCore_chip_derive_signature_step

/-- Bridge claim 6 (OSLF): GF hear/do clause reaches the PyashCore hear dispatch stage. -/
theorem pyashGF_hear_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFHearDoClause)
      pyashStateHearDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_hear_clause_maps] using pyashCore_hear_derive_signature_step

/-- `configure` derive step (decomposed bridge lemma). -/
theorem pyashGF_configure_derive_step :
    langReduces pyashCore pyashStateConfigureDerive pyashStateConfigureDispatched := by
  simpa using pyashCore_configure_derive_signature_step

/-- `configure` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_configure_dispatch_step :
    langReduces pyashCore pyashStateConfigureDispatched pyashStateConfigureRunning := by
  simpa using pyashCore_configure_dispatch_do_step

/-- `configure` run step (decomposed bridge lemma). -/
theorem pyashGF_configure_run_step :
    langReduces pyashCore pyashStateConfigureRunning pyashStateConfigureDoneOk := by
  simpa using pyashCore_configure_run_do_step

/-- Bridge claim 7 (OSLF): GF configure/do clause reaches the PyashCore configure dispatch stage. -/
theorem pyashGF_configure_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFConfigureDoClause)
      pyashStateConfigureDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_configure_clause_maps] using pyashGF_configure_derive_step

/-- Decomposed `configure` one-step bridge package from GF-mapped input. -/
theorem pyashGF_configure_clause_step_decomposition :
    (pyashGFInputOf pyashGFConfigureDoClause = pyashStateConfigureDerive) ∧
      langReduces pyashCore pyashStateConfigureDerive pyashStateConfigureDispatched ∧
      langReduces pyashCore pyashStateConfigureDispatched pyashStateConfigureRunning ∧
      langReduces pyashCore pyashStateConfigureRunning pyashStateConfigureDoneOk := by
  constructor
  · unfold pyashGFInputOf
    simp [pyashGF_configure_clause_maps]
  constructor
  · exact pyashGF_configure_derive_step
  constructor
  · exact pyashGF_configure_dispatch_step
  · exact pyashGF_configure_run_step

/-- Multi-step closure bridge: GF `configure/do` reaches the focused done state. -/
theorem pyashGF_configure_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFConfigureDoClause)
      pyashStateConfigureDoneOk := by
  have hDerive :
      langReduces pyashCore
        (pyashGFInputOf pyashGFConfigureDoClause)
        pyashStateConfigureDispatched :=
    pyashGF_configure_clause_dispatch_bridge
  have hDispatch :
      langReduces pyashCore
        pyashStateConfigureDispatched
        pyashStateConfigureRunning :=
    pyashGF_configure_dispatch_step
  have hRun :
      langReduces pyashCore
        pyashStateConfigureRunning
        pyashStateConfigureDoneOk :=
    pyashGF_configure_run_step
  exact
    (PyashCoreReducesStar.single hDerive).trans
      ((PyashCoreReducesStar.single hDispatch).trans
        (PyashCoreReducesStar.single hRun))

/-- Multi-step closure: configure dispatched state reaches focused done state. -/
theorem pyashGF_configure_dispatched_closure_bridge :
    PyashCoreReducesStar
      pyashStateConfigureDispatched
      pyashStateConfigureDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_configure_dispatch_step).trans
      (PyashCoreReducesStar.single pyashGF_configure_run_step)

/-- One-step closure: configure running state reaches focused done state. -/
theorem pyashGF_configure_running_closure_bridge :
    PyashCoreReducesStar
      pyashStateConfigureRunning
      pyashStateConfigureDoneOk := by
  exact PyashCoreReducesStar.single pyashGF_configure_run_step

/-- `configure/def` derive step (decomposed bridge lemma). -/
theorem pyashGF_configure_def_derive_step :
    langReduces pyashCore pyashStateConfigureDefDerive pyashStateConfigureDefDispatched := by
  simpa using pyashCore_configure_def_derive_signature_step

/-- `configure/def` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_configure_def_dispatch_step :
    langReduces pyashCore pyashStateConfigureDefDispatched pyashStateConfigureDefDoneOk := by
  simpa using pyashCore_configure_def_dispatch_def_step

/-- Bridge claim (OSLF): GF configure/def clause reaches the PyashCore configure-def dispatch stage. -/
theorem pyashGF_configure_def_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFConfigureDefClause)
      pyashStateConfigureDefDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_configure_def_clause_maps] using pyashGF_configure_def_derive_step

/-- Decomposed `configure/def` one-step bridge package from GF-mapped input. -/
theorem pyashGF_configure_def_clause_step_decomposition :
    (pyashGFInputOf pyashGFConfigureDefClause = pyashStateConfigureDefDerive) ∧
      langReduces pyashCore pyashStateConfigureDefDerive pyashStateConfigureDefDispatched ∧
      langReduces pyashCore pyashStateConfigureDefDispatched pyashStateConfigureDefDoneOk := by
  constructor
  · unfold pyashGFInputOf
    simp [pyashGF_configure_def_clause_maps]
  constructor
  · exact pyashGF_configure_def_derive_step
  · exact pyashGF_configure_def_dispatch_step

/-- Multi-step closure bridge: GF `configure/def` reaches the focused done state. -/
theorem pyashGF_configure_def_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFConfigureDefClause)
      pyashStateConfigureDefDoneOk := by
  have hDerive :
      langReduces pyashCore
        (pyashGFInputOf pyashGFConfigureDefClause)
        pyashStateConfigureDefDispatched :=
    pyashGF_configure_def_clause_dispatch_bridge
  have hDispatch :
      langReduces pyashCore
        pyashStateConfigureDefDispatched
        pyashStateConfigureDefDoneOk :=
    pyashGF_configure_def_dispatch_step
  exact
    (PyashCoreReducesStar.single hDerive).trans
      (PyashCoreReducesStar.single hDispatch)

/-- `world` derive step (decomposed bridge lemma). -/
theorem pyashGF_world_derive_step :
    langReduces pyashCore pyashStateWorldDerive pyashStateWorldDispatched := by
  simpa using pyashCore_world_derive_signature_step

/-- `world` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_world_dispatch_step :
    langReduces pyashCore pyashStateWorldDispatched pyashStateWorldRunning := by
  simpa using pyashCore_world_dispatch_do_step

/-- `world` run step (decomposed bridge lemma). -/
theorem pyashGF_world_run_step :
    langReduces pyashCore pyashStateWorldRunning pyashStateWorldDoneOk := by
  simpa using pyashCore_world_run_do_step

/-- `pipeline` derive step (decomposed bridge lemma). -/
theorem pyashGF_pipeline_derive_step :
    langReduces pyashCore pyashStatePipelineDerive pyashStatePipelineDispatched := by
  simpa using pyashCore_pipeline_derive_signature_step

/-- `pipeline` dispatch step (decomposed bridge lemma). -/
theorem pyashGF_pipeline_dispatch_step :
    langReduces pyashCore pyashStatePipelineDispatched pyashStatePipelineRunning := by
  simpa using pyashCore_pipeline_dispatch_do_step

/-- `pipeline` run step (decomposed bridge lemma). -/
theorem pyashGF_pipeline_run_step :
    langReduces pyashCore pyashStatePipelineRunning pyashStatePipelineDoneOk := by
  simpa using pyashCore_pipeline_run_do_step

/-- GF world/do bridge claim using decomposed derive step. -/
theorem pyashGF_world_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFWorldDoClause)
      pyashStateWorldDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_world_clause_maps] using pyashGF_world_derive_step

/-- GF pipeline/do bridge claim using decomposed derive step. -/
theorem pyashGF_pipeline_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFPipelineDoClause)
      pyashStatePipelineDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_pipeline_clause_maps] using pyashGF_pipeline_derive_step

/-- GF world/path-io bridge claim using decomposed derive step. -/
theorem pyashGF_world_path_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFWorldPathDoClause)
      pyashStateWorldDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_world_path_clause_maps] using pyashGF_world_derive_step

/-- GF pipeline/chirp bridge claim using decomposed derive step. -/
theorem pyashGF_pipeline_chirp_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFPipelineChirpDoClause)
      pyashStatePipelineDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_pipeline_chirp_clause_maps] using pyashGF_pipeline_derive_step

/-- GF pipeline/re-entry bridge claim using decomposed derive step. -/
theorem pyashGF_pipeline_reentry_clause_dispatch_bridge :
    langReduces pyashCore
      (pyashGFInputOf pyashGFPipelineReentryDoClause)
      pyashStatePipelineDispatched := by
  unfold pyashGFInputOf
  simpa [pyashGF_pipeline_reentry_clause_maps] using pyashGF_pipeline_derive_step

/-- Decomposed `world` one-step bridge package from GF-mapped input. -/
theorem pyashGF_world_clause_step_decomposition :
    (pyashGFInputOf pyashGFWorldDoClause = pyashStateWorldDerive) ∧
      langReduces pyashCore pyashStateWorldDerive pyashStateWorldDispatched ∧
      langReduces pyashCore pyashStateWorldDispatched pyashStateWorldRunning ∧
      langReduces pyashCore pyashStateWorldRunning pyashStateWorldDoneOk := by
  constructor
  · unfold pyashGFInputOf
    simp [pyashGF_world_clause_maps]
  constructor
  · exact pyashGF_world_derive_step
  constructor
  · exact pyashGF_world_dispatch_step
  · exact pyashGF_world_run_step

/-- Multi-step closure bridge: GF `world/do` reaches the focused done state. -/
theorem pyashGF_world_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFWorldDoClause)
      pyashStateWorldDoneOk := by
  have hDerive :
      langReduces pyashCore
        (pyashGFInputOf pyashGFWorldDoClause)
        pyashStateWorldDispatched :=
    pyashGF_world_clause_dispatch_bridge
  have hDispatch :
      langReduces pyashCore
        pyashStateWorldDispatched
        pyashStateWorldRunning :=
    pyashGF_world_dispatch_step
  have hRun :
      langReduces pyashCore
        pyashStateWorldRunning
        pyashStateWorldDoneOk :=
    pyashGF_world_run_step
  exact
    (PyashCoreReducesStar.single hDerive).trans
      ((PyashCoreReducesStar.single hDispatch).trans
        (PyashCoreReducesStar.single hRun))

/-- Multi-step closure: world dispatched state reaches focused done state. -/
theorem pyashGF_world_dispatched_closure_bridge :
    PyashCoreReducesStar
      pyashStateWorldDispatched
      pyashStateWorldDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_world_dispatch_step).trans
      (PyashCoreReducesStar.single pyashGF_world_run_step)

/-- One-step closure: world running state reaches focused done state. -/
theorem pyashGF_world_running_closure_bridge :
    PyashCoreReducesStar
      pyashStateWorldRunning
      pyashStateWorldDoneOk := by
  exact PyashCoreReducesStar.single pyashGF_world_run_step

/-- Decomposed `pipeline` one-step bridge package from GF-mapped input. -/
theorem pyashGF_pipeline_clause_step_decomposition :
    (pyashGFInputOf pyashGFPipelineDoClause = pyashStatePipelineDerive) ∧
      langReduces pyashCore pyashStatePipelineDerive pyashStatePipelineDispatched ∧
      langReduces pyashCore pyashStatePipelineDispatched pyashStatePipelineRunning ∧
      langReduces pyashCore pyashStatePipelineRunning pyashStatePipelineDoneOk := by
  constructor
  · unfold pyashGFInputOf
    simp [pyashGF_pipeline_clause_maps]
  constructor
  · exact pyashGF_pipeline_derive_step
  constructor
  · exact pyashGF_pipeline_dispatch_step
  · exact pyashGF_pipeline_run_step

/-- Multi-step closure bridge: GF `pipeline/do` reaches the focused done state. -/
theorem pyashGF_pipeline_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFPipelineDoClause)
      pyashStatePipelineDoneOk := by
  have hDerive :
      langReduces pyashCore
        (pyashGFInputOf pyashGFPipelineDoClause)
        pyashStatePipelineDispatched :=
    pyashGF_pipeline_clause_dispatch_bridge
  have hDispatch :
      langReduces pyashCore
        pyashStatePipelineDispatched
        pyashStatePipelineRunning :=
    pyashGF_pipeline_dispatch_step
  have hRun :
      langReduces pyashCore
        pyashStatePipelineRunning
        pyashStatePipelineDoneOk :=
    pyashGF_pipeline_run_step
  exact
    (PyashCoreReducesStar.single hDerive).trans
      ((PyashCoreReducesStar.single hDispatch).trans
        (PyashCoreReducesStar.single hRun))

/-- Multi-step closure bridge: GF `world/path-io` reaches focused done state. -/
theorem pyashGF_world_path_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFWorldPathDoClause)
      pyashStateWorldDoneOk := by
  have hDerive :
      langReduces pyashCore
        (pyashGFInputOf pyashGFWorldPathDoClause)
        pyashStateWorldDispatched :=
    pyashGF_world_path_clause_dispatch_bridge
  have hDispatch :
      langReduces pyashCore
        pyashStateWorldDispatched
        pyashStateWorldRunning :=
    pyashGF_world_dispatch_step
  have hRun :
      langReduces pyashCore
        pyashStateWorldRunning
        pyashStateWorldDoneOk :=
    pyashGF_world_run_step
  exact
    (PyashCoreReducesStar.single hDerive).trans
      ((PyashCoreReducesStar.single hDispatch).trans
        (PyashCoreReducesStar.single hRun))

/-- Multi-step closure bridge: GF `pipeline/chirp` reaches focused done state. -/
theorem pyashGF_pipeline_chirp_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFPipelineChirpDoClause)
      pyashStatePipelineDoneOk := by
  have hDerive :
      langReduces pyashCore
        (pyashGFInputOf pyashGFPipelineChirpDoClause)
        pyashStatePipelineDispatched :=
    pyashGF_pipeline_chirp_clause_dispatch_bridge
  have hDispatch :
      langReduces pyashCore
        pyashStatePipelineDispatched
        pyashStatePipelineRunning :=
    pyashGF_pipeline_dispatch_step
  have hRun :
      langReduces pyashCore
        pyashStatePipelineRunning
        pyashStatePipelineDoneOk :=
    pyashGF_pipeline_run_step
  exact
    (PyashCoreReducesStar.single hDerive).trans
      ((PyashCoreReducesStar.single hDispatch).trans
        (PyashCoreReducesStar.single hRun))

/-- Multi-step closure bridge: GF `pipeline/re-entry` reaches focused done state. -/
theorem pyashGF_pipeline_reentry_clause_closure_bridge :
    PyashCoreReducesStar
      (pyashGFInputOf pyashGFPipelineReentryDoClause)
      pyashStatePipelineDoneOk := by
  have hDerive :
      langReduces pyashCore
        (pyashGFInputOf pyashGFPipelineReentryDoClause)
        pyashStatePipelineDispatched :=
    pyashGF_pipeline_reentry_clause_dispatch_bridge
  have hDispatch :
      langReduces pyashCore
        pyashStatePipelineDispatched
        pyashStatePipelineRunning :=
    pyashGF_pipeline_dispatch_step
  have hRun :
      langReduces pyashCore
        pyashStatePipelineRunning
        pyashStatePipelineDoneOk :=
    pyashGF_pipeline_run_step
  exact
    (PyashCoreReducesStar.single hDerive).trans
      ((PyashCoreReducesStar.single hDispatch).trans
        (PyashCoreReducesStar.single hRun))

/-- Multi-step closure: pipeline dispatched state reaches focused done state. -/
theorem pyashGF_pipeline_dispatched_closure_bridge :
    PyashCoreReducesStar
      pyashStatePipelineDispatched
      pyashStatePipelineDoneOk := by
  exact
    (PyashCoreReducesStar.single pyashGF_pipeline_dispatch_step).trans
      (PyashCoreReducesStar.single pyashGF_pipeline_run_step)

/-- One-step closure: pipeline running state reaches focused done state. -/
theorem pyashGF_pipeline_running_closure_bridge :
    PyashCoreReducesStar
      pyashStatePipelineRunning
      pyashStatePipelineDoneOk := by
  exact PyashCoreReducesStar.single pyashGF_pipeline_run_step

/-- Native-type bridge: GF read/do bridge output inhabits a native state type. -/
def pyashGFReadInputNativeType : langNativeType pyashCore "State" where
  sort := "State"
  pred := fun p => p = pyashStateReadDerive

theorem pyashGF_read_clause_native_bridge :
    pyashGFReadInputNativeType.pred (pyashGFInputOf pyashGFReadDoClause) := by
  unfold pyashGFReadInputNativeType pyashGFInputOf
  simp [pyashGF_read_clause_maps]

/-- OSLF modal corollary: the GF read/do bridge has the expected one-step witness. -/
theorem pyashGF_read_clause_diamond_bridge :
    langDiamond pyashCore (fun q => q = pyashStateReadDispatched)
      (pyashGFInputOf pyashGFReadDoClause) := by
  rw [langDiamond_spec]
  exact ⟨pyashStateReadDispatched, pyashGF_read_clause_dispatch_bridge, rfl⟩

/-- Constructor-grounded GF canary patterns (single source of truth = Lean `Pattern` states). -/
def pyashGFCanaryCasePatterns : List (String × Pattern × Pattern) :=
  [ ("pyash_gf_read_do", pyashStateReadDerive, pyashStateReadDoneOk)
  , ("pyash_gf_write_do", pyashStateWriteDerive, pyashStateWriteDoneOk)
  , ("pyash_gf_say_do", pyashStateSayDerive, pyashStateSayDoneOk)
  , ("pyash_gf_map_do", pyashStateMapDerive, pyashStateMapDoneOk)
  , ("pyash_gf_map_def", pyashStateMapDefDerive, pyashStateMapDefDoneOk)
  , ("pyash_gf_command_do", pyashStateCommandDerive, pyashStateCommandDoneOk)
  , ("pyash_gf_search_do", pyashStateSearchDerive, pyashStateSearchDoneOk)
  , ("pyash_gf_mind_do", pyashStateMindDerive, pyashStateMindDoneOk)
  , ("pyash_gf_read_then_err_dispatch", pyashStateDispatchThenError, pyashStateDoneDispatchErr)
  , ("pyash_gf_configure_then_err_dispatch", pyashStateConfigureThenError, pyashStateConfigureThenDoneDispatchErr)
  , ("pyash_gf_world_then_err_dispatch", pyashStateWorldThenError, pyashStateWorldThenDoneDispatchErr)
  , ("pyash_gf_pipeline_then_err_dispatch", pyashStatePipelineThenError, pyashStatePipelineThenDoneDispatchErr)
  , ("pyash_gf_configure_then_err_terminal", pyashStateConfigureThenDoneDispatchErr, pyashStateConfigureThenDoneDispatchErr)
  , ("pyash_gf_world_then_err_terminal", pyashStateWorldThenDoneDispatchErr, pyashStateWorldThenDoneDispatchErr)
  , ("pyash_gf_pipeline_then_err_terminal", pyashStatePipelineThenDoneDispatchErr, pyashStatePipelineThenDoneDispatchErr)
  , ("pyash_gf_dispatch_error_instr", pyashStateDispatchErrorInstr, pyashStateDoneDispatchErr)
  , ("pyash_gf_chip_do", pyashStateChipDerive, pyashStateChipDoneOk)
  , ("pyash_gf_hear_do", pyashStateHearDerive, pyashStateHearDoneOk)
  , ("pyash_gf_configure_do", pyashStateConfigureDerive, pyashStateConfigureDoneOk)
  , ("pyash_gf_configure_def", pyashStateConfigureDefDerive, pyashStateConfigureDefDoneOk)
  , ("pyash_gf_configure_dispatch_to_done", pyashStateConfigureDispatched, pyashStateConfigureDoneOk)
  , ("pyash_gf_configure_running_to_done", pyashStateConfigureRunning, pyashStateConfigureDoneOk)
  , ("pyash_gf_world_do", pyashStateWorldDerive, pyashStateWorldDoneOk)
  , ("pyash_gf_world_path_io_do", pyashStateWorldDerive, pyashStateWorldDoneOk)
  , ("pyash_gf_world_dispatch_to_done", pyashStateWorldDispatched, pyashStateWorldDoneOk)
  , ("pyash_gf_world_running_to_done", pyashStateWorldRunning, pyashStateWorldDoneOk)
  , ("pyash_gf_pipeline_do", pyashStatePipelineDerive, pyashStatePipelineDoneOk)
  , ("pyash_gf_pipeline_chirp_do", pyashStatePipelineDerive, pyashStatePipelineDoneOk)
  , ("pyash_gf_pipeline_reentry_do", pyashStatePipelineDerive, pyashStatePipelineDoneOk)
  , ("pyash_gf_pipeline_dispatch_to_done", pyashStatePipelineDispatched, pyashStatePipelineDoneOk)
  , ("pyash_gf_pipeline_running_to_done", pyashStatePipelineRunning, pyashStatePipelineDoneOk)
  , ("pyash_gf_compile_do", pyashStateCompileDerive, pyashStateCompileDoneOk)
  , ("pyash_gf_import_do", pyashStateImportDerive, pyashStateImportDoneOk)
  , ("pyash_gf_download_do", pyashStateDownloadDerive, pyashStateDownloadDoneOk)
  , ("pyash_gf_translation_do", pyashStateTranslationDerive, pyashStateTranslationDoneOk)
  ]

/-- Executable GF canary bundle for Lean->Rust artifact flow. -/
def pyashGFCanaryCases : List (String × String × String) :=
  pyashGFCanaryCasePatterns.map (fun caseTriple =>
    let label := caseTriple.1
    let input := caseTriple.2.1
    let expected := caseTriple.2.2
    (label, renderPyashCtorPattern input, renderPyashCtorPattern expected))

def renderPyashGFCanaryBundle : String :=
  String.intercalate "\n" <|
    pyashGFCanaryCases.map (fun caseTriple =>
      let label := caseTriple.1
      let input := caseTriple.2.1
      let expected := caseTriple.2.2
      label ++ "|||" ++ input ++ "|||" ++ expected)

/-- Backwards-compatible first canary line (read/do). -/
def pyashGFCanaryCaseLine : String :=
  match pyashGFCanaryCases with
  | [] => ""
  | caseTriple :: _ =>
      let label := caseTriple.1
      let input := caseTriple.2.1
      let expected := caseTriple.2.2
      label ++ "|||" ++ input ++ "|||" ++ expected

end Mettapedia.OSLF.Framework.PyashGF
