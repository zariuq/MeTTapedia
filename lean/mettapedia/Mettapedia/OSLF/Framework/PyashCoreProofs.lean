import Mettapedia.OSLF.Framework.PyashCoreModel
import Mettapedia.OSLF.Framework.GovernanceInstance

namespace Mettapedia.OSLF.Framework.PyashCoreInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Consolidated executable step corpus used by PyashCore proof extraction. -/
def pyashCoreReductionCases : List (String × Pattern × Pattern) :=
  [ ("subj_alias_normalizes",
      (.apply "RoleType" [.apply "SubjAlias" [], .apply "TNum" []]),
      (.apply "RoleType" [.apply "Su" [], .apply "TNum" []]))
  , ("derive_signature_step", pyashStateDeriveSignature, pyashStateDispatched)
  , ("dispatch_do_step", pyashStateDispatched, pyashStateRunning)
  , ("run_do_step", pyashStateRunning, pyashStateDoneOk)
  , ("read_derive_signature_step", pyashStateReadDerive, pyashStateReadDispatched)
  , ("read_dispatch_do_step", pyashStateReadDispatched, pyashStateReadRunning)
  , ("read_run_do_step", pyashStateReadRunning, pyashStateReadDoneOk)
  , ("write_derive_signature_step", pyashStateWriteDerive, pyashStateWriteDispatched)
  , ("write_dispatch_do_step", pyashStateWriteDispatched, pyashStateWriteRunning)
  , ("write_run_do_step", pyashStateWriteRunning, pyashStateWriteDoneOk)
  , ("say_derive_signature_step", pyashStateSayDerive, pyashStateSayDispatched)
  , ("say_dispatch_do_step", pyashStateSayDispatched, pyashStateSayRunning)
  , ("say_run_do_step", pyashStateSayRunning, pyashStateSayDoneOk)
  , ("map_derive_signature_step", pyashStateMapDerive, pyashStateMapDispatched)
  , ("map_dispatch_do_step", pyashStateMapDispatched, pyashStateMapRunning)
  , ("map_run_do_step", pyashStateMapRunning, pyashStateMapDoneOk)
  , ("map_def_derive_signature_step", pyashStateMapDefDerive, pyashStateMapDefDispatched)
  , ("map_def_dispatch_def_step", pyashStateMapDefDispatched, pyashStateMapDefDoneOk)
  , ("command_derive_signature_step", pyashStateCommandDerive, pyashStateCommandDispatched)
  , ("command_dispatch_do_step", pyashStateCommandDispatched, pyashStateCommandRunning)
  , ("command_run_do_step", pyashStateCommandRunning, pyashStateCommandDoneOk)
  , ("search_derive_signature_step", pyashStateSearchDerive, pyashStateSearchDispatched)
  , ("search_dispatch_do_step", pyashStateSearchDispatched, pyashStateSearchRunning)
  , ("search_run_do_step", pyashStateSearchRunning, pyashStateSearchDoneOk)
  , ("list_derive_signature_step", pyashStateListDerive, pyashStateListDispatched)
  , ("list_dispatch_do_step", pyashStateListDispatched, pyashStateListRunning)
  , ("list_run_do_step", pyashStateListRunning, pyashStateListDoneOk)
  , ("input_derive_signature_step", pyashStateInputDerive, pyashStateInputDispatched)
  , ("input_dispatch_do_step", pyashStateInputDispatched, pyashStateInputRunning)
  , ("input_run_do_step", pyashStateInputRunning, pyashStateInputDoneOk)
  , ("stream_derive_signature_step", pyashStateStreamDerive, pyashStateStreamDispatched)
  , ("stream_dispatch_do_step", pyashStateStreamDispatched, pyashStateStreamRunning)
  , ("stream_run_do_step", pyashStateStreamRunning, pyashStateStreamDoneOk)
  , ("mind_derive_signature_step", pyashStateMindDerive, pyashStateMindDispatched)
  , ("mind_dispatch_do_step", pyashStateMindDispatched, pyashStateMindRunning)
  , ("mind_run_do_step", pyashStateMindRunning, pyashStateMindDoneOk)
  , ("ceremony_derive_signature_step", pyashStateCeremonyDerive, pyashStateCeremonyDispatched)
  , ("ceremony_dispatch_do_step", pyashStateCeremonyDispatched, pyashStateCeremonyRunning)
  , ("ceremony_run_do_step", pyashStateCeremonyRunning, pyashStateCeremonyDoneOk)
  , ("chip_derive_signature_step", pyashStateChipDerive, pyashStateChipDispatched)
  , ("chip_dispatch_do_step", pyashStateChipDispatched, pyashStateChipRunning)
  , ("chip_run_do_step", pyashStateChipRunning, pyashStateChipDoneOk)
  , ("chip_series_derive_signature_step", pyashStateChipSeriesDerive, pyashStateChipSeriesDispatched)
  , ("chip_series_dispatch_do_step", pyashStateChipSeriesDispatched, pyashStateChipSeriesRunning)
  , ("chip_series_run_do_step", pyashStateChipSeriesRunning, pyashStateChipSeriesDoneOk)
  , ("chip_bounded_derive_signature_step", pyashStateChipBoundedDerive, pyashStateChipBoundedDispatched)
  , ("chip_bounded_dispatch_do_step", pyashStateChipBoundedDispatched, pyashStateChipBoundedRunning)
  , ("chip_bounded_run_do_step", pyashStateChipBoundedRunning, pyashStateChipBoundedDoneOk)
  , ("hear_derive_signature_step", pyashStateHearDerive, pyashStateHearDispatched)
  , ("hear_dispatch_do_step", pyashStateHearDispatched, pyashStateHearRunning)
  , ("hear_run_do_step", pyashStateHearRunning, pyashStateHearDoneOk)
  , ("hear_mic_derive_signature_step", pyashStateHearMicRecordDerive, pyashStateHearMicRecordDispatched)
  , ("hear_mic_dispatch_do_step", pyashStateHearMicRecordDispatched, pyashStateHearMicRecordRunning)
  , ("hear_mic_run_do_step", pyashStateHearMicRecordRunning, pyashStateHearMicRecordDoneOk)
  , ("hear_srt_derive_signature_step", pyashStateHearFileSrtDerive, pyashStateHearFileSrtDispatched)
  , ("hear_srt_dispatch_do_step", pyashStateHearFileSrtDispatched, pyashStateHearFileSrtRunning)
  , ("hear_srt_run_do_step", pyashStateHearFileSrtRunning, pyashStateHearFileSrtDoneOk)
  , ("configure_derive_signature_step", pyashStateConfigureDerive, pyashStateConfigureDispatched)
  , ("configure_dispatch_do_step", pyashStateConfigureDispatched, pyashStateConfigureRunning)
  , ("configure_run_do_step", pyashStateConfigureRunning, pyashStateConfigureDoneOk)
  , ("configure_def_derive_signature_step", pyashStateConfigureDefDerive, pyashStateConfigureDefDispatched)
  , ("configure_def_dispatch_def_step", pyashStateConfigureDefDispatched, pyashStateConfigureDefDoneOk)
  , ("configure_command_map_def_derive_signature_step",
      pyashStateConfigureCommandMapDefDerive, pyashStateConfigureCommandMapDefDispatched)
  , ("configure_command_map_def_dispatch_def_step",
      pyashStateConfigureCommandMapDefDispatched, pyashStateConfigureCommandMapDefDoneOk)
  , ("configure_sandbox_map_def_derive_signature_step",
      pyashStateConfigureSandboxMapDefDerive, pyashStateConfigureSandboxMapDefDispatched)
  , ("configure_sandbox_map_def_dispatch_def_step",
      pyashStateConfigureSandboxMapDefDispatched, pyashStateConfigureSandboxMapDefDoneOk)
  , ("configure_verify_loop_map_def_derive_signature_step",
      pyashStateConfigureVerifyLoopMapDefDerive, pyashStateConfigureVerifyLoopMapDefDispatched)
  , ("configure_verify_loop_map_def_dispatch_def_step",
      pyashStateConfigureVerifyLoopMapDefDispatched, pyashStateConfigureVerifyLoopMapDefDoneOk)
  , ("world_derive_signature_step", pyashStateWorldDerive, pyashStateWorldDispatched)
  , ("world_dispatch_do_step", pyashStateWorldDispatched, pyashStateWorldRunning)
  , ("world_run_do_step", pyashStateWorldRunning, pyashStateWorldDoneOk)
  , ("world_path_io_derive_signature_step", pyashStateWorldPathIODerive, pyashStateWorldPathIODispatched)
  , ("world_path_io_dispatch_do_step", pyashStateWorldPathIODispatched, pyashStateWorldPathIORunning)
  , ("world_path_io_run_do_step", pyashStateWorldPathIORunning, pyashStateWorldPathIODoneOk)
  , ("pipeline_derive_signature_step", pyashStatePipelineDerive, pyashStatePipelineDispatched)
  , ("pipeline_dispatch_do_step", pyashStatePipelineDispatched, pyashStatePipelineRunning)
  , ("pipeline_run_do_step", pyashStatePipelineRunning, pyashStatePipelineDoneOk)
  , ("pipeline_refinery_derive_signature_step",
      pyashStatePipelineRefineryDerive, pyashStatePipelineRefineryDispatched)
  , ("pipeline_refinery_dispatch_do_step",
      pyashStatePipelineRefineryDispatched, pyashStatePipelineRefineryRunning)
  , ("pipeline_refinery_run_do_step",
      pyashStatePipelineRefineryRunning, pyashStatePipelineRefineryDoneOk)
  , ("pipeline_chirp_derive_signature_step", pyashStatePipelineChirpDerive, pyashStatePipelineChirpDispatched)
  , ("pipeline_chirp_dispatch_do_step", pyashStatePipelineChirpDispatched, pyashStatePipelineChirpRunning)
  , ("pipeline_chirp_run_do_step", pyashStatePipelineChirpRunning, pyashStatePipelineChirpDoneOk)
  , ("pipeline_reentry_derive_signature_step", pyashStatePipelineReentryDerive, pyashStatePipelineReentryDispatched)
  , ("pipeline_reentry_dispatch_do_step", pyashStatePipelineReentryDispatched, pyashStatePipelineReentryRunning)
  , ("pipeline_reentry_run_do_step", pyashStatePipelineReentryRunning, pyashStatePipelineReentryDoneOk)
  , ("compile_derive_signature_step", pyashStateCompileDerive, pyashStateCompileDispatched)
  , ("compile_dispatch_do_step", pyashStateCompileDispatched, pyashStateCompileRunning)
  , ("compile_run_do_step", pyashStateCompileRunning, pyashStateCompileDoneOk)
  , ("import_derive_signature_step", pyashStateImportDerive, pyashStateImportDispatched)
  , ("import_dispatch_do_step", pyashStateImportDispatched, pyashStateImportRunning)
  , ("import_run_do_step", pyashStateImportRunning, pyashStateImportDoneOk)
  , ("download_derive_signature_step", pyashStateDownloadDerive, pyashStateDownloadDispatched)
  , ("download_dispatch_do_step", pyashStateDownloadDispatched, pyashStateDownloadRunning)
  , ("download_run_do_step", pyashStateDownloadRunning, pyashStateDownloadDoneOk)
  , ("translation_derive_signature_step", pyashStateTranslationDerive, pyashStateTranslationDispatched)
  , ("translation_dispatch_do_step", pyashStateTranslationDispatched, pyashStateTranslationRunning)
  , ("translation_run_do_step", pyashStateTranslationRunning, pyashStateTranslationDoneOk)
  , ("ret_read_derive_signature_step", pyashStateRetReadDerive, pyashStateRetReadDispatched)
  , ("ret_read_dispatch_ret_step", pyashStateRetReadDispatched, pyashStateRetReadDoneOk)
  , ("configure_command_map_def_signature_mismatch_surfaces_error",
      pyashStateConfigureCommandMapDefMismatch, pyashStateConfigureCommandMapDefDoneSignatureErr)
  , ("configure_sandbox_map_def_signature_mismatch_surfaces_error",
      pyashStateConfigureSandboxMapDefMismatch, pyashStateConfigureSandboxMapDefDoneSignatureErr)
  , ("configure_verify_loop_map_def_signature_mismatch_surfaces_error",
      pyashStateConfigureVerifyLoopMapDefMismatch, pyashStateConfigureVerifyLoopMapDefDoneSignatureErr)
  , ("world_path_io_signature_mismatch_surfaces_error",
      pyashStateWorldPathIOMismatch, pyashStateWorldPathIODoneSignatureErr)
  , ("pipeline_refinery_signature_mismatch_surfaces_error",
      pyashStatePipelineRefineryMismatch, pyashStatePipelineRefineryDoneSignatureErr)
  , ("pipeline_chirp_signature_mismatch_surfaces_error",
      pyashStatePipelineChirpMismatch, pyashStatePipelineChirpDoneSignatureErr)
  , ("pipeline_reentry_signature_mismatch_surfaces_error",
      pyashStatePipelineReentryMismatch, pyashStatePipelineReentryDoneSignatureErr)
  , ("list_signature_mismatch_surfaces_error",
      pyashStateListMismatch, pyashStateListDoneSignatureErr)
  , ("input_signature_mismatch_surfaces_error",
      pyashStateInputMismatch, pyashStateInputDoneSignatureErr)
  , ("stream_signature_mismatch_surfaces_error",
      pyashStateStreamMismatch, pyashStateStreamDoneSignatureErr)
  , ("compile_signature_mismatch_surfaces_error",
      pyashStateCompileMismatch, pyashStateCompileDoneSignatureErr)
  , ("import_signature_mismatch_surfaces_error",
      pyashStateImportMismatch, pyashStateImportDoneSignatureErr)
  , ("download_signature_mismatch_surfaces_error",
      pyashStateDownloadMismatch, pyashStateDownloadDoneSignatureErr)
  , ("translation_signature_mismatch_surfaces_error",
      pyashStateTranslationMismatch, pyashStateTranslationDoneSignatureErr)
  , ("dispatch_error_instr_surfaces_dispatch_error", pyashStateDispatchErrorInstr, pyashStateDoneDispatchErr)
  , ("dispatch_then_surfaces_dispatch_error", pyashStateDispatchThenError, pyashStateDoneDispatchErr)
  , ("malformed_signature_shape_surfaces_error",
      pyashStateMalformedSignatureShape, pyashStateDoneMalformedSignatureErr)
  , ("signature_mismatch_surfaces_error", pyashStateMismatch, pyashStateDoneSignatureErr)
  ]

/--
Kernel-checked batch certificate for the consolidated PyashCore executable step corpus.
This replaces repeated per-theorem `decide +kernel` invocations.
-/
theorem pyashCore_reduction_cases_cover :
    List.Forall
      (fun case =>
        case.2.2 ∈ rewriteWithContextWithPremisesUsing RelationEnv.empty pyashCore case.2.1)
      pyashCoreReductionCases := by
  decide +kernel

/-- Extract a concrete executable reduction witness from the batch certificate. -/
theorem pyashCore_reduction_case_exec
    {label : String} {p q : Pattern}
    (hmem : (label, p, q) ∈ pyashCoreReductionCases) :
    langReducesExecUsing RelationEnv.empty pyashCore p q := by
  have hmemExec :
      q ∈ rewriteWithContextWithPremisesUsing RelationEnv.empty pyashCore p :=
    (List.forall_iff_forall_mem.mp pyashCore_reduction_cases_cover) _ hmem
  simpa [langReducesExecUsing] using hmemExec

/-- Extract a concrete `langReduces` step from the batch certificate via list membership. -/
theorem pyashCore_reduction_case
    {label : String} {p q : Pattern}
    (hmem : (label, p, q) ∈ pyashCoreReductionCases) :
    langReduces pyashCore p q := by
  exact exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := pyashCore)
    (p := p) (q := q) (pyashCore_reduction_case_exec hmem)

theorem pyashCore_subj_alias_normalizes :
    langReduces pyashCore
      (.apply "RoleType" [.apply "SubjAlias" [], .apply "TNum" []])
      (.apply "RoleType" [.apply "Su" [], .apply "TNum" []]) := by
  exact pyashCore_reduction_case
    (label := "subj_alias_normalizes")
    (p := (.apply "RoleType" [.apply "SubjAlias" [], .apply "TNum" []]))
    (q := (.apply "RoleType" [.apply "Su" [], .apply "TNum" []]))
    (by simp [pyashCoreReductionCases])

/-- Signature derivation step for a representative `do` sentence. -/
theorem pyashCore_derive_signature_step :
    langReduces pyashCore pyashStateDeriveSignature pyashStateDispatched := by
  exact pyashCore_reduction_case
    (label := "derive_signature_step")
    (p := pyashStateDeriveSignature)
    (q := pyashStateDispatched)
    (by simp [pyashCoreReductionCases])

/-- Dispatching `do` enters run mode. -/
theorem pyashCore_dispatch_do_step :
    langReduces pyashCore pyashStateDispatched pyashStateRunning := by
  exact pyashCore_reduction_case
    (label := "dispatch_do_step")
    (p := pyashStateDispatched)
    (q := pyashStateRunning)
    (by simp [pyashCoreReductionCases])

/-- Running `do` produces a `ya` sentence and reaches `Done`. -/
theorem pyashCore_run_do_step :
    langReduces pyashCore pyashStateRunning pyashStateDoneOk := by
  exact pyashCore_reduction_case
    (label := "run_do_step")
    (p := pyashStateRunning)
    (q := pyashStateDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `read` signature derivation step is executable. -/
theorem pyashCore_read_derive_signature_step :
    langReduces pyashCore pyashStateReadDerive pyashStateReadDispatched := by
  exact pyashCore_reduction_case
    (label := "read_derive_signature_step")
    (p := pyashStateReadDerive)
    (q := pyashStateReadDispatched)
    (by simp [pyashCoreReductionCases])

/-- `read` dispatch path enters run mode. -/
theorem pyashCore_read_dispatch_do_step :
    langReduces pyashCore pyashStateReadDispatched pyashStateReadRunning := by
  exact pyashCore_reduction_case
    (label := "read_dispatch_do_step")
    (p := pyashStateReadDispatched)
    (q := pyashStateReadRunning)
    (by simp [pyashCoreReductionCases])

/-- `read` run path produces a `ya` done state. -/
theorem pyashCore_read_run_do_step :
    langReduces pyashCore pyashStateReadRunning pyashStateReadDoneOk := by
  exact pyashCore_reduction_case
    (label := "read_run_do_step")
    (p := pyashStateReadRunning)
    (q := pyashStateReadDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `write` signature derivation step is executable. -/
theorem pyashCore_write_derive_signature_step :
    langReduces pyashCore pyashStateWriteDerive pyashStateWriteDispatched := by
  exact pyashCore_reduction_case
    (label := "write_derive_signature_step")
    (p := pyashStateWriteDerive)
    (q := pyashStateWriteDispatched)
    (by simp [pyashCoreReductionCases])

/-- `write` dispatch path enters run mode. -/
theorem pyashCore_write_dispatch_do_step :
    langReduces pyashCore pyashStateWriteDispatched pyashStateWriteRunning := by
  exact pyashCore_reduction_case
    (label := "write_dispatch_do_step")
    (p := pyashStateWriteDispatched)
    (q := pyashStateWriteRunning)
    (by simp [pyashCoreReductionCases])

/-- `write` run path produces a `ya` done state. -/
theorem pyashCore_write_run_do_step :
    langReduces pyashCore pyashStateWriteRunning pyashStateWriteDoneOk := by
  exact pyashCore_reduction_case
    (label := "write_run_do_step")
    (p := pyashStateWriteRunning)
    (q := pyashStateWriteDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `say` signature derivation step is executable. -/
theorem pyashCore_say_derive_signature_step :
    langReduces pyashCore pyashStateSayDerive pyashStateSayDispatched := by
  exact pyashCore_reduction_case
    (label := "say_derive_signature_step")
    (p := pyashStateSayDerive)
    (q := pyashStateSayDispatched)
    (by simp [pyashCoreReductionCases])

/-- `say` dispatch path enters run mode. -/
theorem pyashCore_say_dispatch_do_step :
    langReduces pyashCore pyashStateSayDispatched pyashStateSayRunning := by
  exact pyashCore_reduction_case
    (label := "say_dispatch_do_step")
    (p := pyashStateSayDispatched)
    (q := pyashStateSayRunning)
    (by simp [pyashCoreReductionCases])

/-- `say` run path produces a `ya` done state. -/
theorem pyashCore_say_run_do_step :
    langReduces pyashCore pyashStateSayRunning pyashStateSayDoneOk := by
  exact pyashCore_reduction_case
    (label := "say_run_do_step")
    (p := pyashStateSayRunning)
    (q := pyashStateSayDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `map` signature derivation step is executable. -/
theorem pyashCore_map_derive_signature_step :
    langReduces pyashCore pyashStateMapDerive pyashStateMapDispatched := by
  exact pyashCore_reduction_case
    (label := "map_derive_signature_step")
    (p := pyashStateMapDerive)
    (q := pyashStateMapDispatched)
    (by simp [pyashCoreReductionCases])

/-- `map` dispatch path enters run mode. -/
theorem pyashCore_map_dispatch_do_step :
    langReduces pyashCore pyashStateMapDispatched pyashStateMapRunning := by
  exact pyashCore_reduction_case
    (label := "map_dispatch_do_step")
    (p := pyashStateMapDispatched)
    (q := pyashStateMapRunning)
    (by simp [pyashCoreReductionCases])

/-- `map` run path produces a `ya` done state. -/
theorem pyashCore_map_run_do_step :
    langReduces pyashCore pyashStateMapRunning pyashStateMapDoneOk := by
  exact pyashCore_reduction_case
    (label := "map_run_do_step")
    (p := pyashStateMapRunning)
    (q := pyashStateMapDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `map` (`def` mood) signature derivation step is executable. -/
theorem pyashCore_map_def_derive_signature_step :
    langReduces pyashCore pyashStateMapDefDerive pyashStateMapDefDispatched := by
  exact pyashCore_reduction_case
    (label := "map_def_derive_signature_step")
    (p := pyashStateMapDefDerive)
    (q := pyashStateMapDefDispatched)
    (by simp [pyashCoreReductionCases])

/-- `map` (`def` mood) dispatch path reaches terminal `Done`. -/
theorem pyashCore_map_def_dispatch_def_step :
    langReduces pyashCore pyashStateMapDefDispatched pyashStateMapDefDoneOk := by
  exact pyashCore_reduction_case
    (label := "map_def_dispatch_def_step")
    (p := pyashStateMapDefDispatched)
    (q := pyashStateMapDefDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `command` signature derivation step is executable. -/
theorem pyashCore_command_derive_signature_step :
    langReduces pyashCore pyashStateCommandDerive pyashStateCommandDispatched := by
  exact pyashCore_reduction_case
    (label := "command_derive_signature_step")
    (p := pyashStateCommandDerive)
    (q := pyashStateCommandDispatched)
    (by simp [pyashCoreReductionCases])

/-- `command` dispatch path enters run mode. -/
theorem pyashCore_command_dispatch_do_step :
    langReduces pyashCore pyashStateCommandDispatched pyashStateCommandRunning := by
  exact pyashCore_reduction_case
    (label := "command_dispatch_do_step")
    (p := pyashStateCommandDispatched)
    (q := pyashStateCommandRunning)
    (by simp [pyashCoreReductionCases])

/-- `command` run path produces a `ya` done state. -/
theorem pyashCore_command_run_do_step :
    langReduces pyashCore pyashStateCommandRunning pyashStateCommandDoneOk := by
  exact pyashCore_reduction_case
    (label := "command_run_do_step")
    (p := pyashStateCommandRunning)
    (q := pyashStateCommandDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `search` signature derivation step is executable. -/
theorem pyashCore_search_derive_signature_step :
    langReduces pyashCore pyashStateSearchDerive pyashStateSearchDispatched := by
  exact pyashCore_reduction_case
    (label := "search_derive_signature_step")
    (p := pyashStateSearchDerive)
    (q := pyashStateSearchDispatched)
    (by simp [pyashCoreReductionCases])

/-- `search` dispatch path enters run mode. -/
theorem pyashCore_search_dispatch_do_step :
    langReduces pyashCore pyashStateSearchDispatched pyashStateSearchRunning := by
  exact pyashCore_reduction_case
    (label := "search_dispatch_do_step")
    (p := pyashStateSearchDispatched)
    (q := pyashStateSearchRunning)
    (by simp [pyashCoreReductionCases])

/-- `search` run path produces a `ya` done state. -/
theorem pyashCore_search_run_do_step :
    langReduces pyashCore pyashStateSearchRunning pyashStateSearchDoneOk := by
  exact pyashCore_reduction_case
    (label := "search_run_do_step")
    (p := pyashStateSearchRunning)
    (q := pyashStateSearchDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `list` signature derivation step is executable. -/
theorem pyashCore_list_derive_signature_step :
    langReduces pyashCore pyashStateListDerive pyashStateListDispatched := by
  exact pyashCore_reduction_case
    (label := "list_derive_signature_step")
    (p := pyashStateListDerive)
    (q := pyashStateListDispatched)
    (by simp [pyashCoreReductionCases])

/-- `list` dispatch path enters run mode. -/
theorem pyashCore_list_dispatch_do_step :
    langReduces pyashCore pyashStateListDispatched pyashStateListRunning := by
  exact pyashCore_reduction_case
    (label := "list_dispatch_do_step")
    (p := pyashStateListDispatched)
    (q := pyashStateListRunning)
    (by simp [pyashCoreReductionCases])

/-- `list` run path produces a `ya` done state. -/
theorem pyashCore_list_run_do_step :
    langReduces pyashCore pyashStateListRunning pyashStateListDoneOk := by
  exact pyashCore_reduction_case
    (label := "list_run_do_step")
    (p := pyashStateListRunning)
    (q := pyashStateListDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `input` signature derivation step is executable. -/
theorem pyashCore_input_derive_signature_step :
    langReduces pyashCore pyashStateInputDerive pyashStateInputDispatched := by
  exact pyashCore_reduction_case
    (label := "input_derive_signature_step")
    (p := pyashStateInputDerive)
    (q := pyashStateInputDispatched)
    (by simp [pyashCoreReductionCases])

/-- `input` dispatch path enters run mode. -/
theorem pyashCore_input_dispatch_do_step :
    langReduces pyashCore pyashStateInputDispatched pyashStateInputRunning := by
  exact pyashCore_reduction_case
    (label := "input_dispatch_do_step")
    (p := pyashStateInputDispatched)
    (q := pyashStateInputRunning)
    (by simp [pyashCoreReductionCases])

/-- `input` run path produces a `ya` done state. -/
theorem pyashCore_input_run_do_step :
    langReduces pyashCore pyashStateInputRunning pyashStateInputDoneOk := by
  exact pyashCore_reduction_case
    (label := "input_run_do_step")
    (p := pyashStateInputRunning)
    (q := pyashStateInputDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `stream` signature derivation step is executable. -/
theorem pyashCore_stream_derive_signature_step :
    langReduces pyashCore pyashStateStreamDerive pyashStateStreamDispatched := by
  exact pyashCore_reduction_case
    (label := "stream_derive_signature_step")
    (p := pyashStateStreamDerive)
    (q := pyashStateStreamDispatched)
    (by simp [pyashCoreReductionCases])

/-- `stream` dispatch path enters run mode. -/
theorem pyashCore_stream_dispatch_do_step :
    langReduces pyashCore pyashStateStreamDispatched pyashStateStreamRunning := by
  exact pyashCore_reduction_case
    (label := "stream_dispatch_do_step")
    (p := pyashStateStreamDispatched)
    (q := pyashStateStreamRunning)
    (by simp [pyashCoreReductionCases])

/-- `stream` run path produces a `ya` done state. -/
theorem pyashCore_stream_run_do_step :
    langReduces pyashCore pyashStateStreamRunning pyashStateStreamDoneOk := by
  exact pyashCore_reduction_case
    (label := "stream_run_do_step")
    (p := pyashStateStreamRunning)
    (q := pyashStateStreamDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `mind` signature derivation step is executable. -/
theorem pyashCore_mind_derive_signature_step :
    langReduces pyashCore pyashStateMindDerive pyashStateMindDispatched := by
  exact pyashCore_reduction_case
    (label := "mind_derive_signature_step")
    (p := pyashStateMindDerive)
    (q := pyashStateMindDispatched)
    (by simp [pyashCoreReductionCases])

/-- `mind` dispatch path enters run mode. -/
theorem pyashCore_mind_dispatch_do_step :
    langReduces pyashCore pyashStateMindDispatched pyashStateMindRunning := by
  exact pyashCore_reduction_case
    (label := "mind_dispatch_do_step")
    (p := pyashStateMindDispatched)
    (q := pyashStateMindRunning)
    (by simp [pyashCoreReductionCases])

/-- `mind` run path produces a `ya` done state. -/
theorem pyashCore_mind_run_do_step :
    langReduces pyashCore pyashStateMindRunning pyashStateMindDoneOk := by
  exact pyashCore_reduction_case
    (label := "mind_run_do_step")
    (p := pyashStateMindRunning)
    (q := pyashStateMindDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `ceremony` signature derivation step is executable. -/
theorem pyashCore_ceremony_derive_signature_step :
    langReduces pyashCore pyashStateCeremonyDerive pyashStateCeremonyDispatched := by
  exact pyashCore_reduction_case
    (label := "ceremony_derive_signature_step")
    (p := pyashStateCeremonyDerive)
    (q := pyashStateCeremonyDispatched)
    (by simp [pyashCoreReductionCases])

/-- `ceremony` dispatch path enters run mode. -/
theorem pyashCore_ceremony_dispatch_do_step :
    langReduces pyashCore pyashStateCeremonyDispatched pyashStateCeremonyRunning := by
  exact pyashCore_reduction_case
    (label := "ceremony_dispatch_do_step")
    (p := pyashStateCeremonyDispatched)
    (q := pyashStateCeremonyRunning)
    (by simp [pyashCoreReductionCases])

/-- `ceremony` run path produces a `ya` done state. -/
theorem pyashCore_ceremony_run_do_step :
    langReduces pyashCore pyashStateCeremonyRunning pyashStateCeremonyDoneOk := by
  exact pyashCore_reduction_case
    (label := "ceremony_run_do_step")
    (p := pyashStateCeremonyRunning)
    (q := pyashStateCeremonyDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `chip` signature derivation step is executable. -/
theorem pyashCore_chip_derive_signature_step :
    langReduces pyashCore pyashStateChipDerive pyashStateChipDispatched := by
  exact pyashCore_reduction_case
    (label := "chip_derive_signature_step")
    (p := pyashStateChipDerive)
    (q := pyashStateChipDispatched)
    (by simp [pyashCoreReductionCases])

/-- `chip` dispatch path enters run mode. -/
theorem pyashCore_chip_dispatch_do_step :
    langReduces pyashCore pyashStateChipDispatched pyashStateChipRunning := by
  exact pyashCore_reduction_case
    (label := "chip_dispatch_do_step")
    (p := pyashStateChipDispatched)
    (q := pyashStateChipRunning)
    (by simp [pyashCoreReductionCases])

/-- `chip` run path produces a `ya` done state. -/
theorem pyashCore_chip_run_do_step :
    langReduces pyashCore pyashStateChipRunning pyashStateChipDoneOk := by
  exact pyashCore_reduction_case
    (label := "chip_run_do_step")
    (p := pyashStateChipRunning)
    (q := pyashStateChipDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `chip` (series variant) signature derivation step is executable. -/
theorem pyashCore_chip_series_derive_signature_step :
    langReduces pyashCore pyashStateChipSeriesDerive pyashStateChipSeriesDispatched := by
  exact pyashCore_reduction_case
    (label := "chip_series_derive_signature_step")
    (p := pyashStateChipSeriesDerive)
    (q := pyashStateChipSeriesDispatched)
    (by simp [pyashCoreReductionCases])

/-- `chip` (series variant) dispatch path enters run mode. -/
theorem pyashCore_chip_series_dispatch_do_step :
    langReduces pyashCore pyashStateChipSeriesDispatched pyashStateChipSeriesRunning := by
  exact pyashCore_reduction_case
    (label := "chip_series_dispatch_do_step")
    (p := pyashStateChipSeriesDispatched)
    (q := pyashStateChipSeriesRunning)
    (by simp [pyashCoreReductionCases])

/-- `chip` (series variant) run path produces a `ya` done state. -/
theorem pyashCore_chip_series_run_do_step :
    langReduces pyashCore pyashStateChipSeriesRunning pyashStateChipSeriesDoneOk := by
  exact pyashCore_reduction_case
    (label := "chip_series_run_do_step")
    (p := pyashStateChipSeriesRunning)
    (q := pyashStateChipSeriesDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `chip` (bounded variant) signature derivation step is executable. -/
theorem pyashCore_chip_bounded_derive_signature_step :
    langReduces pyashCore pyashStateChipBoundedDerive pyashStateChipBoundedDispatched := by
  exact pyashCore_reduction_case
    (label := "chip_bounded_derive_signature_step")
    (p := pyashStateChipBoundedDerive)
    (q := pyashStateChipBoundedDispatched)
    (by simp [pyashCoreReductionCases])

/-- `chip` (bounded variant) dispatch path enters run mode. -/
theorem pyashCore_chip_bounded_dispatch_do_step :
    langReduces pyashCore pyashStateChipBoundedDispatched pyashStateChipBoundedRunning := by
  exact pyashCore_reduction_case
    (label := "chip_bounded_dispatch_do_step")
    (p := pyashStateChipBoundedDispatched)
    (q := pyashStateChipBoundedRunning)
    (by simp [pyashCoreReductionCases])

/-- `chip` (bounded variant) run path produces a `ya` done state. -/
theorem pyashCore_chip_bounded_run_do_step :
    langReduces pyashCore pyashStateChipBoundedRunning pyashStateChipBoundedDoneOk := by
  exact pyashCore_reduction_case
    (label := "chip_bounded_run_do_step")
    (p := pyashStateChipBoundedRunning)
    (q := pyashStateChipBoundedDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `hear` signature derivation step is executable. -/
theorem pyashCore_hear_derive_signature_step :
    langReduces pyashCore pyashStateHearDerive pyashStateHearDispatched := by
  exact pyashCore_reduction_case
    (label := "hear_derive_signature_step")
    (p := pyashStateHearDerive)
    (q := pyashStateHearDispatched)
    (by simp [pyashCoreReductionCases])

/-- `hear` dispatch path enters run mode. -/
theorem pyashCore_hear_dispatch_do_step :
    langReduces pyashCore pyashStateHearDispatched pyashStateHearRunning := by
  exact pyashCore_reduction_case
    (label := "hear_dispatch_do_step")
    (p := pyashStateHearDispatched)
    (q := pyashStateHearRunning)
    (by simp [pyashCoreReductionCases])

/-- `hear` run path produces a `ya` done state. -/
theorem pyashCore_hear_run_do_step :
    langReduces pyashCore pyashStateHearRunning pyashStateHearDoneOk := by
  exact pyashCore_reduction_case
    (label := "hear_run_do_step")
    (p := pyashStateHearRunning)
    (q := pyashStateHearDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `hear` (microphone-recording variant) signature derivation step is executable. -/
theorem pyashCore_hear_mic_derive_signature_step :
    langReduces pyashCore pyashStateHearMicRecordDerive pyashStateHearMicRecordDispatched := by
  exact pyashCore_reduction_case
    (label := "hear_mic_derive_signature_step")
    (p := pyashStateHearMicRecordDerive)
    (q := pyashStateHearMicRecordDispatched)
    (by simp [pyashCoreReductionCases])

/-- `hear` (microphone-recording variant) dispatch path enters run mode. -/
theorem pyashCore_hear_mic_dispatch_do_step :
    langReduces pyashCore pyashStateHearMicRecordDispatched pyashStateHearMicRecordRunning := by
  exact pyashCore_reduction_case
    (label := "hear_mic_dispatch_do_step")
    (p := pyashStateHearMicRecordDispatched)
    (q := pyashStateHearMicRecordRunning)
    (by simp [pyashCoreReductionCases])

/-- `hear` (microphone-recording variant) run path produces a `ya` done state. -/
theorem pyashCore_hear_mic_run_do_step :
    langReduces pyashCore pyashStateHearMicRecordRunning pyashStateHearMicRecordDoneOk := by
  exact pyashCore_reduction_case
    (label := "hear_mic_run_do_step")
    (p := pyashStateHearMicRecordRunning)
    (q := pyashStateHearMicRecordDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `hear` (file->subtitle-file variant) signature derivation step is executable. -/
theorem pyashCore_hear_srt_derive_signature_step :
    langReduces pyashCore pyashStateHearFileSrtDerive pyashStateHearFileSrtDispatched := by
  exact pyashCore_reduction_case
    (label := "hear_srt_derive_signature_step")
    (p := pyashStateHearFileSrtDerive)
    (q := pyashStateHearFileSrtDispatched)
    (by simp [pyashCoreReductionCases])

/-- `hear` (file->subtitle-file variant) dispatch path enters run mode. -/
theorem pyashCore_hear_srt_dispatch_do_step :
    langReduces pyashCore pyashStateHearFileSrtDispatched pyashStateHearFileSrtRunning := by
  exact pyashCore_reduction_case
    (label := "hear_srt_dispatch_do_step")
    (p := pyashStateHearFileSrtDispatched)
    (q := pyashStateHearFileSrtRunning)
    (by simp [pyashCoreReductionCases])

/-- `hear` (file->subtitle-file variant) run path produces a `ya` done state. -/
theorem pyashCore_hear_srt_run_do_step :
    langReduces pyashCore pyashStateHearFileSrtRunning pyashStateHearFileSrtDoneOk := by
  exact pyashCore_reduction_case
    (label := "hear_srt_run_do_step")
    (p := pyashStateHearFileSrtRunning)
    (q := pyashStateHearFileSrtDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `configure` signature derivation step is executable. -/
theorem pyashCore_configure_derive_signature_step :
    langReduces pyashCore pyashStateConfigureDerive pyashStateConfigureDispatched := by
  exact pyashCore_reduction_case
    (label := "configure_derive_signature_step")
    (p := pyashStateConfigureDerive)
    (q := pyashStateConfigureDispatched)
    (by simp [pyashCoreReductionCases])

/-- `configure` dispatch path enters run mode. -/
theorem pyashCore_configure_dispatch_do_step :
    langReduces pyashCore pyashStateConfigureDispatched pyashStateConfigureRunning := by
  exact pyashCore_reduction_case
    (label := "configure_dispatch_do_step")
    (p := pyashStateConfigureDispatched)
    (q := pyashStateConfigureRunning)
    (by simp [pyashCoreReductionCases])

/-- `configure` run path produces a `ya` done state. -/
theorem pyashCore_configure_run_do_step :
    langReduces pyashCore pyashStateConfigureRunning pyashStateConfigureDoneOk := by
  exact pyashCore_reduction_case
    (label := "configure_run_do_step")
    (p := pyashStateConfigureRunning)
    (q := pyashStateConfigureDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` mood/map baseline) signature derivation step is executable. -/
theorem pyashCore_configure_def_derive_signature_step :
    langReduces pyashCore pyashStateConfigureDefDerive pyashStateConfigureDefDispatched := by
  exact pyashCore_reduction_case
    (label := "configure_def_derive_signature_step")
    (p := pyashStateConfigureDefDerive)
    (q := pyashStateConfigureDefDispatched)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` mood/map baseline) dispatch path reaches terminal `Done`. -/
theorem pyashCore_configure_def_dispatch_def_step :
    langReduces pyashCore pyashStateConfigureDefDispatched pyashStateConfigureDefDoneOk := by
  exact pyashCore_reduction_case
    (label := "configure_def_dispatch_def_step")
    (p := pyashStateConfigureDefDispatched)
    (q := pyashStateConfigureDefDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` command-map) signature derivation step is executable. -/
theorem pyashCore_configure_command_map_def_derive_signature_step :
    langReduces pyashCore
      pyashStateConfigureCommandMapDefDerive
      pyashStateConfigureCommandMapDefDispatched := by
  exact pyashCore_reduction_case
    (label := "configure_command_map_def_derive_signature_step")
    (p := pyashStateConfigureCommandMapDefDerive)
    (q := pyashStateConfigureCommandMapDefDispatched)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` command-map) dispatch path reaches terminal `Done`. -/
theorem pyashCore_configure_command_map_def_dispatch_def_step :
    langReduces pyashCore
      pyashStateConfigureCommandMapDefDispatched
      pyashStateConfigureCommandMapDefDoneOk := by
  exact pyashCore_reduction_case
    (label := "configure_command_map_def_dispatch_def_step")
    (p := pyashStateConfigureCommandMapDefDispatched)
    (q := pyashStateConfigureCommandMapDefDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` sandbox-map) signature derivation step is executable. -/
theorem pyashCore_configure_sandbox_map_def_derive_signature_step :
    langReduces pyashCore
      pyashStateConfigureSandboxMapDefDerive
      pyashStateConfigureSandboxMapDefDispatched := by
  exact pyashCore_reduction_case
    (label := "configure_sandbox_map_def_derive_signature_step")
    (p := pyashStateConfigureSandboxMapDefDerive)
    (q := pyashStateConfigureSandboxMapDefDispatched)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` sandbox-map) dispatch path reaches terminal `Done`. -/
theorem pyashCore_configure_sandbox_map_def_dispatch_def_step :
    langReduces pyashCore
      pyashStateConfigureSandboxMapDefDispatched
      pyashStateConfigureSandboxMapDefDoneOk := by
  exact pyashCore_reduction_case
    (label := "configure_sandbox_map_def_dispatch_def_step")
    (p := pyashStateConfigureSandboxMapDefDispatched)
    (q := pyashStateConfigureSandboxMapDefDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` verify-loop map) signature derivation step is executable. -/
theorem pyashCore_configure_verify_loop_map_def_derive_signature_step :
    langReduces pyashCore
      pyashStateConfigureVerifyLoopMapDefDerive
      pyashStateConfigureVerifyLoopMapDefDispatched := by
  exact pyashCore_reduction_case
    (label := "configure_verify_loop_map_def_derive_signature_step")
    (p := pyashStateConfigureVerifyLoopMapDefDerive)
    (q := pyashStateConfigureVerifyLoopMapDefDispatched)
    (by simp [pyashCoreReductionCases])

/-- `configure` (`def` verify-loop map) dispatch path reaches terminal `Done`. -/
theorem pyashCore_configure_verify_loop_map_def_dispatch_def_step :
    langReduces pyashCore
      pyashStateConfigureVerifyLoopMapDefDispatched
      pyashStateConfigureVerifyLoopMapDefDoneOk := by
  exact pyashCore_reduction_case
    (label := "configure_verify_loop_map_def_dispatch_def_step")
    (p := pyashStateConfigureVerifyLoopMapDefDispatched)
    (q := pyashStateConfigureVerifyLoopMapDefDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `world` signature derivation step is executable. -/
theorem pyashCore_world_derive_signature_step :
    langReduces pyashCore pyashStateWorldDerive pyashStateWorldDispatched := by
  exact pyashCore_reduction_case
    (label := "world_derive_signature_step")
    (p := pyashStateWorldDerive)
    (q := pyashStateWorldDispatched)
    (by simp [pyashCoreReductionCases])

/-- `world` dispatch path enters run mode. -/
theorem pyashCore_world_dispatch_do_step :
    langReduces pyashCore pyashStateWorldDispatched pyashStateWorldRunning := by
  exact pyashCore_reduction_case
    (label := "world_dispatch_do_step")
    (p := pyashStateWorldDispatched)
    (q := pyashStateWorldRunning)
    (by simp [pyashCoreReductionCases])

/-- `world` run path produces a `ya` done state. -/
theorem pyashCore_world_run_do_step :
    langReduces pyashCore pyashStateWorldRunning pyashStateWorldDoneOk := by
  exact pyashCore_reduction_case
    (label := "world_run_do_step")
    (p := pyashStateWorldRunning)
    (q := pyashStateWorldDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `world` (path-io variant) signature derivation step is executable. -/
theorem pyashCore_world_path_io_derive_signature_step :
    langReduces pyashCore pyashStateWorldPathIODerive pyashStateWorldPathIODispatched := by
  exact pyashCore_reduction_case
    (label := "world_path_io_derive_signature_step")
    (p := pyashStateWorldPathIODerive)
    (q := pyashStateWorldPathIODispatched)
    (by simp [pyashCoreReductionCases])

/-- `world` (path-io variant) dispatch path enters run mode. -/
theorem pyashCore_world_path_io_dispatch_do_step :
    langReduces pyashCore pyashStateWorldPathIODispatched pyashStateWorldPathIORunning := by
  exact pyashCore_reduction_case
    (label := "world_path_io_dispatch_do_step")
    (p := pyashStateWorldPathIODispatched)
    (q := pyashStateWorldPathIORunning)
    (by simp [pyashCoreReductionCases])

/-- `world` (path-io variant) run path produces a `ya` done state. -/
theorem pyashCore_world_path_io_run_do_step :
    langReduces pyashCore pyashStateWorldPathIORunning pyashStateWorldPathIODoneOk := by
  exact pyashCore_reduction_case
    (label := "world_path_io_run_do_step")
    (p := pyashStateWorldPathIORunning)
    (q := pyashStateWorldPathIODoneOk)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` signature derivation step is executable. -/
theorem pyashCore_pipeline_derive_signature_step :
    langReduces pyashCore pyashStatePipelineDerive pyashStatePipelineDispatched := by
  exact pyashCore_reduction_case
    (label := "pipeline_derive_signature_step")
    (p := pyashStatePipelineDerive)
    (q := pyashStatePipelineDispatched)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` dispatch path enters run mode. -/
theorem pyashCore_pipeline_dispatch_do_step :
    langReduces pyashCore pyashStatePipelineDispatched pyashStatePipelineRunning := by
  exact pyashCore_reduction_case
    (label := "pipeline_dispatch_do_step")
    (p := pyashStatePipelineDispatched)
    (q := pyashStatePipelineRunning)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` run path produces a `ya` done state. -/
theorem pyashCore_pipeline_run_do_step :
    langReduces pyashCore pyashStatePipelineRunning pyashStatePipelineDoneOk := by
  exact pyashCore_reduction_case
    (label := "pipeline_run_do_step")
    (p := pyashStatePipelineRunning)
    (q := pyashStatePipelineDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (refinery variant) signature derivation step is executable. -/
theorem pyashCore_pipeline_refinery_derive_signature_step :
    langReduces pyashCore pyashStatePipelineRefineryDerive pyashStatePipelineRefineryDispatched := by
  exact pyashCore_reduction_case
    (label := "pipeline_refinery_derive_signature_step")
    (p := pyashStatePipelineRefineryDerive)
    (q := pyashStatePipelineRefineryDispatched)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (refinery variant) dispatch path enters run mode. -/
theorem pyashCore_pipeline_refinery_dispatch_do_step :
    langReduces pyashCore pyashStatePipelineRefineryDispatched pyashStatePipelineRefineryRunning := by
  exact pyashCore_reduction_case
    (label := "pipeline_refinery_dispatch_do_step")
    (p := pyashStatePipelineRefineryDispatched)
    (q := pyashStatePipelineRefineryRunning)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (refinery variant) run path produces a `ya` done state. -/
theorem pyashCore_pipeline_refinery_run_do_step :
    langReduces pyashCore pyashStatePipelineRefineryRunning pyashStatePipelineRefineryDoneOk := by
  exact pyashCore_reduction_case
    (label := "pipeline_refinery_run_do_step")
    (p := pyashStatePipelineRefineryRunning)
    (q := pyashStatePipelineRefineryDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (chirp variant) signature derivation step is executable. -/
theorem pyashCore_pipeline_chirp_derive_signature_step :
    langReduces pyashCore pyashStatePipelineChirpDerive pyashStatePipelineChirpDispatched := by
  exact pyashCore_reduction_case
    (label := "pipeline_chirp_derive_signature_step")
    (p := pyashStatePipelineChirpDerive)
    (q := pyashStatePipelineChirpDispatched)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (chirp variant) dispatch path enters run mode. -/
theorem pyashCore_pipeline_chirp_dispatch_do_step :
    langReduces pyashCore pyashStatePipelineChirpDispatched pyashStatePipelineChirpRunning := by
  exact pyashCore_reduction_case
    (label := "pipeline_chirp_dispatch_do_step")
    (p := pyashStatePipelineChirpDispatched)
    (q := pyashStatePipelineChirpRunning)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (chirp variant) run path produces a `ya` done state. -/
theorem pyashCore_pipeline_chirp_run_do_step :
    langReduces pyashCore pyashStatePipelineChirpRunning pyashStatePipelineChirpDoneOk := by
  exact pyashCore_reduction_case
    (label := "pipeline_chirp_run_do_step")
    (p := pyashStatePipelineChirpRunning)
    (q := pyashStatePipelineChirpDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (re-entry variant) signature derivation step is executable. -/
theorem pyashCore_pipeline_reentry_derive_signature_step :
    langReduces pyashCore pyashStatePipelineReentryDerive pyashStatePipelineReentryDispatched := by
  exact pyashCore_reduction_case
    (label := "pipeline_reentry_derive_signature_step")
    (p := pyashStatePipelineReentryDerive)
    (q := pyashStatePipelineReentryDispatched)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (re-entry variant) dispatch path enters run mode. -/
theorem pyashCore_pipeline_reentry_dispatch_do_step :
    langReduces pyashCore pyashStatePipelineReentryDispatched pyashStatePipelineReentryRunning := by
  exact pyashCore_reduction_case
    (label := "pipeline_reentry_dispatch_do_step")
    (p := pyashStatePipelineReentryDispatched)
    (q := pyashStatePipelineReentryRunning)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` (re-entry variant) run path produces a `ya` done state. -/
theorem pyashCore_pipeline_reentry_run_do_step :
    langReduces pyashCore pyashStatePipelineReentryRunning pyashStatePipelineReentryDoneOk := by
  exact pyashCore_reduction_case
    (label := "pipeline_reentry_run_do_step")
    (p := pyashStatePipelineReentryRunning)
    (q := pyashStatePipelineReentryDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `compile` signature derivation step is executable. -/
theorem pyashCore_compile_derive_signature_step :
    langReduces pyashCore pyashStateCompileDerive pyashStateCompileDispatched := by
  exact pyashCore_reduction_case
    (label := "compile_derive_signature_step")
    (p := pyashStateCompileDerive)
    (q := pyashStateCompileDispatched)
    (by simp [pyashCoreReductionCases])

/-- `compile` dispatch path enters run mode. -/
theorem pyashCore_compile_dispatch_do_step :
    langReduces pyashCore pyashStateCompileDispatched pyashStateCompileRunning := by
  exact pyashCore_reduction_case
    (label := "compile_dispatch_do_step")
    (p := pyashStateCompileDispatched)
    (q := pyashStateCompileRunning)
    (by simp [pyashCoreReductionCases])

/-- `compile` run path produces a `ya` done state. -/
theorem pyashCore_compile_run_do_step :
    langReduces pyashCore pyashStateCompileRunning pyashStateCompileDoneOk := by
  exact pyashCore_reduction_case
    (label := "compile_run_do_step")
    (p := pyashStateCompileRunning)
    (q := pyashStateCompileDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `import` signature derivation step is executable. -/
theorem pyashCore_import_derive_signature_step :
    langReduces pyashCore pyashStateImportDerive pyashStateImportDispatched := by
  exact pyashCore_reduction_case
    (label := "import_derive_signature_step")
    (p := pyashStateImportDerive)
    (q := pyashStateImportDispatched)
    (by simp [pyashCoreReductionCases])

/-- `import` dispatch path enters run mode. -/
theorem pyashCore_import_dispatch_do_step :
    langReduces pyashCore pyashStateImportDispatched pyashStateImportRunning := by
  exact pyashCore_reduction_case
    (label := "import_dispatch_do_step")
    (p := pyashStateImportDispatched)
    (q := pyashStateImportRunning)
    (by simp [pyashCoreReductionCases])

/-- `import` run path produces a `ya` done state. -/
theorem pyashCore_import_run_do_step :
    langReduces pyashCore pyashStateImportRunning pyashStateImportDoneOk := by
  exact pyashCore_reduction_case
    (label := "import_run_do_step")
    (p := pyashStateImportRunning)
    (q := pyashStateImportDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `download` signature derivation step is executable. -/
theorem pyashCore_download_derive_signature_step :
    langReduces pyashCore pyashStateDownloadDerive pyashStateDownloadDispatched := by
  exact pyashCore_reduction_case
    (label := "download_derive_signature_step")
    (p := pyashStateDownloadDerive)
    (q := pyashStateDownloadDispatched)
    (by simp [pyashCoreReductionCases])

/-- `download` dispatch path enters run mode. -/
theorem pyashCore_download_dispatch_do_step :
    langReduces pyashCore pyashStateDownloadDispatched pyashStateDownloadRunning := by
  exact pyashCore_reduction_case
    (label := "download_dispatch_do_step")
    (p := pyashStateDownloadDispatched)
    (q := pyashStateDownloadRunning)
    (by simp [pyashCoreReductionCases])

/-- `download` run path produces a `ya` done state. -/
theorem pyashCore_download_run_do_step :
    langReduces pyashCore pyashStateDownloadRunning pyashStateDownloadDoneOk := by
  exact pyashCore_reduction_case
    (label := "download_run_do_step")
    (p := pyashStateDownloadRunning)
    (q := pyashStateDownloadDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `translation` signature derivation step is executable. -/
theorem pyashCore_translation_derive_signature_step :
    langReduces pyashCore pyashStateTranslationDerive pyashStateTranslationDispatched := by
  exact pyashCore_reduction_case
    (label := "translation_derive_signature_step")
    (p := pyashStateTranslationDerive)
    (q := pyashStateTranslationDispatched)
    (by simp [pyashCoreReductionCases])

/-- `translation` dispatch path enters run mode. -/
theorem pyashCore_translation_dispatch_do_step :
    langReduces pyashCore pyashStateTranslationDispatched pyashStateTranslationRunning := by
  exact pyashCore_reduction_case
    (label := "translation_dispatch_do_step")
    (p := pyashStateTranslationDispatched)
    (q := pyashStateTranslationRunning)
    (by simp [pyashCoreReductionCases])

/-- `translation` run path produces a `ya` done state. -/
theorem pyashCore_translation_run_do_step :
    langReduces pyashCore pyashStateTranslationRunning pyashStateTranslationDoneOk := by
  exact pyashCore_reduction_case
    (label := "translation_run_do_step")
    (p := pyashStateTranslationRunning)
    (q := pyashStateTranslationDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `ret`/`read` signature derivation step is executable. -/
theorem pyashCore_ret_read_derive_signature_step :
    langReduces pyashCore pyashStateRetReadDerive pyashStateRetReadDispatched := by
  exact pyashCore_reduction_case
    (label := "ret_read_derive_signature_step")
    (p := pyashStateRetReadDerive)
    (q := pyashStateRetReadDispatched)
    (by simp [pyashCoreReductionCases])

/-- `ret`/`read` dispatch path produces an explicit `ret` terminal state. -/
theorem pyashCore_ret_read_dispatch_ret_step :
    langReduces pyashCore pyashStateRetReadDispatched pyashStateRetReadDoneOk := by
  exact pyashCore_reduction_case
    (label := "ret_read_dispatch_ret_step")
    (p := pyashStateRetReadDispatched)
    (q := pyashStateRetReadDoneOk)
    (by simp [pyashCoreReductionCases])

/-- `configure` command-map mismatch is surfaced as a signature error state. -/
theorem pyashCore_configure_command_map_def_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateConfigureCommandMapDefMismatch
      pyashStateConfigureCommandMapDefDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "configure_command_map_def_signature_mismatch_surfaces_error")
    (p := pyashStateConfigureCommandMapDefMismatch)
    (q := pyashStateConfigureCommandMapDefDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `configure` sandbox-map mismatch is surfaced as a signature error state. -/
theorem pyashCore_configure_sandbox_map_def_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateConfigureSandboxMapDefMismatch
      pyashStateConfigureSandboxMapDefDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "configure_sandbox_map_def_signature_mismatch_surfaces_error")
    (p := pyashStateConfigureSandboxMapDefMismatch)
    (q := pyashStateConfigureSandboxMapDefDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `configure` verify-loop mismatch is surfaced as a signature error state. -/
theorem pyashCore_configure_verify_loop_map_def_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateConfigureVerifyLoopMapDefMismatch
      pyashStateConfigureVerifyLoopMapDefDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "configure_verify_loop_map_def_signature_mismatch_surfaces_error")
    (p := pyashStateConfigureVerifyLoopMapDefMismatch)
    (q := pyashStateConfigureVerifyLoopMapDefDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `world` path-io mismatch is surfaced as a signature error state. -/
theorem pyashCore_world_path_io_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateWorldPathIOMismatch
      pyashStateWorldPathIODoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "world_path_io_signature_mismatch_surfaces_error")
    (p := pyashStateWorldPathIOMismatch)
    (q := pyashStateWorldPathIODoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` refinery mismatch is surfaced as a signature error state. -/
theorem pyashCore_pipeline_refinery_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStatePipelineRefineryMismatch
      pyashStatePipelineRefineryDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "pipeline_refinery_signature_mismatch_surfaces_error")
    (p := pyashStatePipelineRefineryMismatch)
    (q := pyashStatePipelineRefineryDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` chirp mismatch is surfaced as a signature error state. -/
theorem pyashCore_pipeline_chirp_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStatePipelineChirpMismatch
      pyashStatePipelineChirpDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "pipeline_chirp_signature_mismatch_surfaces_error")
    (p := pyashStatePipelineChirpMismatch)
    (q := pyashStatePipelineChirpDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `pipeline` re-entry mismatch is surfaced as a signature error state. -/
theorem pyashCore_pipeline_reentry_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStatePipelineReentryMismatch
      pyashStatePipelineReentryDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "pipeline_reentry_signature_mismatch_surfaces_error")
    (p := pyashStatePipelineReentryMismatch)
    (q := pyashStatePipelineReentryDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `list` mismatch is surfaced as a signature error state. -/
theorem pyashCore_list_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateListMismatch
      pyashStateListDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "list_signature_mismatch_surfaces_error")
    (p := pyashStateListMismatch)
    (q := pyashStateListDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `input` mismatch is surfaced as a signature error state. -/
theorem pyashCore_input_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateInputMismatch
      pyashStateInputDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "input_signature_mismatch_surfaces_error")
    (p := pyashStateInputMismatch)
    (q := pyashStateInputDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `stream` mismatch is surfaced as a signature error state. -/
theorem pyashCore_stream_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateStreamMismatch
      pyashStateStreamDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "stream_signature_mismatch_surfaces_error")
    (p := pyashStateStreamMismatch)
    (q := pyashStateStreamDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `compile` mismatch is surfaced as a signature error state. -/
theorem pyashCore_compile_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateCompileMismatch
      pyashStateCompileDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "compile_signature_mismatch_surfaces_error")
    (p := pyashStateCompileMismatch)
    (q := pyashStateCompileDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `import` mismatch is surfaced as a signature error state. -/
theorem pyashCore_import_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateImportMismatch
      pyashStateImportDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "import_signature_mismatch_surfaces_error")
    (p := pyashStateImportMismatch)
    (q := pyashStateImportDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `download` mismatch is surfaced as a signature error state. -/
theorem pyashCore_download_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateDownloadMismatch
      pyashStateDownloadDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "download_signature_mismatch_surfaces_error")
    (p := pyashStateDownloadMismatch)
    (q := pyashStateDownloadDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- `translation` mismatch is surfaced as a signature error state. -/
theorem pyashCore_translation_signature_mismatch_surfaces_error :
    langReduces pyashCore
      pyashStateTranslationMismatch
      pyashStateTranslationDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "translation_signature_mismatch_surfaces_error")
    (p := pyashStateTranslationMismatch)
    (q := pyashStateTranslationDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- Explicit dispatch-error instruction surfaces dispatch error deterministically. -/
theorem pyashCore_dispatch_error_instr_surfaces_dispatch_error :
    langReduces pyashCore pyashStateDispatchErrorInstr pyashStateDoneDispatchErr := by
  exact pyashCore_reduction_case
    (label := "dispatch_error_instr_surfaces_dispatch_error")
    (p := pyashStateDispatchErrorInstr)
    (q := pyashStateDoneDispatchErr)
    (by simp [pyashCoreReductionCases])

/-- Unsupported `then` dispatch branch surfaces explicit dispatch error. -/
theorem pyashCore_dispatch_then_surfaces_dispatch_error :
    langReduces pyashCore pyashStateDispatchThenError pyashStateDoneDispatchErr := by
  exact pyashCore_reduction_case
    (label := "dispatch_then_surfaces_dispatch_error")
    (p := pyashStateDispatchThenError)
    (q := pyashStateDoneDispatchErr)
    (by simp [pyashCoreReductionCases])

/-- Malformed nested signature shapes are surfaced via signature-error path. -/
theorem pyashCore_malformed_signature_shape_surfaces_error :
    langReduces pyashCore pyashStateMalformedSignatureShape pyashStateDoneMalformedSignatureErr := by
  exact pyashCore_reduction_case
    (label := "malformed_signature_shape_surfaces_error")
    (p := pyashStateMalformedSignatureShape)
    (q := pyashStateDoneMalformedSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- Signature mismatch is surfaced as an error-state result. -/
theorem pyashCore_signature_mismatch_surfaces_error :
    langReduces pyashCore pyashStateMismatch pyashStateDoneSignatureErr := by
  exact pyashCore_reduction_case
    (label := "signature_mismatch_surfaces_error")
    (p := pyashStateMismatch)
    (q := pyashStateDoneSignatureErr)
    (by simp [pyashCoreReductionCases])

/-- Executable rewrite set for a finished `Done` state is empty. -/
theorem pyashCore_done_rewrite_nil :
    rewriteWithContextWithPremisesUsing RelationEnv.empty pyashCore pyashStateDoneOk = [] := by
  decide +kernel

/-- `Done` states are terminal under the focused Pyash core rewrite set. -/
theorem pyashCore_done_irreducible (q : Pattern) :
    ¬ langReduces pyashCore pyashStateDoneOk q := by
  intro hred
  have hExec : langReducesExecUsing RelationEnv.empty pyashCore pyashStateDoneOk q :=
    langReducesUsing_to_exec (relEnv := RelationEnv.empty) (lang := pyashCore) hred
  have hmem : q ∈ rewriteWithContextWithPremisesUsing RelationEnv.empty pyashCore pyashStateDoneOk := by
    simpa [langReducesExecUsing] using hExec
  simp [pyashCore_done_rewrite_nil] at hmem

open Mettapedia.OSLF.Framework.GovernanceInstance (isGovLive)

/-! ## §2 Liveness and Closure Analysis

These results connect PyashCore's operational semantics to the `isGovLive`
predicate from `GovernanceInstance`. The key mathematical finding is that
`isGovLive` is NOT forward-closed under PyashCore reduction: the `RunDo`
instruction reduces to `Done`, which exits the live set. -/

/-- `pyashStateRunning` (RunDo instruction) is a live state. -/
theorem pyashCore_isGovLive_running : isGovLive pyashStateRunning := by
  simp [isGovLive, pyashStateRunning]

/-- `pyashStateDoneOk` (Done instruction) is NOT live. -/
theorem pyashCore_not_isGovLive_doneOk : ¬ isGovLive pyashStateDoneOk := by
  simp [isGovLive, pyashStateDoneOk]

/-- The `isGovLive` predicate is NOT forward-closed under PyashCore reduction:
    `pyashStateRunning` is live, reduces to `pyashStateDoneOk`, which is not live.

    This shows that `ClosedGovAccessibility.closed` cannot be satisfied with
    `live = isGovLive` for PyashCore. The `isGovLiveAccessibility` function in
    `GovernanceGSLTVertex.lean` correctly parameterizes both proofs, leaving
    them as obligations for whoever instantiates it with a suitable live predicate. -/
theorem pyashCore_isGovLive_not_closed :
    ∃ p q, isGovLive p ∧ langReduces pyashCore p q ∧ ¬ isGovLive q :=
  ⟨pyashStateRunning, pyashStateDoneOk,
   pyashCore_isGovLive_running,
   pyashCore_run_do_step,
   pyashCore_not_isGovLive_doneOk⟩

end Mettapedia.OSLF.Framework.PyashCoreInstance
