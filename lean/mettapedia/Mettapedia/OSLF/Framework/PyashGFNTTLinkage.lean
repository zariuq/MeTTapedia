import Mettapedia.OSLF.Framework.PyashGF
import Mettapedia.CategoryTheory.NativeTypeTheory
import Mettapedia.CategoryTheory.PLNInstance
import Mettapedia.Logic.EvidenceQuantale

/-!
# Pyash GF Canary OSLF→NTT Linkage

The bridge below records theorem-level linkage artifacts for all exported
PyashGF canary labels. Each record carries:
- a canonical canary label,
- the proved OSLF closure witness (`PyashCoreReducesStar`), and
- an explicit NTT object + morphism witness.
-/

namespace Mettapedia.OSLF.Framework.PyashGFNTTLinkage

open Mettapedia.OSLF.Framework.PyashGF
open Mettapedia.OSLF.Framework.PyashCoreInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.CategoryTheory.NativeTypeTheory
open Mettapedia.Logic.EvidenceQuantale

/-- Lightweight OSLF→NTT linkage record keyed by exported canary label. -/
structure PyashGFCanaryNTTLink where
  label : String
  startState : Pattern
  endState : Pattern
  oslfClosure : PyashCoreReducesStar startState endState
  ntObj : NativeTypeBundle
  ntSelfHom : Hom ntObj ntObj

/-- Canonical NTT anchor object for canary linkage witnesses. -/
def pyashCanaryNTTAnchor : NativeTypeBundle :=
  Sigma.mk (PLNObj.Concept "pyash_canary") (⊥ : BinaryEvidence)

/-- Canonical reflexive NTT morphism at the canary anchor. -/
def pyashCanaryNTTAnchorId : Hom pyashCanaryNTTAnchor pyashCanaryNTTAnchor :=
  PLift.up (le_rfl : (⊥ : BinaryEvidence) ≤ ⊥)

/-- Compact constructor for canary linkage rows. -/
private def mkCanaryLink
    (label : String)
    (startState endState : Pattern)
    (oslfClosure : PyashCoreReducesStar startState endState) :
    PyashGFCanaryNTTLink :=
  { label := label
    startState := startState
    endState := endState
    oslfClosure := oslfClosure
    ntObj := pyashCanaryNTTAnchor
    ntSelfHom := pyashCanaryNTTAnchorId
  }

/-- Full linkage bundle for the exported PyashGF canary labels. -/
def pyashGFAllCanaryNTTLinks : List PyashGFCanaryNTTLink :=
  [ mkCanaryLink "pyash_gf_read_do"
      pyashStateReadDerive pyashStateReadDoneOk
      pyashGF_read_clause_closure_bridge
  , mkCanaryLink "pyash_gf_write_do"
      pyashStateWriteDerive pyashStateWriteDoneOk
      pyashGF_write_clause_closure_bridge
  , mkCanaryLink "pyash_gf_say_do"
      pyashStateSayDerive pyashStateSayDoneOk
      pyashGF_say_clause_closure_bridge
  , mkCanaryLink "pyash_gf_map_do"
      pyashStateMapDerive pyashStateMapDoneOk
      pyashGF_map_clause_closure_bridge
  , mkCanaryLink "pyash_gf_map_def"
      pyashStateMapDefDerive pyashStateMapDefDoneOk
      pyashGF_map_def_clause_closure_bridge
  , mkCanaryLink "pyash_gf_command_do"
      pyashStateCommandDerive pyashStateCommandDoneOk
      pyashGF_command_clause_closure_bridge
  , mkCanaryLink "pyash_gf_search_do"
      pyashStateSearchDerive pyashStateSearchDoneOk
      pyashGF_search_clause_closure_bridge
  , mkCanaryLink "pyash_gf_list_do"
      pyashStateListDerive pyashStateListDoneOk
      pyashGF_list_clause_closure_bridge
  , mkCanaryLink "pyash_gf_list_err_signature"
      pyashStateListMismatch pyashStateListDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_list_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_list_err_terminal"
      pyashStateListDoneSignatureErr pyashStateListDoneSignatureErr
      pyashGF_list_err_terminal_closure
  , mkCanaryLink "pyash_gf_input_do"
      pyashStateInputDerive pyashStateInputDoneOk
      pyashGF_input_clause_closure_bridge
  , mkCanaryLink "pyash_gf_input_err_signature"
      pyashStateInputMismatch pyashStateInputDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_input_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_input_err_terminal"
      pyashStateInputDoneSignatureErr pyashStateInputDoneSignatureErr
      pyashGF_input_err_terminal_closure
  , mkCanaryLink "pyash_gf_stream_do"
      pyashStateStreamDerive pyashStateStreamDoneOk
      pyashGF_stream_clause_closure_bridge
  , mkCanaryLink "pyash_gf_stream_err_signature"
      pyashStateStreamMismatch pyashStateStreamDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_stream_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_stream_err_terminal"
      pyashStateStreamDoneSignatureErr pyashStateStreamDoneSignatureErr
      pyashGF_stream_err_terminal_closure
  , mkCanaryLink "pyash_gf_mind_do"
      pyashStateMindDerive pyashStateMindDoneOk
      pyashGF_mind_clause_closure_bridge
  , mkCanaryLink "pyash_gf_read_then_err_dispatch"
      pyashStateDispatchThenError pyashStateDoneDispatchErr
      (PyashCoreReducesStar.single pyashGF_read_then_negative_bridge)
  , mkCanaryLink "pyash_gf_configure_then_err_dispatch"
      pyashStateConfigureThenError pyashStateConfigureThenDoneDispatchErr
      pyashGF_configure_then_negative_closure_bridge
  , mkCanaryLink "pyash_gf_world_then_err_dispatch"
      pyashStateWorldThenError pyashStateWorldThenDoneDispatchErr
      pyashGF_world_then_negative_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_then_err_dispatch"
      pyashStatePipelineThenError pyashStatePipelineThenDoneDispatchErr
      pyashGF_pipeline_then_negative_closure_bridge
  , mkCanaryLink "pyash_gf_configure_then_err_terminal"
      pyashStateConfigureThenDoneDispatchErr pyashStateConfigureThenDoneDispatchErr
      pyashGF_configure_then_terminal_closure
  , mkCanaryLink "pyash_gf_world_then_err_terminal"
      pyashStateWorldThenDoneDispatchErr pyashStateWorldThenDoneDispatchErr
      pyashGF_world_then_terminal_closure
  , mkCanaryLink "pyash_gf_pipeline_then_err_terminal"
      pyashStatePipelineThenDoneDispatchErr pyashStatePipelineThenDoneDispatchErr
      pyashGF_pipeline_then_terminal_closure
  , mkCanaryLink "pyash_gf_dispatch_error_instr"
      pyashStateDispatchErrorInstr pyashStateDoneDispatchErr
      (PyashCoreReducesStar.single pyashGF_dispatch_error_negative_bridge)
  , mkCanaryLink "pyash_gf_chip_do"
      pyashStateChipDerive pyashStateChipDoneOk
      pyashGF_chip_clause_closure_bridge
  , mkCanaryLink "pyash_gf_chip_do_series"
      pyashStateChipSeriesDerive pyashStateChipSeriesDoneOk
      pyashGF_chip_series_clause_closure_bridge
  , mkCanaryLink "pyash_gf_chip_do_bounded"
      pyashStateChipBoundedDerive pyashStateChipBoundedDoneOk
      pyashGF_chip_bounded_clause_closure_bridge
  , mkCanaryLink "pyash_gf_hear_do"
      pyashStateHearDerive pyashStateHearDoneOk
      pyashGF_hear_clause_closure_bridge
  , mkCanaryLink "pyash_gf_hear_do_mic"
      pyashStateHearMicRecordDerive pyashStateHearMicRecordDoneOk
      pyashGF_hear_mic_clause_closure_bridge
  , mkCanaryLink "pyash_gf_hear_do_srt"
      pyashStateHearFileSrtDerive pyashStateHearFileSrtDoneOk
      pyashGF_hear_srt_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_do"
      pyashStateConfigureDerive pyashStateConfigureDoneOk
      pyashGF_configure_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_def"
      pyashStateConfigureDefDerive pyashStateConfigureDefDoneOk
      pyashGF_configure_def_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_command_map_def"
      pyashStateConfigureCommandMapDefDerive pyashStateConfigureCommandMapDefDoneOk
      pyashGF_configure_command_map_def_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_command_map_def_dispatch_to_done"
      pyashStateConfigureCommandMapDefDispatched pyashStateConfigureCommandMapDefDoneOk
      pyashGF_configure_command_map_def_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_configure_sandbox_map_def"
      pyashStateConfigureSandboxMapDefDerive pyashStateConfigureSandboxMapDefDoneOk
      pyashGF_configure_sandbox_map_def_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_sandbox_map_def_dispatch_to_done"
      pyashStateConfigureSandboxMapDefDispatched pyashStateConfigureSandboxMapDefDoneOk
      pyashGF_configure_sandbox_map_def_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_configure_verify_loop_map_def"
      pyashStateConfigureVerifyLoopMapDefDerive pyashStateConfigureVerifyLoopMapDefDoneOk
      pyashGF_configure_verify_loop_map_def_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_verify_loop_map_def_dispatch_to_done"
      pyashStateConfigureVerifyLoopMapDefDispatched pyashStateConfigureVerifyLoopMapDefDoneOk
      pyashGF_configure_verify_loop_map_def_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_configure_command_map_def_err_signature"
      pyashStateConfigureCommandMapDefMismatch pyashStateConfigureCommandMapDefDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_configure_command_map_def_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_configure_command_map_def_err_terminal"
      pyashStateConfigureCommandMapDefDoneSignatureErr pyashStateConfigureCommandMapDefDoneSignatureErr
      pyashGF_configure_command_map_def_err_terminal_closure
  , mkCanaryLink "pyash_gf_configure_sandbox_map_def_err_signature"
      pyashStateConfigureSandboxMapDefMismatch pyashStateConfigureSandboxMapDefDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_configure_sandbox_map_def_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_configure_sandbox_map_def_err_terminal"
      pyashStateConfigureSandboxMapDefDoneSignatureErr pyashStateConfigureSandboxMapDefDoneSignatureErr
      pyashGF_configure_sandbox_map_def_err_terminal_closure
  , mkCanaryLink "pyash_gf_configure_verify_loop_map_def_err_signature"
      pyashStateConfigureVerifyLoopMapDefMismatch
      pyashStateConfigureVerifyLoopMapDefDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_configure_verify_loop_map_def_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_configure_verify_loop_map_def_err_terminal"
      pyashStateConfigureVerifyLoopMapDefDoneSignatureErr
      pyashStateConfigureVerifyLoopMapDefDoneSignatureErr
      pyashGF_configure_verify_loop_map_def_err_terminal_closure
  , mkCanaryLink "pyash_gf_configure_dispatch_to_done"
      pyashStateConfigureDispatched pyashStateConfigureDoneOk
      pyashGF_configure_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_configure_running_to_done"
      pyashStateConfigureRunning pyashStateConfigureDoneOk
      pyashGF_configure_running_closure_bridge
  , mkCanaryLink "pyash_gf_world_do"
      pyashStateWorldDerive pyashStateWorldDoneOk
      pyashGF_world_clause_closure_bridge
  , mkCanaryLink "pyash_gf_world_path_io_do"
      pyashStateWorldPathIODerive pyashStateWorldPathIODoneOk
      pyashGF_world_path_clause_closure_bridge
  , mkCanaryLink "pyash_gf_world_path_io_action_do"
      pyashStateWorldPathIODerive pyashStateWorldPathIODoneOk
      pyashGF_world_path_io_action_clause_closure_bridge
  , mkCanaryLink "pyash_gf_world_path_io_dispatch_to_done"
      pyashStateWorldPathIODispatched pyashStateWorldPathIODoneOk
      pyashGF_world_path_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_world_path_io_running_to_done"
      pyashStateWorldPathIORunning pyashStateWorldPathIODoneOk
      pyashGF_world_path_running_closure_bridge
  , mkCanaryLink "pyash_gf_world_path_io_err_signature"
      pyashStateWorldPathIOMismatch pyashStateWorldPathIODoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_world_path_io_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_world_path_io_err_terminal"
      pyashStateWorldPathIODoneSignatureErr pyashStateWorldPathIODoneSignatureErr
      pyashGF_world_path_err_terminal_closure
  , mkCanaryLink "pyash_gf_world_dispatch_to_done"
      pyashStateWorldDispatched pyashStateWorldDoneOk
      pyashGF_world_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_world_running_to_done"
      pyashStateWorldRunning pyashStateWorldDoneOk
      pyashGF_world_running_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_do"
      pyashStatePipelineDerive pyashStatePipelineDoneOk
      pyashGF_pipeline_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_refinery_do"
      pyashStatePipelineRefineryDerive pyashStatePipelineRefineryDoneOk
      pyashGF_pipeline_refinery_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_refinery_dispatch_to_done"
      pyashStatePipelineRefineryDispatched pyashStatePipelineRefineryDoneOk
      pyashGF_pipeline_refinery_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_refinery_running_to_done"
      pyashStatePipelineRefineryRunning pyashStatePipelineRefineryDoneOk
      pyashGF_pipeline_refinery_running_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_refinery_err_signature"
      pyashStatePipelineRefineryMismatch pyashStatePipelineRefineryDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_pipeline_refinery_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_pipeline_refinery_err_terminal"
      pyashStatePipelineRefineryDoneSignatureErr pyashStatePipelineRefineryDoneSignatureErr
      pyashGF_pipeline_refinery_err_terminal_closure
  , mkCanaryLink "pyash_gf_pipeline_chirp_do"
      pyashStatePipelineChirpDerive pyashStatePipelineChirpDoneOk
      pyashGF_pipeline_chirp_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_chirp_dispatch_to_done"
      pyashStatePipelineChirpDispatched pyashStatePipelineChirpDoneOk
      pyashGF_pipeline_chirp_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_chirp_running_to_done"
      pyashStatePipelineChirpRunning pyashStatePipelineChirpDoneOk
      pyashGF_pipeline_chirp_running_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_chirp_err_signature"
      pyashStatePipelineChirpMismatch pyashStatePipelineChirpDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_pipeline_chirp_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_pipeline_chirp_err_terminal"
      pyashStatePipelineChirpDoneSignatureErr pyashStatePipelineChirpDoneSignatureErr
      pyashGF_pipeline_chirp_err_terminal_closure
  , mkCanaryLink "pyash_gf_pipeline_reentry_do"
      pyashStatePipelineReentryDerive pyashStatePipelineReentryDoneOk
      pyashGF_pipeline_reentry_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_reentry_cycle_do"
      pyashStatePipelineReentryDerive pyashStatePipelineReentryDoneOk
      pyashGF_pipeline_reentry_cycle_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_reentry_dispatch_to_done"
      pyashStatePipelineReentryDispatched pyashStatePipelineReentryDoneOk
      pyashGF_pipeline_reentry_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_reentry_running_to_done"
      pyashStatePipelineReentryRunning pyashStatePipelineReentryDoneOk
      pyashGF_pipeline_reentry_running_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_reentry_err_signature"
      pyashStatePipelineReentryMismatch pyashStatePipelineReentryDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_pipeline_reentry_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_pipeline_reentry_err_terminal"
      pyashStatePipelineReentryDoneSignatureErr pyashStatePipelineReentryDoneSignatureErr
      pyashGF_pipeline_reentry_err_terminal_closure
  , mkCanaryLink "pyash_gf_pipeline_dispatch_to_done"
      pyashStatePipelineDispatched pyashStatePipelineDoneOk
      pyashGF_pipeline_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_running_to_done"
      pyashStatePipelineRunning pyashStatePipelineDoneOk
      pyashGF_pipeline_running_closure_bridge
  , mkCanaryLink "pyash_gf_compile_do"
      pyashStateCompileDerive pyashStateCompileDoneOk
      pyashGF_compile_clause_closure_bridge
  , mkCanaryLink "pyash_gf_compile_dispatch_to_done"
      pyashStateCompileDispatched pyashStateCompileDoneOk
      pyashGF_compile_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_compile_running_to_done"
      pyashStateCompileRunning pyashStateCompileDoneOk
      pyashGF_compile_running_closure_bridge
  , mkCanaryLink "pyash_gf_compile_err_signature"
      pyashStateCompileMismatch pyashStateCompileDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_compile_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_compile_err_terminal"
      pyashStateCompileDoneSignatureErr pyashStateCompileDoneSignatureErr
      pyashGF_compile_err_terminal_closure
  , mkCanaryLink "pyash_gf_import_do"
      pyashStateImportDerive pyashStateImportDoneOk
      pyashGF_import_clause_closure_bridge
  , mkCanaryLink "pyash_gf_import_dispatch_to_done"
      pyashStateImportDispatched pyashStateImportDoneOk
      pyashGF_import_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_import_running_to_done"
      pyashStateImportRunning pyashStateImportDoneOk
      pyashGF_import_running_closure_bridge
  , mkCanaryLink "pyash_gf_import_err_signature"
      pyashStateImportMismatch pyashStateImportDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_import_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_import_err_terminal"
      pyashStateImportDoneSignatureErr pyashStateImportDoneSignatureErr
      pyashGF_import_err_terminal_closure
  , mkCanaryLink "pyash_gf_download_do"
      pyashStateDownloadDerive pyashStateDownloadDoneOk
      pyashGF_download_clause_closure_bridge
  , mkCanaryLink "pyash_gf_download_dispatch_to_done"
      pyashStateDownloadDispatched pyashStateDownloadDoneOk
      pyashGF_download_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_download_running_to_done"
      pyashStateDownloadRunning pyashStateDownloadDoneOk
      pyashGF_download_running_closure_bridge
  , mkCanaryLink "pyash_gf_download_err_signature"
      pyashStateDownloadMismatch pyashStateDownloadDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_download_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_download_err_terminal"
      pyashStateDownloadDoneSignatureErr pyashStateDownloadDoneSignatureErr
      pyashGF_download_err_terminal_closure
  , mkCanaryLink "pyash_gf_translation_do"
      pyashStateTranslationDerive pyashStateTranslationDoneOk
      pyashGF_translation_clause_closure_bridge
  , mkCanaryLink "pyash_gf_translation_dispatch_to_done"
      pyashStateTranslationDispatched pyashStateTranslationDoneOk
      pyashGF_translation_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_translation_running_to_done"
      pyashStateTranslationRunning pyashStateTranslationDoneOk
      pyashGF_translation_running_closure_bridge
  , mkCanaryLink "pyash_gf_translation_err_signature"
      pyashStateTranslationMismatch pyashStateTranslationDoneSignatureErr
      (PyashCoreReducesStar.single
        pyashGF_translation_invalid_signature_negative_bridge)
  , mkCanaryLink "pyash_gf_translation_err_terminal"
      pyashStateTranslationDoneSignatureErr pyashStateTranslationDoneSignatureErr
      pyashGF_translation_err_terminal_closure
  ]

theorem pyashGFAllCanaryNTTLinkLabels :
    pyashGFAllCanaryNTTLinks.map (fun link => link.label) =
      pyashGFCanaryCasePatterns.map (fun caseTriple => caseTriple.1) := by
  decide +kernel

/-- Every linkage record carries a valid OSLF closure witness and NTT morphism. -/
theorem pyashGFAllCanaryNTTLinks_sound :
    ∀ link ∈ pyashGFAllCanaryNTTLinks, Nonempty (Hom link.ntObj link.ntObj) := by
  intro link _hmem
  exact ⟨link.ntSelfHom⟩

end Mettapedia.OSLF.Framework.PyashGFNTTLinkage
