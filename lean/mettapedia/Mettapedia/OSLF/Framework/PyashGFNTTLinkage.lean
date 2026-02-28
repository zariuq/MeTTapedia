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
  Sigma.mk (PLNObj.Concept "pyash_canary") (⊥ : Evidence)

/-- Canonical reflexive NTT morphism at the canary anchor. -/
def pyashCanaryNTTAnchorId : Hom pyashCanaryNTTAnchor pyashCanaryNTTAnchor :=
  PLift.up (le_rfl : (⊥ : Evidence) ≤ ⊥)

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
      pyashStateConfigureDefDerive pyashStateConfigureDefDoneOk
      pyashGF_configure_command_map_def_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_sandbox_map_def"
      pyashStateConfigureDefDerive pyashStateConfigureDefDoneOk
      pyashGF_configure_sandbox_map_def_clause_closure_bridge
  , mkCanaryLink "pyash_gf_configure_verify_loop_map_def"
      pyashStateConfigureDefDerive pyashStateConfigureDefDoneOk
      pyashGF_configure_verify_loop_map_def_clause_closure_bridge
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
      pyashStateWorldDerive pyashStateWorldDoneOk
      pyashGF_world_path_clause_closure_bridge
  , mkCanaryLink "pyash_gf_world_dispatch_to_done"
      pyashStateWorldDispatched pyashStateWorldDoneOk
      pyashGF_world_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_world_running_to_done"
      pyashStateWorldRunning pyashStateWorldDoneOk
      pyashGF_world_running_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_do"
      pyashStatePipelineDerive pyashStatePipelineDoneOk
      pyashGF_pipeline_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_chirp_do"
      pyashStatePipelineDerive pyashStatePipelineDoneOk
      pyashGF_pipeline_chirp_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_reentry_do"
      pyashStatePipelineDerive pyashStatePipelineDoneOk
      pyashGF_pipeline_reentry_clause_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_dispatch_to_done"
      pyashStatePipelineDispatched pyashStatePipelineDoneOk
      pyashGF_pipeline_dispatched_closure_bridge
  , mkCanaryLink "pyash_gf_pipeline_running_to_done"
      pyashStatePipelineRunning pyashStatePipelineDoneOk
      pyashGF_pipeline_running_closure_bridge
  , mkCanaryLink "pyash_gf_compile_do"
      pyashStateCompileDerive pyashStateCompileDoneOk
      pyashGF_compile_clause_closure_bridge
  , mkCanaryLink "pyash_gf_import_do"
      pyashStateImportDerive pyashStateImportDoneOk
      pyashGF_import_clause_closure_bridge
  , mkCanaryLink "pyash_gf_download_do"
      pyashStateDownloadDerive pyashStateDownloadDoneOk
      pyashGF_download_clause_closure_bridge
  , mkCanaryLink "pyash_gf_translation_do"
      pyashStateTranslationDerive pyashStateTranslationDoneOk
      pyashGF_translation_clause_closure_bridge
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
