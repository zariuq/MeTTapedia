import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardConformanceCorpus
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

/-!
# Export of the call-guard StructuredC artifacts

The wires consumed by the StructuredC emitter and the checker: the
StructuredC language, the generated cold compiler program, the generated hot
dispatch program, the generated hot transition program with its primitive
catalog, and the conformance corpus.  The command-line tools are thin shells
over the export entry points; the content lives here so that the root build
gate covers it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardConformanceCorpus
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
  (readyReceipt externalReceipt)

/-- Canonical structural Pattern wire of the generated cold program. -/
def coldProgramWire : String := renderPattern generatedColdProgram ++ "\n"

/-- Canonical structural Pattern wire of the generated hot dispatch program. -/
def hotProgramWire : String := renderPattern generatedHotModeProgram ++ "\n"

/-- Canonical structural Pattern wire of the generated hot transition
program: the source-derived hot body in its ABI wrapper. -/
def hotTransitionProgramWire : String := renderPattern generatedHotProgram ++ "\n"

/-- The externals of a StructuredC program. -/
def programExternals? : Pattern → Option Pattern
  | .apply "structured-c:program" [externals, _] => some externals
  | _ => none

/-- Every hot ABI name, in catalog order. -/
def hotPrimitiveNames : List String :=
  projections.map Projection.externalName ++ frameQueries.map FrameQuery.externalName ++
    decisions.map Decision.externalName ++ deltas.map Delta.externalName

/-- The primitive catalog: the cold externals, the hot externals, and the
receipt every hot primitive leaves, for the checker to compare with the ABI
headers. -/
def primitiveCatalogPattern : Pattern :=
  .apply "petta-call-guard:primitive-catalog" [
    (programExternals? generatedColdProgram).getD (.apply "structured-c:external-functions-nil" []),
    (programExternals? generatedHotProgram).getD (.apply "structured-c:external-functions-nil" []),
    hotPrimitiveNames.foldr
      (fun name rest =>
        .apply "petta-call-guard:receipts-cons"
          [.apply "petta-call-guard:receipt" [.apply name [], externalReceipt name readyReceipt],
            rest])
      (.apply "petta-call-guard:receipts-nil" [])]

def primitiveCatalogWire : String := renderPattern primitiveCatalogPattern ++ "\n"

/-- The conformance corpus wire. -/
def conformanceCorpusWire : String := corpusWire

/-- The StructuredC language wire. -/
def languageWire : String := StructuredC.wire

theorem coldProgramWire_nonempty : coldProgramWire ≠ "" := by
  simp [coldProgramWire]

theorem hotProgramWire_nonempty : hotProgramWire ≠ "" := by
  simp [hotProgramWire]

theorem hotTransitionProgramWire_nonempty : hotTransitionProgramWire ≠ "" := by
  simp [hotTransitionProgramWire]

theorem primitiveCatalogWire_nonempty : primitiveCatalogWire ≠ "" := by
  simp [primitiveCatalogWire]

/-- The catalog lists every hot ABI name exactly once. -/
theorem hotPrimitiveNames_nodup : hotPrimitiveNames.Nodup := by
  decide +kernel

def exportCold (arguments : List String) : IO UInt32 := do
  match arguments with
  | [languagePath, programPath] =>
      IO.FS.writeFile languagePath languageWire
      IO.FS.writeFile programPath coldProgramWire
      pure 0
  | _ =>
      IO.eprintln
        "usage: export-petta-mainline-call-guard-structured-c <language> <program>"
      pure 2

def exportHot (arguments : List String) : IO UInt32 := do
  match arguments with
  | [programPath] =>
      IO.FS.writeFile programPath hotProgramWire
      pure 0
  | _ =>
      IO.eprintln
        "usage: export-petta-mainline-call-guard-hot-structured-c <program>"
      pure 2

def exportHotTransition (arguments : List String) : IO UInt32 := do
  match arguments with
  | [programPath, catalogPath] =>
      IO.FS.writeFile programPath hotTransitionProgramWire
      IO.FS.writeFile catalogPath primitiveCatalogWire
      pure 0
  | _ =>
      IO.eprintln
        "usage: export-petta-mainline-call-guard-hot-transition-structured-c <program> <catalog>"
      pure 2

def exportCorpus (arguments : List String) : IO UInt32 := do
  match arguments with
  | [corpusPath] =>
      IO.FS.writeFile corpusPath conformanceCorpusWire
      pure 0
  | _ =>
      IO.eprintln "usage: export-petta-mainline-call-guard-conformance-corpus <corpus>"
      pure 2

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport
