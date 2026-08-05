import Mettapedia.GSLT.LanguageDef.LF.DTTBenchProofCarryingConversionReplay
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderMeTTaRender

/-!
# MeTTa export for the proof-carrying DTTBench calibration replay

The exporter applies one generic proof producer to every frozen calibration
entry and serializes both completed normal-form paths.  The resulting MeTTa
artifact rechecks the exact validated conversion source, both conversion proof
trees, and the normalized indexed-LF typing judgment.
-/

namespace Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingMeTTaExport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFDTTBenchConversionReplay
open Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingConversionReplay
open Mettapedia.GSLT.LanguageDef.LFFirstOrderCertifiedNormalization
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion
open Mettapedia.GSLT.LanguageDef.LFFirstOrderMeTTaRender
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

private def requireSome (message : String) : Option α → Except String α
  | some value => pure value
  | none => throw message

private def renderEntry
    (indexed :
      LFDTTBenchConversionReplay.ReplayCase × Nat) :
    Except String String := do
  let entry := indexed.1
  let index := indexed.2
  let certificate ←
    requireSome s!"normal-form certificate unavailable for {entry.name}"
      (certificate? entry)
  pure <|
    s!"; calibration entry {index}: {entry.name}\n" ++
    s!"(= (dtt-pc-witness-{index})\n" ++
    renderConvertedWitness "SNil"
      certificate.left certificate.right ++
    ")\n" ++
    "!(assertEqual\n" ++
    s!"  (dtt-pc-check (dtt-pc-witness-{index}))\n" ++
    s!"  (Ok (CheckedPrf ANil " ++
      s!"{renderTerm certificate.left.target} " ++
      s!"{renderTerm certificate.right.target})))\n"

private def render : Except String String := do
  let renderedEntries ←
    LFDTTBenchConversionReplay.cases.zipIdx.mapM renderEntry
  pure <|
    "!(import! &self kernel_signature_lf_indexed_conversion_frontend_bridge_lib_v0)\n\n" ++
    s!"(= (dtt-pc-source) {renderGSLTSource source})\n" ++
    "(= (dtt-pc-check $witness)\n" ++
    "  (kw-lf-fo-check-with-source (dtt-pc-source) $witness))\n\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-validation-v1 (dtt-pc-source))\n" ++
    "  SourceAcceptedV1)\n\n" ++
    String.intercalate "\n" renderedEntries ++
    "\n!(DTTBenchProofCarryingConversionLiveSummary 31 31 0)\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      match render with
      | .error message =>
          IO.eprintln message
          pure 1
      | .ok output =>
          IO.FS.writeFile outputPath output
          IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
          pure 0
  | _ =>
      IO.eprintln "usage: DTTBenchProofCarryingMeTTaExport <output.metta>"
      pure 1

end Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingMeTTaExport.main arguments
