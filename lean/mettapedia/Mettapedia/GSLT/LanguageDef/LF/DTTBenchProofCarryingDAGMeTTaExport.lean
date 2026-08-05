import Mettapedia.GSLT.LanguageDef.InferenceProofDAGCompilation
import Mettapedia.GSLT.LanguageDef.InferencePatternSharing
import Mettapedia.GSLT.LanguageDef.LF.DTTBenchProofCarryingConversionReplay
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderMeTTaRender

/-!
# Compact MeTTa export for the proof-carrying DTTBench calibration replay

This exporter is the DAG counterpart of `DTTBenchProofCarryingMeTTaExport`.
It applies the same generic proof producer to the same frozen entries, then
hash-conses structurally equal subproofs before serialization.  The generated
artifact must still pass the live source-indexed DAG checker and the indexed
LF kernel.  Shared patterns and final-use releases are untrusted transport
optimizations, not trusted shortcuts.
-/

namespace Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingDAGMeTTaExport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceProofDAGCompilation
open Mettapedia.GSLT.LanguageDef.InferencePatternSharing
open Mettapedia.GSLT.LanguageDef.LFDTTBenchConversionReplay
open Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingConversionReplay
open Mettapedia.GSLT.LanguageDef.LFFirstOrderCertifiedNormalization
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion
open Mettapedia.GSLT.LanguageDef.LFFirstOrderMeTTaRender
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

private def requireSome (message : String) : Option α → Except String α
  | some value => pure value
  | none => throw message

private def requireFixture (message : String) (fixture : Bool) :
    Except String Unit :=
  if fixture then pure () else throw message

private def dagChunkSize : Nat := 64
private def processDagChunkSize : Nat := 64
private def patternExpansionDepth : Nat := 2

private structure RenderedDAGConvertedWitness where
  transportDefinitions : String
  witness : String

private structure RenderedProcessBundle where
  common : String
  termTemplates : List String
  typeTemplates : List String
  finalTemplate : String

private def streamStatePlaceholder : String :=
  "__GIC_PURE_STREAM_STATE__"

private def termStatePlaceholder : String :=
  "__GIC_PURE_TERM_STATE__"

private def typeStatePlaceholder : String :=
  "__GIC_PURE_TYPE_STATE__"

private def renderDAGConvertedWitness
    (index : Nat)
    (signature : String)
    (termCertificate typeCertificate :
      LFFirstOrderOperationalCorrespondence.ConversionCertificate) :
    RenderedDAGConvertedWitness :=
  let termDAG := compileRawProof termCertificate.proof
  let typeDAG := compileRawProof typeCertificate.proof
  let shared := shareProofDAGPair termDAG typeDAG
  let termStreaming := annotateStreamingProofDAG shared.left
  let typeStreaming := annotateStreamingProofDAG shared.right
  let patternStem := s!"dtt-pc-dag-pattern-{index}"
  let termChunkStem := s!"dtt-pc-dag-term-{index}"
  let typeChunkStem := s!"dtt-pc-dag-type-{index}"
  let termChunks := termStreaming.nodes.toChunks dagChunkSize
  let typeChunks := typeStreaming.nodes.toChunks dagChunkSize
  { transportDefinitions :=
      renderPatternDefinitionsExpanded patternExpansionDepth patternStem
        shared.patterns ++ "\n" ++
      renderReferencedStreamingDAGChunkDefinitions termChunkStem patternStem
        termChunks ++ "\n" ++
      renderReferencedStreamingDAGChunkDefinitions typeChunkStem patternStem
        typeChunks
    witness :=
      "  (KWCheckConvertedStreamingDAGChunks\n" ++
        s!"    {signature}\n" ++
        s!"    {renderTerm termCertificate.source}\n" ++
        s!"    {renderTerm termCertificate.target}\n" ++
        s!"    {shared.left.rootId}\n" ++
        s!"    {renderReferencedStreamingDAGChunkReferences termChunkStem termChunks}\n" ++
        s!"    {renderTerm typeCertificate.source}\n" ++
        s!"    {renderTerm typeCertificate.target}\n" ++
        s!"    {shared.right.rootId}\n" ++
        s!"    {renderReferencedStreamingDAGChunkReferences typeChunkStem typeChunks})" }

private def renderProcessChunkTemplate
    (patternStem : String)
    (chunk : List ReferencedStreamingDAGNode) : String :=
  "!(import! &self common.metta)\n\n" ++
    "(= (dtt-pc-process-chunk)\n" ++
    s!"  {renderReferencedStreamingDAGNodes patternStem chunk})\n\n" ++
    "!(gslt-source-step-dag-pure-streaming-v1\n" ++
    "  (dtt-pc-process-source)\n" ++
    s!"  {streamStatePlaceholder}\n" ++
    "  (dtt-pc-process-chunk))\n"

private def renderProcessBundle
    (index : Nat)
    (signature : String)
    (termCertificate typeCertificate :
      LFFirstOrderOperationalCorrespondence.ConversionCertificate) :
    RenderedProcessBundle :=
  let termDAG := compileRawProof termCertificate.proof
  let typeDAG := compileRawProof typeCertificate.proof
  let shared := shareProofDAGPair termDAG typeDAG
  let termStreaming := annotateStreamingProofDAG shared.left
  let typeStreaming := annotateStreamingProofDAG shared.right
  let patternStem := s!"dtt-pc-process-pattern-{index}"
  let termChunks := termStreaming.nodes.toChunks processDagChunkSize
  let typeChunks := typeStreaming.nodes.toChunks processDagChunkSize
  let common :=
    "!(import! &self " ++
      "kernel_signature_lf_indexed_conversion_frontend_bridge_lib_v0.metta)\n\n" ++
    s!"(= (dtt-pc-process-source) {renderGSLTSource source})\n\n" ++
    renderPatternDefinitionsExpanded patternExpansionDepth patternStem
      shared.patterns ++ "\n"
  let finalTemplate :=
    "!(import! &self common.metta)\n\n" ++
    "!(assertEqual\n" ++
    "  (kw-lf-fo-check-dag-pure-stream-states-with-source\n" ++
    "    (dtt-pc-process-source)\n" ++
    s!"    {signature}\n" ++
    s!"    {renderTerm termCertificate.source}\n" ++
    s!"    {renderTerm termCertificate.target}\n" ++
    s!"    {shared.left.rootId}\n" ++
    s!"    {termStatePlaceholder}\n" ++
    s!"    {renderTerm typeCertificate.source}\n" ++
    s!"    {renderTerm typeCertificate.target}\n" ++
    s!"    {shared.right.rootId}\n" ++
    s!"    {typeStatePlaceholder})\n" ++
    "  (Ok (CheckedPrf ANil " ++
      s!"{renderTerm termCertificate.target} " ++
      s!"{renderTerm typeCertificate.target})))\n" ++
    s!"!(DTTBenchPureProcessChainSummary {index} 1 1 0)\n"
  { common
    termTemplates :=
      termChunks.map (renderProcessChunkTemplate patternStem)
    typeTemplates :=
      typeChunks.map (renderProcessChunkTemplate patternStem)
    finalTemplate }

private def renderEntry
    (indexed : LFDTTBenchConversionReplay.ReplayCase × Nat) :
    Except String String := do
  let entry := indexed.1
  let index := indexed.2
  let certificate ←
    requireSome s!"normal-form certificate unavailable for {entry.name}"
      (certificate? entry)
  let rendered :=
    renderDAGConvertedWitness index "SNil"
      certificate.left certificate.right
  pure <|
    s!"; calibration entry {index}: {entry.name}\n" ++
    rendered.transportDefinitions ++ "\n\n" ++
    s!"(= (dtt-pc-dag-witness-{index})\n" ++
    rendered.witness ++
    ")\n" ++
    "!(assertEqual\n" ++
    s!"  (dtt-pc-dag-check (dtt-pc-dag-witness-{index}))\n" ++
    s!"  (Ok (CheckedPrf ANil " ++
      s!"{renderTerm certificate.left.target} " ++
      s!"{renderTerm certificate.right.target})))\n"

private def validateProducer : Except String Unit := do
  requireFixture "duplicated-subproof sharing fixture failed"
    duplicatedSharingFixture
  requireFixture "distinct-argument separation fixture failed"
    distinctArgumentsFixture
  requireFixture "final-use annotation fixture failed"
    finalUseAnnotationFixture

private def renderHeader : String :=
  "!(import! &self kernel_signature_lf_indexed_conversion_frontend_bridge_lib_v0)\n\n" ++
    s!"(= (dtt-pc-dag-source) {renderGSLTSource source})\n" ++
    "(= (dtt-pc-dag-check $witness)\n" ++
    "  (kw-lf-fo-check-dag-pure-streaming-with-source " ++
      "(dtt-pc-dag-source) $witness))\n\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-validation-v1 (dtt-pc-dag-source))\n" ++
    "  SourceAcceptedV1)\n\n"

private def renderFooter : String :=
  "\n!(DTTBenchProofCarryingConversionDAGLiveSummary 31 31 0)\n"

private def renderShardFooter (index : Nat) : String :=
  s!"\n!(DTTBenchProofCarryingConversionDAGShardLiveSummary {index} 1 1 0)\n"

private def shardIndex (index : Nat) : String :=
  if index < 10 then "0" ++ toString index else toString index

private def shardFileName (index : Nat) : String :=
  s!"dttbench_proof_carrying_conversion_dag_shard_{shardIndex index}_generated_v0.metta"

private def processChunkFileName
    (kind : String) (index : Nat) : String :=
  let suffix :=
    if index < 10 then s!"00{index}"
    else if index < 100 then s!"0{index}"
    else toString index
  s!"{kind}_chunk_{suffix}.template.metta"

private def writeEntries
    (handle : IO.FS.Handle) :
    List (LFDTTBenchConversionReplay.ReplayCase × Nat) →
      Nat → IO (Except String Nat)
  | [], bytes => pure (.ok bytes)
  | indexed :: entries, bytes =>
      match renderEntry indexed with
      | .error message => pure (.error message)
      | .ok output => do
          handle.putStr output
          if entries.isEmpty then
            writeEntries handle entries (bytes + output.toUTF8.size)
          else
            handle.putStr "\n"
            writeEntries handle entries (bytes + output.toUTF8.size + 1)

private def writeShard
    (outputDirectory : String)
    (indexed : LFDTTBenchConversionReplay.ReplayCase × Nat) :
    IO (Except String Nat) :=
  match renderEntry indexed with
  | .error message => pure (.error message)
  | .ok output => do
      let footer := renderShardFooter indexed.2
      let outputPath := outputDirectory ++ "/" ++ shardFileName indexed.2
      IO.FS.withFile outputPath .write fun handle => do
        handle.putStr renderHeader
        handle.putStr output
        handle.putStr footer
      pure (.ok (renderHeader.toUTF8.size + output.toUTF8.size +
        footer.toUTF8.size))

private def writeShards
    (outputDirectory : String) :
    List (LFDTTBenchConversionReplay.ReplayCase × Nat) →
      Nat → IO (Except String Nat)
  | [], bytes => pure (.ok bytes)
  | indexed :: entries, bytes => do
      match ← writeShard outputDirectory indexed with
      | .error message => pure (.error message)
      | .ok shardBytes =>
          writeShards outputDirectory entries (bytes + shardBytes)

private def writeProcessTemplates
    (outputDirectory kind : String) :
    List (String × Nat) → IO Nat
  | [] => pure 0
  | indexed :: templates => do
      let path :=
        outputDirectory ++ "/" ++
          processChunkFileName kind indexed.2
      IO.FS.writeFile path indexed.1
      let rest ← writeProcessTemplates outputDirectory kind templates
      pure (indexed.1.toUTF8.size + rest)

private def writeProcessBundle
    (outputDirectory : String)
    (indexed : LFDTTBenchConversionReplay.ReplayCase × Nat) :
    IO (Except String Nat) :=
  match certificate? indexed.1 with
  | none =>
      pure (.error
        s!"normal-form certificate unavailable for {indexed.1.name}")
  | some certificate => do
      let bundle :=
        renderProcessBundle indexed.2 "SNil"
          certificate.left certificate.right
      IO.FS.createDirAll outputDirectory
      IO.FS.writeFile
        (outputDirectory ++ "/common.metta") bundle.common
      let termBytes ←
        writeProcessTemplates outputDirectory "term"
          bundle.termTemplates.zipIdx
      let typeBytes ←
        writeProcessTemplates outputDirectory "type"
          bundle.typeTemplates.zipIdx
      IO.FS.writeFile
        (outputDirectory ++ "/final.template.metta")
        bundle.finalTemplate
      let manifest :=
        "schema\tgic-pure-process-bundle-v1\n" ++
        s!"entry_index\t{indexed.2}\n" ++
        s!"term_chunk_count\t{bundle.termTemplates.length}\n" ++
        s!"type_chunk_count\t{bundle.typeTemplates.length}\n" ++
        "expected_summary\t" ++
          s!"[(DTTBenchPureProcessChainSummary {indexed.2} 1 1 0)]\n"
      IO.FS.writeFile
        (outputDirectory ++ "/manifest.tsv") manifest
      pure (.ok
        (bundle.common.toUTF8.size + termBytes + typeBytes +
          bundle.finalTemplate.toUTF8.size + manifest.toUTF8.size))

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      match validateProducer with
      | .error message =>
          IO.eprintln message
          pure 1
      | .ok () =>
          IO.FS.withFile outputPath .write fun handle => do
            handle.putStr renderHeader
            let initialBytes := renderHeader.toUTF8.size
            match ← writeEntries handle
                LFDTTBenchConversionReplay.cases.zipIdx initialBytes with
            | .error message =>
                IO.eprintln message
                pure 1
            | .ok bytes =>
                handle.putStr renderFooter
                let totalBytes := bytes + renderFooter.toUTF8.size
                IO.println s!"wrote {totalBytes} bytes to {outputPath}"
                pure 0
  | ["--shard-directory", outputDirectory] =>
      match validateProducer with
      | .error message =>
          IO.eprintln message
          pure 1
      | .ok () =>
          IO.FS.createDirAll outputDirectory
          match ← writeShards outputDirectory
              LFDTTBenchConversionReplay.cases.zipIdx 0 with
          | .error message =>
              IO.eprintln message
              pure 1
          | .ok bytes =>
              IO.println
                s!"wrote 31 proof-carrying DAG shards ({bytes} total bytes) to {outputDirectory}"
              pure 0
  | ["--process-entry-directory", indexString, outputDirectory] =>
      match validateProducer with
      | .error message =>
          IO.eprintln message
          pure 1
      | .ok () =>
          match indexString.toNat? with
          | none =>
              IO.eprintln s!"invalid entry index: {indexString}"
              pure 1
          | some index =>
              match LFDTTBenchConversionReplay.cases[index]? with
              | none =>
                  IO.eprintln s!"entry index out of range: {index}"
                  pure 1
              | some entry =>
                  match ← writeProcessBundle outputDirectory (entry, index) with
                  | .error message =>
                      IO.eprintln message
                      pure 1
                  | .ok bytes =>
                      IO.println
                        s!"wrote process bundle for entry {index} ({bytes} total bytes) to {outputDirectory}"
                      pure 0
  | _ =>
      IO.eprintln
        "usage: DTTBenchProofCarryingDAGMeTTaExport <output.metta> | --shard-directory <directory> | --process-entry-directory <index> <directory>"
      pure 1

end Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingDAGMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingDAGMeTTaExport.main
    arguments
