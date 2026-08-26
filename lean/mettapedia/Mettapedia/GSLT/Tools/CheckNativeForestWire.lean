import Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness

/-!
# Native packed-forest wire qualification tool

This opt-in executable checks that a `CNF1` snapshot produced by a native
parser has the exact canonical encoding specified in Lean and crosses the
physical-to-semantic boundary as a completed neutral forest view.
-/

namespace Mettapedia.GSLT.Tools.CheckNativeForestWire

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityValidation
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness

private def usage : String :=
  "usage: CheckNativeForestWire backend snapshot.cnf1"

def run (args : List String) : IO UInt32 := do
  match args with
  | [backend, inputPath] =>
      let bytes ← IO.FS.readBinFile inputPath
      let byteList := bytes.data.toList
      match decodeSnapshot? byteList with
      | none =>
          IO.eprintln "native forest snapshot is not a canonical CNF1 packet"
          pure 1
      | some snapshot =>
          if encodeSnapshot snapshot != byteList then
            IO.eprintln "native forest snapshot is not canonically encoded"
            pure 1
          else
            match snapshot.completedView? with
            | none =>
                IO.eprintln
                  "native forest snapshot is not a completed semantic view"
                pure 1
            | some view =>
                if validateStructure view && validatePrefixIndexOrder view then
                  IO.println s!"(NativeForestWireSummary {backend} {view.nodes.length} {view.choices.length} {view.roots.length} {view.codepoints.length} {snapshot.sourcePassCount})"
                  pure 0
                else
                  IO.eprintln
                    "native forest snapshot fails verified structure, reachability, or finite-prefix ordering"
                  pure 1
  | _ =>
      IO.eprintln usage
      pure 1

end Mettapedia.GSLT.Tools.CheckNativeForestWire

def main (args : List String) : IO UInt32 :=
  Mettapedia.GSLT.Tools.CheckNativeForestWire.run args
