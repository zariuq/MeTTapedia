/-
Fixture agreement of the two `.module` readers: CeTTa's parse of each upstream example with the grammar
`module/module_v1.cf`, decoded by `ModuleSource.LbnfDecode`, is the data that `#module_file`
reads in Lean. Run by `check_module_reader.sh`, which writes CeTTa's parses first.
Every malformed packet or disagreement fails the process. This fixture check
does not certify completeness of a packed parse forest.
-/
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../lean/mettapedia/artifacts/upstream-authoring-20261008/UnivAlg.module"
#module_file "../../../lean/mettapedia/artifacts/upstream-authoring-20261008/Rholang.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/RegexCore.module"
#module_file "../module/godelclaw/RetryWake.module"
#module_file "../module/godelclaw/StreamEvents.module"
#module_file "../module/godelclaw/ToolCalls.module"
#module_file "../module/godelclaw/ComponentAPI.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Aliased.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/AmbientComm.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/AmbientNu.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/CCS.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/CCSRec.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/CCSRep.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Coins.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Counting.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Courier.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Crashing.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/FullLambda.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Halting.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Lambda.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Levels.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Peano.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Petri.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Pi.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/PiParallel.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Rho.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Spinner.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/TinyML.module"
#module_file "../../../lean/mettapedia/artifacts/oslf-languages/Wrapped.module"
#module_file "../module/controls/Spellings.module"
#module_file "../module/controls/QuotedVariables.module"
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def readings : List (String × ModuleData) := [("UnivAlg", UnivAlg.module), ("Rholang", Rholang.module),
    ("RegexCore", RegexCore.module), ("RetryWake", GodelClawRetryWake.module),
    ("StreamEvents", StreamEvents.module), ("ToolCalls", ToolCalls.module),
    ("ComponentAPI", ComponentAPI.module),
    ("Aliased", AliasedAsWritten.module),
    ("AmbientComm", MobileAmbientsComm.module),
    ("AmbientNu", MobileAmbientsNu.module),
    ("CCS", CCS.module),
    ("CCSRec", CCSRec.module),
    ("CCSRep", CCSRep.module),
    ("Coins", Coins.module),
    ("Counting", Counting.module),
    ("Courier", Courier.module),
    ("Crashing", Crashing.module),
    ("FullLambda", FullLambda.module),
    ("Halting", Halting.module),
    ("Lambda", LambdaCalc.module),
    ("Levels", Levels.module),
    ("Peano", LambdaPiModulo.module),
    ("Petri", Petri.module),
    ("Pi", PiCalc.module),
    ("PiParallel", PiParallelFragment.module),
    ("Rho", RhoCalc.module),
    ("Spinner", Spinner.module),
    ("TinyML", TinyML.module),
    ("Wrapped", WrappedAsWritten.module),
    ("Spellings", Spellings.module),
    ("QuotedVariables", QuotedVariables.module)]

def check (input : System.FilePath) : IO Unit := do
  let source ← IO.FS.readFile input
  match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource source with
  | .error e => throw (IO.userError s!"read error {e}")
  | .ok [.expression (.symbol "ModuleReads" :: parses)] =>

      unless parses.length == readings.length do
        throw (IO.userError s!"expected {readings.length} parses, got {parses.length}")
      for ((label, lean), parsed) in readings.zip parses do
        match LbnfDecode.acceptedTrees parsed >>= fun trees => match trees with
            | [tree] => LbnfDecode.decode tree
            | _ => .error "expected one tree" with
        | .error e => throw (IO.userError s!"(ModuleReaderControl {label} false) decode error {e}")
        | .ok decoded =>
            if reprStr decoded == reprStr lean then IO.println s!"(ModuleReaderControl {label} true)"
            else
              let a := (reprStr decoded).toList
              let b := (reprStr lean).toList
              let i := (List.zip a b).findIdx (fun p => p.1 != p.2)
              throw (IO.userError s!"(ModuleReaderControl {label} false) differ at {i}: {String.ofList (a.drop (i-80) |>.take 220)} ||| {String.ofList (b.drop (i-80) |>.take 220)}")
  | .ok other => throw (IO.userError s!"unexpected packet shape ({other.length} expressions)")

def main (args : List String) : IO Unit := do
  match args with
  | ["--labels"] => readings.forM fun entry => IO.println entry.1
  | [] => check "../../metta/gslt/tools/out/module_reads.metta"
  | [input] => check input
  | _ => throw (IO.userError "usage: check_module_reader.lean [packet-file]")
