import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceFrontend
import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologDatalogControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinter
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend

/-! Actual native Prolog packets and ordinary Datalog packets meet at the
same independent program IR and existing compiler preparation. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Logic.Prolog
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.Datalog

def main (arguments : List String) : IO Unit := do
  let [dialect,directory] := arguments | throw (IO.userError "expected iso|swi|datalog and fixture directory")
  let root : System.FilePath := directory
  if dialect == "datalog" then
    let input ← IO.FS.readFile (root / "common.dl")
    let .ok [packet] := SpaceSemantics.readSource (← IO.FS.readFile (root / "common.dl.packet"))
      | throw (IO.userError "expected one Datalog packet")
    let .ok program := SouffleDatalog.Frontend.read input packet
      | throw (IO.userError "Datalog frontend refused the printed source")
    unless program == PrologDatalogControls.expected do throw (IO.userError "Datalog IR differs")
    IO.println "(PrologDatalogSourceAgreement true)"
  else
    let profile ← match dialect with
      | "iso" => pure ReaderProfile.iso | "swi" => pure ReaderProfile.swi
      | _ => throw (IO.userError "unknown profile")
    let mut forms := []
    for i in List.range 4 do
      let input ← IO.FS.readFile (root / (toString i ++ ".pl"))
      let .ok [packet] := SpaceSemantics.readSource (← IO.FS.readFile (root / (toString i ++ ".packet")))
        | throw (IO.userError "expected one retained sentence packet")
      let .expression [.symbol "result",tree,.symbol "nil"] := packet
        | throw (IO.userError "invalid source packet")
      let .ok retained := PrologSourceFrontend.read profile input tree
        | throw (IO.userError "checked Prolog frontend refused a sentence")
      let .ok form := ReaderSource.classify retained.lowered.term
        | throw (IO.userError "invalid clause")
      forms := forms ++ [form]
    let some program := PrologDatalog.program? PrologDatalogControls.declarations forms
      | throw (IO.userError "source clauses are outside Datalog admission")
    unless program == PrologDatalogControls.expected do throw (IO.userError "Prolog-derived Datalog IR differs")
    let .ok _ := DatalogIR.Executable.prepare program []
      | throw (IO.userError "existing Datalog compiler refused the IR")
    let .ok printed := SouffleDatalog.SourcePrinter.print? program
      | throw (IO.userError "Datalog printer refused the IR")
    IO.FS.writeFile (root / "common.dl") printed
    IO.println s!"(PrologDatalogAdmission {dialect} true true)"
