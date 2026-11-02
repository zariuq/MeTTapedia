import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable
import Mettapedia.Languages.Datalog.Closure
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead
import Lean.Data.Json.Printer

/-! Independent semantic programs for the ordinary-source printing gate. -/

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR

set_option maxRecDepth 32768

def main (arguments : List String) : IO Unit := do
  let [outputPath] := arguments | throw (IO.userError "expected output directory")
  let output := System.FilePath.mk outputPath
  IO.FS.createDirAll output
  let programs : List (String × Program) :=
    [("duplicates",basic),("escaped-unicode",literalContents),("signed-bounds",signedBounds),
     ("anonymous-comparisons",anonymousComparisons),
     ("empty",⟨[]⟩),
     ("empty-symbol",⟨[.declaration ⟨["Text"],[⟨"value",.symbol⟩]⟩,
       .fact ⟨["Text"],[.symbol ""]⟩,.output ["Text"]]⟩),
     ("nullary-fact",⟨[.declaration ⟨["Flag"],[]⟩,.fact ⟨["Flag"],[]⟩,.output ["Flag"]]⟩),
     ("unsigned-bounds",⟨[.declaration ⟨["U"],[⟨"x",.unsigned⟩]⟩,
       .fact ⟨["U"],[.unsigned 0]⟩,.fact ⟨["U"],[.unsigned (2^64-1)]⟩,.output ["U"]]⟩)]
  let mut expectations : List (String × List (String × List String)) := []
  for (name,program) in programs do
    unless Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.checkProgram program do
      throw (IO.userError "printer control violates its independently checked source profile")
    IO.FS.writeFile (output / (name ++ ".program.metta"))
      (CettaWire.Term.render (InferenceCettaWire.encodePattern (IRCodec.program program)))
    let reference := Closure.run Executable.policy program 10 (Closure.initial [])
    unless Closure.step Executable.policy program reference = reference do
      throw (IO.userError "reference closure did not settle within its declared bound")
    let observed := program.statements.filterMap fun statement => match statement with
      | .output relation => some (String.intercalate "." relation,
          (reference.facts.filter (·.relation == relation)).map fun fact =>
            if fact.values.isEmpty then "()" else String.intercalate "\t" (fact.values.map fun value => match value with
              | .symbol text => text | .number value => value.repr
              | .unsigned value => value.repr | .floating word => toString word))
      | _ => none
    expectations := expectations ++ [(name,observed)]
  IO.FS.writeFile (output / "programs.json") (Lean.toJson (programs.map Prod.fst)).pretty
  IO.FS.writeFile (output / "expected-outputs.json") (Lean.toJson expectations).pretty
