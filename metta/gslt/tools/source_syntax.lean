import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntaxReaders
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-! Read one explicitly selected source packet into retained syntax data,
or print that data independently. Runtime IR elaboration remains separate. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)

private structure Family where
  description : ScalarSyntaxCore.Description
  parser : ScalarSyntaxCore.Parser description
  shape : ScalarSyntaxCore.Shape description

private def family (name : String) : IO Family :=
  match name with
  | "ocaml" => pure ⟨GoldCoreSyntaxViews.ocaml, GoldCoreSyntaxReaders.ocamlParser, GoldCoreSyntaxViews.ocaml_shape⟩
  | "maude" => pure ⟨GoldCoreSyntaxViews.maude, GoldCoreSyntaxReaders.maudeParser, GoldCoreSyntaxViews.maude_shape⟩
  | "erlang" => pure ⟨GoldCoreSyntaxViews.erlang, GoldCoreSyntaxReaders.erlangParser, GoldCoreSyntaxViews.erlang_shape⟩
  | _ => throw (IO.userError "expected ocaml, maude or erlang")

private def freshOutput (path : String) : IO Unit := do
  if ← (System.FilePath.mk path).pathExists then throw (IO.userError "output already exists")

def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["read", name, sourcePath, packetPath, outputPath] =>
      freshOutput outputPath
      let chosen ← family name
      let .ok [.expression [.symbol "result", tree, .symbol "nil"]] :=
          SpaceSemantics.readSource (← IO.FS.readFile packetPath)
        | throw (IO.userError "expected exactly one explicitly selected whole-input packet")
      let input ← IO.FS.readFile sourcePath
      let some core := SourcePacketCertificate.core? chosen.description chosen.parser chosen.shape
          (stringScalars input) "SourceProgram" tree
        | throw (IO.userError "selected source packet failed independent certificate replay")
      IO.FS.writeFile outputPath (CettaWire.Term.render (InferenceCettaWire.encodePattern core) ++ "\n")
      IO.println s!"retained {input.toList.length} source scalars"
  | ["print", name, inputPath, outputPath] =>
      freshOutput outputPath
      let chosen ← family name
      let .ok [atom] := SpaceSemantics.readSource (← IO.FS.readFile inputPath)
        | throw (IO.userError "expected one retained syntax-core payload")
      let some encoded := CettaWireAtom.decode? atom | throw (IO.userError "invalid syntax wire data")
      let some core := InferenceCettaWire.decodePattern encoded | throw (IO.userError "invalid syntax constructor data")
      let some printed := ScalarSyntaxCore.printText? chosen.description "SourceProgram" core
        | throw (IO.userError "constructor data is outside the declared source grammar")
      IO.FS.writeFile outputPath printed
      IO.println s!"printed {printed.toList.length} source scalars"
  | _ => throw (IO.userError "expected read LANGUAGE SOURCE PACKET CORE or print LANGUAGE CORE SOURCE")
