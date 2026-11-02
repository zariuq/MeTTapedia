import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxForest
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueStatus
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! File operations for the shared source-syntax interface. Modules supply
their grammar and lexical profile through the existing authored ports. -/

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

private def fresh (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then throw (IO.userError "output already exists")

def run (library : List (String × ModuleSource.Module)) (module : ModuleSource.Module)
    (arguments : List String) : IO Unit := do
  let some spec := SourceSyntax.description? library module
    | throw (IO.userError "module must supply a grammar and its LexicalProfile port")
  let some admitted := ScalarSyntaxCore.admit? (SourceSyntaxIO.description spec)
    | throw (IO.userError "source declarations do not satisfy the shared syntax-core shape")
  unless SourcePacketEncoding.checkProfile admitted.parser.plan do
    throw (IO.userError "source packet labels do not identify unique consuming parser rows")
  let filters ← match SourceSyntax.selection? library module with
    | some filters => pure filters
    | none =>
        if module.theories.any (fun theory => theory.name == "SourceSelection") then
          throw (IO.userError "declared SourceSelection port is malformed or cannot be resolved")
        else pure []
  match arguments with
  | ["catalogue",sourcePath,forestPath,identityPath,packetsPath,budget] =>
      let some rounds := budget.toNat? | throw (IO.userError "catalogue budget must be a natural number")
      let .ok packets := SpaceSemantics.readSource (← IO.FS.readFile packetsPath)
        | throw (IO.userError "malformed native source result catalogue")
      let input ← IO.FS.readFile sourcePath
      let forest ← IO.FS.readBinFile forestPath
      let identity ← IO.FS.readBinFile identityPath
      match SourceCatalogue.check spec filters input forest.data.toList identity.data.toList packets rounds with
      | .invalid => throw (IO.userError "invalid native forest or result catalogue")
      | .pending => throw (IO.userError "selected catalogue construction remains pending")
      | .different => throw (IO.userError "native results differ from the complete selected catalogue")
      | .complete => IO.println "native results cover the exact selected certificate multiset"
  | ["coverage",sourcePath,forestPath,identityPath,budget] =>
      let some rounds := budget.toNat? | throw (IO.userError "coverage budget must be a natural number")
      let input ← IO.FS.readFile sourcePath
      let forest ← IO.FS.readBinFile forestPath
      let identity ← IO.FS.readBinFile identityPath
      match SourceSyntaxForest.complete? spec input forest.data.toList identity.data.toList rounds with
      | none => throw (IO.userError "native parse coverage remains pending")
      | some false => throw (IO.userError "native forest failed independent whole-input coverage")
      | some true => IO.println "native forest is sound and complete for whole-input derivations"
  | ["forest",sourcePath,forestPath,identityPath] =>
      let input ← IO.FS.readFile sourcePath
      let forest ← IO.FS.readBinFile forestPath
      let identity ← IO.FS.readBinFile identityPath
      unless SourceSyntaxForest.check spec input forest.data.toList identity.data.toList do
        throw (IO.userError "native forest failed authored-plan representation validation")
      IO.println "native identities and exported forest families validated"
  | ["export",directory] =>
      fresh directory
      SourceSyntaxNativePlan.exportDescription spec filters directory
  | ["read",sourcePath,packetPath,outputPath] =>
      fresh outputPath
      let .ok [.expression [.symbol "result",tree,.symbol "nil"]] :=
          SpaceSemantics.readSource (← IO.FS.readFile packetPath)
        | throw (IO.userError "expected one explicitly selected whole-input packet")
      let input ← IO.FS.readFile sourcePath
      let some reading := SourcePacketCertificate.readPacket? (SourceSyntaxIO.description spec)
          admitted.parser admitted.shape (input.toList.map Char.toNat) spec.profile.startSort tree
        | throw (IO.userError "selected source packet failed independent certificate replay")
      unless SourcePacketSelection.selected (SourcePacketSelection.allows filters (input.toList.map Char.toNat))
          spec.profile.startSort reading.certificate do
        throw (IO.userError "source packet violates the declared selection policy")
      let core := reading.core
      IO.FS.writeFile outputPath (CettaWire.Term.render (InferenceCettaWire.encodePattern core))
      IO.println s!"retained {input.toList.length} source scalars"
  | ["print",corePath,outputPath] =>
      fresh outputPath
      let .ok [atom] := SpaceSemantics.readSource (← IO.FS.readFile corePath)
        | throw (IO.userError "expected one syntax-core payload")
      let some wire := CettaWireAtom.decode? atom | throw (IO.userError "invalid syntax wire data")
      let some core := InferenceCettaWire.decodePattern wire | throw (IO.userError "invalid syntax constructor data")
      let some text := SourceSyntaxIO.print? spec core
        | throw (IO.userError "constructor data is outside the source grammar")
      IO.FS.writeFile outputPath text
      IO.println s!"printed {text.toList.length} source scalars"
  | _ => throw (IO.userError "expected export DIRECTORY, read SOURCE PACKET CORE, print CORE SOURCE, forest SOURCE FOREST IDENTITY, coverage SOURCE FOREST IDENTITY ROUNDS, or catalogue SOURCE FOREST IDENTITY PACKETS ROUNDS")

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand
