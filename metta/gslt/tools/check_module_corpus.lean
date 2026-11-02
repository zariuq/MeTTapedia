import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode

/-! Compare decoded module data before and after a grammar change. Refusals
are recorded, never counted as parses. An accepted module must have exactly
one tree, and every previously accepted module must retain its full data. -/

open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def readPacket (path : String) : IO (List Atom) := do
  let text ← IO.FS.readFile path
  match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource text with
  | .ok [.expression (.symbol "ModuleReads" :: parses)] => pure parses
  | _ => throw (IO.userError "expected one ModuleReads packet")

def decoded (packet : Atom) : Except String (Option Mettapedia.GSLT.LanguageDef.ModuleSource.Module) :=
  match packet with
  | .expression (.symbol "LangDef:AuthoredParseAccepted" :: _) => do
      let trees ← LbnfDecode.acceptedTrees packet
      match trees with
      | [tree] => some <$> LbnfDecode.decode tree
      | _ => throw s!"accepted module has {trees.length} trees, expected one"
  | .expression (.symbol "LangDef:AuthoredParseRejected" :: _)
  | .expression (.symbol "LangDef:AuthoredLexicalRefusedV1" :: _) => pure none
  | _ => throw ("unexpected parser outcome: " ++ reprStr packet)

def main (arguments : List String) : IO Unit := do
  let [filesPath, oldPath, newPath] := arguments
    | throw (IO.userError "expected file inventory and two reader packets")
  let files := ((← IO.FS.readFile filesPath).splitOn "\n").filter (!·.isEmpty)
  let old ← readPacket oldPath
  let new ← readPacket newPath
  unless files.length == old.length && files.length == new.length do
    throw (IO.userError "reader packet count differs from inventory")
  let mut rows : List Lean.Json := []
  for (file, before, after) in files.zip (old.zip new) do
    let .ok previous := decoded before | throw (IO.userError s!"reference grammar: {file}: {reprStr (decoded before)}")
    let .ok current := decoded after | throw (IO.userError s!"current grammar: {file}: {reprStr (decoded after)}")
    if let some accepted := previous then
      unless current.any (fun result => reprStr result == reprStr accepted) do
        throw (IO.userError s!"previously accepted module changed or lost its parse: {file}")
    rows := rows ++ [Lean.Json.mkObj [
      ("file", .str file), ("previouslyAccepted", .bool previous.isSome),
      ("accepted", .bool current.isSome),
      ("sameDecodedData", .bool (previous.isSome && reprStr previous == reprStr current))]]
  IO.println (Lean.Json.arr rows.toArray).compress
