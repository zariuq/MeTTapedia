import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering
import Mettapedia.Languages.Maude.Examples
import Mettapedia.Languages.Maude.PeanoNormalization

/-! Interpret every retained structural alternative against the declared
signature. A unique elaborated result is compared with independent IR fixtures.
Imported signature views are checked as interfaces, not admitted modules.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa

def settings : MaudeSourceLowering.Settings := {
  names := Maude.Examples.theories.map fun theory => (theory.name,
    {operators := theory.signature.operators.map MaudeSourceLowering.OperatorBinding.ofOperator,
     equations := theory.equations.map (·.name), rules := theory.rules.map (·.name)})
  imports := [⟨"BOOL", "truth-literal signature only; imported equation theory remains unprovided",
    ⟨["Bool"], [⟨"interface.true", "true", [], "Bool", {constructor := true}⟩,
                ⟨"interface.false", "false", [], "Bool", {constructor := true}⟩]⟩⟩] }

def sorted (theory : Maude.Theory) : Maude.Theory :=
  {theory with signature := {theory.signature with
    sorts := theory.signature.sorts.mergeSort (fun left right => left ≤ right),
    operators := theory.signature.operators.mergeSort (fun left right => left.id ≤ right.id)}}

def main (arguments : List String) : IO Unit := do
  let [sourcePath, packetPath, label] := arguments
    | throw (IO.userError "expected source, retained parser result and case")
  let .ok packets := SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "expected parser-result packets")
  let trees ← packets.mapM fun
    | .expression [.symbol "result", tree, .symbol "nil"] => pure tree
    | _ => throw (IO.userError "malformed parser-result packet")
  let input ← IO.FS.readFile sourcePath
  let attempts := trees.map fun tree => MaudeSourceLowering.lower input tree settings
  let successes := attempts.filterMap (fun result => result.toOption)
  if label == "--ambiguous" then
    unless successes.isEmpty && attempts.any (fun
      | .error reason => (reason.splitOn "ambiguous").length > 1
      | .ok _ => false) do
      throw (IO.userError "expected an explicit ambiguity refusal")
    IO.println "(MaudeSourceAmbiguity true)"
    return
  if label == "--refuse" then
    unless successes.isEmpty do throw (IO.userError "unexpected elaboration acceptance")
    IO.println "(MaudeSourceRefusal true)"
    return
  let first :: rest := successes | throw (IO.userError s!"no valid elaboration: {reprStr (attempts.map fun | .error reason => reason | .ok _ => "accepted")}")
  unless rest.all (fun other => decide (other = first)) do
    throw (IO.userError "retained alternatives have different elaborated meanings")
  let mut unresolved := 0
  for source in first.modules do
    if label == "heterogeneous_comm" then
      unless source.theory.signature.check && source.theory.signature.operators.any (fun op =>
          op.sourceName == "f" && op.arguments == ["S", "S"] && op.result == "T" && op.attributes.commutative) do
        throw (IO.userError "commutative domain/result sorts were not retained")
    else if source.theory.name != "GOLD-COMPOUND-UNIT" then
      let some reference := Maude.Examples.theories.find? (·.name == source.theory.name)
        | throw (IO.userError "unknown independent theory fixture")
      unless sorted source.theory = sorted reference do
        throw (IO.userError s!"elaborated theory differs: {reprStr source.theory}")
    if !source.importInterfaces.isEmpty then
      unresolved := unresolved + 1
      unless source.closedTheory.toOption.isNone do
        throw (IO.userError "an import signature was mistaken for an executable theory")
  if label == "core_peano" then
    let [command] := first.commands | throw (IO.userError "expected one Peano query")
    unless Maude.PeanoNormalization.reduce command.source == Maude.Examples.numeral "peano" 6 do
      throw (IO.userError "parsed Peano query does not normalize to six")
  IO.println s!"(MaudeSourceControl {reprStr label} true {trees.length} {successes.length} {first.modules.length} {first.commands.length} {unresolved})"
