import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceFrontend
import Mettapedia.Logic.LP.TermEquality
import Mettapedia.Logic.Prolog.ReaderProfileState
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Compare every retained native alternative with the independent reader,
including variable identity and exact source printing. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Logic.Prolog
open Mettapedia.Languages.MeTTa.PeTTa

def main (arguments : List String) : IO Unit := do
  let (dialect,sourcePath,packetPath,context) ← match arguments with
    | [dialect,sourcePath,packetPath] => pure (dialect,sourcePath,packetPath,none)
    | ["state",dialect,whole,index,sourcePath,packetPath] => pure (dialect,sourcePath,packetPath,some (whole,index))
    | _ => throw (IO.userError "expected profile, sentence and packets, optionally with state WHOLE INDEX")
  let initial ← match dialect with
    | "iso" => pure ReaderProfile.iso | "swi" => pure ReaderProfile.swi
    | _ => throw (IO.userError "unknown source profile")
  let profile ← match context with
    | none => pure initial
    | some (whole,index) =>
        let some index := index.toNat? | throw (IO.userError "invalid sentence index")
        let input ← IO.FS.readFile whole
        let .ok (sentences,_) := ReaderProfileState.readSource ReaderProfileState.noImports
            (input.toList.length+1) initial input | throw (IO.userError "invalid source profile transition")
        let some sentence := sentences[index]? | throw (IO.userError "missing sentence")
        unless sentence.text == (← IO.FS.readFile sourcePath) do throw (IO.userError "sentence origin differs")
        pure sentence.before
  let input ← IO.FS.readFile sourcePath
  let .ok reference := ReaderTerm.readOneWith profile profile.operators input
    | throw (IO.userError "reference reader refused the source")
  let .ok packets := SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "invalid packet catalogue")
  unless !packets.isEmpty do throw (IO.userError "no retained alternative")
  for packet in packets do
    let .expression [.symbol "result",tree,.symbol "nil"] := packet
      | throw (IO.userError "invalid source result")
    let retained ← match PrologSourceFrontend.read profile input tree with
      | .ok result => pure result | .error reason => throw (IO.userError reason)
    unless retained.lowered.term = reference.term do
      throw (IO.userError "constructor interpretation differs")
    unless retained.lowered.bindings == reference.bindings do
      throw (IO.userError "source variable identities differ")
    unless ScalarSyntaxCore.printText? (PrologSourceFrontend.description profile) "PlSentence" retained.sourceCore == some input do
      throw (IO.userError "source spelling changed")
  let trees ← packets.mapM fun
    | .expression [.symbol "result",tree,.symbol "nil"] => pure tree
    | _ => throw (IO.userError "invalid source result")
  let .ok agreed := PrologSourceFrontend.readAlternatives profile input trees
    | throw (IO.userError "source alternatives do not have one admitted interpretation")
  unless agreed.sourceCores.length == packets.length && decide (agreed.lowered.term = reference.term) do
    throw (IO.userError "source alternatives were lost or invented extra program meanings")
  IO.println s!"(PrologSourceControl {dialect} {packets.length} true true true)"
