import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceFrontend

/-! CHR source enters through the ordinary retained syntax boundary. The
program packet is replayed before its sentence packets use the existing
Prolog constructor interpretation and independent term reader. The sentence
texts must also cover the input, in order, up to a remainder the independent
lexer reads as layout only. Reading does not execute directives, queries or
CHR rules. Forest completeness is a separate source-catalogue obligation; for
a catalogue the certified verifier accepts, `CHRSourceCoverage` shows that
every selected interpretation of the source is read to the same program. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend

open SourcePacketView RetainedSourceLowering ScalarSyntaxCore
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)
open CHRPrologSyntax

def description := SourceSyntaxIO.description CHRPrologSyntax.description

def view := SourcePacketView.view (.ok CHRPrologSyntax.description) PrologSourceLowering.keepField

/-- The ordinal of the rule after `form`. -/
def nextOrdinal (ordinal : Nat) : CHRPrologLowering.Form → Nat
  | .rule _ => ordinal + 1
  | _ => ordinal

/-- The sentence packets in order: each one's text and form. Rules are
numbered from `ordinal`. -/
def readSentences : Nat → List SourcePacket.Packet → Except String (List (String × CHRPrologLowering.Form))
  | _, [] => .ok []
  | ordinal, sentence :: rest => do
    let text ← PrologSourceLowering.text profile "PlSentence" sentence
    let parsed ← PrologSourceFrontend.checkedLower profile text sentence
    let form ← CHRPrologLowering.form ordinal parsed.term
    let later ← readSentences (nextOrdinal ordinal form) rest
    pure ((text, form) :: later)

/-- The texts, one after another, are the input up to a remainder that the
independent lexer reads as layout only. -/
def covers (input : String) (texts : List String) : Bool :=
  let consumed := (texts.map String.toList).flatten
  consumed.isPrefixOf input.toList &&
    match Mettapedia.Logic.Prolog.ReaderLexer.scan (String.ofList (input.toList.drop consumed.length)) with
    | .ok [] => true
    | _ => false

/-- Assemble the read sentences once they cover the input. -/
def finish (input : String) (read : List (String × CHRPrologLowering.Form)) :
    Except String CHRPrologLowering.Program :=
  if covers input (read.map Prod.fst) then CHRPrologLowering.assemble (read.map Prod.snd)
  else .error "CHR source sentences do not cover the input up to layout"

def elaborate (input : String) (packet : SourcePacket.Packet) : Except String CHRPrologLowering.Program := do
  let ("chr:program", [body]) ← view packet | .error "expected a CHR source program"
  let sentences ← SourcePacketView.series view "chr:sentences" (SourcePacket.packetNodes body + 1) body
  let read ← readSentences 0 sentences
  finish input read

def read (input : String) (packet : SourcePacket.Packet) :
    Except String (Retained CHRPrologLowering.Program) :=
  match admit? description with
  | none => .error "CHR source grammar does not meet the shared admission conditions"
  | some admitted =>
      lower description admitted.parser admitted.shape (fun text tree => do
        let some reading := SourcePacketCertificate.readPacket? description admitted.parser admitted.shape
          (stringScalars text) "ChrSourceProgram" tree | .error "CHR source certificate replay failed"
        unless SourcePacketSelection.selected
            (SourcePacketSelection.allows selection (stringScalars text)) "ChrSourceProgram" reading.certificate do
          .error "CHR lexical selection failed"
        elaborate text tree) input packet

theorem read_prints {input : String} {packet : SourcePacket.Packet}
    {result : Retained CHRPrologLowering.Program} (accepted : read input packet = .ok result) :
    printText? description "ChrSourceProgram" result.sourceCore = some input := by
  unfold read at accepted
  cases admitted : admit? description with
  | none => simp [admitted] at accepted
  | some witness =>
      simp only [admitted] at accepted
      exact lower_prints accepted

#print axioms read_prints

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend
