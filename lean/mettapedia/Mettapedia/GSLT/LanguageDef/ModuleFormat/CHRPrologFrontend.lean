import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceFrontend

/-! CHR source enters through the ordinary retained syntax boundary. The
program packet is replayed before its sentence packets use the existing
Prolog constructor interpretation and independent term reader. Reading does
not execute directives, queries or CHR rules. Forest completeness remains a
separate source-catalogue obligation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend

open SourcePacketView RetainedSourceLowering ScalarSyntaxCore
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)
open CHRPrologSyntax

def description := SourceSyntaxIO.description CHRPrologSyntax.description

def view := SourcePacketView.view (.ok CHRPrologSyntax.description) PrologSourceLowering.keepField

def elaborate (_input : String) (packet : SourcePacket.Packet) : Except String CHRPrologLowering.Program := do
  let ("chr:program", [body]) ← view packet | .error "expected a CHR source program"
  let sentences ← SourcePacketView.series view "chr:sentences" (SourcePacket.packetNodes body + 1) body
  let mut forms := []
  let mut ordinal := 0
  for sentence in sentences do
    let text ← PrologSourceLowering.text profile "PlSentence" sentence
    let parsed ← PrologSourceFrontend.checkedLower profile text sentence
    let form ← CHRPrologLowering.form ordinal parsed.term
    match form with
    | .rule _ => ordinal := ordinal + 1
    | _ => pure ()
    forms := form :: forms
  CHRPrologLowering.assemble forms.reverse

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
