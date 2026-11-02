import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntaxViews
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCertificate

/-! One checked source reader per authored Gold grammar, sharing the
scalar construction, certificate replay and independent source printer. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntaxReaders

open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)
open ScalarSyntaxCore GoldCoreSyntaxViews

def ocamlParser : Parser ocaml := (compileParser? ocaml).get (by decide +kernel)
def maudeParser : Parser maude := (compileParser? maude).get (by decide +kernel)
def erlangParser : Parser erlang := (compileParser? erlang).get (by decide +kernel)

def ocamlCore? (input : String) (packet : SourcePacket.Packet) :=
  SourcePacketCertificate.core? ocaml ocamlParser ocaml_shape (stringScalars input) "SourceProgram" packet

def maudeCore? (input : String) (packet : SourcePacket.Packet) :=
  SourcePacketCertificate.core? maude maudeParser maude_shape (stringScalars input) "SourceProgram" packet

def erlangCore? (input : String) (packet : SourcePacket.Packet) :=
  SourcePacketCertificate.core? erlang erlangParser erlang_shape (stringScalars input) "SourceProgram" packet

theorem ocaml_prints {input : String} {packet : SourcePacket.Packet} {core : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (accepted : ocamlCore? input packet = some core) : printText? ocaml "SourceProgram" core = some input := by
  have scalars := SourcePacketCertificate.core?_prints accepted
  unfold printText?
  rw [scalars]
  simp [stringScalars, List.map_map, Function.comp_def]

theorem maude_prints {input : String} {packet : SourcePacket.Packet} {core : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (accepted : maudeCore? input packet = some core) : printText? maude "SourceProgram" core = some input := by
  have scalars := SourcePacketCertificate.core?_prints accepted
  unfold printText?
  rw [scalars]
  simp [stringScalars, List.map_map, Function.comp_def]

theorem erlang_prints {input : String} {packet : SourcePacket.Packet} {core : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (accepted : erlangCore? input packet = some core) : printText? erlang "SourceProgram" core = some input := by
  have scalars := SourcePacketCertificate.core?_prints accepted
  unfold printText?
  rw [scalars]
  simp [stringScalars, List.map_map, Function.comp_def]

#print axioms ocaml_prints
#print axioms maude_prints
#print axioms erlang_prints

end Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntaxReaders
