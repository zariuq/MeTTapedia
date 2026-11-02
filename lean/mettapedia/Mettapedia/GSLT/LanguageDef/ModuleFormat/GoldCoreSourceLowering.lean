import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntaxReaders
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RetainedSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering

/-! The three existing source elaborators share a source-faithful entry:
an independently replayed syntax core is retained beside the unchanged
language-specific result. Runtime semantics and binding correspondence are
separate obligations of those lowerers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSourceLowering

open Mettapedia.Languages
open ScalarSyntaxCore GoldCoreSyntaxViews GoldCoreSyntaxReaders
open RetainedSourceLowering

/-- Source interpretation produces an expression tree. Arena assembly and
formation checking consume that tree without rereading source syntax. -/
def ocamlTree (input : String) (packet : SourcePacket.Packet) : Except String (Retained OCaml.TreeProgram) :=
  lower GoldCoreSyntaxViews.ocaml ocamlParser ocaml_shape OCamlSourceLowering.lowerTree input packet

def ocamlAssemble (tree : OCaml.TreeProgram) : Except String OCaml.Program :=
  Except.checkedMap (.ok tree) OCaml.TreeProgram.assemble (fun program => program.checkScope)
    "lowered program fails the independent IR formation check"

def ocaml (input : String) (packet : SourcePacket.Packet) : Except String (Retained OCaml.Program) :=
  continueWith ocamlAssemble (ocamlTree input packet)

theorem ocaml_eq_lower (input : String) (packet : SourcePacket.Packet) :
    ocaml input packet =
      lower GoldCoreSyntaxViews.ocaml ocamlParser ocaml_shape OCamlSourceLowering.lower input packet := by
  rw [ocaml, ocamlTree, lower_then]
  have same : (fun text tree => (OCamlSourceLowering.lowerTree text tree).bind ocamlAssemble) =
      OCamlSourceLowering.lower := by
    funext text tree
    unfold OCamlSourceLowering.lower
    cases OCamlSourceLowering.lowerTree text tree <;> rfl
  exact congrArg (fun elaborate =>
    lower GoldCoreSyntaxViews.ocaml ocamlParser ocaml_shape elaborate input packet) same

def erlang (input : String) (packet : SourcePacket.Packet) (entryName : String) (arguments : List Erlang.Value) :
    Except String (Retained ErlangSourceLowering.CompiledEntry) :=
  lower GoldCoreSyntaxViews.erlang erlangParser erlang_shape
    (fun text tree => ErlangSourceLowering.lower text tree entryName arguments) input packet

def maude (input : String) (packet : SourcePacket.Packet) (settings : MaudeSourceLowering.Settings) :
    Except String (Retained MaudeSourceLowering.SourceFile) :=
  lower GoldCoreSyntaxViews.maude maudeParser maude_shape
    (fun text tree => MaudeSourceLowering.lower text tree settings) input packet

theorem ocaml_retains {input : String} {packet : SourcePacket.Packet} {retained : Retained OCaml.Program}
    (accepted : ocaml input packet = .ok retained) :
    OCamlSourceLowering.lower input packet = .ok retained.lowered ∧
      printText? GoldCoreSyntaxViews.ocaml "SourceProgram" retained.sourceCore = some input := by
  rw [ocaml_eq_lower] at accepted
  exact ⟨(lower_readback accepted).2, lower_prints accepted⟩

theorem erlang_retains {input entryName : String} {packet : SourcePacket.Packet} {arguments : List Erlang.Value}
    {retained : Retained ErlangSourceLowering.CompiledEntry}
    (accepted : erlang input packet entryName arguments = .ok retained) :
    ErlangSourceLowering.lower input packet entryName arguments = .ok retained.lowered ∧
      printText? GoldCoreSyntaxViews.erlang "SourceProgram" retained.sourceCore = some input :=
  ⟨(lower_readback accepted).2, lower_prints accepted⟩

theorem maude_retains {input : String} {packet : SourcePacket.Packet} {settings : MaudeSourceLowering.Settings}
    {retained : Retained MaudeSourceLowering.SourceFile}
    (accepted : maude input packet settings = .ok retained) :
    MaudeSourceLowering.lower input packet settings = .ok retained.lowered ∧
      printText? GoldCoreSyntaxViews.maude "SourceProgram" retained.sourceCore = some input :=
  ⟨(lower_readback accepted).2, lower_prints accepted⟩

#print axioms ocaml_retains
#print axioms erlang_retains
#print axioms maude_retains

end Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSourceLowering
