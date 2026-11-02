import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologDatalog
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable
import Mettapedia.Logic.Prolog.ReaderProfileState

/-! ISO and SWI common-clause syntax enters the same Datalog IR and its
existing preparation boundary. Controls include source-sharing failures. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologDatalogControls

open Mettapedia.Logic.Prolog ReaderProfile
open Mettapedia.Languages.Datalog

def declarations : List RelationDeclaration :=
  [⟨["edge"],[⟨"x",.symbol⟩,⟨"y",.symbol⟩]⟩, ⟨["path"],[⟨"x",.symbol⟩,⟨"y",.symbol⟩]⟩]

def source := "edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). path(X,Z) :- edge(X,Y),path(Y,Z)."

def expected : Program := ⟨declarations.map .declaration ++ [
  .fact ⟨["edge"],[.symbol "a",.symbol "b"]⟩,
  .fact ⟨["edge"],[.symbol "b",.symbol "c"]⟩,
  .rule ⟨⟨["path"],[.var "X",.var "Y"]⟩,[.atom ⟨["edge"],[.var "X",.var "Y"]⟩]⟩,
  .rule ⟨⟨["path"],[.var "X",.var "Z"]⟩,[.atom ⟨["edge"],[.var "X",.var "Y"]⟩,
    .atom ⟨["path"],[.var "Y",.var "Z"]⟩]⟩]⟩

def read (profile : Profile) (input : String) : Option Program := do
  let (sentences,_) ← (ReaderProfileState.readSource ReaderProfileState.noImports 64 profile input).toOption
  PrologDatalog.program? declarations (sentences.map (·.form))

#guard read iso source = some expected
#guard read swi source = some expected
#guard (DatalogIR.Executable.prepare expected []).toOption.map (·.source) = some expected
#guard read iso "path(X,Y) :- edge(X,Y),!." = none
#guard read iso "path(X,Y) :- edge(X,Y);edge(Y,X)." = none
#guard read iso "edge(f(a),b)." = none
#guard read iso "path(X,Y) :- edge(X,Z)." = none
#guard read iso ":- op(600,xfy,likes)." = none
#guard read swi "edge(\"a\",b)." = none
#guard read iso "edge(a,b,b)." = none

def forgedSharing : SourceSignature.Clause := {
  head := SourceSignature.predicate "path" [SourceSignature.var "X" 0,SourceSignature.var "Y" 1]
  body := SourceSignature.call "edge" [SourceSignature.var "X" 2,SourceSignature.var "Y" 1] }
#guard (PrologDatalog.clause? forgedSharing).isNone

def changes := ReaderProfileState.readSource ReaderProfileState.noImports 16 iso
  ":- op(600,xfy,likes). a likes b. :- op(0,xfy,likes)."
#guard changes.toOption.any (fun (sentences,final) => sentences.length == 3 &&
  sentences[1]?.any (fun sentence => sentence.before.operators.any (·.name == "likes")) &&
  !(final.operators.any (·.name == "likes")))

def quoteChanges := ReaderProfileState.readSource ReaderProfileState.noImports 16 swi
  ":- set_prolog_flag(double_quotes,codes). \"ab\"."
#guard quoteChanges.toOption.any (fun (sentences,final) => sentences.length == 2 && final.doubleQuotes == .codes)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologDatalogControls
