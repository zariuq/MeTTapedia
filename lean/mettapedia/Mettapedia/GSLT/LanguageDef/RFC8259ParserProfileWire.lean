import Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT

/-!
# RFC 8259 parser-profile wire projection

The external ParserPack compiler consumes the canonical rendering of the same
lexical profile whose classes and structural schema are analyzed in Lean.
-/

namespace Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileWire

open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderList (entries : List String) : String :=
  entries.foldr (fun entry rest => s!"(LCons {entry} {rest})") "LNil"

private def renderCodepoints (codepoints : List Nat) : String :=
  renderList (codepoints.map toString)

private def renderClass (declaration : LexicalClassDecl) : String :=
  match declaration.kind with
  | .points codepoints =>
      s!"(LexicalClassPoints {quote declaration.name} {renderCodepoints codepoints})"
  | .except excluded =>
      s!"(LexicalClassExcept {quote declaration.name} {renderCodepoints excluded})"

private def renderState (state : LexicalStateDecl) : String :=
  s!"(LexicalState {quote state.resultSort} {quote state.className} " ++
    s!"{quote state.ruleLabel})"

/-- Canonical wire rendering of a parser-profile layer. -/
def renderProfile (profile : ParserProfileLayer) : String :=
  "(GSLTParserProfileLayerV1\n" ++
    s!"  {quote profile.name}\n" ++
    s!"  {quote profile.startSort}\n" ++
    s!"  {renderList (profile.classes.map renderClass)}\n" ++
    s!"  {renderList (profile.states.map renderState)})\n"

/-- Canonical generated wire text for the authored RFC 8259 parser profile. -/
def wire : String := renderProfile rfc8259ParserProfile

theorem wire_nonempty : wire != "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_nonempty

end Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileWire
